import Hurst.ActualQuadratureFinal
import Hurst.GridErrorRate
import Hurst.WeightEnergy
import Hurst.ActiveSetReindex
import Hurst.OptimalActiveRowDensity

/-!
# Discharging `hFrozenPert` via the weight-energy route

This file discharges the dimension-weighted frozen-perturbation hypothesis

```
hFrozenPert : card * ‖A_n - F_n‖_F² → 0
```

of `Hurst.ActualQuadratureFinal.actualQ1_trace_pow_tendsto_of_frozenPert`
(the obstruction blocking the corrected quadrature route), using the
weight-energy analysis run against the VERIFIED per-entry bound
`actualQ1_frozenError_entry_le`:

* **Per entry** (verified, no diagonal exception):
  `|Δ_ij| ≤ 4 * S^{2-2ft-1} * |u_i| * gridCovarianceError n` with
  `S = n * δ`, `u_i = actualQ1ChainWeight = S * w_i` (the `S`-scaled local
  polynomial weight).  Note the error carries the ROW weight `u_i` only.
* **Weight energy** (verified, `localPolynomialWeights_energy`):
  `S * ∑ w_i² ≤ D` eventually, so `∑_i u_i² = S² ∑ w_{σ(i)}² ≤ S² * D / S = D * S`
  (the active-index map `localWeightActiveIndex` is injective).
* **Frobenius assembly** (`frob_sq_of_entry_le`): with `m = card ≤ 3S`,

```
card * ‖Δ‖_F² ≤ 16 * (3S)² * S^{2(2-2ft)-2} * g² * (D * S)
             = 144 * D * S^{2(2-2ft)+1} * g²,
g = gridCovarianceError b C₀ n = C₀ (1 + log 2n) (n⁻¹ + n^{2b-2}).
```

## The honest bandwidth threshold (exponent bookkeeping)

`S^{2(2-2ft)+1} g²` splits as
`(1+log 2n)² [S^{2(2-2ft)+1} n⁻² + S^{2(2-2ft)+1} n^{4b-4}]`.

* Part 1: `S^{2(2-2ft)+1} ≤ n^{2(2-2ft)+1}`, so part 1 is
  `O((1+log)² n^{3-4ft})`, which tends to 0 exactly under `f t > 3 / 4` — the
  existing long-memory hypothesis `hlong`.
* Part 2: `S^{2(2-2ft)+1} n^{4b-4} = δ^{2(2-2ft)+1} n^{2(2-2ft)+4b-3}`.  The
  grid-error exponent `b` dominates the point value (`f t ≤ b` since
  `f` maps into `Icc a b`), so `2(2-2ft)+4b-3 = 4b+1-4ft ≥ 1` is never
  negative: NO pure-bandwidth condition on `b` alone (such as the route
  sketch's `ψ + 2b < 3/2`, which assumed the symmetric bound
  `|Δ_ij| ≤ 4 S^{ψ-1} |u_i| |u_j| g` carrying both weights) can make part 2
  vanish.  The vanishing is governed by the RATE of `δ`, so the master theorem
  takes the exact decay hypothesis

```
hdecay : (1+log 2n)² * S_n^{2(2-2ft)+1} * n^{4b-4} → 0
```

  and the polynomial-bandwidth corollary specializes it: for `δ n = n^{-γ}`,
  `hdecay` holds iff `4b + 1 - 4 f t < γ * (2 (2 - 2 f t) + 1)`, which is
  satisfiable for EVERY Hölder range `b < 1` by taking
  `γ > (4b + 1 - 4 f t) / (2 (2 - 2 f t) + 1) < 1`.

## Contents

1. `frob_sq_of_entry_le` : the generic Frobenius-assembly lemma
   (`row-weight` structure: `card * ‖Δ‖_F²` from a per-entry row-weight bound).
2. `chainWeight_sq_sum_le` : the ℓ² energy of the active chain weights from
   `localPolynomialWeights_energy` + injectivity of `localWeightActiveIndex`.
3. `frozenPert_card_tendsto_of_weightEnergy` : the discharge —
   `card * ‖A_n - F_n‖_F² → 0` from `hdecay` (all other inputs ordinary).
4. `frozenPert_card_tendsto_powBandwidth` : the `δ n = n^{-γ}` specialization;
   explicit bandwidth condition `4b + 1 - 4 f t < γ * (2 (2 - 2 f t) + 1)`.
5. `actualQ1_trace_pow_tendsto_of_weightEnergy` : the composition —
   `actualQ1_trace_pow_tendsto_of_frozenPert` with `hFrozenPert` discharged.
   The remaining quadrature-run input is `hFrozenQuad` (frozen-kernel
   quadrature), separate per the module scope of `Hurst.ActualQuadratureFinal`.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Set MeasureTheory Filter Matrix
open scoped BigOperators Topology RealInnerProductSpace Matrix.Norms.Frobenius

namespace Hurst

/-! ## Private helpers -/

private theorem sq_le_sq_of_abs_le {x B : ℝ} (h : |x| ≤ B) : x ^ 2 ≤ B ^ 2 := by
  rcases abs_le.mp h with ⟨h1, h2⟩
  nlinarith

private theorem frobenius_norm_eq_sqrt_sum_sq {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) :
    ‖A‖ = Real.sqrt (∑ i : Fin m, ∑ j : Fin m, A i j ^ 2) := by
  rw [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  congr 1
  exact Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => by rw [Real.norm_eq_abs, Real.rpow_two, sq_abs]

/-! ## The generic Frobenius-assembly lemma -/

/-- **Frobenius assembly from a row-weight entry bound.**  If every entry of
`A - F` obeys `|Δ_ij| ≤ 4 c |u i| g` (the row weight `u i` only — this is the
shape of `actualQ1_frozenError_entry_le`), the row-sum of weights is at most
`E` and the cardinality is at most `mS`, then

`card * ‖A - F‖_F² ≤ 16 * mS² * c² * g² * E`. -/
theorem frob_sq_of_entry_le {m : ℕ} (A F : Matrix (Fin m) (Fin m) ℝ) (u : Fin m → ℝ)
    (c g E mS : ℝ) (hΔ : ∀ i j, |(A - F) i j| ≤ 4 * c * |u i| * g)
    (hE : ∑ i, u i ^ 2 ≤ E) (hm : (m : ℝ) ≤ mS)
    (hc0 : 0 ≤ c) (hg0 : 0 ≤ g) (hE0 : 0 ≤ E) (hm0 : 0 ≤ (m : ℝ)) (hmS0 : 0 ≤ mS) :
    (m : ℝ) * ‖A - F‖ ^ 2 ≤ 16 * mS ^ 2 * c ^ 2 * g ^ 2 * E := by
  have hFsq : ‖A - F‖ ^ 2 = ∑ i : Fin m, ∑ j : Fin m, (A - F) i j ^ 2 := by
    rw [frobenius_norm_eq_sqrt_sum_sq,
      Real.sq_sqrt (show (0 : ℝ) ≤ ∑ i : Fin m, ∑ j : Fin m, (A - F) i j ^ 2 by
        positivity)]
  have hper : ∀ i j : Fin m, (A - F) i j ^ 2 ≤ 16 * c ^ 2 * g ^ 2 * u i ^ 2 := by
    intro i j
    have habs : (4 * c * |u i| * g) ^ 2 = (4 * c * g) ^ 2 * |u i| ^ 2 := by ring
    calc (A - F) i j ^ 2 ≤ (4 * c * |u i| * g) ^ 2 := sq_le_sq_of_abs_le (hΔ i j)
      _ = 16 * c ^ 2 * g ^ 2 * u i ^ 2 := by rw [habs, sq_abs]; ring
  have hrow : ∀ i : Fin m, ∑ j : Fin m, u i ^ 2 = (m : ℝ) * u i ^ 2 := by
    intro i
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
  have hsum : ∑ i : Fin m, ∑ j : Fin m, (A - F) i j ^ 2
      ≤ 16 * c ^ 2 * g ^ 2 * ((m : ℝ) * ∑ i : Fin m, u i ^ 2) := by
    have hstep : (m : ℝ) * ∑ i : Fin m, u i ^ 2 = ∑ i : Fin m, ((m : ℝ) * u i ^ 2) := by
      rw [Finset.mul_sum]
    calc ∑ i : Fin m, ∑ j : Fin m, (A - F) i j ^ 2
        ≤ ∑ i : Fin m, ∑ j : Fin m, 16 * c ^ 2 * g ^ 2 * u i ^ 2 :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hper i j
      _ = ∑ i : Fin m, ((m : ℝ) * (16 * c ^ 2 * g ^ 2 * u i ^ 2)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
      _ = 16 * c ^ 2 * g ^ 2 * ∑ i : Fin m, ((m : ℝ) * u i ^ 2) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = 16 * c ^ 2 * g ^ 2 * ((m : ℝ) * ∑ i : Fin m, u i ^ 2) := by rw [hstep]
  have hm2 : (m : ℝ) * (m : ℝ) ≤ mS * mS := mul_le_mul hm hm hm0 hmS0
  have h3 : (m : ℝ) * (m : ℝ) * ∑ i, u i ^ 2 ≤ mS * mS * E :=
    mul_le_mul hm2 hE (Finset.sum_nonneg fun i _ => sq_nonneg _)
      (mul_nonneg hmS0 hmS0)
  calc (m : ℝ) * ‖A - F‖ ^ 2
      = (m : ℝ) * (∑ i : Fin m, ∑ j : Fin m, (A - F) i j ^ 2) := by rw [hFsq]
    _ ≤ (m : ℝ) * (16 * c ^ 2 * g ^ 2 * ((m : ℝ) * ∑ i : Fin m, u i ^ 2)) :=
        mul_le_mul_of_nonneg_left hsum hm0
    _ = 16 * c ^ 2 * g ^ 2 * ((m : ℝ) * (m : ℝ) * ∑ i, u i ^ 2) := by ring
    _ ≤ 16 * c ^ 2 * g ^ 2 * (mS * mS * E) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 16 * mS ^ 2 * c ^ 2 * g ^ 2 * E := by ring

/-! ## The chain-weight ℓ² energy -/

/-- **The chain-weight ℓ² energy.**  With `u_i = S * w_i` the `S`-scaled local
polynomial weight (`actualQ1ChainWeight`), the verified weight-energy control
`S * ∑ w² ≤ D` (`localPolynomialWeights_energy`) gives
`∑_{i active} u_i² ≤ S * D`: the sum over the active window injects into the
full index type (`localWeightActiveIndex_injective`). -/
theorem chainWeight_sq_sum_le (f : ℝ → ℝ) (r n : ℕ) (δ t : ℝ) (D : ℝ)
    (hD : (n : ℝ) * δ * ∑ i, localPolynomialWeights r n 1 δ t i ^ 2 ≤ D)
    (hS0 : 0 < (n : ℝ) * δ) :
    ∑ i : Fin (localWeightActiveSet n 1 δ t).card,
      actualQ1ChainWeight f r n δ t i ^ 2 ≤ (n : ℝ) * δ * D := by
  have hunfold : ∀ i : Fin (localWeightActiveSet n 1 δ t).card,
      actualQ1ChainWeight f r n δ t i
        = (n : ℝ) * δ * localPolynomialWeights r n 1 δ t
            (localWeightActiveIndex n 1 δ t i) := fun _ => rfl
  have hbase : ∑ i : Fin (localWeightActiveSet n 1 δ t).card,
      actualQ1ChainWeight f r n δ t i ^ 2
      = ∑ i : Fin (localWeightActiveSet n 1 δ t).card,
        (((n : ℝ) * δ) * localPolynomialWeights r n 1 δ t
            (localWeightActiveIndex n 1 δ t i)) ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hunfold i]
  refine le_trans (le_of_eq hbase) ?_
  have h1 : ∑ i : Fin (localWeightActiveSet n 1 δ t).card,
      (((n : ℝ) * δ) * localPolynomialWeights r n 1 δ t
          (localWeightActiveIndex n 1 δ t i)) ^ 2
      = ((n : ℝ) * δ) ^ 2 * ∑ i : Fin (localWeightActiveSet n 1 δ t).card,
        localPolynomialWeights r n 1 δ t (localWeightActiveIndex n 1 δ t i) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [mul_pow]
  have hinj := localWeightActiveIndex_injective n 1 δ t
  have h2 : ∑ i : Fin (localWeightActiveSet n 1 δ t).card,
      localPolynomialWeights r n 1 δ t (localWeightActiveIndex n 1 δ t i) ^ 2
      ≤ ∑ k : Fin (n - 1), localPolynomialWeights r n 1 δ t k ^ 2 := by
    have himage : ∑ x ∈ Finset.univ.image (localWeightActiveIndex n 1 δ t),
        localPolynomialWeights r n 1 δ t x ^ 2
        = ∑ i : Fin (localWeightActiveSet n 1 δ t).card,
          localPolynomialWeights r n 1 δ t (localWeightActiveIndex n 1 δ t i) ^ 2 :=
      Finset.sum_image (f := fun k : Fin (n - 1) => localPolynomialWeights r n 1 δ t k ^ 2)
        (g := localWeightActiveIndex n 1 δ t) (s := Finset.univ)
        (fun x _ y _ hxy => hinj hxy)
    rw [← himage]
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun x _ _ => sq_nonneg _
  calc ∑ i : Fin (localWeightActiveSet n 1 δ t).card,
        (((n : ℝ) * δ) * localPolynomialWeights r n 1 δ t
            (localWeightActiveIndex n 1 δ t i)) ^ 2
      = ((n : ℝ) * δ) ^ 2 * ∑ i : Fin (localWeightActiveSet n 1 δ t).card,
          localPolynomialWeights r n 1 δ t (localWeightActiveIndex n 1 δ t i) ^ 2 := h1
    _ ≤ ((n : ℝ) * δ) ^ 2 * ∑ k : Fin (n - 1), localPolynomialWeights r n 1 δ t k ^ 2 :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg ((n : ℝ) * δ))
    _ = ((n : ℝ) * δ) * (((n : ℝ) * δ) *
            ∑ k : Fin (n - 1), localPolynomialWeights r n 1 δ t k ^ 2) := by ring
    _ ≤ ((n : ℝ) * δ) * D := mul_le_mul_of_nonneg_left hD hS0.le

/-! ## The discharge -/

/-- **The frozen-perturbation discharge (weight-energy route).**  Under the
long-memory hypothesis `3 / 4 < f t` (which kills the `n⁻¹`-part of the grid
covariance error) and the explicit decay hypothesis

```
hdecay : (1 + log (2n))² * S_n^{2(2-2ft)+1} * n^{4b-4} → 0,   S_n = n * δ_n,
```

the dimension-weighted frozen perturbation vanishes:
`card * ‖A_n - F_n‖_F² → 0`.  This is exactly hypothesis `hFrozenPert` of
`actualQ1_trace_pow_tendsto_of_frozenPert`; see the module docstring for the
exponent bookkeeping (no pure-bandwidth condition on `b` alone can work, since
the verified entry bound couples `f t ≤ b`; the vanishing is governed by the
rate of `δ`). -/
theorem frozenPert_card_tendsto_of_weightEnergy
    (p a b M : ℝ) (r : ℕ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (hM : 0 ≤ M) (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n : ℕ in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (hdecay : Tendsto (fun n : ℕ => (1 + Real.log (2 * (n : ℝ))) ^ 2 *
      ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) + 1) * ((n : ℝ) ^ ((4 : ℝ) * b - 4)))
      atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
        ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
        ‖actualQ1NormalizedActualMatrix f hf r n (δ n) t -
          actualQ1NormalizedFrozenMatrix f hf r n (δ n) t‖ ^ 2) atTop (𝓝 0) := by
  -- the long-memory value sits in (3/4, 1) (via the Hölder range bound)
  have hftle : f t ≤ b := (hF ht).2
  have hft1 : f t < 1 := lt_of_le_of_lt hftle hb
  -- the frozen-error constant and the grid-error vanishing
  obtain ⟨C₀, hC₀, hentry⟩ := actualQ1_frozenError_entry_le p a b M hp ha hb hab hM f hf hF t
  have hgridsmall : ∀ᶠ n : ℕ in atTop, gridCovarianceError b C₀ n < 1 / 2 :=
    (gridCovarianceError_tendsto b C₀ hb).eventually
      (Iio_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  -- the weight-energy constant
  obtain ⟨N₀, hN₀, D, hD0, henergy⟩ := localPolynomialWeights_energy r 1
  -- the bandwidth-smallness events
  have hδhalf : ∀ᶠ n : ℕ in atTop, δ n < 1 / 2 :=
    hδ0.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  -- the master bound: card * ‖Δ‖² ≤ (288 C₀² D) * (K1 + K2)
  have hbound : ∀ᶠ n : ℕ in atTop,
      ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
        ‖actualQ1NormalizedActualMatrix f hf r n (δ n) t -
          actualQ1NormalizedFrozenMatrix f hf r n (δ n) t‖ ^ 2
      ≤ (288 * C₀ ^ 2 * D) *
        ((1 + Real.log (2 * (n : ℝ))) ^ 2 *
            ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) + 1) * ((n : ℝ) ^ ((-2 : ℝ))) +
          (1 + Real.log (2 * (n : ℝ))) ^ 2 *
            ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) + 1) * ((n : ℝ) ^ ((4 : ℝ) * b - 4))) := by
    filter_upwards [eventually_ge_atTop 1, hδpos, hδhalf,
      hN.eventually_ge_atTop (max N₀ 1), hgridsmall] with n hn1 hδ hδhalf hSbig hgsml
    have hn0 : 0 < n := by omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    have hS0 : 0 < (n : ℝ) * δ n := mul_pos hnR hδ
    have hS0le : 0 ≤ (n : ℝ) * δ n := hS0.le
    have hS1 : (1 : ℝ) ≤ (n : ℝ) * δ n := le_trans (le_max_right _ _) hSbig
    have hSle : (n : ℝ) * δ n ≤ (n : ℝ) := by
      have h := mul_le_mul_of_nonneg_left (le_of_lt hδhalf) hnR.le
      have h2 : (n : ℝ) * (1 / 2) ≤ (n : ℝ) := by linarith
      exact le_trans h h2
    have hc1pos : 0 ≤ ((n : ℝ) * δ n) ^ (2 - 2 * f t - 1) := Real.rpow_nonneg hS0le _
    have hg0 : 0 ≤ gridCovarianceError b C₀ n := by
      have hlog : (0 : ℝ) ≤ Real.log (2 * (n : ℝ)) :=
        Real.log_nonneg (show (1 : ℝ) ≤ 2 * (n : ℝ) by norm_cast; omega)
      unfold gridCovarianceError
      exact mul_nonneg (mul_nonneg hC₀ (by linarith))
        (add_nonneg (Real.rpow_nonneg hnR.le _) (Real.rpow_nonneg hnR.le _))
    have hE0 : 0 ≤ ((n : ℝ) * δ n) * D := mul_nonneg hS0le hD0.le
    -- Step 1: the entrywise frozen-error bound
    have hΔ : ∀ i j : Fin (localWeightActiveSet n 1 (δ n) t).card,
        |(actualQ1NormalizedActualMatrix f hf r n (δ n) t -
            actualQ1NormalizedFrozenMatrix f hf r n (δ n) t) i j|
          ≤ 4 * ((n : ℝ) * δ n) ^ (2 - 2 * f t - 1) *
            |actualQ1ChainWeight f r n (δ n) t i| * gridCovarianceError b C₀ n := by
      intro i j
      have h := hentry n hn0 (δ n) hδ (le_of_lt hgsml) i j
      rw [Matrix.sub_apply]
      exact h
    -- Step 2: the chain-weight energy ∑ u_i² ≤ D * S
    have hw : ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        actualQ1ChainWeight f r n (δ n) t i ^ 2 ≤ ((n : ℝ) * δ n) * D := by
      refine chainWeight_sq_sum_le f r n (δ n) t D ?_ hS0
      have hinst := henergy n hn0 (by omega) (δ n) t hδ (le_of_lt hδhalf)
        (show t ∈ Icc (0 : ℝ) 1 from ⟨ht.1.le, ht.2.le⟩)
        (le_trans (le_max_left _ _) hSbig)
      linarith [hinst]
    -- Step 3: the active-card bound m ≤ 3S
    have hm3 : ((localWeightActiveSet n 1 (δ n) t).card : ℝ) ≤ 3 * ((n : ℝ) * δ n) :=
      localWeightActiveSet_card n 1 hn0 (δ n) t hδ hS1
    -- Step 4: the Frobenius assembly
    have hinst : ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
        ‖actualQ1NormalizedActualMatrix f hf r n (δ n) t -
          actualQ1NormalizedFrozenMatrix f hf r n (δ n) t‖ ^ 2
        ≤ 16 * (3 * ((n : ℝ) * δ n)) ^ 2 *
          (((n : ℝ) * δ n) ^ (2 - 2 * f t - 1)) ^ 2 *
          (gridCovarianceError b C₀ n) ^ 2 * (((n : ℝ) * δ n) * D) := by
      refine frob_sq_of_entry_le
        (actualQ1NormalizedActualMatrix f hf r n (δ n) t)
        (actualQ1NormalizedFrozenMatrix f hf r n (δ n) t)
        (fun i => actualQ1ChainWeight f r n (δ n) t i)
        (((n : ℝ) * δ n) ^ (2 - 2 * f t - 1)) (gridCovarianceError b C₀ n)
        (((n : ℝ) * δ n) * D) (3 * ((n : ℝ) * δ n)) hΔ hw hm3 hc1pos hg0 hE0
        (Nat.cast_nonneg _) (mul_nonneg (by norm_num) hS0le)
    -- Step 5: the S-exponent combination  S^{2(2-2ft)+1} = S³ * (S^{2-2ft-1})²
    have hScomb : ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) + 1)
        = ((n : ℝ) * δ n) ^ 3 * (((n : ℝ) * δ n) ^ (2 - 2 * f t - 1)) ^ 2 := by
      have h3 : ((n : ℝ) * δ n) ^ 3 = ((n : ℝ) * δ n) ^ ((3 : ℝ)) :=
        (Real.rpow_natCast ((n : ℝ) * δ n) 3).symm
      have h2 : (((n : ℝ) * δ n) ^ (2 - 2 * f t - 1)) ^ 2
          = ((n : ℝ) * δ n) ^ ((2 : ℝ) * (2 - 2 * f t - 1)) := by
        rw [pow_two, ← Real.rpow_add hS0 (2 - 2 * f t - 1) (2 - 2 * f t - 1)]
        congr 1
        ring
      rw [h3, h2, ← Real.rpow_add hS0 (3 : ℝ) ((2 : ℝ) * (2 - 2 * f t - 1))]
      congr 1
      ring
    -- Step 6: the grid-error square split
    have hgd : gridCovarianceError b C₀ n = C₀ * (1 + Real.log (2 * (n : ℝ))) *
        ((n : ℝ) ^ (-1 : ℝ) + (n : ℝ) ^ (2 * b - 2)) := rfl
    have he1 : ((n : ℝ) ^ (-1 : ℝ)) ^ 2 = (n : ℝ) ^ ((-2 : ℝ)) := by
      rw [pow_two, ← Real.rpow_add hnR (-1 : ℝ) (-1 : ℝ)]
      congr 1
      ring
    have he2 : ((n : ℝ) ^ (2 * b - 2)) ^ 2 = (n : ℝ) ^ ((4 : ℝ) * b - 4) := by
      rw [pow_two, ← Real.rpow_add hnR (2 * b - 2) (2 * b - 2)]
      congr 1
      ring
    have hpair : ((n : ℝ) ^ (-1 : ℝ) + (n : ℝ) ^ (2 * b - 2)) ^ 2
        ≤ 2 * ((n : ℝ) ^ ((-2 : ℝ)) + (n : ℝ) ^ ((4 : ℝ) * b - 4)) := by
      have hXY : ((n : ℝ) ^ (-1 : ℝ) + (n : ℝ) ^ (2 * b - 2)) ^ 2
          ≤ 2 * ((n : ℝ) ^ (-1 : ℝ)) ^ 2 + 2 * ((n : ℝ) ^ (2 * b - 2)) ^ 2 := by
        nlinarith [sq_nonneg ((n : ℝ) ^ (-1 : ℝ) - (n : ℝ) ^ (2 * b - 2))]
      rw [he1, he2] at hXY
      rw [mul_add]
      exact hXY
    have hgsq : (gridCovarianceError b C₀ n) ^ 2
        ≤ 2 * C₀ ^ 2 * (1 + Real.log (2 * (n : ℝ))) ^ 2 *
          ((n : ℝ) ^ ((-2 : ℝ)) + (n : ℝ) ^ ((4 : ℝ) * b - 4)) := by
      have hpref : (0 : ℝ) ≤ (C₀ * (1 + Real.log (2 * (n : ℝ)))) ^ 2 := by positivity
      rw [hgd, mul_pow]
      calc (C₀ * (1 + Real.log (2 * (n : ℝ)))) ^ 2 *
              ((n : ℝ) ^ (-1 : ℝ) + (n : ℝ) ^ (2 * b - 2)) ^ 2
          ≤ (C₀ * (1 + Real.log (2 * (n : ℝ)))) ^ 2 *
              (2 * ((n : ℝ) ^ ((-2 : ℝ)) + (n : ℝ) ^ ((4 : ℝ) * b - 4))) :=
            mul_le_mul_of_nonneg_left hpair hpref
        _ = 2 * C₀ ^ 2 * (1 + Real.log (2 * (n : ℝ))) ^ 2 *
              ((n : ℝ) ^ ((-2 : ℝ)) + (n : ℝ) ^ ((4 : ℝ) * b - 4)) := by ring
    -- the master chain
    have hX : 16 * (3 * ((n : ℝ) * δ n)) ^ 2 *
        (((n : ℝ) * δ n) ^ (2 - 2 * f t - 1)) ^ 2 *
        (gridCovarianceError b C₀ n) ^ 2 * (((n : ℝ) * δ n) * D)
        = 144 * D * ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) + 1) *
          (gridCovarianceError b C₀ n) ^ 2 := by rw [hScomb]; ring
    have hmult : (0 : ℝ) ≤ 144 * D * ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) + 1) :=
      mul_nonneg (mul_nonneg (by norm_num) hD0.le)
        (Real.rpow_nonneg hS0le ((2 : ℝ) * (2 - 2 * f t) + 1))
    calc ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
          ‖actualQ1NormalizedActualMatrix f hf r n (δ n) t -
            actualQ1NormalizedFrozenMatrix f hf r n (δ n) t‖ ^ 2
        ≤ 16 * (3 * ((n : ℝ) * δ n)) ^ 2 *
            (((n : ℝ) * δ n) ^ (2 - 2 * f t - 1)) ^ 2 *
            (gridCovarianceError b C₀ n) ^ 2 * (((n : ℝ) * δ n) * D) := hinst
      _ = 144 * D * ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) + 1) *
            (gridCovarianceError b C₀ n) ^ 2 := hX
      _ ≤ 144 * D * ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) + 1) *
            (2 * C₀ ^ 2 * (1 + Real.log (2 * (n : ℝ))) ^ 2 *
              ((n : ℝ) ^ ((-2 : ℝ)) + (n : ℝ) ^ ((4 : ℝ) * b - 4))) :=
          mul_le_mul_of_nonneg_left hgsq hmult
      _ = (288 * C₀ ^ 2 * D) *
            ((1 + Real.log (2 * (n : ℝ))) ^ 2 *
                ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) + 1) * ((n : ℝ) ^ ((-2 : ℝ))) +
              (1 + Real.log (2 * (n : ℝ))) ^ 2 *
                ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) + 1) *
                ((n : ℝ) ^ ((4 : ℝ) * b - 4))) := by ring
  -- Part 1: (1+log)² S^{2(2-2ft)+1} n⁻² → 0 under hlong
  have hK1 : Tendsto (fun n : ℕ => (1 + Real.log (2 * (n : ℝ))) ^ 2 *
      ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) + 1) * ((n : ℝ) ^ ((-2 : ℝ)))) atTop (𝓝 0) := by
    have hexp : (0 : ℝ) < 2 * (2 - 2 * f t) + 1 := by linarith [hlong, hft1]
    have hmain : Tendsto (fun n : ℕ => (1 + Real.log (2 * (n : ℝ))) ^ 2 *
        (n : ℝ) ^ (2 * (2 - 2 * f t) - 1)) atTop (𝓝 0) :=
      mesh_log_power_rpow_tendsto (2 * (2 - 2 * f t) - 1) (by linarith) 2
    have hK1pos : ∀ᶠ n : ℕ in atTop, (0 : ℝ) ≤ (1 + Real.log (2 * (n : ℝ))) ^ 2 *
        ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) + 1) * ((n : ℝ) ^ ((-2 : ℝ))) := by
      filter_upwards [eventually_ge_atTop 1, hδpos] with n hn1 hδ
      have hlog : (0 : ℝ) ≤ Real.log (2 * (n : ℝ)) :=
        Real.log_nonneg (show (1 : ℝ) ≤ 2 * (n : ℝ) by norm_cast; omega)
      exact mul_nonneg (mul_nonneg (pow_nonneg (by linarith) _)
        (Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg n) (le_of_lt hδ)) _))
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    refine squeeze_zero' hK1pos ?_ hmain
    · filter_upwards [hδpos, hδhalf, eventually_ge_atTop 1] with n hδ hδhalf hn1
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
      have hSle : (n : ℝ) * δ n ≤ (n : ℝ) := by
        have h := mul_le_mul_of_nonneg_left (le_of_lt hδhalf) hnR.le
        have h2 : (n : ℝ) * (1 / 2) ≤ (n : ℝ) := by linarith
        exact le_trans h h2
      have hpow : ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) + 1)
          ≤ (n : ℝ) ^ (2 * (2 - 2 * f t) + 1) :=
        Real.rpow_le_rpow (mul_nonneg hnR.le (le_of_lt hδ)) hSle hexp.le
      calc (1 + Real.log (2 * (n : ℝ))) ^ 2 * ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) + 1) *
            (n : ℝ) ^ ((-2 : ℝ))
          ≤ (1 + Real.log (2 * (n : ℝ))) ^ 2 * (n : ℝ) ^ (2 * (2 - 2 * f t) + 1) *
            (n : ℝ) ^ ((-2 : ℝ)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow
              (sq_nonneg ((1 : ℝ) + Real.log (2 * (n : ℝ)))))
            (Real.rpow_nonneg (Nat.cast_nonneg n) ((-2 : ℝ)))
        _ = (1 + Real.log (2 * (n : ℝ))) ^ 2 * (n : ℝ) ^ (2 * (2 - 2 * f t) - 1) := by
          rw [mul_assoc, ← Real.rpow_add hnR (2 * (2 - 2 * f t) + 1) ((-2 : ℝ)),
            show ((2 : ℝ) * (2 - 2 * f t) + 1) + (-2 : ℝ) = 2 * (2 - 2 * f t) - 1 by ring]
  -- Part 2 is exactly hdecay
  have hK2 : Tendsto (fun n : ℕ => (1 + Real.log (2 * (n : ℝ))) ^ 2 *
      ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) + 1) * ((n : ℝ) ^ ((4 : ℝ) * b - 4)))
      atTop (𝓝 0) := hdecay
  refine squeeze_zero' (Eventually.of_forall fun _ => ?_) hbound ?_
  · exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  · have h := (hK1.add hK2).const_mul (288 * C₀ ^ 2 * D)
    simp only [mul_zero, add_zero] at h
    exact h

/-! ## The polynomial-bandwidth specialization -/

/-- **The discharge under a polynomial bandwidth rate.**  For the polynomial
bandwidth `δ n = n^{-γ}` (a standard ordinary bandwidth-rate assumption), the
decay hypothesis of `frozenPert_card_tendsto_of_weightEnergy` holds exactly
under the explicit bandwidth condition

```
4 * b + 1 - 4 * f t < γ * (2 * (2 - 2 * f t) + 1),
```

which is satisfiable for EVERY Hölder range `b < 1` by taking
`γ > (4b + 1 - 4 f t) / (2 (2 - 2 f t) + 1) < 1` (at `γ = 1` the right side is
`2 (2 - 2 f t) + 1 ≥ 4 - 4 f t > 4 b + 1 - 4 f t` since `b < 1`). -/
theorem frozenPert_card_tendsto_powBandwidth
    (p a b M : ℝ) (r : ℕ) (γ : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (hM : 0 ≤ M) (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hband : (4 : ℝ) * b + 1 - 4 * f t < γ * (2 * (2 - 2 * f t) + 1)) :
    Tendsto (fun n : ℕ =>
        ((localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card : ℝ) *
        ‖actualQ1NormalizedActualMatrix f hf r n ((n : ℝ) ^ (-γ)) t -
          actualQ1NormalizedFrozenMatrix f hf r n ((n : ℝ) ^ (-γ)) t‖ ^ 2) atTop (𝓝 0) := by
  -- δ n = n^{-γ} satisfies the three ordinary bandwidth events
  have hδpos : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) ^ (-γ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn1
    exact Real.rpow_pos_of_pos (by exact_mod_cast hn1) _
  have hδ0 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-γ)) atTop (𝓝 0) := by
    have h := mesh_log_power_rpow_tendsto (-γ) (by linarith) 0
    refine h.congr' (Eventually.of_forall fun n => ?_)
    rw [pow_zero, one_mul]
  have hN : Tendsto (fun n : ℕ => (n : ℝ) * (n : ℝ) ^ (-γ)) atTop atTop := by
    have h : Tendsto (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) - γ)) atTop atTop :=
      (tendsto_rpow_atTop (show (0 : ℝ) < 1 - γ by linarith)).comp
        tendsto_natCast_atTop_atTop
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn1
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [show ((1 : ℝ) - γ) = ((1 : ℝ) + (-γ)) by ring, Real.rpow_add hnR (1 : ℝ) (-γ),
      Real.rpow_one]
  -- the decay hypothesis from the bandwidth condition
  have hdecay : Tendsto (fun n : ℕ => (1 + Real.log (2 * (n : ℝ))) ^ 2 *
      ((n : ℝ) * (n : ℝ) ^ (-γ)) ^ (2 * (2 - 2 * f t) + 1) *
      ((n : ℝ) ^ ((4 : ℝ) * b - 4))) atTop (𝓝 0) := by
    have hneg : ((1 : ℝ) - γ) * (2 * (2 - 2 * f t) + 1) + ((4 : ℝ) * b - 4) < 0 := by
      have hexp : ((1 : ℝ) - γ) * (2 * (2 - 2 * f t) + 1)
          = (2 * (2 - 2 * f t) + 1) - γ * (2 * (2 - 2 * f t) + 1) := by ring
      linarith [hexp, hband]
    have hmain := mesh_log_power_rpow_tendsto
      (((1 : ℝ) - γ) * (2 * (2 - 2 * f t) + 1) + ((4 : ℝ) * b - 4)) hneg 2
    refine hmain.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn1
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
    have hSn : ((n : ℝ) * (n : ℝ) ^ (-γ)) = (n : ℝ) ^ ((1 : ℝ) - γ) := by
      rw [show ((1 : ℝ) - γ) = ((1 : ℝ) + (-γ)) by ring, Real.rpow_add hnR (1 : ℝ) (-γ),
        Real.rpow_one]
    have hpow : ((n : ℝ) ^ ((1 : ℝ) - γ)) ^ (2 * (2 - 2 * f t) + 1)
        = (n : ℝ) ^ (((1 : ℝ) - γ) * (2 * (2 - 2 * f t) + 1)) := by
      rw [← Real.rpow_mul hnR.le]
    rw [hSn, hpow, Real.rpow_add hnR
      (((1 : ℝ) - γ) * (2 * (2 - 2 * f t) + 1)) (((4 : ℝ) * b - 4))]
    ring
  exact frozenPert_card_tendsto_of_weightEnergy p a b M r hp ha hb hab hM f hf hF t ht hlong
    (fun n => (n : ℝ) ^ (-γ)) hδpos hδ0 hN hdecay

/-! ## The composition corollary -/

/-- **The corrected-route endpoint with `hFrozenPert` discharged.**  This is
`actualQ1_trace_pow_tendsto_of_frozenPert` with its dimension-weighted
frozen-perturbation hypothesis replaced by the weight-energy discharge
`frozenPert_card_tendsto_of_weightEnergy`: all inputs are ordinary (the
long-memory hypothesis `3 / 4 < f t`, the ordinary bandwidth events on `δ`,
and the explicit decay hypothesis `hdecay` — under a polynomial bandwidth
`δ n = n^{-γ}` exactly the bandwidth condition
`4b + 1 - 4 f t < γ * (2 (2 - 2 f t) + 1)` of
`frozenPert_card_tendsto_powBandwidth`), modulo the frozen-quadrature run
`hFrozenQuad`, which is the separate documented quadrature residue of
`Hurst.ActualQuadratureFinal`. -/
theorem actualQ1_trace_pow_tendsto_of_weightEnergy
    (p a b M : ℝ) (r : ℕ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (hM : 0 ≤ M) (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n : ℕ in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (hdecay : Tendsto (fun n : ℕ => (1 + Real.log (2 * (n : ℝ))) ^ 2 *
      ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) + 1) * ((n : ℝ) ^ ((4 : ℝ) * b - 4)))
      atTop (𝓝 0))
    (R : ℕ → ℕ) (hR : ∀ᶠ n in atTop, 1 ≤ R n)
    (hcut : Tendsto (fun n : ℕ => ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 2) *
      ((localWeightActiveSet n 1 (δ n) t).card : ℝ) * (2 * (R n : ℝ) + 1))
      atTop (𝓝 0))
    (henv : ∀ Ccov ≥ 0, ∀ Ctail ≥ 0, ∀ L > 0, Tendsto (fun n : ℕ =>
      q1ActualLongTailEnvelope b Ccov Ctail L M (f t) n (δ n) ((n : ℝ) * δ n)
        (R n)) atTop (𝓝 0))
    (Bω : ℝ) (hBω : ∀ z ∈ Set.Icc (-1 : ℝ) 1, |equivalentKernel r z| ≤ Bω)
    (Cref : ℝ)
    (hCref : ∀ (S : ℝ) (m : ℕ), 1 ≤ S → (m : ℝ) ≤ 3 * S →
      realScaleMeshEnergy S
        (rankRieszKernel S (2 - 2 * f t) (f t * (2 * f t - 1)) :
          Fin m → Fin m → ℝ) ≤ Cref)
    (hcard : ∀ n : ℕ, 0 < (localWeightActiveSet n 1 (δ n) t).card)
    (k : ℕ)
    (hFrozenQuad : Tendsto (fun n : ℕ => Matrix.trace
        ((actualQ1NormalizedFrozenMatrix f hf r n (δ n) t) ^ k)) atTop
      (𝓝 (weightedRieszCycleIntegral k (2 - 2 * f t)
        (f t * (2 * f t - 1)) (equivalentKernel r)))) :
    Tendsto (fun n : ℕ => Matrix.trace
        ((actualQ1NormalizedActualMatrix f hf r n (δ n) t) ^ k)) atTop
      (𝓝 (weightedRieszCycleIntegral k (2 - 2 * f t)
        (f t * (2 * f t - 1)) (equivalentKernel r))) :=
  actualQ1_trace_pow_tendsto_of_frozenPert p a b M r hp ha hb hab hM f hf hF t ht hlong
    δ hδpos hδ0 hN R hR hcut henv Bω hBω Cref hCref hcard
    (frozenPert_card_tendsto_of_weightEnergy p a b M r hp ha hb hab hM f hf hF t ht hlong
      δ hδpos hδ0 hN hdecay)
    k hFrozenQuad

end Hurst
