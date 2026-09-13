import Hurst.ActualQuadratureConfluence

/-!
# Actual kernel band asymptotics: the corrected quadrature route

## Route correction (supersedes the Frobenius-perturbation bridge)

The previous route compared the ACTUAL matrix `A n` (entries
`S ^ ψ * vectorCorrelation` of the first-stride increments) to the mesh-Riesz
matrix `U n` (entries `c * (S / x) ^ ψ` for rank distance `x`, and `0` on the
diagonal) entrywise.  That bridge is structurally dead:

* (diagonal obstruction) `A`-diagonal entries are `S ^ ψ * corr(i,i)`, i.e.
  variance-scale and nonvanishing (they tend to `S ^ ψ`), while `U`-diagonal
  entries are `0`; a per-entry Frobenius bound therefore carries a nonvanishing
  diagonal energy `m * S ^ (2 * ψ)` that diverges under the quadrature
  normalization.
* (short-range constants) at finite rank distance `x = O(1)` the actual kernel
  agrees with the pure power law only up to an `O(1)` relative error
  (the frozen cross-lag correlation `firstIncrementCrossLagCorrelation h0 h0 x`
  has its own short-range constants; the pure power law `c * x ^ (-ψ)` is only
  the large-`x` asymptotic, and the `16 * x⁻¹` term in
  `hurstHolder_q1_active_scaled_actual_tail_error` reflects exactly this).

## The corrected route

Run the quadrature architecture DIRECTLY for the actual kernel, comparing it
not to the pure power law but to ITS OWN frozen-kernel approximation
`actualQ1FrozenApproxKernel`: `S ^ ψ` times the inner product of the unit-norm
frozen increments.  The proved perturbation lemma
`hurstHolder_stride_first_correlation_perturbation` bounds the difference
uniformly over ALL pairs (no band restriction, diagonal included):

`|A i j - S ^ ψ * ⟪frozen_i, frozen_j⟫| ≤ 4 * S ^ ψ * gridCovarianceError n`,
with `gridCovarianceError → 0`.  Both sides share the same diagonal structure,
so no diagonal removal is needed on the difference.  The corrected chain is:

1. (this file, deliverable 1) uniform kernel asymptotics
   `actual_q1_kernel_frozen_uniform_approx`: the actual kernel equals its
   frozen approximation with uniform relative error `4 * gridCovarianceError`
   (which is `o(1)`); the diagonal correlation tends to `1` uniformly
   (`actual_q1_diagonal_correlation_sub_one_le`).
2. (this file, deliverable 2) the actual-kernel band predicate
   `actual_q1_kernel_band_predicate_tendsto_zero`: under the same cutoff
   hypothesis `S ^ (2ψ - 2) * card * (2R + 1) → 0` used for the Riesz band
   predicate, the band energy of `A - frozen-approx` tends to `0`.
3. (this file, deliverable 3) the diagonal contribution lemma
   `actual_q1_diagonal_trace_contribution_tendsto_zero`: under the
   `S ^ (ψ - 1)` normalization of `actualQ1NormalizedActualMatrix` (the matrix
   whose power traces are the eigenvalue power sums via
   `trace_pow_weightedFeatureQuadraticMatrix_eq`), the pure-diagonal cycles
   `∑ i, (matrix i i) ^ k` tend to `0` for `k ≥ 2` when `ψ < 1 / 2` (i.e.
   `3 / 4 < f t`): explicitly `≤ 3 * (S ^ (k(1-ψ)-1))⁻¹ * W ^ k` with
   `W → U` bounded, hence `→ 0`.  So the actual kernel's nonvanishing diagonal
   contributes a VANISHING amount: no diagonal removal needed on the actual
   side (the answer to the "diagonal contribution" question is: → 0, not a
   finite term).
4. (continuation, not in this file) the frozen approximation is itself a
   rank-distance kernel `S ^ ψ * firstIncrementCrossLagCorrelation(h_i, h_j, x)`
   (`normalizedFrozenIncrement_grid_inner_eq_cross_dist`), which agrees with
   the pure power law at relative error `O(1/x)` uniformly on the far band
   (existing tail machinery
   `hurstHolder_q1_active_scaled_actual_tail_error_le_envelope`); combined with
   2 (on-band) and the continuum Riesz quadrature (the diagonal is a
   measure-zero set of the continuum limit), this yields the actual-kernel
   quadrature: power traces of `actualQ1NormalizedActualMatrix` converge to the
   Riesz spectrum power sums, and `HcoeffBridge` applies unchanged.

## Honest scope note

The near-diagonal relative asymptotics to the PURE power law demanded by the
original plan is FALSE at finite rank distance (different short-range
constants: `O(1)` relative error at `x = O(1)`); the correct uniform
asymptotics is the absolute-error statement of deliverable 1 to the frozen
kernel, which is what the band predicate (deliverable 2) consumes.  The pure
power law re-enters only at relative error `O(1/x)` on the far band, where the
existing tail machinery already applies.
-/

noncomputable section

open Set MeasureTheory Filter Matrix
open scoped Topology RealInnerProductSpace

namespace Hurst

/-! ## Private helpers -/

/-- Band-cardinality: the rank-distance-`R` band around `i` has at most
`2 * R + 1` entries. -/
private theorem bandCardLem {m : ℕ} (R : ℕ) (i : Fin m) :
    (Finset.univ.filter (fun j : Fin m => Nat.dist j.val i.val ≤ R)).card ≤
      2 * R + 1 := by
  let T : Finset (Fin m) := Finset.univ.filter
    (fun j => Nat.dist j.val i.val ≤ R)
  have hc := finite_lattice_interval_card T
    ((i.val : ℝ) - R) ((i.val : ℝ) + R) (by linarith) (by
      intro j hj
      have hd : Nat.dist j.val i.val ≤ R := (Finset.mem_filter.mp hj).2
      have hleft : j.val ≤ i.val + R := by
        rcases le_total i.val j.val with hij | hji
        · rw [Nat.dist_eq_sub_of_le_right hij] at hd
          omega
        · omega
      have hright : i.val ≤ j.val + R := by
        rcases le_total j.val i.val with hji | hij
        · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le_right hji] at hd
          omega
        · omega
      have hleftR : (j.val : ℝ) ≤ i.val + R := by exact_mod_cast hleft
      have hrightR : (i.val : ℝ) ≤ j.val + R := by exact_mod_cast hright
      constructor <;> linarith)
  have hcR : (T.card : ℝ) ≤ (2 * R + 1 : ℕ) := by
    convert hc using 1 <;> push_cast <;> ring
  exact_mod_cast hcR

private theorem abs_le_sq_le {x B : ℝ} (h : |x| ≤ B) : x ^ 2 ≤ B ^ 2 := by
  have hB : 0 ≤ B := (abs_nonneg x).trans h
  have h2 : x ^ 2 = x * x := by ring
  have hB2 : B ^ 2 = B * B := by ring
  rw [h2, hB2]
  rcases abs_le.mp h with ⟨h1, h3⟩
  nlinarith

private theorem pow_le_pow_of_abs_le {x y : ℝ} (h : |x| ≤ y) (k : ℕ) :
    x ^ k ≤ y ^ k := by
  have hy : 0 ≤ y := (abs_nonneg x).trans h
  have hmono : ∀ j : ℕ, |x| ^ j ≤ y ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        rw [pow_succ, pow_succ]
        calc |x| ^ j * |x| ≤ y ^ j * |x| := mul_le_mul_of_nonneg_right ih (abs_nonneg x)
          _ ≤ y ^ j * y := mul_le_mul_of_nonneg_left h (pow_nonneg hy j)
  calc x ^ k ≤ |x| ^ k := by rw [← abs_pow]; exact le_abs_self _
    _ ≤ y ^ k := hmono k

private theorem tendsto_le_tendsto_zero {f g : ℕ → ℝ}
    (h : ∀ᶠ n in atTop, |f n| ≤ g n) (hg : Tendsto g atTop (𝓝 0)) :
    Tendsto f atTop (𝓝 0) := by
  have habs : Tendsto (fun n => |f n|) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) h hg
  have hneg : Tendsto (fun n => -|f n|) atTop (𝓝 0) := by simpa using habs.neg
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hneg habs
    (Pi.le_def.mpr fun i => by
      have h1 := le_abs_self (-(f i))
      have h2 := abs_neg (f i)
      linarith)
    (Pi.le_def.mpr fun i => le_abs_self _)

/-- `x ^ (-(n : ℝ)) = x⁻¹ ^ n` for `x ≥ 0`. -/
private theorem rpow_neg_nat_eq_inv_pow {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    x ^ (-(n : ℝ)) = x⁻¹ ^ n := by
  rw [Real.rpow_neg hx, Real.rpow_natCast, inv_pow]

/-- `x * (x ^ β)⁻¹ = (x ^ (β - 1))⁻¹` for positive `x`. -/
private theorem rpow_inv_mul {x : ℝ} (hx : 0 < x) {β : ℝ} :
    x * (x ^ β)⁻¹ = (x ^ (β - 1))⁻¹ := by
  have h1 : x * (x ^ β)⁻¹ = x ^ ((1 : ℝ) + -β) := by
    rw [Real.rpow_add hx, Real.rpow_one, ← Real.rpow_neg hx.le]
  have h2 : (x ^ (β - 1))⁻¹ = x ^ (-(β - 1)) := (Real.rpow_neg hx.le _).symm
  calc x * (x ^ β)⁻¹ = x ^ ((1 : ℝ) + -β) := h1
    _ = x ^ (-(β - 1)) := by congr 1; ring
    _ = (x ^ (β - 1))⁻¹ := h2.symm

/-! ## The frozen comparison kernel of the actual kernel -/

/-- **The actual kernel's own power-law comparison kernel.**  `S ^ ψ` times the
inner product of the unit-norm frozen increments at the two active indices
(`ψ = 2 - 2 * f t`).  By `normalizedFrozenIncrement_grid_inner_eq_cross_dist`
this is `S ^ ψ * firstIncrementCrossLagCorrelation(h_i, h_j, rank dist)`; it
shares the diagonal structure of the actual kernel (value `S ^ ψ` on the
diagonal), which is exactly what the Frobenius-perturbation route lacked. -/
def actualQ1FrozenApproxKernel (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (n : ℕ) (δ t S : ℝ)
    (i j : Fin (localWeightActiveSet n 1 δ t).card) : ℝ :=
  S ^ (2 - 2 * f t) * ⟪
    normalizedFrozenIncrement
      (midpointSampleHurst f hf.1 n
        (strideFirstLeft n 1 (localWeightActiveIndex n 1 δ t i)))
      (grid n (localWeightActiveIndex n 1 δ t i).val) (((1 : ℕ) : ℝ) / n),
    normalizedFrozenIncrement
      (midpointSampleHurst f hf.1 n
        (strideFirstLeft n 1 (localWeightActiveIndex n 1 δ t j)))
      (grid n (localWeightActiveIndex n 1 δ t j).val) (((1 : ℕ) : ℝ) / n)⟫

/-! ## Deliverable (1): the uniform kernel asymptotics -/

/-- **Uniform actual-kernel asymptotics (key analytic input).**  The actual
long-memory kernel agrees with its frozen-kernel approximation at uniform
relative error `4 * gridCovarianceError → 0`, over ALL pairs — near-diagonal,
band, and diagonal alike.  This replaces the (false) near-diagonal
relative-asymptotics to the pure power law. -/
theorem actual_q1_kernel_frozen_uniform_approx
    (p a b M : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) :
    ∃ C ≥ 0, ∀ n : ℕ, 0 < n → ∀ δ S : ℝ, 0 < δ → 0 < S →
      gridCovarianceError b C n ≤ 1 / 2 →
      ∀ i j : Fin (localWeightActiveSet n 1 δ t).card,
      |q1ActualLongActiveKernel f hf n δ t S (2 - 2 * f t) i j -
          actualQ1FrozenApproxKernel f hf n δ t S i j| ≤
        4 * S ^ (2 - 2 * f t) * gridCovarianceError b C n := by
  obtain ⟨C, hC, hpert⟩ :=
    hurstHolder_stride_first_correlation_perturbation
      p a b M hp ha hb hab hM f hf hF 1 (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro n hn δ S hδ hS0 hsmall i j
  have hS0' : 0 ≤ S ^ (2 - 2 * f t) := Real.rpow_nonneg hS0.le _
  have hpert' := hpert n hn hsmall
    (localWeightActiveIndex n 1 δ t i) (localWeightActiveIndex n 1 δ t j)
  unfold q1ActualLongActiveKernel actualQ1FrozenApproxKernel
  rw [← mul_sub, abs_mul, abs_of_nonneg hS0']
  exact (mul_le_mul_of_nonneg_left hpert' hS0').trans_eq (by ring)

/-- **Uniform diagonal correlation asymptotics.**  The actual kernel's diagonal
entries are `S ^ ψ * corr(i,i)` with `corr(i,i) → 1` uniformly (the frozen
increments have unit norm), so the diagonal of the actual kernel is `S ^ ψ`
up to `4 * gridCovarianceError`. -/
theorem actual_q1_diagonal_correlation_sub_one_le
    (p a b M : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) :
    ∃ C ≥ 0, ∀ n : ℕ, 0 < n → ∀ δ : ℝ, 0 < δ →
      gridCovarianceError b C n ≤ 1 / 2 →
      ∀ i : Fin (localWeightActiveSet n 1 δ t).card,
      |vectorCorrelation
          (gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
            (localWeightActiveIndex n 1 δ t i))
          (gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
            (localWeightActiveIndex n 1 δ t i)) - 1| ≤
        4 * gridCovarianceError b C n := by
  obtain ⟨C, hC, hpert⟩ :=
    hurstHolder_stride_first_correlation_perturbation
      p a b M hp ha hb hab hM f hf hF 1 (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro n hn δ hδ hsmall i
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hAA : ⟪normalizedFrozenIncrement
        (midpointSampleHurst f hf.1 n
          (strideFirstLeft n 1 (localWeightActiveIndex n 1 δ t i)))
        (grid n (localWeightActiveIndex n 1 δ t i).val)
        (((1 : ℕ) : ℝ) / n),
      normalizedFrozenIncrement
        (midpointSampleHurst f hf.1 n
          (strideFirstLeft n 1 (localWeightActiveIndex n 1 δ t i)))
        (grid n (localWeightActiveIndex n 1 δ t i).val)
        (((1 : ℕ) : ℝ) / n)⟫
      = 1 := by
    rw [real_inner_self_eq_norm_sq]
    exact normalizedFrozenIncrement_norm_sq _ _ _ (div_pos (by norm_num) hnR)
  have h1 := hpert n hn hsmall
    (localWeightActiveIndex n 1 δ t i) (localWeightActiveIndex n 1 δ t i)
  rw [hAA] at h1
  exact h1

/-! ## Deliverable (2): the actual-kernel band predicate -/

/-- **The actual-kernel band predicate.**  Under the same cutoff hypothesis
used for the Riesz-side band predicate, the band energy of the difference
between the actual kernel and ITS OWN frozen approximation tends to `0`.  Both
sides share the same diagonal structure, so the band predicate is satisfiable
where the entrywise comparison to the pure power law was not. -/
theorem actual_q1_kernel_band_predicate_tendsto_zero
    (p a b M : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ)
    (δ : ℕ → ℝ) (R : ℕ → ℕ)
    (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hS : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (hR : ∀ᶠ n in atTop, 1 ≤ R n)
    (hcut : Tendsto (fun n : ℕ =>
      ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 2) *
        ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
        (2 * (R n : ℝ) + 1)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      realScaleMeshBandEnergy ((n : ℝ) * δ n) (R n)
        (fun i j => q1ActualLongActiveKernel f hf n (δ n) t
            ((n : ℝ) * δ n) (2 - 2 * f t) i j -
          actualQ1FrozenApproxKernel f hf n (δ n) t
            ((n : ℝ) * δ n) i j)) atTop (𝓝 0) := by
  obtain ⟨C, hC, happrox⟩ :=
    actual_q1_kernel_frozen_uniform_approx p a b M hp ha hb hab hM f hf hF t
  have hg := gridCovarianceError_tendsto b C hb
  have hsmall : ∀ᶠ n in atTop, gridCovarianceError b C n ≤ 1 / 2 :=
    hg.eventually_le_const (by norm_num)
  have hnEv : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_gt_atTop 0
  have hS1ev : ∀ᶠ n : ℕ in atTop, 1 ≤ (n : ℝ) * δ n := hS.eventually_ge_atTop 1
  have hbound : ∀ᶠ n : ℕ in atTop,
      realScaleMeshBandEnergy ((n : ℝ) * δ n) (R n)
        (fun i j => q1ActualLongActiveKernel f hf n (δ n) t
            ((n : ℝ) * δ n) (2 - 2 * f t) i j -
          actualQ1FrozenApproxKernel f hf n (δ n) t
            ((n : ℝ) * δ n) i j)
      ≤ 16 * (gridCovarianceError b C n) ^ 2 *
        (((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 2) *
          ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
          (2 * (R n : ℝ) + 1)) := by
    filter_upwards [hδpos, hS1ev, hR, hsmall, hnEv] with n hδ hS1n hRn hsm hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    set Sn := (n : ℝ) * δ n with hSn
    set psif := 2 - 2 * f t with hpsif
    have hSn0 : 0 < Sn := by rw [hSn]; exact mul_pos hnR hδ
    have hB0 : 0 ≤ 4 * Sn ^ psif * gridCovarianceError b C n := by
      refine mul_nonneg (mul_nonneg (by norm_num)
        (Real.rpow_nonneg hSn0.le psif)) ?_
      unfold gridCovarianceError
      have hlog := Real.log_nonneg
        (show (1 : ℝ) ≤ 2 * n by norm_cast; omega)
      positivity
    have hentry : ∀ i j : Fin (localWeightActiveSet n 1 (δ n) t).card,
        |q1ActualLongActiveKernel f hf n (δ n) t Sn psif i j -
            actualQ1FrozenApproxKernel f hf n (δ n) t Sn i j| ≤
          4 * Sn ^ psif * gridCovarianceError b C n :=
      happrox n hn (δ n) Sn hδ hSn0 hsm
    have hinner : ∀ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        ∑ j ∈ Finset.univ.filter
            (fun j : Fin (localWeightActiveSet n 1 (δ n) t).card =>
              Nat.dist j.val i.val ≤ R n),
          (q1ActualLongActiveKernel f hf n (δ n) t Sn psif i j -
              actualQ1FrozenApproxKernel f hf n (δ n) t Sn i j) ^ 2
          ≤ (2 * (R n : ℝ) + 1) *
            (4 * Sn ^ psif * gridCovarianceError b C n) ^ 2 := by
      intro i
      calc ∑ j ∈ Finset.univ.filter
              (fun j : Fin (localWeightActiveSet n 1 (δ n) t).card =>
                Nat.dist j.val i.val ≤ R n),
            (q1ActualLongActiveKernel f hf n (δ n) t Sn psif i j -
                actualQ1FrozenApproxKernel f hf n (δ n) t Sn i j) ^ 2
          ≤ ∑ _j ∈ Finset.univ.filter
              (fun j : Fin (localWeightActiveSet n 1 (δ n) t).card =>
                Nat.dist j.val i.val ≤ R n),
            (4 * Sn ^ psif * gridCovarianceError b C n) ^ 2 :=
            Finset.sum_le_sum fun j _ => abs_le_sq_le (hentry i j)
        _ = ((Finset.univ.filter
              (fun j : Fin (localWeightActiveSet n 1 (δ n) t).card =>
                Nat.dist j.val i.val ≤ R n)).card : ℝ) *
            (4 * Sn ^ psif * gridCovarianceError b C n) ^ 2 := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (2 * (R n : ℝ) + 1) *
            (4 * Sn ^ psif * gridCovarianceError b C n) ^ 2 := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact_mod_cast bandCardLem (R n) i
    have hsq4 : (4 * Sn ^ psif * gridCovarianceError b C n) ^ 2
        = 16 * (Sn ^ psif) ^ 2 * (gridCovarianceError b C n) ^ 2 := by
      rw [mul_pow, mul_pow]
      norm_num
    have hrpow : (Sn ^ psif) ^ 2 * Sn ^ (-2 : ℝ) = Sn ^ (2 * psif - 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hSn0.le, ← Real.rpow_add hSn0]
      congr 1
      ring
    have hinv2 : Sn ^ (-2 : ℝ) = Sn⁻¹ ^ 2 := rpow_neg_nat_eq_inv_pow hSn0.le 2
    calc realScaleMeshBandEnergy Sn (R n)
            (fun i j => q1ActualLongActiveKernel f hf n (δ n) t Sn psif i j -
              actualQ1FrozenApproxKernel f hf n (δ n) t Sn i j)
        = Sn⁻¹ ^ 2 * ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
            ∑ j ∈ Finset.univ.filter
                (fun j : Fin (localWeightActiveSet n 1 (δ n) t).card =>
                  Nat.dist j.val i.val ≤ R n),
              (q1ActualLongActiveKernel f hf n (δ n) t Sn psif i j -
                  actualQ1FrozenApproxKernel f hf n (δ n) t Sn i j) ^ 2 := rfl
      _ ≤ Sn⁻¹ ^ 2 * (((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
            ((2 * (R n : ℝ) + 1) *
              (4 * Sn ^ psif * gridCovarianceError b C n) ^ 2)) := by
          refine mul_le_mul_of_nonneg_left
            (le_trans (Finset.sum_le_sum fun i _ => hinner i) ?_)
            (pow_nonneg (inv_nonneg.mpr hSn0.le) 2)
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
            Fintype.card_fin]
      _ = 16 * (gridCovarianceError b C n) ^ 2 *
            (Sn ^ (2 * psif - 2) *
              ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
              (2 * (R n : ℝ) + 1)) := by
          rw [hsq4, ← hrpow, hinv2]
          ring
  have h16 : Tendsto (fun n : ℕ => 16 * (gridCovarianceError b C n) ^ 2)
      atTop (𝓝 0) := by
    have h2 : Tendsto (fun n : ℕ => (gridCovarianceError b C n) ^ 2) atTop (𝓝 0) :=
      by simpa using Tendsto.congr'
          (Eventually.of_forall fun n => (pow_two _).symm) (hg.mul hg)
    simpa using h2.const_mul 16
  have hprod : Tendsto (fun n : ℕ => 16 * (gridCovarianceError b C n) ^ 2 *
      (((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 2) *
        ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
        (2 * (R n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using h16.mul hcut
  refine tendsto_le_tendsto_zero (hbound.mono fun n hn => ?_) hprod
  have hnn : 0 ≤ realScaleMeshBandEnergy ((n : ℝ) * δ n) (R n)
      (fun i j => q1ActualLongActiveKernel f hf n (δ n) t
          ((n : ℝ) * δ n) (2 - 2 * f t) i j -
        actualQ1FrozenApproxKernel f hf n (δ n) t
          ((n : ℝ) * δ n) i j) := by
    unfold realScaleMeshBandEnergy
    positivity
  rw [abs_of_nonneg hnn]
  exact hn

/-! ## Deliverable (3): the diagonal contribution under the quadrature
normalization -/

/-- **Diagonal trace contribution tends to zero.**  Under the `S ^ (ψ - 1)`
normalization of `actualQ1NormalizedActualMatrix` — the exact entrywise form of
the spectral matrix whose power traces are the eigenvalue power sums
(`trace_pow_weightedFeatureQuadraticMatrix_eq`) — the pure-diagonal cycles
`∑ i, (matrix i i) ^ k` of the ACTUAL matrix tend to `0` for `k ≥ 2` when
`ψ < 1 / 2` (i.e. `3 / 4 < f t`).  Explicitly the contribution is bounded by
`3 * (S ^ (k * (1 - ψ) - 1))⁻¹ * W ^ k` with `W → U` bounded, hence `→ 0`:
the actual kernel's nonvanishing diagonal (variance `S ^ ψ` per entry,
attenuated by the normalization to `S ^ (ψ - 1) * u_i`) contributes a
vanishing amount to the second-chaos power sums, and NO diagonal removal is
needed on the actual side. -/
theorem actual_q1_diagonal_trace_contribution_tendsto_zero
    (p a b M : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (hlong : 3 / 4 < f t)
    (r k : ℕ) (hk : 2 ≤ k) (U : ℝ) (hU0 : 0 ≤ U)
    (δ : ℕ → ℝ)
    (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hS : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (hU : ∀ᶠ n in atTop,
      ∀ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
      |actualQ1ChainWeight f r n (δ n) t i| ≤ U) :
    Tendsto (fun n : ℕ => ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
      (actualQ1NormalizedActualMatrix f hf r n (δ n) t i i) ^ k)
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hdiag⟩ :=
    actual_q1_diagonal_correlation_sub_one_le p a b M hp ha hb hab hM f hf hF t
  have hg := gridCovarianceError_tendsto b C hb
  have hsmall : ∀ᶠ n in atTop, gridCovarianceError b C n ≤ 1 / 2 :=
    hg.eventually_le_const (by norm_num)
  set psif := 2 - 2 * f t with hpsif
  have hpsihalf : psif < 1 / 2 := by
    rw [hpsif]
    linarith
  have h1p : (1 : ℝ) / 2 < 1 - psif := by linarith
  have hKpos : (0 : ℝ) < k * (1 - psif) - 1 := by
    have h2k : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have hprod : 2 * (1 - psif) ≤ k * (1 - psif) :=
      mul_le_mul_of_nonneg_right h2k (by linarith)
    have hring : 2 * (1 - psif) = (1 - psif) + (1 - psif) := by ring
    linarith
  have hW : Tendsto (fun n : ℕ => U * (1 + 4 * gridCovarianceError b C n))
      atTop (𝓝 U) := by
    have h4 : Tendsto (fun n : ℕ => 4 * gridCovarianceError b C n)
        atTop (𝓝 (4 * 0)) := hg.const_mul 4
    have h1 : Tendsto (fun n : ℕ => (1 : ℝ) + 4 * gridCovarianceError b C n)
        atTop (𝓝 1) := by simpa using tendsto_const_nhds.add h4
    simpa using h1.const_mul U
  have hinv : Tendsto (fun n : ℕ =>
      (((n : ℝ) * δ n) ^ (k * (1 - psif) - 1))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_rpow_atTop hKpos).comp hS)
  have hWk : Tendsto (fun n : ℕ =>
      (U * (1 + 4 * gridCovarianceError b C n)) ^ k) atTop (𝓝 (U ^ k)) :=
    (Continuous.tendsto (continuous_pow k) U).comp hW
  have hfinal : Tendsto (fun n : ℕ => (3 : ℝ) *
      ((((n : ℝ) * δ n) ^ (k * (1 - psif) - 1))⁻¹ *
      (U * (1 + 4 * gridCovarianceError b C n)) ^ k)) atTop (𝓝 0) := by
    simpa using (hinv.mul hWk).const_mul 3
  have hnEv : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_gt_atTop 0
  have hS1ev : ∀ᶠ n : ℕ in atTop, 1 ≤ (n : ℝ) * δ n := hS.eventually_ge_atTop 1
  refine tendsto_le_tendsto_zero ?_ hfinal
  filter_upwards [hδpos, hsmall, hnEv, hS1ev, hU] with n hδ hsm hn hS1n hu
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set Sn := (n : ℝ) * δ n with hSn
  set Wn := U * (1 + 4 * gridCovarianceError b C n) with hWn
  have hSn0 : 0 < Sn := by rw [hSn]; exact mul_pos hnR hδ
  have hgnonneg : 0 ≤ gridCovarianceError b C n := by
    unfold gridCovarianceError
    have hlog := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by norm_cast; omega)
    positivity
  have hWn0 : 0 ≤ Wn := by
    rw [hWn]
    exact mul_nonneg hU0 (by linarith)
  have hm : ((localWeightActiveSet n 1 (δ n) t).card : ℝ) ≤ 3 * Sn :=
    localWeightActiveSet_card n 1 hn (δ n) t hδ hS1n
  have hk1 : Sn ^ (-1 : ℝ) * Sn ^ psif = Sn ^ (psif - 1) := by
    rw [← Real.rpow_add hSn0]
    congr 1
    ring
  have habsK : ∀ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
      |q1ActualLongActiveKernel f hf n (δ n) t Sn psif i i| ≤
        Sn ^ psif * (1 + 4 * gridCovarianceError b C n) := by
    intro i
    have hc1 := hdiag n hn (δ n) hδ hsm i
    have hc2 : |vectorCorrelation
        (gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
          (localWeightActiveIndex n 1 (δ n) t i))
        (gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
          (localWeightActiveIndex n 1 (δ n) t i))|
        ≤ 1 + 4 * gridCovarianceError b C n := by
      rcases abs_le.mp hc1 with ⟨hlo, hhi⟩
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hmul : |q1ActualLongActiveKernel f hf n (δ n) t Sn psif i i|
        = Sn ^ psif * |vectorCorrelation
            (gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
              (localWeightActiveIndex n 1 (δ n) t i))
            (gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
              (localWeightActiveIndex n 1 (δ n) t i))| := by
      unfold q1ActualLongActiveKernel
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hSn0.le psif)]
    rw [hmul]
    exact mul_le_mul_of_nonneg_left hc2 (Real.rpow_nonneg hSn0.le psif)
  have hentry : ∀ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
      |actualQ1NormalizedActualMatrix f hf r n (δ n) t i i| ≤
        Sn ^ (psif - 1) * Wn := by
    intro i
    have heq : actualQ1NormalizedActualMatrix f hf r n (δ n) t i i
        = ((n : ℝ) * δ n)⁻¹ *
          (actualQ1ChainWeight f r n (δ n) t i *
            q1ActualLongActiveKernel f hf n (δ n) t Sn psif i i) := rfl
    rw [heq, abs_mul, abs_mul, abs_of_nonneg (inv_nonneg.mpr hSn0.le), hWn]
    have hu1 : |actualQ1ChainWeight f r n (δ n) t i| ≤ U := hu i
    have hk := habsK i
    rw [← mul_assoc]
    calc Sn⁻¹ * |actualQ1ChainWeight f r n (δ n) t i| *
            |q1ActualLongActiveKernel f hf n (δ n) t Sn psif i i| ≤
          Sn⁻¹ * U * (Sn ^ psif * (1 + 4 * gridCovarianceError b C n)) :=
        mul_le_mul
          (mul_le_mul_of_nonneg_left hu1 (inv_nonneg.mpr hSn0.le))
          hk (abs_nonneg _)
          (mul_nonneg (inv_nonneg.mpr hSn0.le) hU0)
      _ = Sn ^ (psif - 1) * (U * (1 + 4 * gridCovarianceError b C n)) := by
          rw [← hk1, Real.rpow_neg_one]
          ring
  have hsum : |∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        (actualQ1NormalizedActualMatrix f hf r n (δ n) t i i) ^ k|
      ≤ (3 : ℝ) * ((Sn ^ (k * (1 - psif) - 1))⁻¹ * Wn ^ k) := by
    have hstep : |∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
          (actualQ1NormalizedActualMatrix f hf r n (δ n) t i i) ^ k|
        ≤ ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
          (Sn ^ (psif - 1) * Wn) ^ k := by
      calc |∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
            (actualQ1NormalizedActualMatrix f hf r n (δ n) t i i) ^ k|
          ≤ ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
              |actualQ1NormalizedActualMatrix f hf r n (δ n) t i i ^ k| :=
            Finset.abs_sum_le_sum_abs
              (f := fun i => (actualQ1NormalizedActualMatrix f hf r n (δ n) t i i) ^ k)
              (s := Finset.univ)
        _ ≤ ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
              (Sn ^ (psif - 1) * Wn) ^ k :=
            Finset.sum_le_sum (fun i _ => by
              rw [abs_pow]
              exact pow_le_pow_of_abs_le (by simpa using hentry i) k)
        _ = ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
              (Sn ^ (psif - 1) * Wn) ^ k := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
              Fintype.card_fin]
    have hp1 : (Sn ^ (psif - 1)) ^ k = (Sn ^ (k * (1 - psif)))⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hSn0.le,
        ← Real.rpow_neg hSn0.le (k * (1 - psif))]
      congr 1
      ring
    calc _ ≤ ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
            (Sn ^ (psif - 1) * Wn) ^ k := hstep
      _ ≤ 3 * Sn * (Sn ^ (k * (1 - psif)))⁻¹ * Wn ^ k := by
          have hmid : (localWeightActiveSet n 1 (δ n) t).card *
              (Sn ^ (k * (1 - psif)))⁻¹ ≤
              3 * Sn * (Sn ^ (k * (1 - psif)))⁻¹ := by
            refine mul_le_mul_of_nonneg_right hm ?_
            exact inv_nonneg.mpr (Real.rpow_nonneg hSn0.le (k * (1 - psif)))
          have hfin := mul_le_mul_of_nonneg_right hmid (pow_nonneg hWn0 k)
          have hmid2 : ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
              (Sn ^ (psif - 1) * Wn) ^ k
              = (localWeightActiveSet n 1 (δ n) t).card *
                (Sn ^ (k * (1 - psif)))⁻¹ * Wn ^ k := by
            rw [mul_pow, hp1]
            ring
          rw [hmid2]
          exact hfin
      _ = (3 : ℝ) * ((Sn ^ (k * (1 - psif) - 1))⁻¹ * Wn ^ k) := by
          rw [mul_assoc 3 Sn (Sn ^ (k * (1 - psif)))⁻¹, rpow_inv_mul hSn0,
            mul_assoc]
  rw [hWn] at hsum
  exact hsum

end Hurst
