import Hurst.FarWordAssembly
import Hurst.ActualKernelBandAsymptotics
import Hurst.FrozenQuadratureRun
import Hurst.BandPowerSum
import Hurst.GridErrorRate
import Hurst.ActualQuadratureConfluence

/-!
# The frozen quadrature, closed: Frobenius inputs, composition, final chain

This file instantiates the last assembly of the corrected route: it produces
the two Frobenius inputs consumed by
`Hurst.frozenQuad_hFquad_of_frobeniusSmall` (of `Hurst.FarWordAssembly`) for
the ACTUAL frozen quadrature matrix `actualQ1NormalizedFrozenMatrix` and the
Riesz quadrature matrix `actualQ1RieszMatrix`, composes them into the frozen
quadrature `hFrozenQuad`, and chains it through
`Hurst.actualQ1_trace_pow_tendsto_of_frozenBandwidth` into the even-power-sum
endpoint `actualQ1EigenvaluePowerSums_tendsto_frozenComplete`.

## The bookkeeping (how the two inputs are landed)

* (a) **Uniform Frobenius bounds** with the explicit constant
  `B = B_omega * sqrt Cref + 1`, where `B_omega` bounds `|equivalentKernel r ·|`
  (`equivalentKernel_bounded`) and
  `Cref = 2 * c^2 * (3 + 3 * 4^(1-2psi) / (1 - 2*psi))` is the constant of
  `rankRieszKernel_energy_le_const` (`psi = 2 - 2 * f t < 1/2` from
  `3/4 < f t`).
  - T side: `‖T_n‖ ≤ B_omega * sqrt Cref` — the entrywise bound
    `|T i j| ≤ B_omega * S⁻¹ * |R i j|` plus the Riesz kernel-energy constant
    (the private `rieszMatrix_frobenius_le`, the T-side of the discharge of
    `ActualQ1UniformFrobeniusBound`).
  - F side: `‖F_n‖ ≤ ‖T_n‖ + ‖F_n - T_n‖ ≤ B` eventually, by the triangle
    inequality once (b) is in hand.
* (b) **Frobenius vanishing** `‖F_n - T_n‖_F → 0` by the TRIANGLE route through
  the actual matrix `A_n` (NOT the stratified near/far entry envelope, whose
  far-band relative `16/x` form hits the documented `delta * log n` drift
  residue — see the honest gap note):
  `‖F_n - T_n‖ ≤ ‖F_n - A_n‖ + ‖A_n - T_n‖` with
  - `‖F_n - A_n‖ → 0` from the dimension-weighted frozen perturbation
    `frozenQ1_frozenPert_tendsto_zero_of_bandwidth` (ordinary model +
    bandwidth condition `2 * b + psi < 3/2`; `card ≥ 1` strips the
    cardinality factor and the square root undoes the square), and
  - `‖A_n - T_n‖ → 0` from `actualQ1_frobenius_norm_tendsto_zero` applied to
    the mesh-energy convergence `hE` (the unweighted energy of the
    A-side-minus-G-side kernel comparison; derived from the ordinary model +
    bandwidth-rate data by `actualQ1_meshEnergy_tendsto_zero`).

## Honest gap note (the remaining hypothesis of the final chain)

The single analytic input left to the whole chain is `hE`, the unweighted
mesh-energy convergence
`realScaleMeshEnergy S_n (A-side - G-side) → 0`.  Concretely
(`actualQ1_meshEnergy_tendsto_zero`) it follows from the bandwidth-rate data
`(R, hR, hcut, henv)`; of these `hcut` is free for every FIXED `R` (it is
`S^{2psi-2} * card * (2R+1) ≤ 9 * S^{2psi-1} → 0` since `2*psi - 1 < 0`), but
`henv` — the tail envelope
`18 Ctail D (1 + e^E E) + 9 e^E E + 16/(R+1) + (3/2) D + 4 (2S)^psi gridErr`
with `D = 2 L (1+M) delta`, `E = D log n` — does NOT tend to zero for fixed
`R` (the `16/(R+1)` term) and for growing `R` carries the residue
`delta * log n` in `E` (the profile/class drift `D * |log x|` of
`firstIncrementCrossLagCorrelation_scaled_error_le_explicit`), which is not
forced to vanish by `delta → 0`, `n * delta → ∞` alone (e.g.
`delta n = 1/log n`).  This is exactly the documented gap of
`Hurst.FarWordAssembly` (the non-`d^{-(1+psi)}`-decaying class/profile error
terms); the Frobenius input (b) is landed here CONDITIONAL on `hE`, which is
the weakest known form of that single input.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Set Filter Matrix
open scoped Matrix.Norms.Frobenius Topology

namespace Hurst

/-! ## Private helpers -/

/-- Frobenius norm of a real finite matrix as the square root of the sum of
squared entries. -/
private theorem frobenius_norm_eq_sqrt_sum_sq' {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) :
    ‖A‖ = Real.sqrt (∑ i : Fin m, ∑ j : Fin m, A i j ^ 2) := by
  rw [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  congr 1
  exact Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => by rw [Real.norm_eq_abs, Real.rpow_two, sq_abs]

/-! ## (a), T side: the uniform Riesz Frobenius bound -/

/-- **The T-side uniform Frobenius bound.**  `‖actualQ1RieszMatrix‖ ≤ B_ω * √Cref`:
entrywise `G_ij = S⁻¹ * ω(x_i) * R_ij` with `|ω| ≤ B_ω` on `[-1,1]`
(`rieszCycleGridPoint_mem_Icc`), summed against the Riesz kernel-energy
constant `Cref` in the shape of `rankRieszKernel_energy_le_const`. -/
private theorem rieszMatrix_frobenius_le
    (f : ℝ → ℝ) (r : ℕ) (n : ℕ) (δ t : ℝ)
    (hcard : 0 < (localWeightActiveSet n 1 δ t).card)
    (hS1 : 1 ≤ (n : ℝ) * δ)
    (hcardle : ((localWeightActiveSet n 1 δ t).card : ℝ) ≤ 3 * ((n : ℝ) * δ))
    (Bω : ℝ) (hBω : ∀ z ∈ Set.Icc (-1 : ℝ) 1, |equivalentKernel r z| ≤ Bω)
    (Cref : ℝ)
    (hCref : ∀ (S : ℝ) (m : ℕ), 1 ≤ S → (m : ℝ) ≤ 3 * S →
      realScaleMeshEnergy S
        (rankRieszKernel S (2 - 2 * f t) (f t * (2 * f t - 1)) :
          Fin m → Fin m → ℝ) ≤ Cref) :
    ‖actualQ1RieszMatrix f r n δ t‖ ≤ Bω * Real.sqrt Cref := by
  have hS0 : 0 < (n : ℝ) * δ := lt_of_lt_of_le zero_lt_one hS1
  have hinv : 0 < ((n : ℝ) * δ)⁻¹ := inv_pos.mpr hS0
  have hw : ∀ i : Fin (localWeightActiveSet n 1 δ t).card,
      |equivalentKernel r
        (rieszCycleGridPoint (localWeightActiveSet n 1 δ t).card i)| ≤ Bω :=
    fun i => hBω _ (rieszCycleGridPoint_mem_Icc hcard i)
  have hBω0 : 0 ≤ Bω := le_trans (abs_nonneg _) (hw ⟨0, hcard⟩)
  -- entrywise square bound
  have hpt : ∀ i j : Fin (localWeightActiveSet n 1 δ t).card,
      actualQ1RieszMatrix f r n δ t i j ^ 2
        ≤ (Bω * ((n : ℝ) * δ)⁻¹) ^ 2 *
          rankRieszKernel ((n : ℝ) * δ) (2 - 2 * f t) (f t * (2 * f t - 1)) i j ^ 2 := by
    intro i j
    have hentry : actualQ1RieszMatrix f r n δ t i j
        = ((n : ℝ) * δ)⁻¹ *
          equivalentKernel r
            (rieszCycleGridPoint (localWeightActiveSet n 1 δ t).card i) *
          rankRieszKernel ((n : ℝ) * δ) (2 - 2 * f t) (f t * (2 * f t - 1)) i j := by
      simp only [actualQ1RieszMatrix, weightedRieszDiscreteMatrix_apply]
    rw [hentry, mul_pow]
    have hwij : |((n : ℝ) * δ)⁻¹ *
        equivalentKernel r
          (rieszCycleGridPoint (localWeightActiveSet n 1 δ t).card i)|
        ≤ Bω * ((n : ℝ) * δ)⁻¹ := by
      rw [abs_mul, abs_of_pos hinv]
      calc ((n : ℝ) * δ)⁻¹ *
            |equivalentKernel r
              (rieszCycleGridPoint (localWeightActiveSet n 1 δ t).card i)|
          = |equivalentKernel r
              (rieszCycleGridPoint (localWeightActiveSet n 1 δ t).card i)| *
            ((n : ℝ) * δ)⁻¹ := mul_comm _ _
        _ ≤ Bω * ((n : ℝ) * δ)⁻¹ :=
          mul_le_mul_of_nonneg_right (hw i) hinv.le
    have hsq : (((n : ℝ) * δ)⁻¹ *
        equivalentKernel r
          (rieszCycleGridPoint (localWeightActiveSet n 1 δ t).card i)) ^ 2
        ≤ (Bω * ((n : ℝ) * δ)⁻¹) ^ 2 := by
      rw [← sq_abs]
      exact sq_le_sq'
        (by linarith [hwij, abs_nonneg (((n : ℝ) * δ)⁻¹ *
          equivalentKernel r
            (rieszCycleGridPoint (localWeightActiveSet n 1 δ t).card i))])
        hwij
    exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
  -- the energy bound, unfolded to the square-sum form
  have hCref' : ((n : ℝ) * δ)⁻¹ ^ 2 *
      ∑ i : Fin (localWeightActiveSet n 1 δ t).card,
        ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
          rankRieszKernel ((n : ℝ) * δ) (2 - 2 * f t) (f t * (2 * f t - 1)) i j ^ 2
      ≤ Cref := by
    have h := hCref ((n : ℝ) * δ) (localWeightActiveSet n 1 δ t).card hS1 hcardle
    simpa only [realScaleMeshEnergy] using h
  -- the square-sum bound for the Riesz matrix
  have hsum : ∑ i : Fin (localWeightActiveSet n 1 δ t).card,
      ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
        actualQ1RieszMatrix f r n δ t i j ^ 2
      ≤ Bω ^ 2 * Cref := by
    have h1 : ∑ i : Fin (localWeightActiveSet n 1 δ t).card,
        ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
          actualQ1RieszMatrix f r n δ t i j ^ 2
        ≤ ∑ i : Fin (localWeightActiveSet n 1 δ t).card,
          ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
            (Bω * ((n : ℝ) * δ)⁻¹) ^ 2 *
              rankRieszKernel ((n : ℝ) * δ) (2 - 2 * f t)
                (f t * (2 * f t - 1)) i j ^ 2 :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpt i j
    calc ∑ i : Fin (localWeightActiveSet n 1 δ t).card,
        ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
          actualQ1RieszMatrix f r n δ t i j ^ 2
        ≤ ∑ i : Fin (localWeightActiveSet n 1 δ t).card,
          ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
            (Bω * ((n : ℝ) * δ)⁻¹) ^ 2 *
              rankRieszKernel ((n : ℝ) * δ) (2 - 2 * f t)
                (f t * (2 * f t - 1)) i j ^ 2 := h1
      _ = (Bω * ((n : ℝ) * δ)⁻¹) ^ 2 *
            ∑ i : Fin (localWeightActiveSet n 1 δ t).card,
              ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
                rankRieszKernel ((n : ℝ) * δ) (2 - 2 * f t)
                  (f t * (2 * f t - 1)) i j ^ 2 := by
          simp only [Finset.mul_sum]
      _ = Bω ^ 2 * (((n : ℝ) * δ)⁻¹ ^ 2 *
            ∑ i : Fin (localWeightActiveSet n 1 δ t).card,
              ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
                rankRieszKernel ((n : ℝ) * δ) (2 - 2 * f t)
                  (f t * (2 * f t - 1)) i j ^ 2) := by
          rw [mul_pow]
          ring
      _ ≤ Bω ^ 2 * Cref := mul_le_mul_of_nonneg_left hCref' (sq_nonneg Bω)
  calc ‖actualQ1RieszMatrix f r n δ t‖
      = Real.sqrt (∑ i : Fin (localWeightActiveSet n 1 δ t).card,
          ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
            actualQ1RieszMatrix f r n δ t i j ^ 2) :=
        frobenius_norm_eq_sqrt_sum_sq' _
    _ ≤ Real.sqrt (Bω ^ 2 * Cref) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (Bω ^ 2) * Real.sqrt Cref := Real.sqrt_mul (sq_nonneg Bω) Cref
    _ = Bω * Real.sqrt Cref := by rw [Real.sqrt_sq hBω0]

/-! ## (a) + (b): the two Frobenius inputs for the frozen quadrature -/

/-- **The two Frobenius inputs of the frozen quadrature (deliverable of this
file).**  Under the ordinary model hypotheses, the bandwidth condition
`2 * b + psi < 3 / 2` (`psi = 2 - 2 * f t`, i.e. `hband`), the weight bound
`|u_i| ≤ U` and the mesh-energy convergence `hE`, the eventual uniform
Frobenius bounds (a) hold with the EXPLICIT constant
`B = B_omega * sqrt Cref + 1` and the Frobenius difference (b) tends to zero:
this is exactly the input shape consumed by
`Hurst.frozenQuad_hFquad_of_frobeniusSmall`. -/
theorem frozenQuad_frobeniusInputs_of_meshEnergy
    (p a b M : ℝ) (r : ℕ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (hM : 0 ≤ M) (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (hband : 2 * b + (2 - 2 * f t) < 3 / 2)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (U : ℝ) (hU0 : 0 ≤ U)
    (hU : ∀ᶠ n in atTop, ∀ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
      |actualQ1ChainWeight f r n (δ n) t i| ≤ U)
    (hE : Tendsto (fun n : ℕ => realScaleMeshEnergy ((n : ℝ) * δ n)
        (actualQ1WeightedActualKernel f hf r n (δ n) t -
          actualQ1WeightedRieszKernel f r n (δ n) t)) atTop (𝓝 0)) :
    ∃ B : ℝ, 0 ≤ B ∧
      (∀ᶠ n in atTop,
        ‖actualQ1NormalizedFrozenMatrix f hf r n (δ n) t‖ ≤ B) ∧
      (∀ᶠ n in atTop,
        ‖actualQ1RieszMatrix f r n (δ n) t‖ ≤ B) ∧
      Tendsto (fun n : ℕ =>
        ‖actualQ1NormalizedFrozenMatrix f hf r n (δ n) t
            - actualQ1RieszMatrix f r n (δ n) t‖) atTop (𝓝 0) := by
  -- the eventual cardinality bookkeeping
  obtain ⟨hm0, hratio⟩ := localWeightActiveSet_card_ratio_tendsto_two 1 t ht δ
    hδpos hδ0 hN
  have hcardpos : ∀ᶠ n : ℕ in atTop,
      0 < (localWeightActiveSet n 1 (δ n) t).card := hm0
  have hS1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ (n : ℝ) * δ n := hN.eventually_ge_atTop 1
  have hcard3 : ∀ᶠ n : ℕ in atTop,
      ((localWeightActiveSet n 1 (δ n) t).card : ℝ) ≤ 3 * ((n : ℝ) * δ n) := by
    filter_upwards [hcardpos, hδpos, hratio.eventually_lt_const
      (show ((2 : ℝ) < 3) by norm_num)] with n hcard hδ hlt
    have hn : 0 < n := by
      have hlt2 := (localWeightActiveIndex n 1 (δ n) t ⟨0, hcard⟩).isLt
      omega
    have hS0 : (0 : ℝ) < (n : ℝ) * δ n := mul_pos (by exact_mod_cast hn) hδ
    have hle := (div_lt_iff₀ hS0).mp hlt
    linarith
  -- the explicit constants
  obtain ⟨Bω, hBω0, hBωall⟩ := equivalentKernel_bounded r
  have hBω : ∀ z ∈ Set.Icc (-1 : ℝ) 1, |equivalentKernel r z| ≤ Bω :=
    fun z hz => hBωall z
  have hft1 : (f t : ℝ) < 1 := lt_of_le_of_lt (hF ht).2 hb
  have hψle : (0 : ℝ) ≤ 2 - 2 * f t := by linarith
  have hψhalf : (2 : ℝ) - 2 * f t < 1 / 2 := by linarith
  have hCref : ∀ (S : ℝ) (m : ℕ), 1 ≤ S → (m : ℝ) ≤ 3 * S →
      realScaleMeshEnergy S
        (rankRieszKernel S (2 - 2 * f t) (f t * (2 * f t - 1)) :
          Fin m → Fin m → ℝ) ≤
        2 * (f t * (2 * f t - 1)) ^ 2 *
          (3 + 3 * 4 ^ (1 - 2 * (2 - 2 * f t)) / (1 - 2 * (2 - 2 * f t))) :=
    fun S m hS hm =>
      rankRieszKernel_energy_le_const S (2 - 2 * f t) (f t * (2 * f t - 1))
        hS hm hψle hψhalf
  -- (b): the Frobenius difference vanishes, via the triangle route through A_n
  have hAT0 := actualQ1_frobenius_norm_tendsto_zero f hf r δ t hδpos hE
  have hAFsq := frozenQ1_frozenPert_tendsto_zero_of_bandwidth p a b M r hp ha hb
    hab hM f hf hF t ht hlong hband δ hδpos hδ0 hN U hU0 hU
  have hAF0 : Tendsto (fun n : ℕ =>
      ‖actualQ1NormalizedActualMatrix f hf r n (δ n) t -
        actualQ1NormalizedFrozenMatrix f hf r n (δ n) t‖) atTop (𝓝 0) := by
    have hsq0 : Tendsto (fun n : ℕ =>
        ‖actualQ1NormalizedActualMatrix f hf r n (δ n) t -
          actualQ1NormalizedFrozenMatrix f hf r n (δ n) t‖ ^ 2) atTop (𝓝 0) := by
      refine squeeze_zero' (Eventually.of_forall fun _ => sq_nonneg _) ?_ hAFsq
      filter_upwards [hcardpos] with n hcard
      have h1 : ((1 : ℝ) : ℝ)
          ≤ (localWeightActiveSet n 1 (δ n) t).card := by
        exact_mod_cast (Nat.succ_le_of_lt hcard)
      calc ‖actualQ1NormalizedActualMatrix f hf r n (δ n) t -
              actualQ1NormalizedFrozenMatrix f hf r n (δ n) t‖ ^ 2
          = (1 : ℝ) * ‖actualQ1NormalizedActualMatrix f hf r n (δ n) t -
              actualQ1NormalizedFrozenMatrix f hf r n (δ n) t‖ ^ 2 := (one_mul _).symm
        _ ≤ (localWeightActiveSet n 1 (δ n) t).card *
              ‖actualQ1NormalizedActualMatrix f hf r n (δ n) t -
                actualQ1NormalizedFrozenMatrix f hf r n (δ n) t‖ ^ 2 :=
              mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
    refine Tendsto.congr' (Eventually.of_forall fun n =>
      Real.sqrt_sq (norm_nonneg _)) ?_
    have hcomp := Filter.Tendsto.comp
      (Real.continuous_sqrt.continuousAt (x := (0 : ℝ))).tendsto hsq0
    rwa [Real.sqrt_zero] at hcomp
  have hΔ0 : Tendsto (fun n : ℕ =>
      ‖actualQ1NormalizedFrozenMatrix f hf r n (δ n) t
          - actualQ1RieszMatrix f r n (δ n) t‖) atTop (𝓝 0) := by
    have hsum0 : Tendsto (fun n : ℕ =>
        ‖actualQ1NormalizedActualMatrix f hf r n (δ n) t
            - actualQ1NormalizedFrozenMatrix f hf r n (δ n) t‖ +
          ‖actualQ1NormalizedActualMatrix f hf r n (δ n) t
            - actualQ1RieszMatrix f r n (δ n) t‖) atTop (𝓝 0) := by
      simpa using hAF0.add hAT0
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hsum0
    filter_upwards [] with n
    have hsplit : actualQ1NormalizedFrozenMatrix f hf r n (δ n) t
        - actualQ1RieszMatrix f r n (δ n) t
        = (actualQ1NormalizedActualMatrix f hf r n (δ n) t
            - actualQ1RieszMatrix f r n (δ n) t)
          - (actualQ1NormalizedActualMatrix f hf r n (δ n) t
            - actualQ1NormalizedFrozenMatrix f hf r n (δ n) t) := by abel
    rw [hsplit]
    exact (norm_sub_le
      (actualQ1NormalizedActualMatrix f hf r n (δ n) t
        - actualQ1RieszMatrix f r n (δ n) t)
      (actualQ1NormalizedActualMatrix f hf r n (δ n) t
        - actualQ1NormalizedFrozenMatrix f hf r n (δ n) t)).trans_eq
      (add_comm _ _)
  -- (a), T side: the explicit Riesz bound
  have hTb : ∀ᶠ n : ℕ in atTop,
      ‖actualQ1RieszMatrix f r n (δ n) t‖ ≤ Bω * Real.sqrt
        (2 * (f t * (2 * f t - 1)) ^ 2 *
          (3 + 3 * 4 ^ (1 - 2 * (2 - 2 * f t)) / (1 - 2 * (2 - 2 * f t)))) := by
    filter_upwards [hcardpos, hδpos, hS1, hcard3] with n hcard hδ hS1n hcard3n
    have hn : 0 < n := by
      have hlt := (localWeightActiveIndex n 1 (δ n) t ⟨0, hcard⟩).isLt
      omega
    exact rieszMatrix_frobenius_le f r n (δ n) t hcard hS1n hcard3n Bω hBω _ hCref
  -- (a), F side: the triangle bound against T
  set B : ℝ := Bω * Real.sqrt (2 * (f t * (2 * f t - 1)) ^ 2 *
    (3 + 3 * 4 ^ (1 - 2 * (2 - 2 * f t)) / (1 - 2 * (2 - 2 * f t)))) + 1 with hBdef
  have hB0 : 0 ≤ B := by
    refine add_nonneg ?_ zero_le_one
    refine mul_nonneg hBω0 (Real.sqrt_nonneg _)
  have hFb : ∀ᶠ n : ℕ in atTop,
      ‖actualQ1NormalizedFrozenMatrix f hf r n (δ n) t‖ ≤ B := by
    have hΔ1 : ∀ᶠ n : ℕ in atTop,
        ‖actualQ1NormalizedFrozenMatrix f hf r n (δ n) t
            - actualQ1RieszMatrix f r n (δ n) t‖ ≤ 1 :=
      hΔ0.eventually_le_const (show ((0 : ℝ) < 1) by norm_num)
    filter_upwards [hTb, hΔ1] with n hT hΔ
    have hjoin : (actualQ1NormalizedFrozenMatrix f hf r n (δ n) t
            - actualQ1RieszMatrix f r n (δ n) t)
          + actualQ1RieszMatrix f r n (δ n) t
        = actualQ1NormalizedFrozenMatrix f hf r n (δ n) t := by abel
    calc ‖actualQ1NormalizedFrozenMatrix f hf r n (δ n) t‖
        = ‖(actualQ1NormalizedFrozenMatrix f hf r n (δ n) t
              - actualQ1RieszMatrix f r n (δ n) t) +
            actualQ1RieszMatrix f r n (δ n) t‖ := by rw [hjoin]
      _ ≤ ‖actualQ1NormalizedFrozenMatrix f hf r n (δ n) t
              - actualQ1RieszMatrix f r n (δ n) t‖
            + ‖actualQ1RieszMatrix f r n (δ n) t‖ :=
          norm_add_le
            (actualQ1NormalizedFrozenMatrix f hf r n (δ n) t
              - actualQ1RieszMatrix f r n (δ n) t)
            (actualQ1RieszMatrix f r n (δ n) t)
      _ ≤ B := by rw [hBdef]; linarith
  have hTbB : ∀ᶠ n : ℕ in atTop,
      ‖actualQ1RieszMatrix f r n (δ n) t‖ ≤ B := by
    refine hTb.mono fun n h => ?_
    exact le_trans h (by rw [hBdef]; linarith)
  exact ⟨B, hB0, hFb, hTbB, hΔ0⟩

/-! ## The composed frozen quadrature -/

/-- **The frozen quadrature, composed (the `hFrozenQuad` deliverable).**
Composing `frozenQuad_frobeniusInputs_of_meshEnergy` with
`Hurst.frozenQuad_hFquad_of_frobeniusSmall`: under the ordinary model
hypotheses, the bandwidth condition, the weight bound and the mesh-energy
convergence `hE`, the frozen-side power traces converge to the weighted Riesz
cycle integral:
`tr(F_n ^ k) → weightedRieszCycleIntegral k psi c (equivalentKernel r)`. -/
theorem frozenQuad_tendsto_of_meshEnergy
    (p a b M : ℝ) (r : ℕ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (hM : 0 ≤ M) (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (hband : 2 * b + (2 - 2 * f t) < 3 / 2)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (k : ℕ) (hk : 2 ≤ k)
    (U : ℝ) (hU0 : 0 ≤ U)
    (hU : ∀ᶠ n in atTop, ∀ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
      |actualQ1ChainWeight f r n (δ n) t i| ≤ U)
    (hE : Tendsto (fun n : ℕ => realScaleMeshEnergy ((n : ℝ) * δ n)
        (actualQ1WeightedActualKernel f hf r n (δ n) t -
          actualQ1WeightedRieszKernel f r n (δ n) t)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => Matrix.trace
        ((actualQ1NormalizedFrozenMatrix f hf r n (δ n) t) ^ k)) atTop
      (𝓝 (weightedRieszCycleIntegral k (2 - 2 * f t)
        (f t * (2 * f t - 1)) (equivalentKernel r))) := by
  obtain ⟨B, hB0, hFb, hTb, hΔ⟩ :=
    frozenQuad_frobeniusInputs_of_meshEnergy p a b M r hp ha hb hab hM f hf hF
      t ht hlong hband δ hδpos hδ0 hN U hU0 hU hE
  exact frozenQuad_hFquad_of_frobeniusSmall p a b M r hp ha hb hab hM f hf hF
    t ht hlong δ hδpos hδ0 hN k hk B hFb hTb hΔ

/-! ## The final chain: even eigenvalue power sums of the actual statistic -/

/-- **The final chain of the corrected route, composed.**  From the ordinary
model hypotheses plus the bandwidth-rate data `(R, hR, hcut, henv)`, the
bandwidth condition `2 * b + psi < 3/2` and the weight bound `|u_i| ≤ U`:
the `k`-th power sums of the eigenvalues of the actual weighted
feature-quadratic spectral matrix `actualQ1Hermitian` converge to
`∑' j, lam j ^ k` — via
1. the mesh-energy convergence `hE` (`actualQ1_meshEnergy_tendsto_zero`),
2. the frozen quadrature (`frozenQuad_tendsto_of_meshEnergy`, i.e. the
   composed `hFrozenQuad` of `frozenQuad_hFquad_of_frobeniusSmall`),
3. the frozen-bandwidth trace transfer
   (`actualQ1_trace_pow_tendsto_of_frozenBandwidth`, whose `hFrozenPert` is
   discharged internally by `frozenQ1_frozenPert_tendsto_zero_of_bandwidth`),
4. the eigenvalue trace identity
   (`hermitian_trace_pow_eq_sum_eigenvalues_pow` +
   `trace_pow_weightedFeatureQuadraticMatrix_eq` +
   `actualQ1_diagonalCorrelation_eq`), and
5. the Riesz spectral identification `hRiesz` (`HasSum` at exponent `k`).

The only non-ordinary input is the bandwidth-rate tail envelope `henv` — see
the honest gap note at the top of this file. -/
theorem actualQ1EigenvaluePowerSums_tendsto_frozenComplete
    (p a b M : ℝ) (r : ℕ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (hM : 0 ≤ M) (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (hband : 2 * b + (2 - 2 * f t) < 3 / 2)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (R : ℕ → ℕ) (hR : ∀ᶠ n in atTop, 1 ≤ R n)
    (hcut : Tendsto (fun n : ℕ => ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 2) *
      ((localWeightActiveSet n 1 (δ n) t).card : ℝ) * (2 * (R n : ℝ) + 1))
      atTop (𝓝 0))
    (henv : ∀ Ccov ≥ 0, ∀ Ctail ≥ 0, ∀ L > 0, Tendsto (fun n : ℕ =>
      q1ActualLongTailEnvelope b Ccov Ctail L M (f t) n (δ n) ((n : ℝ) * δ n)
        (R n)) atTop (𝓝 0))
    (hcard : ∀ n : ℕ, 0 < (localWeightActiveSet n 1 (δ n) t).card)
    (U : ℝ) (hU0 : 0 ≤ U)
    (hU : ∀ᶠ n in atTop, ∀ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
      |actualQ1ChainWeight f r n (δ n) t i| ≤ U)
    (lam : ℕ → ℝ)
    (hRiesz : ∀ k : ℕ, 2 ≤ k → HasSum (fun j => lam j ^ k)
      (weightedRieszCycleIntegral k (2 - 2 * f t) (f t * (2 * f t - 1))
        (equivalentKernel r)))
    (k : ℕ) (hk : 2 ≤ k) :
    Tendsto (fun n : ℕ => ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        (actualQ1Hermitian f hf r n (δ n) t).eigenvalues i ^ k)
      atTop (𝓝 (∑' j : ℕ, lam j ^ k)) := by
  -- 1. the mesh-energy convergence from the bandwidth-rate data
  have hE := actualQ1_meshEnergy_tendsto_zero p a b M r hp ha hb hab hM f hf hF
    t ht hlong δ hδpos hδ0 hN R hR hcut henv
  -- 2. the frozen quadrature
  have hFQ := frozenQuad_tendsto_of_meshEnergy p a b M r hp ha hb hab hM f hf hF
    t ht hlong hband δ hδpos hδ0 hN k hk U hU0 hU hE
  -- the explicit constants for the trace transfer
  obtain ⟨Bω, hBω0, hBωall⟩ := equivalentKernel_bounded r
  have hBω : ∀ z ∈ Set.Icc (-1 : ℝ) 1, |equivalentKernel r z| ≤ Bω :=
    fun z hz => hBωall z
  have hft1 : (f t : ℝ) < 1 := lt_of_le_of_lt (hF ht).2 hb
  have hψle : (0 : ℝ) ≤ 2 - 2 * f t := by linarith
  have hψhalf : (2 : ℝ) - 2 * f t < 1 / 2 := by linarith
  set Cref : ℝ := 2 * (f t * (2 * f t - 1)) ^ 2 *
    (3 + 3 * 4 ^ (1 - 2 * (2 - 2 * f t)) / (1 - 2 * (2 - 2 * f t))) with hCrefdef
  have hCref : ∀ (S : ℝ) (m : ℕ), 1 ≤ S → (m : ℝ) ≤ 3 * S →
      realScaleMeshEnergy S
        (rankRieszKernel S (2 - 2 * f t) (f t * (2 * f t - 1)) :
          Fin m → Fin m → ℝ) ≤ Cref := by
    intro S m hS hm
    rw [hCrefdef]
    exact rankRieszKernel_energy_le_const S (2 - 2 * f t) (f t * (2 * f t - 1))
      hS hm hψle hψhalf
  -- 3. the actual trace powers through the frozen bandwidth transfer
  have htr := actualQ1_trace_pow_tendsto_of_frozenBandwidth p a b M r hp ha hb
    hab hM f hf hF t ht hlong hband δ hδpos hδ0 hN R hR hcut henv Bω hBω Cref
    hCref hcard U hU0 hU k hFQ
  -- 4. the eigenvalue trace identity along the sequence
  have hcardpos : ∀ᶠ n : ℕ in atTop,
      0 < (localWeightActiveSet n 1 (δ n) t).card :=
    (localWeightActiveSet_card_ratio_tendsto_two 1 t ht δ hδpos hδ0 hN).1
  have hsum : ∀ᶠ n : ℕ in atTop,
      ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        (actualQ1Hermitian f hf r n (δ n) t).eigenvalues i ^ k
      = Matrix.trace ((actualQ1NormalizedActualMatrix f hf r n (δ n) t) ^ k) := by
    filter_upwards [hcardpos, hδpos] with n hcard hδ
    have hn : 0 < n := by
      have hlt := (localWeightActiveIndex n 1 (δ n) t ⟨0, hcard⟩).isLt
      omega
    rw [← hermitian_trace_pow_eq_sum_eigenvalues_pow
      (actualQ1Hermitian f hf r n (δ n) t) k]
    rw [trace_pow_weightedFeatureQuadraticMatrix_eq
      (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
      (actualQ1Coeff n (δ n) t) (actualQ1SpectralWeight f r n (δ n) t) k]
    rw [actualQ1_diagonalCorrelation_eq f hf r n hn (δ n) t hδ]
  -- 5. the Riesz spectral identification and the conclusion
  rw [show (∑' j : ℕ, lam j ^ k)
      = weightedRieszCycleIntegral k (2 - 2 * f t) (f t * (2 * f t - 1))
        (equivalentKernel r) from (hRiesz k hk).tsum_eq]
  refine Tendsto.congr' (hsum.mono fun n h => h.symm) ?_
  exact htr

end Hurst
