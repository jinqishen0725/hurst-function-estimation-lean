import Mathlib
import Hurst.EquivalentKernelSpectrum
import Hurst.TensorParsevalTracePair

/-!
# The compression identity, `k = 2` closure: `Diag_2(B) = weightedRieszCycleIntegral 2`

The last mathematical gap of M1 (spec §5 of `milestone1_hconst_elimination_math_spec.md`,
A8–A9 route) is the **compression identity** `Diag_k(B) = Diag_k((WK)^k)`.  This file
lands its `k = 2` member — the hTwo statement of CapstoneV3 on the hconst-free line —
unconditionally and without any `hconst`-type premise:

* `diag2_Bop_eq_weightedCycle` — for every Hilbert basis `e` of `L2`,
  `∑' i, ⟪(B ^ 2) (e i), e i⟫ = Hurst.weightedRieszCycleIntegral 2 psi c omega`,
  where `B = Bop = S ∘ M_omega ∘ S` on a complete nonnegative eigenfamily `(v, κ)` of
  the *unweighted* Riesz operator.
* `tsum_Briesz_valSq_eq_weightedCycle` — combined with the landed
  `exists_Briesz_spectral_enumeration`: the model `B` carries a multiplicity-exact,
  square-summable spectral enumeration whose square sum is exactly the weighted Riesz
  cycle integral of order 2.

## Route (all `k = 2`; no truncations needed at this order)

1. `mulOperator_comp_TOp_riesz` — **left multiplication by the weight IS the kernel
   operation**: `TOp (rieszKernel psi c omega) = M_omega ∘ TOp (unweightedRieszKernel psi c)`
   as bundled operators.  The proof is a pure a.e.-congruence chain (no Fubini): by
   self-adjointness of `M_omega` move the multiplication operator to the test side,
   then replace `⇑(M_omega g)` by `omega • g` a.e. and `omega` by its `I`-indicator
   a.e. (the carrier measure lives on `I`).
2. `TOp_riesz_apply_eigenfamily` — consequently the weighted operator acts on the
   eigenfamily as `T_R (v j) = κ j • M_omega (v j)`.
3. `kernel_inner_eq_tsum_prodKernel'`, `cycle2_eq_tsum_pair'` — the general-index
   (complete orthonormal family) forms of the landed tensor-ONB Parseval and the
   `cycle2` matrix-entry expansion (verbatim proofs of
   `Hurst.TensorParsevalTracePair` at index type `ι` instead of `ℕ`).
4. `diag2_TOpRiesz_eq_kappaWeighted_matrixSum` (sublemma ②, kernel side): the second
   power diagonal of the weighted kernel operator equals the κ-weighted matrix-square
   sum `∑'_{ι²} κ_i κ_j ⟪v i, M_omega (v j)⟫²` — via the landed
   `tracePair_comp_tsum` (diagonal pairing = `cycle2`), the `v`-family expansion of
   `cycle2` (3), the eigenfamily action (2) and the symmetry flip of `M_omega`.
5. `matrixSq_sum_eq_of_complete` (sublemma ①, basis transport): for a self-adjoint
   `B` with both matrix-square families ℝ-summable, the matrix-square double sums over
   any Hilbert basis `e` and over the complete eigenfamily `v` coincide — the ENNReal
   Tonelli/Parseval chain of the landed `A7_aux` with every step kept as an equality
   (the final `≤`-collapse against `MR² ∑' κ²` replaced by the identity stop).
6. Assembly `diag2_Bop_eq_weightedCycle`:
   `∑' ⟪B² e_i, e_i⟫ = ∑' ‖B e_i‖²` (landed `diag2_symmetric_eq_sumSq`)
   `= ∑'_{ℕ²} ⟪e p.1, B e p.2⟫²` (per-column Parseval + reassembly)
   `= ∑'_{ι²} ⟪v q.1, B v q.2⟫²` (5)
   `= ∑'_{ι²} κ_q.1 κ_q.2 ⟪v q.1, M_omega (v q.2)⟫²` (landed `inner_Bop_matrix`)
   `= ∑' ⟪T_R² e_i, e_i⟫` (4)
   `= weightedRieszCycleIntegral 2 psi c omega` (landed
   `diagSum_TOpRiesz_pow_eq_weightedCycle` at `k = 2`).

## Honest boundary (declared, not hidden)

The **general-`k`** compression identity (`k ≥ 3`) is NOT landed here: it needs the
truncation route of spec §5 steps 0–3 (spectral projections `P_N`, finite-rank
`B_N' = P_N B P_N`, the A8 finite-matrix identity, the three convergences (a)/(b)
with (c) = A4 landed).  Until that lands, `diagSum_B_eq_weightedCycle` (all `k ≥ 2`)
and `exists_weightedRieszSpectrum_min` are NOT produced by this file, and M1
acceptance (spec §6) remains unpassed.  The `k = 2` closure delivered here is the
seed of that route and is independently valuable (CapstoneV3's `hTwo`).
-/

open MeasureTheory Measure Real Set Submodule
open scoped Real

noncomputable section

namespace HS

/-! ### 1. Left multiplication by the weight is the kernel operation -/

/-- The `I`-indicator of the weight equals the weight a.e. on the carrier measure
(the measure lives on `I`; local helper for `mulOperator_comp_TOp_riesz`). -/
private theorem indicator_omega_ae {omega : ℝ → ℝ} :
    (fun x : ℝ => (I : Set ℝ).indicator omega x) =ᵐ[vol] omega := by
  filter_upwards [MeasureTheory.ae_restrict_mem
    (measurableSet_Icc : MeasurableSet (I : Set ℝ))] with x hx
  rw [Set.indicator_of_mem hx]

/-- Pointwise splitting of the weighted kernel into indicator weight times the
unweighted kernel (local helper for `mulOperator_comp_TOp_riesz`). -/
private theorem rieszKernel_eq_indicator_mul_unweighted {psi c : ℝ} {omega : ℝ → ℝ}
    (p : ℝ × ℝ) :
    rieszKernel psi c omega p
      = (I : Set ℝ).indicator omega p.1 * unweightedRieszKernel psi c p := by
  show (I : Set ℝ).indicator omega p.1 * c * |p.1 - p.2| ^ (-psi)
      = (I : Set ℝ).indicator omega p.1 * (c * |p.1 - p.2| ^ (-psi))
  ring

/-- **Left multiplication by the weight is the kernel operation** (the `W ∘ T = T_R`
operator identity of spec §5): the weighted Riesz kernel operator factors as the
multiplication operator composed with the *unweighted* Riesz operator.  Proof:
pure inner-product transport with two a.e. congruences (no Fubini) — the
multiplication operator is moved to the test side by self-adjointness, its
representative is `omega • g` a.e., and `omega` agrees with its `I`-indicator
a.e. on the carrier. -/
theorem mulOperator_comp_TOp_riesz {psi c : ℝ} {omega : ℝ → ℝ} (hm : Measurable omega)
    {MR : ℝ} (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR)
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (hbdd : ∀ x : ℝ, |omega x| ≤ MR)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hpsi0 : 0 ≤ psi) (hpsi2 : 2 * psi < 1) :
    TOp (rieszKernel psi c omega) (hsKernel_rieszKernel hpow hm hbdd hg)
      = (mulOperator omega hm hess).comp
          (TOp (unweightedRieszKernel psi c)
            (hsKernel_unweightedRieszKernel hpsi0 hpsi2)) := by
  have hK : HSKernel (unweightedRieszKernel psi c) :=
    hsKernel_unweightedRieszKernel hpsi0 hpsi2
  have hKR : HSKernel (rieszKernel psi c omega) := hsKernel_rieszKernel hpow hm hbdd hg
  refine ContinuousLinearMap.ext fun f => eq_of_forall_inner_eq fun g => ?_
  calc inner ℝ (TOp (rieszKernel psi c omega) hKR f) g
      = kpair (rieszKernel psi c omega) f g := inner_TOp hKR f g
    _ = ∫ p : ℝ × ℝ, (I : Set ℝ).indicator omega p.1 * unweightedRieszKernel psi c p
          * (⇑f) p.2 * (⇑g) p.1 ∂vol2 := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
          show rieszKernel psi c omega p * (⇑f) p.2 * (⇑g) p.1
              = (I : Set ℝ).indicator omega p.1 * unweightedRieszKernel psi c p
                * (⇑f) p.2 * (⇑g) p.1
          rw [rieszKernel_eq_indicator_mul_unweighted p]
    _ = ∫ p : ℝ × ℝ, omega p.1 * unweightedRieszKernel psi c p
          * (⇑f) p.2 * (⇑g) p.1 ∂vol2 := by
          refine integral_congr_ae ?_
          filter_upwards [eventual_fst indicator_omega_ae] with p hp
          show (I : Set ℝ).indicator omega p.1 * unweightedRieszKernel psi c p
              * (⇑f) p.2 * (⇑g) p.1
            = omega p.1 * unweightedRieszKernel psi c p * (⇑f) p.2 * (⇑g) p.1
          rw [hp]
    _ = ∫ p : ℝ × ℝ, unweightedRieszKernel psi c p * (⇑f) p.2
          * (omega p.1 * (⇑g) p.1) ∂vol2 := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
          show omega p.1 * unweightedRieszKernel psi c p * (⇑f) p.2 * (⇑g) p.1
              = unweightedRieszKernel psi c p * (⇑f) p.2 * (omega p.1 * (⇑g) p.1)
          ring
    _ = ∫ p : ℝ × ℝ, unweightedRieszKernel psi c p * (⇑f) p.2
          * (⇑(mulOperator omega hm hess g)) p.1 ∂vol2 := by
          refine integral_congr_ae ?_
          filter_upwards [eventual_fst (coeFn_mulOperator_action omega hm hess g)]
            with p hp
          show unweightedRieszKernel psi c p * (⇑f) p.2 * (omega p.1 * (⇑g) p.1)
              = unweightedRieszKernel psi c p * (⇑f) p.2
                * (⇑(mulOperator omega hm hess g)) p.1
          rw [hp]
    _ = kpair (unweightedRieszKernel psi c) f (mulOperator omega hm hess g) := rfl
    _ = inner ℝ (TOp (unweightedRieszKernel psi c) hK f)
          (mulOperator omega hm hess g) := (inner_TOp hK f _).symm
    _ = inner ℝ (mulOperator omega hm hess
          (TOp (unweightedRieszKernel psi c) hK f)) g :=
        (mulOperator_symm omega hm hess
          (TOp (unweightedRieszKernel psi c) hK f) g).symm
    _ = inner ℝ ((mulOperator omega hm hess).comp
          (TOp (unweightedRieszKernel psi c) hK) f) g := rfl

/-- **The weighted kernel operator acts on the eigenfamily through the weight**:
if `v` is an eigenfamily of the *unweighted* Riesz operator with eigenvalues `κ`,
then `TOp (rieszKernel psi c omega) (v j) = κ j • M_omega (v j)`. -/
theorem TOp_riesz_apply_eigenfamily {psi c : ℝ} {omega : ℝ → ℝ} (hm : Measurable omega)
    {MR : ℝ} (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR)
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (hbdd : ∀ x : ℝ, |omega x| ≤ MR)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hpsi0 : 0 ≤ psi) (hpsi2 : 2 * psi < 1)
    {ι : Type} {v : ι → L2} {κ : ι → ℝ}
    (he : ∀ i, TOp (unweightedRieszKernel psi c)
        (hsKernel_unweightedRieszKernel hpsi0 hpsi2) (v i) = κ i • v i) (j : ι) :
    TOp (rieszKernel psi c omega) (hsKernel_rieszKernel hpow hm hbdd hg) (v j)
      = κ j • mulOperator omega hm hess (v j) := by
  rw [mulOperator_comp_TOp_riesz hm hess hpow hbdd hg hpsi0 hpsi2,
    ContinuousLinearMap.comp_apply, he j,
    (mulOperator omega hm hess).map_smul (κ j) (v j)]

/-! ### 2. The general-index tensor-ONB Parseval and `cycle2` expansion -/

/-- **Tensor-ONB Parseval along a complete orthonormal family** (general-index form
of the landed `kernel_inner_eq_tsum_prodKernel`, verbatim proof): the section family
`p ↦ v p.2 ⊗ v p.1` of a complete orthonormal family `v` is a Hilbert basis of the
kernel space `L²(vol2)`, so kernel inner products expand as coordinate series. -/
theorem kernel_inner_eq_tsum_prodKernel' {ι : Type*} {v : ι → L2}
    (hv : Orthonormal ℝ v) (hcomp : (span ℝ (Set.range v))ᗮ = ⊥)
    (g₁ g₂ : MeasureTheory.Lp ℝ 2 vol2) :
    inner ℝ g₁ g₂ = ∑' p : ι × ι,
      inner ℝ g₁ (prodKernel (v p.2) (v p.1))
        * inner ℝ g₂ (prodKernel (v p.2) (v p.1)) := by
  have hWcomp : (span ℝ (Set.range fun p : ι × ι => prodKernel (v p.2) (v p.1)))ᗮ
      = ⊥ := sections_span_orthogonal_eq_bot hcomp
  have hexp := (HilbertBasis.mkOfOrthogonalEqBot (orthonormal_prodKernel hv)
    hWcomp).tsum_inner_mul_inner g₁ g₂
  simp only [HilbertBasis.coe_mkOfOrthogonalEqBot] at hexp
  refine hexp.symm.trans (tsum_congr fun p => ?_)
  rw [real_inner_comm (prodKernel (v p.2) (v p.1)) g₂]

/-- **`cycle2` as the matrix-entry double series along a complete orthonormal
family** (general-index form of the landed `cycle2_eq_tsum_pair`, verbatim proof):
`cycle2 L K = ∑' (i, j), ⟪TOp K (v j), v i⟫ · ⟪TOp L (v i), v j⟫`. -/
theorem cycle2_eq_tsum_pair' {ι : Type*} {v : ι → L2}
    (hv : Orthonormal ℝ v) (hcomp : (span ℝ (Set.range v))ᗮ = ⊥)
    {K L : ℝ × ℝ → ℝ} (hK : HSKernel K) (hL : HSKernel L) :
    HS.cycle2 L K = ∑' p : ι × ι,
      inner ℝ (TOp K hK (v p.2)) (v p.1) * inner ℝ (TOp L hL (v p.1)) (v p.2) := by
  have hcyc : HS.cycle2 L K = ∫ p : ℝ × ℝ, L p * (ktranspose K) p ∂vol2 := rfl
  have key := kernel_inner_eq_tsum_prodKernel' hv hcomp (MemLp.toLp L hL)
    (MemLp.toLp (ktranspose K) (hsKernel_transpose hK))
  rw [inner_toLp_toLp hL (hsKernel_transpose hK)] at key
  refine hcyc.trans (key.trans (tsum_congr fun p => ?_))
  rw [inner_prodKernel_pairing (K := L) (hK := hL) (v := v) p,
    inner_prodKernel_pairing (K := ktranspose K) (hK := hsKernel_transpose hK)
      (v := v) p,
    inner_TOp_transpose hK (v p.1) (v p.2), mul_comm]

/-! ### 3. Sublemma ②: the kernel-side `k = 2` expansion -/

/-- **Sublemma ② (kernel side of the `k = 2` compression identity)**: the
second-power diagonal sum of the weighted kernel operator over any Hilbert basis
equals the κ-weighted matrix-square sum of the multiplication operator on the
unweighted eigenfamily,

  `∑' i, ⟪(T_R ^ 2) (e i), e i⟫ = ∑'_{p : ι²} κ p.1 κ p.2 ⟪v p.1, M_omega (v p.2)⟫²`.

Route: the landed `tracePair_comp_tsum` identifies the diagonal pairing with
`cycle2 K_R K_R` (this replaces the per-fiber Parseval over `e` of the old plan);
the general-index `cycle2_eq_tsum_pair'` expands `cycle2` along the eigenfamily;
`TOp_riesz_apply_eigenfamily` supplies the matrix entries; the symmetry of
`M_omega` (real weight) collapses the cross factors. -/
theorem diag2_TOpRiesz_eq_kappaWeighted_matrixSum {psi c : ℝ} {omega : ℝ → ℝ}
    (hm : Measurable omega) {MR : ℝ} (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR)
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (hbdd : ∀ x : ℝ, |omega x| ≤ MR)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hpsi0 : 0 ≤ psi) (hpsi2 : 2 * psi < 1)
    {ι : Type} {v : ι → L2} {κ : ι → ℝ}
    (hv : Orthonormal ℝ v)
    (he : ∀ i, TOp (unweightedRieszKernel psi c)
        (hsKernel_unweightedRieszKernel hpsi0 hpsi2) (v i) = κ i • v i)
    (hcomp : (span ℝ (Set.range v))ᗮ = ⊥)
    (e : HilbertBasis ℕ ℝ L2) :
    (∑' i : ℕ, inner ℝ
        ((TOp (rieszKernel psi c omega) (hsKernel_rieszKernel hpow hm hbdd hg) ^ 2)
          (e i)) (e i))
      = ∑' p : ι × ι, κ p.1 * κ p.2
          * inner ℝ (v p.1) (mulOperator omega hm hess (v p.2)) ^ 2 := by
  have hKR : HSKernel (rieszKernel psi c omega) := hsKernel_rieszKernel hpow hm hbdd hg
  -- the operator power is iterated application (k = 2)
  have hp2 : ∀ i : ℕ,
      ((TOp (rieszKernel psi c omega) hKR ^ 2) (e i))
        = TOp (rieszKernel psi c omega) hKR
            (TOp (rieszKernel psi c omega) hKR (e i)) := by
    intro i
    rw [pow_two]
    rfl
  -- the eigenfamily action supplies the matrix entries
  have hWs : ∀ x y : L2,
      inner ℝ (mulOperator omega hm hess x) y
        = inner ℝ x (mulOperator omega hm hess y) := mulOperator_symm omega hm hess
  have hentW : ∀ (i j : ι),
      inner ℝ (TOp (rieszKernel psi c omega) hKR (v j)) (v i)
        = κ j * inner ℝ (mulOperator omega hm hess (v j)) (v i) := by
    intro i j
    rw [TOp_riesz_apply_eigenfamily hm hess hpow hbdd hg hpsi0 hpsi2 he j,
      real_inner_smul_left]
  -- the weight-matrix entries are symmetric (real weight)
  have hcross : ∀ (i j : ι),
      inner ℝ (v j) (mulOperator omega hm hess (v i))
        = inner ℝ (v i) (mulOperator omega hm hess (v j)) := by
    intro i j
    rw [← real_inner_comm (v j) (mulOperator omega hm hess (v i)),
      hWs (v i) (v j)]
  -- pointwise collapse of the pair product to the κ-weighted square
  have hpt : ∀ p : ι × ι,
      inner ℝ (TOp (rieszKernel psi c omega) hKR (v p.2)) (v p.1)
          * inner ℝ (TOp (rieszKernel psi c omega) hKR (v p.1)) (v p.2)
        = κ p.1 * κ p.2
            * inner ℝ (v p.1) (mulOperator omega hm hess (v p.2)) ^ 2 := by
    intro p
    rw [hentW p.1 p.2, hentW p.2 p.1, hWs (v p.2) (v p.1),
      real_inner_comm (v p.2) (mulOperator omega hm hess (v p.1)),
      hcross p.1 p.2]
    ring
  calc (∑' i : ℕ, inner ℝ
          ((TOp (rieszKernel psi c omega) hKR ^ 2) (e i)) (e i))
      = ∑' i : ℕ, inner ℝ (TOp (rieszKernel psi c omega) hKR
            (TOp (rieszKernel psi c omega) hKR (e i))) (e i) :=
        tsum_congr fun i => by rw [hp2 i]
    _ = HS.cycle2 (rieszKernel psi c omega) (rieszKernel psi c omega) :=
        tracePair_comp_tsum hKR hKR e
    _ = ∑' p : ι × ι,
          inner ℝ (TOp (rieszKernel psi c omega) hKR (v p.2)) (v p.1)
            * inner ℝ (TOp (rieszKernel psi c omega) hKR (v p.1)) (v p.2) :=
        cycle2_eq_tsum_pair' hv hcomp hKR hKR
    _ = ∑' p : ι × ι, κ p.1 * κ p.2
            * inner ℝ (v p.1) (mulOperator omega hm hess (v p.2)) ^ 2 :=
        tsum_congr hpt

/-! ### 4. Sublemma ①: basis ↔ eigenfamily matrix-square equality -/

/-- **Sublemma ① (basis transport of matrix squares)**: for a self-adjoint `B`
whose matrix-square families over both the complete orthonormal eigenfamily `v`
and the Hilbert basis `e` are ℝ-summable, the two matrix-square double sums
coincide,

  `∑'_{p : ℕ²} ⟪e p.1, B (e p.2)⟫² = ∑'_{q : ι²} ⟪v q.1, B (v q.2)⟫²`.

Route: the ENNReal Tonelli/Parseval chain of the landed `A7_aux` with every step
an equality (the final collapse against `MR² ∑' κ²` replaced by the identity stop
at the `v`-matrix family); the ℝ-level equality is then transported through the
injectivity of `ENNReal.ofReal` on both sides. -/
theorem matrixSq_sum_eq_of_complete {ι : Type} {B : L2 →L[ℝ] L2} {v : ι → L2}
    (hv : Orthonormal ℝ v) (hcomp : (span ℝ (Set.range v))ᗮ = ⊥)
    (hBsymm : (↑B : L2 →ₗ[ℝ] L2).IsSymmetric)
    (hQ : Summable (fun p : ι × ι => inner ℝ (v p.2) (B (v p.1)) ^ 2))
    (e : HilbertBasis ℕ ℝ L2)
    (hE : Summable (fun p : ℕ × ℕ => inner ℝ (e p.1) (B (e p.2)) ^ 2)) :
    (∑' p : ℕ × ℕ, inner ℝ (e p.1) (B (e p.2)) ^ 2)
      = ∑' q : ι × ι, inner ℝ (v q.1) (B (v q.2)) ^ 2 := by
  classical
  -- Parseval with the family on the left, for `v` and for `e` (as in `A7_aux`)
  have pvv : ∀ u : L2, ‖u‖ ^ 2 = ∑' i : ι, inner ℝ (v i) u ^ 2 := by
    intro u
    rw [norm_sq_eq_tsum_inner_sq_of_complete hv hcomp u]
    exact tsum_congr fun i => by rw [real_inner_comm]
  have pee : ∀ u : L2, ‖u‖ ^ 2 = ∑' i : ℕ, inner ℝ (e i) u ^ 2 := by
    intro u
    have h := e.tsum_inner_mul_inner u u
    rw [real_inner_self_eq_norm_sq] at h
    rw [← h]
    exact tsum_congr fun i => by rw [real_inner_comm u (e i)]; ring
  have hsumE : ∀ u : L2, Summable (fun i : ℕ => inner ℝ (e i) u ^ 2) := fun u =>
    (summable_inner_sq_of_hilbertBasis e u).congr fun i => by rw [real_inner_comm]
  -- flip `⟪v k, B (e j)⟫ = ⟪e j, B (v k)⟫` by self-adjointness of `B` (as in `A7_aux`)
  have hflip : ∀ (k : ι) (j : ℕ),
      inner ℝ (v k) (B (e j)) = inner ℝ (e j) (B (v k)) := by
    intro k j
    calc inner ℝ (v k) (B (e j))
        = inner ℝ (B (v k)) (e j) := (hBsymm (v k) (e j)).symm
      _ = inner ℝ (e j) (B (v k)) := real_inner_comm (e j) (B (v k))
  -- the v-matrix-square flip by self-adjointness of `B` (for the final orientation)
  have hflipB : ∀ (i j : ι),
      inner ℝ (v i) (B (v j)) = inner ℝ (v j) (B (v i)) := by
    intro i j
    calc inner ℝ (v i) (B (v j))
        = inner ℝ (B (v j)) (v i) := (real_inner_comm (v i) (B (v j))).symm
      _ = inner ℝ (v j) (B (v i)) := hBsymm (v j) (v i)
  -- the ENNReal Tonelli chain, all steps equalities (as in `A7_aux`)
  have key : ∑' p : ℕ × ℕ, ENNReal.ofReal (inner ℝ (e p.1) (B (e p.2)) ^ 2)
      = ENNReal.ofReal (∑' q : ι × ι, inner ℝ (v q.2) (B (v q.1)) ^ 2) := by
    calc ∑' p : ℕ × ℕ, ENNReal.ofReal (inner ℝ (e p.1) (B (e p.2)) ^ 2)
        = ∑' i : ℕ, ∑' j : ℕ,
            ENNReal.ofReal (inner ℝ (e i) (B (e j)) ^ 2) :=
          ENNReal.tsum_prod' (f := fun p : ℕ × ℕ =>
            ENNReal.ofReal (inner ℝ (e p.1) (B (e p.2)) ^ 2))
      _ = ∑' j : ℕ, ∑' i : ℕ,
            ENNReal.ofReal (inner ℝ (e i) (B (e j)) ^ 2) := ENNReal.tsum_comm
      _ = ∑' j : ℕ,
            ENNReal.ofReal (∑' i : ℕ, inner ℝ (e i) (B (e j)) ^ 2) :=
          tsum_congr fun j => (ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _)
            (hsumE (B (e j)))).symm
      _ = ∑' j : ℕ, ENNReal.ofReal (‖B (e j)‖ ^ 2) :=
          tsum_congr fun j => by rw [pee (B (e j))]
      _ = ∑' j : ℕ, ∑' k : ι,
            ENNReal.ofReal (inner ℝ (v k) (B (e j)) ^ 2) := by
          refine tsum_congr fun j => ?_
          rw [pvv (B (e j)), ENNReal.ofReal_tsum_of_nonneg (fun k => sq_nonneg _)
            (summable_inner_sq_orth hv (B (e j)))]
      _ = ∑' k : ι, ∑' j : ℕ,
            ENNReal.ofReal (inner ℝ (v k) (B (e j)) ^ 2) := ENNReal.tsum_comm
      _ = ∑' k : ι, ∑' j : ℕ,
            ENNReal.ofReal (inner ℝ (e j) (B (v k)) ^ 2) :=
          tsum_congr fun k => tsum_congr fun j =>
            congrArg (fun t : ℝ => ENNReal.ofReal (t ^ 2)) (hflip k j)
      _ = ∑' k : ι, ENNReal.ofReal (‖B (v k)‖ ^ 2) := by
          refine tsum_congr fun k => ?_
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => sq_nonneg _) (hsumE (B (v k))),
            ← pee (B (v k))]
      _ = ∑' k : ι, ∑' i : ι,
            ENNReal.ofReal (inner ℝ (v i) (B (v k)) ^ 2) := by
          refine tsum_congr fun k => ?_
          rw [pvv (B (v k)), ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _)
            (summable_inner_sq_orth hv (B (v k)))]
      _ = ∑' q : ι × ι,
            ENNReal.ofReal (inner ℝ (v q.2) (B (v q.1)) ^ 2) :=
          (ENNReal.tsum_prod' (f := fun q : ι × ι =>
            ENNReal.ofReal (inner ℝ (v q.2) (B (v q.1)) ^ 2))).symm
      _ = ENNReal.ofReal (∑' q : ι × ι, inner ℝ (v q.2) (B (v q.1)) ^ 2) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun q => sq_nonneg _) hQ).symm
  -- transport through `ofReal` using the ℝ-summability on both sides
  have hE' : ∑' p : ℕ × ℕ, ENNReal.ofReal (inner ℝ (e p.1) (B (e p.2)) ^ 2)
      = ENNReal.ofReal (∑' p : ℕ × ℕ, inner ℝ (e p.1) (B (e p.2)) ^ 2) :=
    (ENNReal.ofReal_tsum_of_nonneg (fun p => sq_nonneg _) hE).symm
  have hfull : ENNReal.ofReal (∑' p : ℕ × ℕ, inner ℝ (e p.1) (B (e p.2)) ^ 2)
      = ENNReal.ofReal (∑' q : ι × ι, inner ℝ (v q.2) (B (v q.1)) ^ 2) :=
    hE'.symm.trans key
  have htr := congrArg ENNReal.toReal hfull
  rw [ENNReal.toReal_ofReal (tsum_nonneg fun p => sq_nonneg _),
    ENNReal.toReal_ofReal (tsum_nonneg fun q => sq_nonneg _)] at htr
  calc (∑' p : ℕ × ℕ, inner ℝ (e p.1) (B (e p.2)) ^ 2)
      = ∑' q : ι × ι, inner ℝ (v q.2) (B (v q.1)) ^ 2 := htr
    _ = ∑' q : ι × ι, inner ℝ (v q.1) (B (v q.2)) ^ 2 := by
        refine tsum_congr fun q => ?_
        rw [hflipB q.2 q.1]

/-! ### 5. The `k = 2` assembly -/

set_option linter.unusedVariables false in
/-- **The `k = 2` compression identity** (CapstoneV3's `hTwo` on the hconst-free
line): the second-power diagonal sum of the model `B = S ∘ M_omega ∘ S` over any
Hilbert basis equals the weighted Riesz cycle integral of order 2,

  `∑' i, ⟪(B ^ 2) (e i), e i⟫ = Hurst.weightedRieszCycleIntegral 2 psi c omega`.

Route (all landed pieces plus the two sublemmas above): symmetric collapse
`diag2_symmetric_eq_sumSq` → per-column Parseval + reassembly over `e` → sublemma ①
basis transport → the `√(κ_i κ_j)`-matrix formula `inner_Bop_matrix` → sublemma ②
kernel-side expansion → `diagSum_TOpRiesz_pow_eq_weightedCycle` at `k = 2`.
(`{T}` is named only implicitly, through `he`; it is kept as a binder so that
consumers can pass it by name — see `tsum_Briesz_valSq_eq_weightedCycle`.) -/
theorem diag2_Bop_eq_weightedCycle {psi c : ℝ} (hpsi0 : 0 ≤ psi) (hpsi2 : 2 * psi < 1)
    (omega : ℝ → ℝ) (hm : Measurable omega) {MR : ℝ}
    (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR)
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (hbdd : ∀ x : ℝ, |omega x| ≤ MR)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    {T : L2 →L[ℝ] L2} {ι : Type} {v : ι → L2} {κ : ι → ℝ}
    (hv : Orthonormal ℝ v)
    (he : ∀ i, TOp (unweightedRieszKernel psi c)
        (hsKernel_unweightedRieszKernel hpsi0 hpsi2) (v i) = κ i • v i)
    (hcomp : (span ℝ (Set.range v))ᗮ = ⊥)
    (hκ0 : ∀ i, 0 ≤ κ i) (hκ : Summable (fun i => κ i ^ 2))
    (e : HilbertBasis ℕ ℝ L2) :
    (∑' i : ℕ, inner ℝ ((Bop hv he hκ0 omega hm hess ^ 2) (e i)) (e i))
      = Hurst.weightedRieszCycleIntegral 2 psi c omega := by
  classical
  have hKR : HSKernel (rieszKernel psi c omega) := hsKernel_rieszKernel hpow hm hbdd hg
  -- the A7 pieces (landed): e-side and v-side matrix-square summability
  obtain ⟨hD, _hDb⟩ := Bop_A7_matrix_summable_bound hv he hcomp hκ0 hκ omega hm hess e
  obtain ⟨hF, _hFb⟩ := summable_and_bound_matrix (v := v) hv hcomp hκ0 hκ
    (mulOperator omega hm hess) (mulOperator_symm omega hm hess)
    (norm_mulOperator_apply_le omega hm hess)
  have hQpoint : ∀ p : ι × ι,
      inner ℝ (v p.2) (Bop hv he hκ0 omega hm hess (v p.1)) ^ 2
        = κ p.1 * κ p.2
            * inner ℝ (v p.2) (mulOperator omega hm hess (v p.1)) ^ 2 := by
    intro p
    rw [inner_Bop_matrix hv he hκ0 omega hm hess p.2 p.1, mul_pow,
      Real.sq_sqrt (mul_nonneg (hκ0 p.2) (hκ0 p.1))]
    ring
  have hQ : Summable (fun p : ι × ι =>
      inner ℝ (v p.2) (Bop hv he hκ0 omega hm hess (v p.1)) ^ 2) :=
    hF.congr fun p => (hQpoint p).symm
  -- the weight-matrix symmetry (for the orientation of the matrix formula)
  have hWs : ∀ x y : L2,
      inner ℝ (mulOperator omega hm hess x) y
        = inner ℝ x (mulOperator omega hm hess y) := mulOperator_symm omega hm hess
  have hWcross : ∀ (i j : ι),
      inner ℝ (v j) (mulOperator omega hm hess (v i))
        = inner ℝ (v i) (mulOperator omega hm hess (v j)) := by
    intro i j
    rw [← real_inner_comm (v j) (mulOperator omega hm hess (v i)), hWs (v i) (v j)]
  have hMat : ∀ q : ι × ι,
      inner ℝ (v q.1) (Bop hv he hκ0 omega hm hess (v q.2)) ^ 2
        = κ q.1 * κ q.2
            * inner ℝ (v q.1) (mulOperator omega hm hess (v q.2)) ^ 2 := by
    intro q
    rw [inner_Bop_matrix hv he hκ0 omega hm hess q.1 q.2, mul_pow,
      Real.sq_sqrt (mul_nonneg (hκ0 q.1) (hκ0 q.2)), hWcross q.2 q.1]
  -- Parseval over `e` (as in `A7_aux`)
  have pee : ∀ u : L2, ‖u‖ ^ 2 = ∑' i : ℕ, inner ℝ (e i) u ^ 2 := by
    intro u
    have h := e.tsum_inner_mul_inner u u
    rw [real_inner_self_eq_norm_sq] at h
    rw [← h]
    exact tsum_congr fun i => by rw [real_inner_comm u (e i)]; ring
  have hsumE : ∀ u : L2, Summable (fun i : ℕ => inner ℝ (e i) u ^ 2) := fun u =>
    (summable_inner_sq_of_hilbertBasis e u).congr fun i => by rw [real_inner_comm]
  -- column reassembly data: the swapped double family and its fibers
  have hDswap : Summable (fun p : ℕ × ℕ =>
      inner ℝ (e p.2) (Bop hv he hκ0 omega hm hess (e p.1)) ^ 2) := by
    have h2 : Summable ((fun p : ℕ × ℕ =>
        (inner ℝ (e p.1) (Bop hv he hκ0 omega hm hess (e p.2))) ^ 2)
        ∘ (Equiv.prodComm ℕ ℕ)) := Equiv.summable_iff (Equiv.prodComm ℕ ℕ) |>.mpr hD
    exact h2.congr fun p => rfl
  have hDfibswap : ∀ b : ℕ, Summable (fun c : ℕ =>
      inner ℝ (e c) (Bop hv he hκ0 omega hm hess (e b)) ^ 2) :=
    fun b => hsumE (Bop hv he hκ0 omega hm hess (e b))
  -- summability of the column norms, then the landed symmetric collapse
  have hnnDswap : ∀ p : ℕ × ℕ,
      0 ≤ inner ℝ (e p.2) (Bop hv he hκ0 omega hm hess (e p.1)) ^ 2 :=
    fun p => sq_nonneg _
  obtain ⟨_, hcolsum⟩ := (summable_prod_of_nonneg hnnDswap).mp hDswap
  have hBS : Summable (fun j : ℕ =>
      ‖Bop hv he hκ0 omega hm hess (e j)‖ ^ 2) :=
    hcolsum.congr fun j => (pee (Bop hv he hκ0 omega hm hess (e j))).symm
  obtain ⟨_, hdiag2⟩ :=
    diag2_symmetric_eq_sumSq (Bop_symm hv he hκ0 omega hm hess) e hBS
  -- the e-matrix-square flip by self-adjointness of `B` (orientation fix)
  have hflipE : ∀ p : ℕ × ℕ,
      inner ℝ (e p.2) (Bop hv he hκ0 omega hm hess (e p.1))
        = inner ℝ (e p.1) (Bop hv he hκ0 omega hm hess (e p.2)) := by
    intro p
    calc inner ℝ (e p.2) (Bop hv he hκ0 omega hm hess (e p.1))
        = inner ℝ (Bop hv he hκ0 omega hm hess (e p.1)) (e p.2) :=
          (real_inner_comm (e p.2) (Bop hv he hκ0 omega hm hess (e p.1))).symm
      _ = inner ℝ (e p.1) (Bop hv he hκ0 omega hm hess (e p.2)) :=
          Bop_symm hv he hκ0 omega hm hess (e p.1) (e p.2)
  -- the assembly chain
  calc (∑' i : ℕ, inner ℝ ((Bop hv he hκ0 omega hm hess ^ 2) (e i)) (e i))
      = ∑' i : ℕ, ‖Bop hv he hκ0 omega hm hess (e i)‖ ^ 2 := hdiag2
    _ = ∑' j : ℕ, ∑' i : ℕ,
            inner ℝ (e i) (Bop hv he hκ0 omega hm hess (e j)) ^ 2 :=
          tsum_congr fun j => pee (Bop hv he hκ0 omega hm hess (e j))
    _ = ∑' p : ℕ × ℕ,
            inner ℝ (e p.2) (Bop hv he hκ0 omega hm hess (e p.1)) ^ 2 :=
          (Summable.tsum_prod' hDswap hDfibswap).symm
    _ = ∑' p : ℕ × ℕ,
            inner ℝ (e p.1) (Bop hv he hκ0 omega hm hess (e p.2)) ^ 2 :=
          tsum_congr fun p => by rw [hflipE p]
    _ = ∑' q : ι × ι,
            inner ℝ (v q.1) (Bop hv he hκ0 omega hm hess (v q.2)) ^ 2 :=
          matrixSq_sum_eq_of_complete hv hcomp
            (Bop_symm hv he hκ0 omega hm hess) hQ e hD
    _ = ∑' q : ι × ι, κ q.1 * κ q.2
            * inner ℝ (v q.1) (mulOperator omega hm hess (v q.2)) ^ 2 :=
          tsum_congr hMat
    _ = (∑' i : ℕ, inner ℝ
            ((TOp (rieszKernel psi c omega) hKR ^ 2) (e i)) (e i)) :=
        (diag2_TOpRiesz_eq_kappaWeighted_matrixSum hm hess hpow hbdd hg hpsi0 hpsi2
          hv he hcomp e).symm
    _ = Hurst.weightedRieszCycleIntegral 2 psi c omega :=
        (diagSum_TOpRiesz_pow_eq_weightedCycle hpow hm hbdd hg hpsi2 hpsi0
          2 (by norm_num) e).2

/-- **The `k = 2` spectral identification** (combination of the landed B-side
enumeration with the `k = 2` compression identity): the model `B = S ∘ M_omega ∘ S`
carries a multiplicity-exact, square-summable spectral enumeration whose square sum
`∑' val ^ 2` is exactly the weighted Riesz cycle integral of order 2 — the `hTwo`
member of `exists_weightedRieszSpectrum_min` (whose general-`k` form remains a
declared gap). -/
theorem tsum_Briesz_valSq_eq_weightedCycle {psi c : ℝ} (hpsi0 : 0 < psi)
    (hpsi2 : 2 * psi < 1) (hc : 0 < c) (omega : ℝ → ℝ) (hm : Measurable omega)
    {MR : ℝ} (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR)
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (hbdd : ∀ x : ℝ, |omega x| ≤ MR)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (e : HilbertBasis ℕ ℝ L2) :
    ∃ (ι : Type) (v : ι → L2) (κ : ι → ℝ) (B : L2 →L[ℝ] L2) (val : ℕ → ℝ)
      (vec : ℕ → L2),
      Orthonormal ℝ v
      ∧ (∀ i, TOp (unweightedRieszKernel psi c)
          (hsKernel_unweightedRieszKernel (le_of_lt hpsi0) hpsi2) (v i) = κ i • v i)
      ∧ ((span ℝ (Set.range v))ᗮ = ⊥)
      ∧ (∀ i, 0 ≤ κ i)
      ∧ Summable (fun i => κ i ^ 2)
      ∧ IsCompactOperator B
      ∧ (↑B : L2 →ₗ[ℝ] L2).IsSymmetric
      ∧ (∀ i j : ι, inner ℝ (v i) (B (v j))
          = Real.sqrt (κ i * κ j) * inner ℝ (v i) (mulOperator omega hm hess (v j)))
      ∧ (∃ Cbar : ℝ, 0 ≤ Cbar ∧ ∀ g : HilbertBasis ℕ ℝ L2,
          Summable (fun p : ℕ × ℕ => (inner ℝ (g p.1) (B (g p.2))) ^ 2)
            ∧ (∑' p : ℕ × ℕ, (inner ℝ (g p.1) (B (g p.2))) ^ 2) ≤ Cbar)
      ∧ IsDiagEnum (↑B : L2 →ₗ[ℝ] L2) val vec
      ∧ (∀ μ : ℝ, Module.End.HasEigenvalue (↑B : L2 →ₗ[ℝ] L2) μ → μ ≠ 0 →
          Nat.card {m : ℕ // val m = μ}
            = Module.finrank ℝ (Module.End.eigenspace (↑B : L2 →ₗ[ℝ] L2) μ))
      ∧ Summable (fun m : ℕ => val m ^ 2)
      ∧ (∑' m : ℕ, val m ^ 2)
          = Hurst.weightedRieszCycleIntegral 2 psi c omega := by
  classical
  -- the concrete structural package, verbatim from the landed
  -- `exists_Briesz_spectral_enumeration` (kept concrete so that the `k = 2`
  -- compression identity applies to the very same operator)
  obtain ⟨ι, v, κ, hv, he, hcomp, hκ0, hκs⟩ :=
    exists_nonneg_eigenfamily hpsi0 hpsi2 hc.le
  have hBcomp : IsCompactOperator (Bop hv he hκ0 omega hm hess) :=
    Bop_isCompactOperator hv he hκ0 hκs omega hm hess
  have hBsym : (↑(Bop hv he hκ0 omega hm hess) : L2 →ₗ[ℝ] L2).IsSymmetric :=
    Bop_symm hv he hκ0 omega hm hess
  have hBmat : ∀ i j : ι, inner ℝ (v i) (Bop hv he hκ0 omega hm hess (v j))
      = Real.sqrt (κ i * κ j) * inner ℝ (v i) (mulOperator omega hm hess (v j)) :=
    inner_Bop_matrix hv he hκ0 omega hm hess
  have hBA7 : ∃ Cbar : ℝ, 0 ≤ Cbar ∧ ∀ g : HilbertBasis ℕ ℝ L2,
      Summable (fun p : ℕ × ℕ =>
        (inner ℝ (g p.1) (Bop hv he hκ0 omega hm hess (g p.2))) ^ 2)
        ∧ (∑' p : ℕ × ℕ,
          (inner ℝ (g p.1) (Bop hv he hκ0 omega hm hess (g p.2))) ^ 2) ≤ Cbar :=
    ⟨MR ^ 2 * ∑' i : ι, κ i ^ 2,
      mul_nonneg (sq_nonneg MR) (tsum_nonneg fun i => sq_nonneg (κ i)),
      fun g => Bop_A7_matrix_summable_bound hv he hcomp hκ0 hκs omega hm hess g⟩
  obtain ⟨val, vec, hdiag, hmult, _hbound⟩ :=
    exists_diag_enumeration_clm (T := Bop hv he hκ0 omega hm hess) hBsym hBcomp
  have hbridge := hBridge_clm hBsym hBcomp hBA7 hdiag hmult 2 (by norm_num) e
  -- the k = 2 compression identity for the very same operator
  have hdiag2 := diag2_Bop_eq_weightedCycle
    (T := TOp (unweightedRieszKernel psi c)
      (hsKernel_unweightedRieszKernel (le_of_lt hpsi0) hpsi2))
    (le_of_lt hpsi0) hpsi2 omega hm hess hpow hbdd hg hv he hcomp hκ0 hκs e
  -- the enumeration's k = 2 HasSum identifies ∑' val ^ 2 with the diagonal sum
  rw [hbridge.2.tsum_eq] at hdiag2
  exact ⟨ι, v, κ, Bop hv he hκ0 omega hm hess, val, vec, hv, he, hcomp, hκ0, hκs,
    hBcomp, hBsym, hBmat, hBA7, hdiag, hmult, hbridge.1, hdiag2⟩

end HS

end
