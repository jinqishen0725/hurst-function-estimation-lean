import Hurst.HSOperatorLayer3
import Hurst.ExternalSecondChaosLimit

/-!
# Cycle trace identification for the Riesz spectrum construction

This file is the last piece of P2's `rieszSpectrum` construction: the identification
between the operator-side cycle pairings on the landed `HS` layer and the
continuum cycle integrals `Hurst.weightedRieszCycleIntegral k psi c omega`
(the `HasSum` targets of `Hurst.IsWeightedRieszSpectrum`).

## What is landed here (all sorry-free)

* `weightedRieszCycleIntegral_eq_kernelProd` — **general `k`**: the cycle integral is
  exactly the `volume^k`-integral of the product `∏ i, HS.rieszKernel psi c omega
  (z i, z (Hurst.finCyclicSucc i))` of the Riesz kernel along the cycle, i.e. the
  kernel integrand matches `weightedRieszCycleIntegral`'s integrand **exactly**
  (the `ω`-row indicator times `c·|z i − z_{succ i}|^(−ψ)` over the cyclic pairs).
* `cycle2_rieszKernel_eq_weighted` — **`k = 2` kernel identification**:
  `HS.cycle2 (rieszKernel psi c omega) (rieszKernel psi c omega)
    = weightedRieszCycleIntegral 2 psi c omega`, consistent with the landed
  `HS.cycle2 K L = ∫∫ K(x,y) L(y,x)` and `HS.cycle2_bound`.  The proof moves the
  integral along the measure-preserving equiv `MeasurableEquiv.piFinTwo`
  (`measurePreserving_piFinTwo` with target `vol.prod vol`), so no integrability
  side conditions are needed.
* `tracePair_hasSum_degenerate` — **the `k = 2` trace identification over a
  Hilbert basis `e` of `L2`**, for degenerate (finite-rank) kernels:
  `HasSum (fun j => ⟪TOp K (e j), (TOp K)† (e j)⟫) (cycle2 K K)`; the `j`-th term
  is exactly the diagonal trace-power term `⟪(TOp K)^2 (e j), e j⟫`
  (`tracePower2_hasSum_degenerate`).
* `tracePair_kpair_tsum` — the operator-side trace pairing is the `kpair` cycle.

## Paper verdict on the general-`k` trace-identity route

The general CLM trace `tr(T)` (basis-independent for trace-class operators only)
has **no mathlib v4.31 API** (no Schatten/trace-class library), so the honest
formulation of the trace-power identification is the *eigenbasis-restricted*
one: for compact self-adjoint `T = TOp K` with eigenbasis `{e_j}` of `(ker T)⊥`
and eigenvalues `κ_j`, `Σ_j ⟪T^k e_j, e_j⟫ = Σ_j κ_j^k` (kernel vectors
contribute `0`), and the HasSum consumption of P2 needs precisely
`Σ_j κ_j^k = weightedRieszCycleIntegral k psi c omega`.

For `k = 2` this file reduces that to `cycle2 K K` (which is
`weightedRieszCycleIntegral 2` for the Riesz kernel).  The extension from
degenerate kernels to general `HSKernel K` — and the whole general-`k` induction
`tr((TOp K)^{k+1}) = tr((TOp K)^k · TOp K)` peeling one kernel factor per step —
is blocked by a single mathlib gap, isolated here:

* **Gap (isolated):** `Σ_j ⟪T (e j), S (e j)⟫ = ⟪K_T, K_S⟫_{L²(vol²)}` for general
  HS kernels requires Parseval for the **tensor-product orthonormal system**
  `ψ_{ij}(x,y) = (e i)(x) · (e j)(y)` in `L²(vol.prod vol)`, i.e. completeness of
  the product of two Hilbert bases under the `vol ⊗ vol` encoding.  Mathlib
  v4.31 has nothing for `L²` of a product measure, and the double series
  `Σ_{i,j} |⟪TOp K (e j), e i⟫|² = hsNorm K²` genuinely *needs* it (Bessel per
  column only bounds `Σ_j |⟪T (e j), e i⟫|² ≤ ‖T‖²`, and summing over `i`
  diverges without the HS-norm identity).  Once the product-basis completeness
  lemma is landed, the density route finishes: degenerate kernels are `hsNorm`-
  dense (`HS.exists_continuous_approx` + mesh kernels), and the trace pairing
  satisfies the trace-class bound `|Σ_j ⟪X (e j), Y (e j)⟫| ≤ (∫∫ X²)^{1/2}(∫∫ Y²)^{1/2}`
  by Cauchy–Schwarz over the basis, so both sides of the identification are
  continuous in the kernel and the degenerate case extends.
* For general `k ≥ 3`, the same gap plus an iterated-Fubini composition bound
  `|cycle_k| ≤ hsNorm K^k` (the file-23 A2 bound; `k = 2` is `HS.cycle2_bound`)
  would give the induction.  The kernel-side integrand bookkeeping for general
  `k` is already exact (`weightedRieszCycleIntegral_eq_kernelProd`).

`IsWeightedRieszSpectrum`'s `HasSum` consumption path is therefore:
`Σ_j λ_j^k` —(eigenbasis of the enumerated compact self-adjoint `TOp K_R`)→
`Σ_j ⟪(TOp K_R)^k e_j, e_j⟫` —(this file for `k = 2`; Gap for `k ≥ 3`)→
`cycle_k K_R … K_R` —(`weightedRieszCycleIntegral_eq_kernelProd`)→
`weightedRieszCycleIntegral k psi c omega`.
-/

open MeasureTheory Measure Real Set
open scoped Real

noncomputable section

namespace HS

/-! ### Small private helpers -/

private theorem hasSum_congr {f g : ℕ → ℝ} {a : ℝ} (h : ∀ j, f j = g j) (hf : HasSum f a) :
    HasSum g a := by
  rw [← funext h]
  exact hf

private theorem hasSum_const_mul {f : ℕ → ℝ} {t : ℝ} (h : HasSum f t) (C : ℝ) :
    HasSum (fun j => C * f j) (C * t) := by
  have h2 : HasSum (fun j => f j * C) (t * C) := HasSum.smul_const h C
  have h3 : HasSum (fun j => C * f j) (t * C) := hasSum_congr (fun j => mul_comm (f j) C) h2
  rw [mul_comm C t]
  exact h3

private theorem hasSum_finset_mul {ι : Type*} (t : Finset ι) (c : ι → ℝ)
    (f : ι → ℕ → ℝ) (g : ι → ℝ) (h : ∀ p ∈ t, HasSum (f p) (g p)) :
    HasSum (fun j => ∑ p ∈ t, c p * f p j) (∑ p ∈ t, c p * g p) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      have hzero : ∀ j : ℕ, (∑ p ∈ (∅ : Finset ι), c p * f p j) = 0 := fun j => Finset.sum_empty
      refine hasSum_congr hzero ?_
      exact hasSum_zero
  | insert p t hp ih =>
      have hfun : ∀ j : ℕ,
          (∑ q ∈ insert p t, c q * f q j) = c p * f p j + ∑ q ∈ t, c q * f q j :=
        fun j => Finset.sum_insert hp
      have hval : (∑ q ∈ insert p t, c q * g q) = c p * g p + ∑ q ∈ t, c q * g q :=
        Finset.sum_insert hp
      rw [hval]
      refine hasSum_congr (fun j => (hfun j).symm) ?_
      exact (hasSum_const_mul (h p (Finset.mem_insert_self p t)) (c p)).add
        (ih fun q hq => h q (Finset.mem_insert_of_mem hq))

/-! ### The cyclic product form of the Riesz kernel -/

/-- The cyclic integrand of `weightedRieszCycleIntegral` is exactly the product of
the Riesz kernel along the cycle — for **every** `k`, pointwise in `z`. -/
theorem rieszCycleIntegrand_eq (k : ℕ) (psi c : ℝ) (omega : ℝ → ℝ)
    (z : Fin k → ℝ) :
    (∏ i : Fin k, HS.rieszKernel psi c omega (z i, z (Hurst.finCyclicSucc i)))
      = ∏ i : Fin k, (Icc (-1 : ℝ) 1).indicator omega (z i) * c
          * |z i - z (Hurst.finCyclicSucc i)| ^ (-psi) :=
  Finset.prod_congr rfl fun i _ => rieszKernel_apply psi c omega (z i) (z (Hurst.finCyclicSucc i))

/-- **General-`k` kernel identification**: the continuum cycle integral is the
`volume^k`-integral of the Riesz-kernel cycle product. -/
theorem weightedRieszCycleIntegral_eq_kernelProd (k : ℕ) (psi c : ℝ) (omega : ℝ → ℝ) :
    Hurst.weightedRieszCycleIntegral k psi c omega
      = ∫ z : Fin k → ℝ,
          ∏ i : Fin k, HS.rieszKernel psi c omega (z i, z (Hurst.finCyclicSucc i))
          ∂(volume : Measure (Fin k → ℝ)) := by
  unfold Hurst.weightedRieszCycleIntegral
  exact integral_congr_ae (Filter.Eventually.of_forall (rieszCycleIntegrand_eq k psi c omega))

/-! ### The `k = 2` identification between `cycle2` and the cycle integral -/

/-- The unit cube `[-1,1]²` inside `Fin 2 → ℝ`. -/
abbrev cube2 : Set (Fin 2 → ℝ) := Set.pi univ (fun _ : Fin 2 => (I : Set ℝ))

private theorem measurableSet_cube2 : MeasurableSet cube2 :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc

private theorem integral_eq_cube2 {M : Measure (Fin 2 → ℝ)} (F : (Fin 2 → ℝ) → ℝ)
    (hF : ∀ z, F z = cube2.indicator F z) :
    ∫ z, F z ∂M = ∫ z in cube2, F z ∂M := by
  rw [integral_congr_ae (Filter.Eventually.of_forall hF), integral_indicator measurableSet_cube2]

private theorem integral_pi_vol_eq_pi_volume (F : (Fin 2 → ℝ) → ℝ)
    (hF : ∀ z, F z = cube2.indicator F z) :
    ∫ z, F z ∂(Measure.pi (fun _ : Fin 2 => vol))
      = ∫ z, F z ∂(volume : Measure (Fin 2 → ℝ)) := by
  have hmeq : (Measure.pi (fun _ : Fin 2 => (volume : Measure ℝ))).restrict cube2
      = (Measure.pi (fun _ : Fin 2 => vol)).restrict cube2 := by
    simp only [cube2, restrict_pi_pi, vol]
    rw [Measure.restrict_restrict_of_subset (Set.Subset.refl (I : Set ℝ))]
  have hmeq2 : (∫ z, F z ∂((Measure.pi (fun _ : Fin 2 => (volume : Measure ℝ))).restrict cube2))
      = (∫ z, F z ∂((Measure.pi (fun _ : Fin 2 => vol)).restrict cube2)) :=
    congrArg (fun M : Measure (Fin 2 → ℝ) => (∫ z, F z ∂M)) hmeq
  have hint1 : ∫ z, F z ∂(Measure.pi (fun _ : Fin 2 => vol))
      = ∫ z in cube2, F z ∂(Measure.pi (fun _ : Fin 2 => vol)) := integral_eq_cube2 F hF
  have hint2 : ∫ z, F z ∂(volume : Measure (Fin 2 → ℝ))
      = ∫ z in cube2, F z ∂(volume : Measure (Fin 2 → ℝ)) := integral_eq_cube2 F hF
  rw [hint1, hint2, hmeq2]

private theorem finCyclicSucc_two_zero : Hurst.finCyclicSucc (0 : Fin 2) = 1 := rfl

private theorem finCyclicSucc_two_one : Hurst.finCyclicSucc (1 : Fin 2) = 0 := rfl

private theorem cycle2_integrand_fin2 (psi c : ℝ) (omega : ℝ → ℝ) (z : Fin 2 → ℝ) :
    (∏ i : Fin 2, (Icc (-1 : ℝ) 1).indicator omega (z i) * c
        * |z i - z (Hurst.finCyclicSucc i)| ^ (-psi))
      = (fun w : ℝ × ℝ =>
          rieszKernel psi c omega w * rieszKernel psi c omega w.swap)
          (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ) z) := by
  show (∏ i : Fin 2, (Icc (-1 : ℝ) 1).indicator omega (z i) * c
        * |z i - z (Hurst.finCyclicSucc i)| ^ (-psi))
      = rieszKernel psi c omega (z 0, z 1) * rieszKernel psi c omega (z 1, z 0)
  rw [Fin.prod_univ_two, finCyclicSucc_two_zero, finCyclicSucc_two_one,
    rieszKernel_apply, rieszKernel_apply]

private theorem cube2_indicator_fin2 (F : (Fin 2 → ℝ) → ℝ) (hzero : ∀ z ∉ cube2, F z = 0)
    (z : Fin 2 → ℝ) : F z = cube2.indicator F z := by
  by_cases hz : z ∈ cube2
  · rw [Set.indicator_of_mem hz]
  · rw [Set.indicator_of_notMem hz]
    exact hzero z hz

/-- **`k = 2` identification**: the two-point cycle pairing of the Riesz kernel
with itself is exactly the continuum cycle integral of the weight —
`∫∫ K_R(x,y) K_R(y,x) dxdy = weightedRieszCycleIntegral 2 psi c omega`. -/
theorem cycle2_rieszKernel_eq_weighted (psi c : ℝ) (omega : ℝ → ℝ) :
    cycle2 (rieszKernel psi c omega) (rieszKernel psi c omega)
      = Hurst.weightedRieszCycleIntegral 2 psi c omega := by
  have hzero : ∀ z ∉ cube2,
      (∏ i : Fin 2, (Icc (-1 : ℝ) 1).indicator omega (z i) * c
          * |z i - z (Hurst.finCyclicSucc i)| ^ (-psi)) = 0 := by
    intro z hz
    simp only [Set.mem_pi, Set.mem_univ] at hz
    have hex : ∃ i : Fin 2, z i ∉ (Icc (-1 : ℝ) 1 : Set ℝ) := by
      by_contra hall
      refine hz (fun i _ => ?_)
      by_contra hi
      exact hall ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hex
    exact Finset.prod_eq_zero (i := i) (Finset.mem_univ i)
      (by rw [Set.indicator_of_notMem hi]; ring)
  calc cycle2 (rieszKernel psi c omega) (rieszKernel psi c omega)
      = ∫ w : ℝ × ℝ, rieszKernel psi c omega w * rieszKernel psi c omega w.swap ∂vol2 := rfl
    _ = ∫ z : Fin 2 → ℝ,
          (fun w : ℝ × ℝ => rieszKernel psi c omega w * rieszKernel psi c omega w.swap)
            (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ) z)
          ∂(Measure.pi (fun _ : Fin 2 => vol)) :=
        (measurePreserving_piFinTwo (fun _ : Fin 2 => vol)).integral_comp' _ |>.symm
    _ = ∫ z : Fin 2 → ℝ,
          ∏ i : Fin 2, (Icc (-1 : ℝ) 1).indicator omega (z i) * c
            * |z i - z (Hurst.finCyclicSucc i)| ^ (-psi)
          ∂(Measure.pi (fun _ : Fin 2 => vol)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        exact (cycle2_integrand_fin2 psi c omega z).symm
    _ = ∫ z : Fin 2 → ℝ,
          ∏ i : Fin 2, (Icc (-1 : ℝ) 1).indicator omega (z i) * c
            * |z i - z (Hurst.finCyclicSucc i)| ^ (-psi)
          ∂(volume : Measure (Fin 2 → ℝ)) :=
        integral_pi_vol_eq_pi_volume _ (fun z => cube2_indicator_fin2 _ hzero z)
    _ = Hurst.weightedRieszCycleIntegral 2 psi c omega := by
        rw [weightedRieszCycleIntegral_eq_kernelProd]
        exact integral_congr_ae (Filter.Eventually.of_forall fun z =>
          (rieszCycleIntegrand_eq 2 psi c omega z).symm)

/-! ### The operator-side trace pairing as the `kpair` cycle -/

/-- The operator-side trace pairing (over a Hilbert basis) is the kernel pairing
cycle: each `TOp` application converts one kernel factor into a `kpair` slot. -/
theorem tracePair_kpair_tsum {K : ℝ × ℝ → ℝ} (hK : HSKernel K)
    (S : L2 →L[ℝ] L2) (e : HilbertBasis ℕ ℝ L2) :
    (∑' j : ℕ, inner ℝ (TOp K hK (S (e j))) (e j))
      = ∑' j : ℕ, kpair K (S (e j)) (e j) :=
  tsum_congr fun j => inner_TOp hK _ _

/-! ### The `k = 2` trace identification over a Hilbert basis (degenerate kernels) -/

private theorem inner_degenerate_pair {ι : Type*} (s : Finset ι) (a b : ι → ℝ → ℝ)
    (ha : ∀ i, MemLp (a i) 2 vol) (hb : ∀ i, MemLp (b i) 2 vol)
    (c d : ι → ℝ) (e : L2) :
    inner ℝ (∑ i ∈ s, c i • MemLp.toLp (a i) (ha i))
        (∑ i ∈ s, d i • MemLp.toLp (b i) (hb i))
      = ∑ i' ∈ s, (∑ i ∈ s, c i * (∫ x, a i x * b i' x ∂vol)) * d i' := by
  rw [inner_sum]
  refine Finset.sum_congr rfl fun i' _ => ?_
  rw [real_inner_smul_right, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hcoe : (fun x : ℝ => a i x * ⇑(MemLp.toLp (b i') (hb i')) x) =ᵐ[vol]
      (fun x : ℝ => a i x * b i' x) :=
    Filter.EventuallyEq.mul Filter.EventuallyEq.rfl (MemLp.coeFn_toLp (hb i'))
  rw [real_inner_smul_left, inner_toLp (ha i), integral_congr_ae hcoe]

private theorem hasSum_pair_term (e : HilbertBasis ℕ ℝ L2) {u v : ℝ → ℝ}
    (hu : MemLp u 2 vol) (hv : MemLp v 2 vol) (C : ℝ) :
    HasSum
      (fun j : ℕ => C * ((∫ x, u x * ⇑(e j) x ∂vol) * (∫ x, ⇑(e j) x * v x ∂vol)))
      (C * ∫ x, u x * v x ∂vol) := by
  have hcongr : ∀ j : ℕ,
      inner ℝ (MemLp.toLp u hu) (e j) * inner ℝ (e j) (MemLp.toLp v hv)
        = (∫ x, u x * ⇑(e j) x ∂vol) * (∫ x, ⇑(e j) x * v x ∂vol) := by
    intro j
    have hcoe : (fun x : ℝ => ⇑(e j) x * ⇑(MemLp.toLp v hv) x) =ᵐ[vol]
        (fun x : ℝ => ⇑(e j) x * v x) :=
      Filter.EventuallyEq.mul Filter.EventuallyEq.rfl (MemLp.coeFn_toLp hv)
    rw [inner_toLp hu, L2_inner_eq, integral_congr_ae hcoe]
  have hval : inner ℝ (MemLp.toLp u hu) (MemLp.toLp v hv) = ∫ x, u x * v x ∂vol := by
    have hcoe : (fun x : ℝ => u x * ⇑(MemLp.toLp v hv) x) =ᵐ[vol]
        (fun x : ℝ => u x * v x) :=
      Filter.EventuallyEq.mul Filter.EventuallyEq.rfl (MemLp.coeFn_toLp hv)
    rw [inner_toLp hu, integral_congr_ae hcoe]
  have hfin := hasSum_congr hcongr (hasSum_const_mul (e.hasSum_inner_mul_inner _ _) C)
  rw [hval] at hfin
  exact hfin

/-- **The `k = 2` trace identification over a Hilbert basis** (degenerate kernels):
the diagonal adjoint pairings `⟪TOp K (e j), (TOp K)ᵀ (e j)⟫` have sum exactly
`cycle2 K K = ∫∫ K(x,y) K(y,x) dxdy`.  The second kernel is the transpose
`ktranspose K` in its degenerate form `∑ i ∈ s, b i p.1 * a i p.2`. -/
theorem tracePair_hasSum_degenerate {ι : Type*} (s : Finset ι) (a b : ι → ℝ → ℝ)
    (ha : ∀ i, MemLp (a i) 2 vol) (hb : ∀ i, MemLp (b i) 2 vol)
    (e : HilbertBasis ℕ ℝ L2) :
    HasSum
      (fun j : ℕ => inner ℝ
        (TOp (fun p => ∑ i ∈ s, a i p.1 * b i p.2) (hsKernel_degenerate s a b ha hb) (e j))
        (TOp (fun p => ∑ i ∈ s, b i p.1 * a i p.2) (hsKernel_degenerate s b a hb ha) (e j)))
      (cycle2 (fun p => ∑ i ∈ s, a i p.1 * b i p.2)
        (fun p => ∑ i ∈ s, a i p.1 * b i p.2)) := by
  classical
  -- pointwise expansion of the `j`-th pairing term over the kernel summands
  have hstep : ∀ j : ℕ,
      inner ℝ
        (TOp (fun p => ∑ i ∈ s, a i p.1 * b i p.2) (hsKernel_degenerate s a b ha hb) (e j))
        (TOp (fun p => ∑ i ∈ s, b i p.1 * a i p.2) (hsKernel_degenerate s b a hb ha) (e j))
      = ∑ p ∈ s.product s, (∫ x, a p.1 x * b p.2 x ∂vol)
          * ((∫ y, b p.1 y * ⇑(e j) y ∂vol) * (∫ y, ⇑(e j) y * a p.2 y ∂vol)) := by
    intro j
    rw [TOp_apply, TOp_apply, TOpFun_degenerate s a b ha hb (e j),
      TOpFun_degenerate s b a hb ha (e j), inner_degenerate_pair s a b ha hb,
      Finset.sum_mul, Finset.sum_comm, ← Finset.sum_product]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [integral_congr_ae (Filter.Eventually.of_forall fun y => mul_comm (⇑(e j) y) (a p.2 y))]
    ring
  -- the `cycle2` value as the same double sum
  have hcycle2 : cycle2 (fun p => ∑ i ∈ s, a i p.1 * b i p.2)
        (fun p => ∑ i ∈ s, a i p.1 * b i p.2)
      = ∑ p ∈ s.product s, (∫ x, a p.1 x * b p.2 x ∂vol)
          * (∫ y, b p.1 y * a p.2 y ∂vol) := by
    have hint1 : ∀ i ∈ s, Integrable (fun q : ℝ × ℝ =>
        a i q.1 * b i q.2 * ∑ i' ∈ s, b i' q.1 * a i' q.2) vol2 := by
      intro i _
      have hS : MemLp (fun q : ℝ × ℝ => ∑ i' ∈ s, b i' q.1 * a i' q.2) 2 vol2 :=
        memLp_sum_finset s (fun i' q => b i' q.1 * a i' q.2)
          fun i' _ => memLp2_prod_fst_snd (hb i') (ha i')
      exact memLp_one_iff_integrable.mp
        (MemLp.mul hS (memLp2_prod_fst_snd (ha i) (hb i)))
    have hint2 : ∀ i ∈ s, ∀ i' ∈ s,
        Integrable (fun q : ℝ × ℝ =>
          a i q.1 * b i q.2 * (b i' q.1 * a i' q.2)) vol2 := by
      intro i _ i' _
      exact memLp_one_iff_integrable.mp
        (MemLp.mul (memLp2_prod_fst_snd (hb i') (ha i'))
          (memLp2_prod_fst_snd (ha i) (hb i)))
    have e0 : cycle2 (fun p => ∑ i ∈ s, a i p.1 * b i p.2)
        (fun p => ∑ i ∈ s, a i p.1 * b i p.2)
        = ∫ q : ℝ × ℝ, (∑ i ∈ s, a i q.1 * b i q.2)
            * (∑ i ∈ s, b i q.1 * a i q.2) ∂vol2 := rfl
    rw [e0, integral_congr_ae (Filter.Eventually.of_forall fun q => Finset.sum_mul _ _ _),
      integral_finsetSum s hint1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_congr_ae (Filter.Eventually.of_forall fun q => Finset.sum_mul _ _ _),
      integral_finsetSum s (hint2 i), ← Finset.sum_product]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [show (∫ q : ℝ × ℝ, a p.1 q.1 * b p.1 q.2 * (b p.2 q.1 * a p.2 q.2) ∂vol2)
        = ∫ q : ℝ × ℝ, (a p.1 q.1 * b p.2 q.1) * (b p.1 q.2 * a p.2 q.2) ∂vol2 from
      integral_congr_ae (Filter.Eventually.of_forall fun _q => by ring),
      integral_prod_mul (μ := vol) (ν := vol)
        (f := fun x => a p.1 x * b p.2 x) (g := fun y => b p.1 y * a p.2 y)]
  rw [hcycle2]
  exact hasSum_congr (fun j => (hstep j).symm)
    (hasSum_finset_mul s.product s
      (fun p => ∫ x, a p.1 x * b p.2 x ∂vol)
      (fun p j => (∫ y, b p.1 y * ⇑(e j) y ∂vol) * (∫ y, ⇑(e j) y * a p.2 y ∂vol))
      (fun p => ∫ y, b p.1 y * a p.2 y ∂vol)
      (fun p _ => hasSum_pair_term e (hb p.1) (ha p.2) _))

/-- **The `k = 2` trace-power identification over a Hilbert basis** (degenerate
kernels): the diagonal terms of the squared operator have sum exactly
`cycle2 K K`; by `cycle2_rieszKernel_eq_weighted` this is
`weightedRieszCycleIntegral 2` for the Riesz kernel.  This is the
`HasSum`-consumption shape of `IsWeightedRieszSpectrum` at `k = 2`. -/
theorem tracePower2_hasSum_degenerate {ι : Type*} (s : Finset ι) (a b : ι → ℝ → ℝ)
    (ha : ∀ i, MemLp (a i) 2 vol) (hb : ∀ i, MemLp (b i) 2 vol)
    (e : HilbertBasis ℕ ℝ L2) :
    HasSum
      (fun j : ℕ => inner ℝ
        (TOp (fun p => ∑ i ∈ s, a i p.1 * b i p.2) (hsKernel_degenerate s a b ha hb)
          (TOp (fun p => ∑ i ∈ s, a i p.1 * b i p.2)
            (hsKernel_degenerate s a b ha hb) (e j)))
        (e j))
      (cycle2 (fun p => ∑ i ∈ s, a i p.1 * b i p.2)
        (fun p => ∑ i ∈ s, a i p.1 * b i p.2)) := by
  classical
  have hKTpt : ∀ p : ℝ × ℝ,
      (fun p => ∑ i ∈ s, a i p.1 * b i p.2) p.swap
        = (∑ i ∈ s, b i p.1 * a i p.2 : ℝ × ℝ → ℝ) := by
    intro p
    show (∑ i ∈ s, a i p.2 * b i p.1) = _
    rw [Finset.sum_congr rfl fun i _ => mul_comm (a i p.2) (b i p.1)]
  refine hasSum_congr (fun j => ?_) (tracePair_hasSum_degenerate s a b ha hb e)
  rw [inner_TOp (hsKernel_degenerate s a b ha hb), inner_TOp (hsKernel_degenerate s b a hb ha),
    ← funext hKTpt, kpair_transpose (hsKernel_degenerate s a b ha hb)]

end HS

end
