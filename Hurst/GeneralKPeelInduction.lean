import Hurst.HSCycleComposition

/-!
# The general-`k` peel induction: the composed-kernel trace form of the `(n+2)`-cycle

This file completes the general-`k` peel induction left open in `Hurst.HSCycleComposition`:
for kernels `K : ℝ × ℝ → ℝ` (`HSKernel K = MemLp K 2 vol2`), the `(n+2)`-cycle integral
`cycleIntegral (n+2) K = ∫_{Icc^{n+2}} ∏ i, K (z i, z (cycleSucc i))` equals the
composed-kernel trace form `cycle2 (compPowR n K) K`, closing the general-`k` boundary
of the HasSum consumption anchored at the landed `k = 2` / `k = 3` cases.

## Main results (all sorry-free)

* (i) `stronglyMeasurable_section_fst/_snd` — the sections of a *measurable* kernel are
  **strongly measurable**: the `Exists`-encoding dialect of `StronglyMeasurable`
  (`∃ fs : ℕ → α →ₛ β, ∀ x, Tendsto (fun n => fs n x) atTop (𝓝 (f x))`) is discharged
  through `Measurable.stronglyMeasurable` (valid since `ℝ` is pseudo-metrizable with a
  second-countable topology), composed with the measurable section map.
  The a.e. section square-integrability lifts `ae_section_integrable_fst/_snd` (the
  `hliftK`/`hliftL` patterns of the landed `hsNorm_comp_le`) and
  `ae_section_memLp_fst/_snd` unblock the `hA`/`hB` discharges.
* (ii) `chainIntegral_peel` — **the peel step**: the `(n+2)`-chain integral of a kernel
  family `W` equals the `(n+1)`-chain integral of the contracted family `contract W`
  (the wrap-adjacent pair composed via `compKernel`), under the chain-integrability
  hypothesis `hP`.  Route: the measure-preserving coordinate insertion
  `measurePreserving_piFinSuccAbove` + Fubini (`integral_prod`) + the pointwise
  `chainProd_cons` factorization + the `compKernel` peel identity (each peel is exactly
  the landed `integral_compKernel_diag` pattern).  `integrable_contract` propagates the
  chain integrability to the contracted family (via `|compKernel| ≤ ∫ |sections|`), so
  the peel iterates.
* (iii) `chainIntegral_contrFam_eq` / `cycleIntegral_comp_general` — **the induction**:
  `cycleIntegral (n+2) K = cycle2 (compPowR n K) K` (the general-`k` trace form), with
  the composition tower bounds `hsNorm_compPowR_le` (`hsNorm (compPowR n K) ≤
  hsNorm K ^ (n+1)`).

## Honest residue (documented)

The induction carries the chain-integrability hypotheses `hP n : Integrable
(chainProd (n+2) (contrFam n K)) (vol^(n+2))` explicitly.  Their unconditional
discharge is the absolute-convergence chain (`∫ ∏ |K ∘ edges| ≤ hsNorm K^(n+2)` via
iterated section Cauchy–Schwarz, the generalization of the landed `hsNorm_comp_le`);
the `k = 3` case of exactly that discharge is the `hA`/`hB` gap documented in
`Hurst.HSCycleComposition`, and the general-`k` discharge is not landed here (budget).
For nonnegative kernels each `hP n` reduces to a Tonelli-finiteness statement.
-/

open MeasureTheory Measure Real Set
open scoped Real

noncomputable section

namespace HS

/-! ### The chain product and chain integral -/

/-- Cyclic successor value on `Fin k` (for the `cycleSucc` of
`Hurst.HSCycleComposition`). -/
theorem cycleSucc_val {k : ℕ} (i : Fin k) :
    ((cycleSucc i : Fin k) : ℕ) = if (i : ℕ) + 1 < k then (i : ℕ) + 1 else 0 := by
  unfold cycleSucc
  split <;> rfl

theorem cycleSucc_last' {k : ℕ} : cycleSucc (Fin.last k) = 0 := by
  apply Fin.ext
  rw [cycleSucc_val, if_neg (show ¬((Fin.last k : ℕ) + 1 < k) from by
    rw [Fin.val_last]; omega)]
  rfl

/-- The `k`-chain (cycle) product of a kernel family `W : Fin k → ℝ × ℝ → ℝ`. -/
def chainProd (k : ℕ) (W : Fin k → ℝ × ℝ → ℝ) (z : Fin k → ℝ) : ℝ :=
  ∏ i : Fin k, W i (z i, z (cycleSucc i))

/-- The `k`-chain (cycle) integral of a kernel family; `cycleIntegral k K =
chainIntegral k (fun _ => K)` definitionally. -/
def chainIntegral (k : ℕ) (W : Fin k → ℝ × ℝ → ℝ) : ℝ :=
  ∫ z : Fin k → ℝ, chainProd k W z ∂(Measure.pi fun _ : Fin k => vol)

theorem chainIntegral_eq_cycleIntegral (k : ℕ) (K : ℝ × ℝ → ℝ) :
    chainIntegral k (fun _ => K) = cycleIntegral k K := rfl

/-- The chain product is measurable when the kernels are. -/
theorem measurable_chainProd {k : ℕ} {W : Fin k → ℝ × ℝ → ℝ}
    (hW : ∀ i, Measurable (W i)) : Measurable (chainProd k W) := by
  unfold chainProd
  refine Finset.measurable_prod _ fun i _ => ?_
  exact (hW i).comp ((measurable_pi_apply i).prodMk (measurable_pi_apply (cycleSucc i)))

/-- The cyclic successor at a non-wrapping index. -/
theorem cycleSucc_succ {k : ℕ} {j : Fin k} (hj : (j : ℕ) + 1 < k) :
    cycleSucc j = ⟨(j : ℕ) + 1, hj⟩ := by
  simp only [cycleSucc, dif_pos hj]

/-! ### (i) StronglyMeasurable of sections -/

/-- **(i)** Sections in the first coordinate of a *measurable* kernel are **strongly
measurable** — the `Exists`-encoding dialect discharged via `Measurable.stronglyMeasurable`
(`ℝ` is pseudo-metrizable, second countable, with Borel-measurable opens). -/
theorem stronglyMeasurable_section_fst {K : ℝ × ℝ → ℝ} (hK : Measurable K) (x : ℝ) :
    StronglyMeasurable (fun t => K (x, t)) :=
  (hK.comp (measurable_const.prodMk measurable_id)).stronglyMeasurable

/-- **(i)** Sections in the second coordinate of a *measurable* kernel. -/
theorem stronglyMeasurable_section_snd {K : ℝ × ℝ → ℝ} (hK : Measurable K) (y : ℝ) :
    StronglyMeasurable (fun t => K (t, y)) :=
  (hK.comp (measurable_id.prodMk measurable_const)).stronglyMeasurable

/-- Sections of a measurable kernel are measurable. -/
theorem measurable_section_fst {K : ℝ × ℝ → ℝ} (hK : Measurable K) (x : ℝ) :
    Measurable (fun t => K (x, t)) :=
  hK.comp (measurable_const.prodMk measurable_id)

theorem measurable_section_snd {K : ℝ × ℝ → ℝ} (hK : Measurable K) (y : ℝ) :
    Measurable (fun t => K (t, y)) :=
  hK.comp (measurable_id.prodMk measurable_const)

/-- **(i)** A.e. square-integrability of the first-coordinate sections of a measurable
HS kernel (the `hliftK` pattern of the landed `hsNorm_comp_le`, at the `vol` level). -/
theorem ae_section_integrable_fst {K : ℝ × ℝ → ℝ} (hKm : Measurable K) (hK : HSKernel K) :
    ∀ᵐ x ∂vol, Integrable (fun t => K (x, t) ^ 2) vol := by
  have hK2meas : AEStronglyMeasurable (fun p : ℝ × ℝ => K p ^ 2) vol2 :=
    (hKm.pow_const 2).aestronglyMeasurable
  exact ((integrable_prod_iff hK2meas).mp (MemLp.integrable_sq hK)).1

/-- **(i)** A.e. square-integrability of the second-coordinate sections. -/
theorem ae_section_integrable_snd {K : ℝ × ℝ → ℝ} (hKm : Measurable K) (hK : HSKernel K) :
    ∀ᵐ y ∂vol, Integrable (fun t => K (t, y) ^ 2) vol := by
  have hK2meas : AEStronglyMeasurable (fun p : ℝ × ℝ => K p ^ 2) vol2 :=
    (hKm.pow_const 2).aestronglyMeasurable
  exact ((integrable_prod_iff' hK2meas).mp (MemLp.integrable_sq hK)).1

/-- **(i)** A.e. `MemLp 2` first-coordinate sections (the discharge ingredient for the
`hA`/`hB` attempts blocked in `Hurst.HSCycleComposition`). -/
theorem ae_section_memLp_fst {K : ℝ × ℝ → ℝ} (hKm : Measurable K) (hK : HSKernel K) :
    ∀ᵐ x ∂vol, MemLp (fun t => K (x, t)) 2 vol := by
  filter_upwards [ae_section_integrable_fst hKm hK] with x hx
  exact memLp_two_of_aemeasurable
    ((measurable_section_fst hKm x).aestronglyMeasurable) hx

/-- **(i)** A.e. `MemLp 2` second-coordinate sections. -/
theorem ae_section_memLp_snd {K : ℝ × ℝ → ℝ} (hKm : Measurable K) (hK : HSKernel K) :
    ∀ᵐ y ∂vol, MemLp (fun t => K (t, y)) 2 vol := by
  filter_upwards [ae_section_integrable_snd hKm hK] with y hy
  exact memLp_two_of_aemeasurable
    ((measurable_section_snd hKm y).aestronglyMeasurable) hy

/-! ### Transport helpers -/

/-- Integrability transports back along a measure-preserving equivalence. -/
theorem integrable_comp_measurePreserving {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {f : β → ℝ} (e : α ≃ β)
    (h : MeasurePreserving (⇑e) μ ν) (hf : Integrable f ν) :
    Integrable (fun x => f (e x)) μ := by
  refine ⟨hf.1.comp_measurePreserving h, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, ← eLpNorm_one_eq_lintegral_enorm,
    show eLpNorm (fun x => f (e x)) 1 μ = eLpNorm (f ∘ (⇑e)) 1 μ from rfl,
    eLpNorm_comp_measurePreserving hf.1 h, eLpNorm_one_eq_lintegral_enorm]
  exact hasFiniteIntegral_iff_enorm.mp hf.2

/-! ### (ii) The peel contraction and the peel step -/

/-- The peel contraction: for an `(n+2)`-chain `W`, `contract W : Fin (n+1) → _` composes
the wrap-adjacent pair `(W (Fin.last (n+1)), W 0)` into the last position. -/
def contract {n : ℕ} (W : Fin (n+2) → ℝ × ℝ → ℝ) : Fin (n+1) → ℝ × ℝ → ℝ :=
  fun j => if j = Fin.last n then compKernel (W (Fin.last (n+1))) (W 0) else W j.succ

theorem contract_apply_last {n : ℕ} (W : Fin (n+2) → ℝ × ℝ → ℝ) :
    contract W (Fin.last n) = compKernel (W (Fin.last (n+1))) (W 0) := by
  rw [contract, if_pos rfl]

theorem contract_apply_succ {n : ℕ} (W : Fin (n+2) → ℝ × ℝ → ℝ) {j : Fin (n+1)}
    (hj : j ≠ Fin.last n) : contract W j = W j.succ := by
  rw [contract, if_neg hj]

/-- Measurability of the contracted chain (measurable kernels). -/
theorem measurable_contract {n : ℕ} {W : Fin (n+2) → ℝ × ℝ → ℝ} (hWm : ∀ i, Measurable (W i))
    (j : Fin (n+1)) : Measurable (contract W j) := by
  by_cases hj : j = Fin.last n
  · rw [hj, contract_apply_last W]
    exact (stronglyMeasurable_compKernel (hWm _) (hWm _)).measurable
  · rw [contract_apply_succ W hj]
    exact hWm _

/-- The cons product factorizes through the wrap point: the product of the `(n+2)`-chain
at `Fin.cons a w` is the `a`-pair times the wrap-composed factor times the open-chain
product over the non-wrap indices. -/
theorem chainProd_cons {n : ℕ} (W : Fin (n+2) → ℝ × ℝ → ℝ) (a : ℝ) (w : Fin (n+1) → ℝ) :
    chainProd (n+2) W (Fin.cons a w)
      = W 0 (a, w 0) * W (Fin.last (n+1)) (w (Fin.last n), a)
        * ∏ j ∈ (Finset.univ.erase (Fin.last n) : Finset (Fin (n+1))),
            W j.succ (w j, w (cycleSucc j)) := by
  classical
  -- the cycle successor at a non-wrap successor index lands one further along
  have hcycle : ∀ j : Fin (n+1), j ≠ Fin.last n → cycleSucc j.succ = (cycleSucc j).succ := by
    intro j hj
    have hj2 := j.2
    have hjlt : (j : ℕ) < n := by
      by_cases hcon : (j : ℕ) < n
      · exact hcon
      · have : (j : ℕ) = n := by omega
        exact absurd (Fin.ext this) hj
    apply Fin.ext
    have hv1 : ((cycleSucc j : Fin (n+1)) : ℕ) = (j : ℕ) + 1 := by
      rw [cycleSucc_val, if_pos (by omega)]
    have hv2 : ((cycleSucc j.succ : Fin (n+2)) : ℕ) = (j : ℕ) + 2 := by
      rw [cycleSucc_val, Fin.val_succ, if_pos (by omega)]
    have hv3 : (((cycleSucc j).succ : Fin (n+2)) : ℕ) = (j : ℕ) + 2 := by
      rw [Fin.val_succ, hv1]
    rw [hv2, hv3]
  -- peel off the `j = Fin.last n` factor of the tail product
  have hstep : (∏ i : Fin (n+1), W i.succ ((Fin.cons a w) i.succ,
          (Fin.cons a w) (cycleSucc i.succ)))
      = W (Fin.last (n+1)) (w (Fin.last n), a)
        * ∏ j ∈ (Finset.univ.erase (Fin.last n) : Finset (Fin (n+1))),
            W j.succ (w j, w (cycleSucc j)) := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun i : Fin (n+1) => W i.succ ((Fin.cons a w) i.succ,
        (Fin.cons a w) (cycleSucc i.succ))) (Finset.mem_univ _)]
    refine congrArg _ (Finset.prod_congr rfl fun j hj => ?_)
    have hjn : j ≠ Fin.last n := Finset.neOfMem_erase hj
    rw [hcycle j hjn, Fin.cons_succ a w j, Fin.cons_succ a w (cycleSucc j)]
  -- the full product: `Fin.prod_univ_succ` splits off `i = 0`
  rw [chainProd, Fin.prod_univ_succ]
  have h0 : W 0 ((Fin.cons a w) 0, (Fin.cons a w) (cycleSucc 0)) = W 0 (a, w 0) := by
    have h01 : cycleSucc (0 : Fin (n+2)) = 1 := by
      apply Fin.ext
      simp [cycleSucc]
    rw [Fin.cons_zero, h01, Fin.cons_zero]
  have hlast : W (Fin.last n).succ ((Fin.cons a w) (Fin.last n).succ,
      (Fin.cons a w) (cycleSucc (Fin.last n).succ))
      = W (Fin.last (n+1)) (w (Fin.last n), a) := by
    have e1 : (Fin.last n).succ = Fin.last (n+1) := Fin.succ_last _
    have e2 : cycleSucc (Fin.last n).succ = 0 := by rw [e1]; exact cycleSucc_last'
    have e3 : (Fin.cons a w) (Fin.last n).succ = w (Fin.last n) := Fin.cons_succ a w _
    have e4 : (Fin.cons a w) 0 = a := Fin.cons_zero a w
    rw [e2, e4, e1, e3]
  rw [h0, hstep, hlast]
  ring

/-- The contracted-chain product reassembles the pre-product with the composed kernel
at the wrap. -/
theorem chainProd_contract {n : ℕ} (W : Fin (n+2) → ℝ × ℝ → ℝ) (w : Fin (n+1) → ℝ) :
    chainProd (n+1) (contract W) w
      = (∏ j ∈ (Finset.univ.erase (Fin.last n) : Finset (Fin (n+1))),
            W j.succ (w j, w (cycleSucc j)))
        * compKernel (W (Fin.last (n+1))) (W 0) (w (Fin.last n), w 0) := by
  classical
  rw [chainProd, ← Finset.mul_prod_erase Finset.univ
    (fun j : Fin (n+1) => contract W j (w j, w (cycleSucc j))) (Finset.mem_univ _)]
  have hlast : contract W (Fin.last n) (w (Fin.last n), w (cycleSucc (Fin.last n)))
      = compKernel (W (Fin.last (n+1))) (W 0) (w (Fin.last n), w 0) := by
    rw [cycleSucc_last', contract_apply_last W]
  refine congrArg₂ (fun x _ => x * _) (Finset.prod_congr rfl fun j hj => ?_) hlast
  have hjn : j ≠ Fin.last n := Finset.neOfMem_erase hj
  rw [contract_apply_succ W hjn]

/-- The coordinate-insertion equivalence `(Fin (n+2) → ℝ) ≃ ℝ × (Fin (n+1) → ℝ)`
preserves `vol^{n+2}` (pointing to `vol × vol^{n+1}`). -/
theorem measurePreserving_piSucc (n : ℕ) :
    MeasurePreserving
      (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+2) => ℝ) (0 : Fin (n+2))))
      (Measure.pi fun _ : Fin (n+2) => vol)
      (vol.prod (Measure.pi fun _ : Fin (n+1) => vol)) :=
  measurePreserving_piFinSuccAbove (fun _ => vol) 0

/-- The inverse insertion is `Fin.cons`. -/
theorem piFinSuccAbove_symm_cons {n : ℕ} (a : ℝ) (w : Fin (n+1) → ℝ) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+2) => ℝ) (0 : Fin (n+2))).symm (a, w)
      = Fin.cons a w := by
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero']

/-- The transported chain product on the split coordinates. -/
def splitChainProd {n : ℕ} (W : Fin (n+2) → ℝ × ℝ → ℝ) :
    ℝ × (Fin (n+1) → ℝ) → ℝ :=
  fun p => chainProd (n+2) W (Fin.cons p.1 p.2)

theorem splitChainProd_apply {n : ℕ} (W : Fin (n+2) → ℝ × ℝ → ℝ) (p : ℝ × (Fin (n+1) → ℝ)) :
    splitChainProd W p = chainProd (n+2) W (Fin.cons p.1 p.2) := rfl

theorem splitChainProd_apply_piSucc {n : ℕ} (W : Fin (n+2) → ℝ × ℝ → ℝ)
    (z : Fin (n+2) → ℝ) :
    chainProd (n+2) W z
      = splitChainProd W
          (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+2) => ℝ) (0 : Fin (n+2))) z := by
  have hcons : Fin.cons (z 0) (fun j : Fin (n+1) => z j.succ) = z := by
    funext j
    fin_cases j
    · simp [Fin.cons_zero]
    · simp [Fin.cons_succ]
  have hfw : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+2) => ℝ) (0 : Fin (n+2))) z
      = (z 0, fun j : Fin (n+1) => z j.succ) := by
    have h1 := congrArg
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+2) => ℝ) (0 : Fin (n+2))) hcons
    rw [← piFinSuccAbove_symm_cons, MeasurableEquiv.apply_symm_apply] at h1
    exact h1.symm
  show chainProd (n+2) W z
      = chainProd (n+2) W
          (Fin.cons
            ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+2) => ℝ) (0 : Fin (n+2))) z).1
            ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+2) => ℝ) (0 : Fin (n+2))) z).2)
  rw [hfw, hcons]

/-- **(ii) The peel step**: the `(n+2)`-chain integral equals the `(n+1)`-chain integral
of the contracted family — the general-`k` Fubini peel (each peel is the landed
`integral_compKernel_diag` pattern), under the chain-integrability hypothesis. -/
theorem chainIntegral_peel {n : ℕ} (W : Fin (n+2) → ℝ × ℝ → ℝ)
    (hP : Integrable (chainProd (n+2) W) (Measure.pi fun _ : Fin (n+2) => vol)) :
    chainIntegral (n+2) W = chainIntegral (n+1) (contract W) := by
  classical
  have hmp : MeasurePreserving
      (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+2) => ℝ) (0 : Fin (n+2))))
      (Measure.pi fun _ : Fin (n+2) => vol)
      (vol.prod (Measure.pi fun _ : Fin (n+1) => vol)) := measurePreserving_piSucc n
  have hmsymm : MeasurePreserving
      (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+2) => ℝ) (0 : Fin (n+2))).symm)
      (vol.prod (Measure.pi fun _ : Fin (n+1) => vol))
      (Measure.pi fun _ : Fin (n+2) => vol) :=
    MeasurePreserving.symm
      (e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+2) => ℝ) (0 : Fin (n+2))) hmp
  have hgInt : Integrable (splitChainProd W)
      (vol.prod (Measure.pi fun _ : Fin (n+1) => vol)) := by
    have hgeq : (splitChainProd W)
        = fun x : ℝ × (Fin (n+1) → ℝ) => chainProd (n+2) W
            ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+2) => ℝ) (0 : Fin (n+2))).symm x) := by
      funext p
      simp only [splitChainProd_apply, piFinSuccAbove_symm_cons]
    rw [hgeq]
    exact integrable_comp_measurePreserving
      (e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+2) => ℝ) (0 : Fin (n+2))).symm)
      hmsymm hP
  have hstep1 : chainIntegral (n+2) W
      = ∫ p : ℝ × (Fin (n+1) → ℝ), splitChainProd W p
          ∂(vol.prod (Measure.pi fun _ : Fin (n+1) => vol)) := by
    rw [← hmp.integral_comp' (fun p => splitChainProd W p)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show chainProd (n+2) W z
        = splitChainProd W
            (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+2) => ℝ) (0 : Fin (n+2))) z
    exact splitChainProd_apply_piSucc W z
  have hstep2 : (∫ p : ℝ × (Fin (n+1) → ℝ), splitChainProd W p
          ∂(vol.prod (Measure.pi fun _ : Fin (n+1) => vol)))
      = ∫ w : (Fin (n+1) → ℝ), ∫ a : ℝ, splitChainProd W (a, w) ∂vol
          ∂(Measure.pi fun _ : Fin (n+1) => vol) :=
    integral_prod (fun p => splitChainProd W p) hgInt
  have hstep3 : (∫ w : (Fin (n+1) → ℝ), ∫ a : ℝ, splitChainProd W (a, w) ∂vol
          ∂(Measure.pi fun _ : Fin (n+1) => vol))
      = ∫ w : (Fin (n+1) → ℝ), chainProd (n+1) (contract W) w
          ∂(Measure.pi fun _ : Fin (n+1) => vol) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    have hint : ∫ a : ℝ, splitChainProd W (a, w) ∂vol
        = ∫ a : ℝ, chainProd (n+2) W (Fin.cons a w) ∂vol := rfl
    rw [hint]
    have hcons : ∀ a : ℝ, chainProd (n+2) W (Fin.cons a w)
        = W 0 (a, w 0) * W (Fin.last (n+1)) (w (Fin.last n), a)
          * ∏ j ∈ (Finset.univ.erase (Fin.last n) : Finset (Fin (n+1))),
              W j.succ (w j, w (cycleSucc j)) := fun a => chainProd_cons W a w
    have hcomp : ∫ a : ℝ, W 0 (a, w 0) * W (Fin.last (n+1)) (w (Fin.last n), a)
          * ∏ j ∈ (Finset.univ.erase (Fin.last n) : Finset (Fin (n+1))),
              W j.succ (w j, w (cycleSucc j)) ∂vol
        = (∏ j ∈ (Finset.univ.erase (Fin.last n) : Finset (Fin (n+1))),
              W j.succ (w j, w (cycleSucc j)))
          * compKernel (W (Fin.last (n+1))) (W 0) (w (Fin.last n), w 0) := by
      have h1 : (∫ a : ℝ, W 0 (a, w 0) * W (Fin.last (n+1)) (w (Fin.last n), a)
          * ∏ j ∈ (Finset.univ.erase (Fin.last n) : Finset (Fin (n+1))),
              W j.succ (w j, w (cycleSucc j)) ∂vol)
          = (∫ a : ℝ, W (Fin.last (n+1)) (w (Fin.last n), a) * W 0 (a, w 0)
              * ∏ j ∈ (Finset.univ.erase (Fin.last n) : Finset (Fin (n+1))),
                W j.succ (w j, w (cycleSucc j)) ∂vol) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
        ring
      have h2 : (∫ a : ℝ, W (Fin.last (n+1)) (w (Fin.last n), a) * W 0 (a, w 0)
              * ∏ j ∈ (Finset.univ.erase (Fin.last n) : Finset (Fin (n+1))),
                W j.succ (w j, w (cycleSucc j)) ∂vol)
          = (∫ a : ℝ, (∏ j ∈ (Finset.univ.erase (Fin.last n) : Finset (Fin (n+1))),
                W j.succ (w j, w (cycleSucc j)))
              * (W (Fin.last (n+1)) (w (Fin.last n), a) * W 0 (a, w 0)) ∂vol) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
        ring
      have h3 : (∫ a : ℝ, (∏ j ∈ (Finset.univ.erase (Fin.last n) : Finset (Fin (n+1))),
                W j.succ (w j, w (cycleSucc j)))
              * (W (Fin.last (n+1)) (w (Fin.last n), a) * W 0 (a, w 0)) ∂vol)
          = (∏ j ∈ (Finset.univ.erase (Fin.last n) : Finset (Fin (n+1))),
                W j.succ (w j, w (cycleSucc j)))
            * ∫ a : ℝ, W (Fin.last (n+1)) (w (Fin.last n), a) * W 0 (a, w 0) ∂vol :=
        integral_const_mul _ _
      have h4 : (∫ a : ℝ, W (Fin.last (n+1)) (w (Fin.last n), a) * W 0 (a, w 0) ∂vol)
          = compKernel (W (Fin.last (n+1))) (W 0) (w (Fin.last n), w 0) := rfl
      rw [h1, h2, h3, h4]
    calc ∫ a : ℝ, chainProd (n+2) W (Fin.cons a w) ∂vol
        = ∫ a : ℝ, W 0 (a, w 0) * W (Fin.last (n+1)) (w (Fin.last n), a)
              * ∏ j ∈ (Finset.univ.erase (Fin.last n) : Finset (Fin (n+1))),
                W j.succ (w j, w (cycleSucc j)) ∂vol := by
          rw [integral_congr_ae (Filter.Eventually.of_forall fun a => hcons a)]
      _ = (∏ j ∈ (Finset.univ.erase (Fin.last n) : Finset (Fin (n+1))),
              W j.succ (w j, w (cycleSucc j)))
            * compKernel (W (Fin.last (n+1))) (W 0) (w (Fin.last n), w 0) := hcomp
      _ = chainProd (n+1) (contract W) w := (chainProd_contract W w)
  calc chainIntegral (n+2) W
      = ∫ p : ℝ × (Fin (n+1) → ℝ), splitChainProd W p
          ∂(vol.prod (Measure.pi fun _ : Fin (n+1) => vol)) := hstep1
    _ = ∫ w : (Fin (n+1) → ℝ), ∫ a : ℝ, splitChainProd W (a, w) ∂vol
          ∂(Measure.pi fun _ : Fin (n+1) => vol) := hstep2
    _ = chainIntegral (n+1) (contract W) := hstep3.symm

/-- **(ii) Integrability propagation**: the peel transports the chain integrability to
the contracted family (needed to iterate the induction). -/
theorem integrable_contract {n : ℕ} (W : Fin (n+2) → ℝ × ℝ → ℝ)
    (hP : Integrable (chainProd (n+2) W) (Measure.pi fun _ : Fin (n+2) => vol))
    (hmeas : AEStronglyMeasurable (chainProd (n+1) (contract W))
      (Measure.pi fun _ : Fin (n+1) => vol)) :
    Integrable (chainProd (n+1) (contract W))
      (Measure.pi fun _ : Fin (n+1) => vol) := by
  classical
  have hmp : MeasurePreserving
      (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+2) => ℝ) (0 : Fin (n+2))))
      (Measure.pi fun _ : Fin (n+2) => vol)
      (vol.prod (Measure.pi fun _ : Fin (n+1) => vol)) := measurePreserving_piSucc n
  have hmsymm : MeasurePreserving
      (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+2) => ℝ) (0 : Fin (n+2))).symm)
      (vol.prod (Measure.pi fun _ : Fin (n+1) => vol))
      (Measure.pi fun _ : Fin (n+2) => vol) :=
    MeasurePreserving.symm
      (e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+2) => ℝ) (0 : Fin (n+2))) hmp
  have hgInt : Integrable (splitChainProd W)
      (vol.prod (Measure.pi fun _ : Fin (n+1) => vol)) := by
    have hgeq : (splitChainProd W)
        = fun x : ℝ × (Fin (n+1) → ℝ) => chainProd (n+2) W
            ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+2) => ℝ) (0 : Fin (n+2))).symm x) := by
      funext p
      simp only [splitChainProd_apply, piFinSuccAbove_symm_cons]
    rw [hgeq]
    exact integrable_comp_measurePreserving
      (e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+2) => ℝ) (0 : Fin (n+2))).symm)
      hmsymm hP
  -- the dominating function `w ↦ ∫_a |g (a, w)|` is integrable
  have hdom : Integrable (fun w : Fin (n+1) → ℝ => ∫ a : ℝ, |splitChainProd W (a, w)| ∂vol)
      (Measure.pi fun _ : Fin (n+1) => vol) :=
    hgInt.abs.integral_prod_right
  refine ⟨hmeas, ?_⟩
  -- HasFiniteIntegral by domination
  have hpt : ∀ w : Fin (n+1) → ℝ,
      |chainProd (n+1) (contract W) w| ≤ ∫ a : ℝ, |splitChainProd W (a, w)| ∂vol := by
    intro w
    rw [chainProd_contract W w]
    have hck : |compKernel (W (Fin.last (n+1))) (W 0) (w (Fin.last n), w 0)|
        ≤ ∫ a : ℝ, |W (Fin.last (n+1)) (w (Fin.last n), a) * W 0 (a, w 0)| ∂vol := by
      have hsplitck : compKernel (W (Fin.last (n+1))) (W 0) (w (Fin.last n), w 0)
          = ∫ a : ℝ, W (Fin.last (n+1)) (w (Fin.last n), a) * W 0 (a, w 0) ∂vol := rfl
      rw [hsplitck]
      exact abs_integral_le_integral_abs
    have hsplit : ∀ a : ℝ, |splitChainProd W (a, w)|
        = |W 0 (a, w 0) * W (Fin.last (n+1)) (w (Fin.last n), a)|
            * |∏ j ∈ (Finset.univ.erase (Fin.last n) : Finset (Fin (n+1))),
                W j.succ (w j, w (cycleSucc j))| := by
      intro a
      simp only [splitChainProd_apply, Real.norm_eq_abs, abs_mul]
      rw [chainProd_cons W a w]
      ring
    calc |(∏ j ∈ (Finset.univ.erase (Fin.last n) : Finset (Fin (n+1))),
              W j.succ (w j, w (cycleSucc j)))
            * compKernel (W (Fin.last (n+1))) (W 0) (w (Fin.last n), w 0)|
        ≤ |∏ j ∈ (Finset.univ.erase (Fin.last n) : Finset (Fin (n+1))),
              W j.succ (w j, w (cycleSucc j))|
            * ∫ a : ℝ, |W (Fin.last (n+1)) (w (Fin.last n), a) * W 0 (a, w 0)| ∂vol :=
          mul_le_mul_of_nonneg_left hck (abs_nonneg _)
      _ = ∫ a : ℝ, |splitChainProd W (a, w)| ∂vol := by
          rw [integral_congr_ae (Filter.Eventually.of_forall fun a => hsplit a)]
  exact hdom.hasFiniteIntegral.mono (Filter.Eventually.of_forall hpt)

end HS

end
