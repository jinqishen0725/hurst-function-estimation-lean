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
* (ii) `peelChainIntegral_peel` — **the peel step**: the `(n+2)`-chain integral of a kernel
  family `W` equals the `(n+1)`-chain integral of the contracted family `peelContract W`
  (the wrap-adjacent pair composed via `compKernel`), under the chain-integrability
  hypothesis `hP`.  Route: the measure-preserving coordinate insertion
  `measurePreserving_piFinSuccAbove` + Fubini (`integral_prod`) + the pointwise
  `peelChainProd_cons` factorization + the `compKernel` peel identity (each peel is exactly
  the landed `integral_compKernel_diag` pattern).  `integrable_contract` propagates the
  chain integrability to the contracted family (via `|compKernel| ≤ ∫ |sections|`), so
  the peel iterates.
* (iii) `chainIntegral_contrFam_eq` / `cycleIntegral_comp_general` — **the induction**:
  `cycleIntegral (n+2) K = cycle2 (compPowR n K) K` (the general-`k` trace form), with
  the composition tower bounds `hsNorm_compPowR_le` (`hsNorm (compPowR n K) ≤
  hsNorm K ^ (n+1)`).

## Honest residue (documented)

The induction carries the chain-integrability hypotheses `hP n : Integrable
(peelChainProd (n+2) (contrFam n K)) (vol^(n+2))` explicitly.  Their unconditional
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
theorem peelCycleSucc_val {k : ℕ} (i : Fin k) :
    ((cycleSucc i : Fin k) : ℕ) = if (i : ℕ) + 1 < k then (i : ℕ) + 1 else 0 := by
  unfold cycleSucc
  split <;> rfl

theorem peelCycleSucc_last' {k : ℕ} : cycleSucc (Fin.last k) = 0 := by
  apply Fin.ext
  rw [peelCycleSucc_val, Fin.val_last, if_neg (by omega : ¬((k : ℕ) + 1 < k + 1))]
  rfl

/-- The `k`-chain (cycle) product of a kernel family `W : Fin k → ℝ × ℝ → ℝ`. -/
def peelChainProd (k : ℕ) (W : Fin k → ℝ × ℝ → ℝ) (z : Fin k → ℝ) : ℝ :=
  ∏ i : Fin k, W i (z i, z (cycleSucc i))

/-- The `k`-chain (cycle) integral of a kernel family; `cycleIntegral k K =
peelChainIntegral k (fun _ => K)` definitionally. -/
def peelChainIntegral (k : ℕ) (W : Fin k → ℝ × ℝ → ℝ) : ℝ :=
  ∫ z : Fin k → ℝ, peelChainProd k W z ∂(Measure.pi fun _ : Fin k => vol)

theorem peelChainIntegral_eq_cycleIntegral (k : ℕ) (K : ℝ × ℝ → ℝ) :
    peelChainIntegral k (fun _ => K) = cycleIntegral k K := rfl

/-- The chain product is measurable when the kernels are. -/
theorem peelMeasurable_chainProd {k : ℕ} {W : Fin k → ℝ × ℝ → ℝ}
    (hW : ∀ i, Measurable (W i)) : Measurable (peelChainProd k W) := by
  unfold peelChainProd
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

/-- The peel contraction: for an `(n+2)`-chain `W`, `peelContract W : Fin (n+1) → _` composes
the wrap-adjacent pair `(W (Fin.last (n+1)), W 0)` into the last position. -/
def peelContract {n : ℕ} (W : Fin (n+2) → ℝ × ℝ → ℝ) : Fin (n+1) → ℝ × ℝ → ℝ :=
  fun j => if j = Fin.last n then compKernel (W (Fin.last (n+1))) (W 0) else W j.succ

theorem peelContract_apply_last {n : ℕ} (W : Fin (n+2) → ℝ × ℝ → ℝ) :
    peelContract W (Fin.last n) = compKernel (W (Fin.last (n+1))) (W 0) := by
  rw [peelContract, if_pos rfl]

theorem peelContract_apply_succ {n : ℕ} (W : Fin (n+2) → ℝ × ℝ → ℝ) {j : Fin (n+1)}
    (hj : j ≠ Fin.last n) : peelContract W j = W j.succ := by
  rw [peelContract, if_neg hj]

/-- Measurability of the contracted chain (measurable kernels). -/
theorem peelMeasurable_contract {n : ℕ} {W : Fin (n+2) → ℝ × ℝ → ℝ} (hWm : ∀ i, Measurable (W i))
    (j : Fin (n+1)) : Measurable (peelContract W j) := by
  by_cases hj : j = Fin.last n
  · rw [hj, peelContract_apply_last W]
    exact (stronglyMeasurable_compKernel (hWm _) (hWm _)).measurable
  · rw [peelContract_apply_succ W hj]
    exact hWm _

/-- The cons product factorizes through the wrap point: the product of the `(n+2)`-chain
at `Fin.cons a w` is the `a`-pair times the wrap-composed factor times the open-chain
product over the non-wrap indices. -/
theorem peelChainProd_cons {n : ℕ} (W : Fin (n+2) → ℝ × ℝ → ℝ) (a : ℝ) (w : Fin (n+1) → ℝ) :
    peelChainProd (n+2) W (Fin.cons a w)
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
      rw [peelCycleSucc_val, if_pos (by omega)]
    have hv2 : ((cycleSucc j.succ : Fin (n+2)) : ℕ) = (j : ℕ) + 2 := by
      rw [peelCycleSucc_val, Fin.val_succ, if_pos (by omega)]
    have hv3 : (((cycleSucc j).succ : Fin (n+2)) : ℕ) = (j : ℕ) + 2 := by
      rw [Fin.val_succ, hv1]
    rw [hv2, hv3]
  have hlast : W (Fin.last n).succ (((Fin.cons a w : Fin (n+2) → ℝ)) (Fin.last n).succ,
      ((Fin.cons a w : Fin (n+2) → ℝ)) (cycleSucc (Fin.last n).succ))
      = W (Fin.last (n+1)) (w (Fin.last n), a) := by
    rw [Fin.cons_succ (α := fun _ : Fin (n+2) => ℝ) a w (Fin.last n), Fin.succ_last,
      peelCycleSucc_last', Fin.cons_zero]
  -- peel off the `j = Fin.last n` factor of the tail product
  have hstep : (∏ i : Fin (n+1), W i.succ (((Fin.cons a w : Fin (n+2) → ℝ)) i.succ,
          ((Fin.cons a w : Fin (n+2) → ℝ)) (cycleSucc i.succ)))
      = W (Fin.last (n+1)) (w (Fin.last n), a)
        * ∏ j ∈ (Finset.univ.erase (Fin.last n) : Finset (Fin (n+1))),
            W j.succ (w j, w (cycleSucc j)) := by
    have key := Finset.mul_prod_erase (ι := Fin (n+1)) (M := ℝ) Finset.univ
      (f := fun i : Fin (n+1) => W i.succ (((Fin.cons a w : Fin (n+2) → ℝ)) i.succ,
        ((Fin.cons a w : Fin (n+2) → ℝ)) (cycleSucc i.succ))) (Finset.mem_univ (Fin.last n))
    rw [← key, hlast]
    refine congrArg _ (Finset.prod_congr rfl fun j hj => ?_)
    have hjn : j ≠ Fin.last n := Finset.ne_of_mem_erase hj
    simp only [hcycle j hjn, Fin.cons_succ (α := fun _ : Fin (n+2) => ℝ)]
  -- the full product: `Fin.prod_univ_succ` splits off `i = 0`
  rw [peelChainProd, Fin.prod_univ_succ]
  have h0 : W 0 (((Fin.cons a w : Fin (n+2) → ℝ)) 0,
      ((Fin.cons a w : Fin (n+2) → ℝ)) (cycleSucc 0)) = W 0 (a, w 0) := rfl
  rw [h0, hstep]
  ring

/-- The contracted-chain product reassembles the pre-product with the composed kernel
at the wrap. -/
theorem peelChainProd_contract {n : ℕ} (W : Fin (n+2) → ℝ × ℝ → ℝ) (w : Fin (n+1) → ℝ) :
    peelChainProd (n+1) (peelContract W) w
      = (∏ j ∈ (Finset.univ.erase (Fin.last n) : Finset (Fin (n+1))),
            W j.succ (w j, w (cycleSucc j)))
        * compKernel (W (Fin.last (n+1))) (W 0) (w (Fin.last n), w 0) := by
  classical
  have hlast : peelContract W (Fin.last n) (w (Fin.last n), w (cycleSucc (Fin.last n)))
      = compKernel (W (Fin.last (n+1))) (W 0) (w (Fin.last n), w 0) := by
    rw [peelCycleSucc_last', peelContract_apply_last W]
  calc peelChainProd (n+1) (peelContract W) w
      = ∏ j : Fin (n+1), peelContract W j (w j, w (cycleSucc j)) := rfl
    _ = peelContract W (Fin.last n) (w (Fin.last n), w (cycleSucc (Fin.last n)))
        * ∏ j ∈ (Finset.univ.erase (Fin.last n) : Finset (Fin (n+1))),
            peelContract W j (w j, w (cycleSucc j)) :=
          (Finset.mul_prod_erase (ι := Fin (n+1)) (M := ℝ) Finset.univ
            (f := fun j : Fin (n+1) => peelContract W j (w j, w (cycleSucc j)))
            (Finset.mem_univ (Fin.last n))).symm
    _ = (∏ j ∈ (Finset.univ.erase (Fin.last n) : Finset (Fin (n+1))),
            W j.succ (w j, w (cycleSucc j)))
        * compKernel (W (Fin.last (n+1))) (W 0) (w (Fin.last n), w 0) := by
        rw [hlast, mul_comm (∏ j ∈ (Finset.univ.erase (Fin.last n) : Finset (Fin (n+1))),
            W j.succ (w j, w (cycleSucc j)))
          (compKernel (W (Fin.last (n+1))) (W 0) (w (Fin.last n), w 0))]
        exact congrArg (fun x : ℝ => compKernel (W (Fin.last (n+1))) (W 0)
          (w (Fin.last n), w 0) * x)
          (Finset.prod_congr rfl fun j hj => by
            have hjn : j ≠ Fin.last n := Finset.ne_of_mem_erase hj
            rw [peelContract_apply_succ W hjn])

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
  set g := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+2) => ℝ) (0 : Fin (n+2))).symm (a, w)
    with hgd
  have hab : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+2) => ℝ) (0 : Fin (n+2))) g
      = (a, w) :=
    MeasurableEquiv.apply_symm_apply _ (a, w)
  have hg0 : g (0 : Fin (n+2)) = a := by
    have h := congrArg Prod.fst hab
    exact h
  have hgt2 : Fin.tail g = w := by
    have h : Fin.removeNth (α := fun _ : Fin (n+2) => ℝ) (0 : Fin (n+2)) g = w := by
      have h2 := congrArg Prod.snd hab
      show Fin.removeNth (α := fun _ : Fin (n+2) => ℝ) (0 : Fin (n+2)) g = w
      exact h2
    rw [← Fin.removeNth_zero (α := fun _ : Fin (n+2) => ℝ) (f := g)]
    exact h
  funext j
  rcases j with ⟨m, hm⟩
  match m, hm with
  | 0, hm => show g (0 : Fin (n+2)) = a; exact hg0
  | m + 1, hm =>
      show g (Fin.succ ((⟨m, by omega⟩ : Fin (n+1)))) = w ((⟨m, by omega⟩ : Fin (n+1)))
      exact congrFun hgt2 (⟨m, by omega⟩ : Fin (n+1))

/-- The transported chain product on the split coordinates. -/
def splitChainProd {n : ℕ} (W : Fin (n+2) → ℝ × ℝ → ℝ) :
    ℝ × (Fin (n+1) → ℝ) → ℝ :=
  fun p => peelChainProd (n+2) W (Fin.cons p.1 p.2)

theorem splitChainProd_apply {n : ℕ} (W : Fin (n+2) → ℝ × ℝ → ℝ) (p : ℝ × (Fin (n+1) → ℝ)) :
    splitChainProd W p = peelChainProd (n+2) W (Fin.cons p.1 p.2) := rfl

theorem splitChainProd_apply_piSucc {n : ℕ} (W : Fin (n+2) → ℝ × ℝ → ℝ)
    (z : Fin (n+2) → ℝ) :
    peelChainProd (n+2) W z
      = splitChainProd W
          (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+2) => ℝ) (0 : Fin (n+2))) z) := by
  show peelChainProd (n+2) W z
      = peelChainProd (n+2) W
          (Fin.cons
            (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+2) => ℝ) (0 : Fin (n+2))) z).1
            (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+2) => ℝ) (0 : Fin (n+2))) z).2)
  have hs := MeasurableEquiv.symm_apply_apply
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+2) => ℝ) (0 : Fin (n+2))) z
  rw [piFinSuccAbove_symm_cons] at hs
  exact congrArg _ hs.symm

/-- **(ii) The peel step**: the `(n+2)`-chain integral equals the `(n+1)`-chain integral
of the contracted family — the general-`k` Fubini peel (each peel is the landed
`integral_compKernel_diag` pattern), under the chain-integrability hypothesis. -/
theorem peelChainIntegral_peel {n : ℕ} (W : Fin (n+2) → ℝ × ℝ → ℝ)
    (hP : Integrable (peelChainProd (n+2) W) (Measure.pi fun _ : Fin (n+2) => vol)) :
    peelChainIntegral (n+2) W = peelChainIntegral (n+1) (peelContract W) := by
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
    have hgeq : splitChainProd W
        = fun x : ℝ × (Fin (n+1) → ℝ) => peelChainProd (n+2) W
            (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+2) => ℝ) (0 : Fin (n+2))).symm x) := by
      funext p
      show peelChainProd (n+2) W (Fin.cons p.1 p.2)
          = peelChainProd (n+2) W
              (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+2) => ℝ) (0 : Fin (n+2))).symm
                (p.1, p.2))
      rw [piFinSuccAbove_symm_cons]
    rw [hgeq]
    exact integrable_comp_measurePreserving
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+2) => ℝ) (0 : Fin (n+2))).symm.toEquiv
      hmsymm hP
  have hstep1 : peelChainIntegral (n+2) W
      = ∫ p : ℝ × (Fin (n+1) → ℝ), splitChainProd W p
          ∂(vol.prod (Measure.pi fun _ : Fin (n+1) => vol)) := by
    rw [← hmp.integral_comp' (fun p => splitChainProd W p)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show peelChainProd (n+2) W z
        = splitChainProd W
            (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+2) => ℝ) (0 : Fin (n+2))) z)
    exact splitChainProd_apply_piSucc W z
  have hstep2 : (∫ p : ℝ × (Fin (n+1) → ℝ), splitChainProd W p
          ∂(vol.prod (Measure.pi fun _ : Fin (n+1) => vol)))
      = ∫ w : (Fin (n+1) → ℝ), ∫ a : ℝ, splitChainProd W (a, w) ∂vol
          ∂(Measure.pi fun _ : Fin (n+1) => vol) :=
    integral_prod_symm (fun p => splitChainProd W p) hgInt
  have hstep3 : (∫ w : (Fin (n+1) → ℝ), ∫ a : ℝ, splitChainProd W (a, w) ∂vol
          ∂(Measure.pi fun _ : Fin (n+1) => vol))
      = ∫ w : (Fin (n+1) → ℝ), peelChainProd (n+1) (peelContract W) w
          ∂(Measure.pi fun _ : Fin (n+1) => vol) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    show (∫ a : ℝ, splitChainProd W (a, w) ∂vol)
        = peelChainProd (n+1) (peelContract W) w
    have hint : ∫ a : ℝ, splitChainProd W (a, w) ∂vol
        = ∫ a : ℝ, peelChainProd (n+2) W (Fin.cons a w) ∂vol := rfl
    rw [hint]
    have hcons : ∀ a : ℝ, peelChainProd (n+2) W (Fin.cons a w)
        = W 0 (a, w 0) * W (Fin.last (n+1)) (w (Fin.last n), a)
          * ∏ j ∈ (Finset.univ.erase (Fin.last n) : Finset (Fin (n+1))),
              W j.succ (w j, w (cycleSucc j)) := fun a => peelChainProd_cons W a w
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
    calc ∫ a : ℝ, peelChainProd (n+2) W (Fin.cons a w) ∂vol
        = ∫ a : ℝ, W 0 (a, w 0) * W (Fin.last (n+1)) (w (Fin.last n), a)
              * ∏ j ∈ (Finset.univ.erase (Fin.last n) : Finset (Fin (n+1))),
                W j.succ (w j, w (cycleSucc j)) ∂vol := by
          rw [integral_congr_ae (Filter.Eventually.of_forall fun a => hcons a)]
      _ = (∏ j ∈ (Finset.univ.erase (Fin.last n) : Finset (Fin (n+1))),
              W j.succ (w j, w (cycleSucc j)))
            * compKernel (W (Fin.last (n+1))) (W 0) (w (Fin.last n), w 0) := hcomp
      _ = peelChainProd (n+1) (peelContract W) w := (peelChainProd_contract W w).symm
  calc peelChainIntegral (n+2) W
      = ∫ p : ℝ × (Fin (n+1) → ℝ), splitChainProd W p
          ∂(vol.prod (Measure.pi fun _ : Fin (n+1) => vol)) := hstep1
    _ = ∫ w : (Fin (n+1) → ℝ), ∫ a : ℝ, splitChainProd W (a, w) ∂vol
          ∂(Measure.pi fun _ : Fin (n+1) => vol) := hstep2
    _ = peelChainIntegral (n+1) (peelContract W) := hstep3

/-- **(ii) Integrability propagation**: the peel transports the chain integrability to
the contracted family (needed to iterate the induction). -/
theorem integrable_contract {n : ℕ} (W : Fin (n+2) → ℝ × ℝ → ℝ)
    (hP : Integrable (peelChainProd (n+2) W) (Measure.pi fun _ : Fin (n+2) => vol))
    (hmeas : AEStronglyMeasurable (peelChainProd (n+1) (peelContract W))
      (Measure.pi fun _ : Fin (n+1) => vol)) :
    Integrable (peelChainProd (n+1) (peelContract W))
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
    have hgeq : splitChainProd W
        = fun x : ℝ × (Fin (n+1) → ℝ) => peelChainProd (n+2) W
            (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+2) => ℝ) (0 : Fin (n+2))).symm x) := by
      funext p
      show peelChainProd (n+2) W (Fin.cons p.1 p.2)
          = peelChainProd (n+2) W
              (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+2) => ℝ) (0 : Fin (n+2))).symm
                (p.1, p.2))
      rw [piFinSuccAbove_symm_cons]
    rw [hgeq]
    exact integrable_comp_measurePreserving
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+2) => ℝ) (0 : Fin (n+2))).symm.toEquiv
      hmsymm hP
  -- the dominating function `w ↦ ∫_a |g (a, w)|` is integrable
  have hdom : Integrable (fun w : Fin (n+1) → ℝ => ∫ a : ℝ, |splitChainProd W (a, w)| ∂vol)
      (Measure.pi fun _ : Fin (n+1) => vol) :=
    hgInt.abs.integral_prod_right
  refine ⟨hmeas, ?_⟩
  -- HasFiniteIntegral by domination
  have hpt : ∀ w : Fin (n+1) → ℝ,
      ‖peelChainProd (n+1) (peelContract W) w‖
        ≤ ‖∫ a : ℝ, |splitChainProd W (a, w)| ∂vol‖ := by
    intro w
    have hcc := peelChainProd_contract W w
    have hck : |compKernel (W (Fin.last (n+1))) (W 0) (w (Fin.last n), w 0)|
        ≤ ∫ a : ℝ, |W (Fin.last (n+1)) (w (Fin.last n), a) * W 0 (a, w 0)| ∂vol := by
      rw [show compKernel (W (Fin.last (n+1))) (W 0) (w (Fin.last n), w 0)
          = ∫ a : ℝ, W (Fin.last (n+1)) (w (Fin.last n), a) * W 0 (a, w 0) ∂vol from rfl]
      exact abs_integral_le_integral_abs
    have hsplit : ∀ a : ℝ, |splitChainProd W (a, w)|
        = |W 0 (a, w 0)| * |W (Fin.last (n+1)) (w (Fin.last n), a)|
            * |∏ j ∈ (Finset.univ.erase (Fin.last n) : Finset (Fin (n+1))),
                W j.succ (w j, w (cycleSucc j))| := by
      intro a
      show |peelChainProd (n+2) W (Fin.cons a w)| = _
      rw [peelChainProd_cons W a w, abs_mul, abs_mul]
    have hstep : |(∏ j ∈ (Finset.univ.erase (Fin.last n) : Finset (Fin (n+1))),
            W j.succ (w j, w (cycleSucc j)))
          * compKernel (W (Fin.last (n+1))) (W 0) (w (Fin.last n), w 0)|
        ≤ |∏ j ∈ (Finset.univ.erase (Fin.last n) : Finset (Fin (n+1))),
              W j.succ (w j, w (cycleSucc j))|
          * ∫ a : ℝ, |W (Fin.last (n+1)) (w (Fin.last n), a) * W 0 (a, w 0)| ∂vol := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hck
        (abs_nonneg (∏ j ∈ (Finset.univ.erase (Fin.last n) : Finset (Fin (n+1))),
          W j.succ (w j, w (cycleSucc j))))
    have heq : |∏ j ∈ (Finset.univ.erase (Fin.last n) : Finset (Fin (n+1))),
          W j.succ (w j, w (cycleSucc j))|
        * ∫ a : ℝ, |W (Fin.last (n+1)) (w (Fin.last n), a) * W 0 (a, w 0)| ∂vol
        = ∫ a : ℝ, |splitChainProd W (a, w)| ∂vol := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
      show |∏ j ∈ (Finset.univ.erase (Fin.last n) : Finset (Fin (n+1))),
            W j.succ (w j, w (cycleSucc j))|
          * |W (Fin.last (n+1)) (w (Fin.last n), a) * W 0 (a, w 0)|
          = |splitChainProd W (a, w)|
      rw [hsplit a, abs_mul]
      ring
    calc ‖peelChainProd (n+1) (peelContract W) w‖
        = |peelChainProd (n+1) (peelContract W) w| :=
          Real.norm_eq_abs (peelChainProd (n+1) (peelContract W) w)
      _ = |(∏ j ∈ (Finset.univ.erase (Fin.last n) : Finset (Fin (n+1))),
              W j.succ (w j, w (cycleSucc j)))
            * compKernel (W (Fin.last (n+1))) (W 0) (w (Fin.last n), w 0)| := congrArg _ hcc
      _ ≤ |∏ j ∈ (Finset.univ.erase (Fin.last n) : Finset (Fin (n+1))),
              W j.succ (w j, w (cycleSucc j))|
            * ∫ a : ℝ, |W (Fin.last (n+1)) (w (Fin.last n), a) * W 0 (a, w 0)| ∂vol := hstep
      _ = ∫ a : ℝ, |splitChainProd W (a, w)| ∂vol := heq
      _ = |∫ a : ℝ, |splitChainProd W (a, w)| ∂vol| :=
          (abs_of_nonneg (integral_nonneg
            (fun a : ℝ => abs_nonneg (splitChainProd W (a, w))))).symm
      _ = ‖∫ a : ℝ, |splitChainProd W (a, w)| ∂vol‖ :=
          (Real.norm_eq_abs (∫ a : ℝ, |splitChainProd W (a, w)| ∂vol)).symm
  exact hdom.hasFiniteIntegral.mono (Filter.Eventually.of_forall hpt)

/-! ### (iii) The composition tower and the general-`k` peel induction -/

/-- The right-growing composition tower: `compPowR 0 K = K`,
`compPowR (n+1) K = compKernel (compPowR n K) K`. -/
def compPowR : ℕ → (ℝ × ℝ → ℝ) → (ℝ × ℝ → ℝ)
  | 0, K => K
  | n + 1, K => compKernel (compPowR n K) K

/-- Composition keeps measurable HS kernels HS (the domination argument of the landed
`hsNorm_comp_le`). -/
theorem peelHsKernel_comp {K L : ℝ × ℝ → ℝ} (hKm : Measurable K) (hLm : Measurable L)
    (hK : HSKernel K) (hL : HSKernel L) : HSKernel (compKernel K L) := by
  classical
  have hK2meas : AEStronglyMeasurable (fun p : ℝ × ℝ => K p ^ 2) vol2 :=
    (hKm.pow_const 2).aestronglyMeasurable
  obtain ⟨hsecK, hnormK⟩ := (integrable_prod_iff hK2meas).mp (MemLp.integrable_sq hK)
  have hIK : Integrable (secE2 K) vol := by
    refine hnormK.congr (Filter.Eventually.of_forall fun x => ?_)
    show (∫ y : ℝ, ‖K (x, y) ^ 2‖ ∂vol) = (∫ t : ℝ, K (x, t) ^ 2 ∂vol)
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show ‖K (x, t) ^ 2‖ = K (x, t) ^ 2
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hL2tr : MemLp (ktranspose L) 2 vol2 := hsKernel_transpose hL
  obtain ⟨g, hgme, hgc⟩ := hL2tr.1
  have hL2meas : AEStronglyMeasurable (fun q : ℝ × ℝ => ktranspose L q ^ 2) vol2 :=
    ⟨g * g, hgme.mul hgme, by
      filter_upwards [hgc] with q hq
      show ktranspose L q ^ 2 = g q * g q
      rw [hq, pow_two]⟩
  obtain ⟨hsecL, hnormL⟩ := (integrable_prod_iff hL2meas).mp (MemLp.integrable_sq hL2tr)
  have hsecL' : ∀ᵐ y ∂vol, Integrable (fun t => L (t, y) ^ 2) vol := by
    filter_upwards [hsecL] with x hx
    exact hx
  have hIL : Integrable (secE1 L) vol := by
    refine hnormL.congr (Filter.Eventually.of_forall fun y => ?_)
    show (∫ t : ℝ, ‖ktranspose L (y, t) ^ 2‖ ∂vol) = (∫ t : ℝ, L (t, y) ^ 2 ∂vol)
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show ‖ktranspose L (y, t) ^ 2‖ = L (t, y) ^ 2
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rfl
  have hliftK : ∀ᵐ p : ℝ × ℝ ∂vol2, MemLp (fun t => K (p.1, t)) 2 vol := by
    have hind : ∀ᵐ x ∂vol,
        (if Integrable (fun t => K (x, t) ^ 2) vol then (1 : ℝ) else 0) = (1 : ℝ) := by
      filter_upwards [hsecK] with x hx
      rw [if_pos hx]
    filter_upwards [eventual_fst hind] with p hp
    by_cases hc : Integrable (fun t => K (p.1, t) ^ 2) vol
    · exact memLp_two_of_aemeasurable
        ((hKm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable) hc
    · rw [if_neg hc] at hp
      exact absurd hp (by norm_num)
  have hliftL : ∀ᵐ p : ℝ × ℝ ∂vol2, MemLp (fun t => L (t, p.2)) 2 vol := by
    have hind : ∀ᵐ y ∂vol,
        (if Integrable (fun t => L (t, y) ^ 2) vol then (1 : ℝ) else 0) = (1 : ℝ) := by
      filter_upwards [hsecL'] with y hy
      rw [if_pos hy]
    filter_upwards [eventual_snd hind] with p hp
    by_cases hc : Integrable (fun t => L (t, p.2) ^ 2) vol
    · exact memLp_two_of_aemeasurable
        ((hLm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable) hc
    · rw [if_neg hc] at hp
      exact absurd hp (by norm_num)
  have hpt : ∀ᵐ p : ℝ × ℝ ∂vol2, compKernel K L p ^ 2 ≤ secE2 K p.1 * secE1 L p.2 := by
    filter_upwards [hliftK, hliftL] with p hx hy
    have h1 := abs_compKernel_le (p.1) (p.2) hx hy
    have hab : 0 ≤ Real.sqrt (secE2 K p.1) * Real.sqrt (secE1 L p.2) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    calc compKernel K L p ^ 2
        = |compKernel K L p| ^ 2 := (sq_abs _).symm
      _ ≤ (Real.sqrt (secE2 K p.1) * Real.sqrt (secE1 L p.2)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = secE2 K p.1 * secE1 L p.2 := by
        have hn1 : 0 ≤ secE2 K p.1 := integral_nonneg fun _ => sq_nonneg _
        have hn2 : 0 ≤ secE1 L p.2 := integral_nonneg fun _ => sq_nonneg _
        rw [mul_pow, Real.sq_sqrt hn1, Real.sq_sqrt hn2]
  have hB : Integrable (fun p : ℝ × ℝ => secE2 K p.1 * secE1 L p.2) vol2 :=
    Integrable.op_fst_snd (op := fun a b : ℝ => a * b) (by fun_prop)
      ⟨1, fun a b => by simp [Real.norm_eq_abs]⟩ hIK hIL
  have hcmp : AEStronglyMeasurable (compKernel K L) vol2 :=
    (stronglyMeasurable_compKernel hKm hLm).aestronglyMeasurable
  have hcmp2 : Integrable (fun p : ℝ × ℝ => compKernel K L p ^ 2) vol2 := by
    obtain ⟨gm, hgme, hgc⟩ := hcmp
    have hae : AEStronglyMeasurable (fun p : ℝ × ℝ => compKernel K L p ^ 2) vol2 :=
      ⟨gm * gm, hgme.mul hgme, by
        filter_upwards [hgc] with p hp
        show compKernel K L p ^ 2 = gm p * gm p
        rw [hp, pow_two]⟩
    refine hB.mono hae ?_
    filter_upwards [hpt] with p hp
    have hn : 0 ≤ secE2 K p.1 * secE1 L p.2 :=
      mul_nonneg (integral_nonneg fun _ => sq_nonneg _)
        (integral_nonneg fun _ => sq_nonneg _)
    calc ‖compKernel K L p ^ 2‖
        = compKernel K L p ^ 2 := by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      _ ≤ secE2 K p.1 * secE1 L p.2 := hp
      _ = ‖secE2 K p.1 * secE1 L p.2‖ := by
            rw [Real.norm_eq_abs, abs_of_nonneg hn]
  exact memLp_two_of_aemeasurable hcmp hcmp2

/-- Measurability propagates up the tower. -/
theorem measurable_compPowR (n : ℕ) {K : ℝ × ℝ → ℝ} (hKm : Measurable K) :
    Measurable (compPowR n K) := by
  induction n with
  | zero => exact hKm
  | succ m ih => exact (stronglyMeasurable_compKernel ih hKm).measurable

/-- HS membership propagates up the tower. -/
theorem hsKernel_compPowR (n : ℕ) {K : ℝ × ℝ → ℝ} (hKm : Measurable K) (hK : HSKernel K) :
    HSKernel (compPowR n K) := by
  induction n with
  | zero => exact hK
  | succ m ih => exact peelHsKernel_comp (measurable_compPowR m hKm) hKm ih hK

/-- **Iterated submultiplicativity** up the tower: `hsNorm (compPowR n K) ≤ hsNorm K ^ (n+1)`. -/
theorem hsNorm_compPowR_le (n : ℕ) {K : ℝ × ℝ → ℝ} (hKm : Measurable K) (hK : HSKernel K) :
    hsNorm (compPowR n K) ≤ hsNorm K ^ (n + 1) := by
  induction n with
  | zero => simp [compPowR]
  | succ m ih =>
      refine (hsNorm_comp_le (measurable_compPowR m hKm) hKm
        (hsKernel_compPowR m hKm hK) hK).trans ?_
      calc hsNorm (compPowR m K) * hsNorm K
          ≤ hsNorm K ^ (m + 1) * hsNorm K := by
            exact mul_le_mul_of_nonneg_right ih (hsNorm_nonneg K)
        _ = hsNorm K ^ (m + 2) := by ring

/-- **The `k = 2` anchor for general chains**: `peelChainIntegral 2 W = cycle2 (W 0) (W 1)`
(the landed `cycleIntegral_two` route via `measurePreserving_piFinTwo`). -/
theorem peelChainIntegral_two (W : Fin 2 → ℝ × ℝ → ℝ) :
    peelChainIntegral 2 W = cycle2 (W 0) (W 1) := by
  have hpt : ∀ z : Fin 2 → ℝ,
      peelChainProd 2 W z = (fun w : ℝ × ℝ => W 0 w * W 1 w.swap)
        (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ) z) := by
    intro z
    show (∏ i : Fin 2, W i (z i, z (cycleSucc i))) = W 0 (z 0, z 1) * W 1 (z 1, z 0)
    rw [Fin.prod_univ_two, cycleSucc_two_zero, cycleSucc_two_one]
  calc peelChainIntegral 2 W
      = ∫ z : Fin 2 → ℝ, peelChainProd 2 W z ∂(Measure.pi fun _ : Fin 2 => vol) := rfl
    _ = ∫ w : ℝ × ℝ, W 0 w * W 1 w.swap ∂(vol.prod vol) :=
        (integral_congr_ae (Filter.Eventually.of_forall hpt)).trans
          ((measurePreserving_piFinTwo (fun _ : Fin 2 => vol)).integral_comp'
            (fun w : ℝ × ℝ => W 0 w * W 1 w.swap))
    _ = cycle2 (W 0) (W 1) := rfl

/-- The `n`-times-peeled constant-`K` family: `n+1` copies of `K` with the `n`-fold
composition `compPowR r K` at the wrap (here `n` counts the remaining plain copies and
`r` the performed peels; `n + r` is invariant under peeling). -/
def kchain (n r : ℕ) (K : ℝ × ℝ → ℝ) : Fin (n+2) → ℝ × ℝ → ℝ :=
  fun j => if j = Fin.last (n+1) then compPowR r K else K

/-- Peeling one coordinate turns the `(n+1)`-copies/`r`-fold family into the
`n`-copies/`(r+1)`-fold family. -/
theorem contract_kchain {n r : ℕ} (K : ℝ × ℝ → ℝ) :
    peelContract (kchain (n+1) r K) = kchain n (r+1) K := by
  funext j
  by_cases hjk : j = Fin.last (n+1)
  · subst hjk
    have hWlast : kchain (n+1) r K (Fin.last (n+2)) = compPowR r K := by
      show (if (Fin.last (n+2) : Fin (n+3)) = Fin.last (n+2) then compPowR r K else K)
          = compPowR r K
      rw [if_pos rfl]
    have hW0 : kchain (n+1) r K (0 : Fin (n+3)) = K := by
      show (if (0 : Fin (n+3)) = Fin.last (n+2) then compPowR r K else K) = K
      have h02 : (0 : Fin (n+3)) ≠ Fin.last (n+2) := by
        intro hc
        have := congrArg Fin.val hc
        simp [Fin.val_last] at this
      rw [if_neg h02]
    rw [peelContract, if_pos rfl, hWlast, hW0, kchain, if_pos rfl]
    rfl
  · have hjn : j ≠ Fin.last (n+1) := hjk
    have hjsn : j.succ ≠ Fin.last (n+2) := by
      intro hc
      have h1 : ((j.succ : Fin (n+3)) : ℕ) = ((Fin.last (n+2) : Fin (n+3)) : ℕ) := by rw [hc]
      have h2 : ((j.succ : Fin (n+3)) : ℕ) = (j : ℕ) + 1 := Fin.val_succ _
      have h3 : ((Fin.last (n+2) : Fin (n+3)) : ℕ) = n + 2 := Fin.val_last _
      have h4 : ((Fin.last (n+1) : Fin (n+2)) : ℕ) = n + 1 := Fin.val_last _
      have h5 := j.2
      have h6 : (j : ℕ) ≠ n + 1 := by
        intro hcc
        refine hjn (Fin.ext ?_)
        omega
      rw [h2, h3] at h1
      omega
    have hL : kchain (n+1) r K j.succ = K := by
      rw [kchain, if_neg hjsn]
    rw [peelContract, if_neg hjk, hL, kchain, if_neg hjk]

/-- **(iii) The peel induction**: iterating the peel over the peeled constant-`K`
family identifies every chain integral with the `cycle2` of the composed tower,
`peelChainIntegral (n+2) (kchain n r K) = cycle2 (compPowR r K) (compPowR r K)`, under the
chain-integrability hypotheses `hP` (carried; see the residue note). -/
theorem chainIntegral_kchain_eq (K : ℝ × ℝ → ℝ)
    (hP : ∀ n r : ℕ, Integrable (peelChainProd (n+2) (kchain n r K))
      (Measure.pi fun _ : Fin (n+2) => vol)) :
    ∀ n r : ℕ,
      peelChainIntegral (n+2) (kchain n r K)
        = cycle2 K (compPowR (n+r) K) := by
  intro n r
  induction n generalizing r with
  | zero =>
      rw [show 0 + r = r from Nat.zero_add r, peelChainIntegral_two]
      have hW0 : kchain 0 r K 0 = K := by
        show (if (0 : Fin 2) = Fin.last 1 then compPowR r K else K) = K
        rw [if_neg (by decide)]
      have hW1 : kchain 0 r K 1 = compPowR r K := by
        show (if (1 : Fin 2) = Fin.last 1 then compPowR r K else K) = compPowR r K
        rw [if_pos (by decide)]
      rw [hW0, hW1]
  | succ m ih =>
      have hpeel : peelChainIntegral ((m+1)+2) (kchain (m+1) r K)
          = peelChainIntegral (m+2) (kchain m (r+1) K) := by
        rw [peelChainIntegral_peel (kchain (m+1) r K) (hP (m+1) r), contract_kchain]
      rw [show (m+1)+r = m+(r+1) from by ring, hpeel, ih (r+1)]

/-- **(iii) The general-`k` trace form**: the `(n+2)`-cycle integral of a measurable HS
kernel equals the `cycle2` of the `n`-fold composition tower, closing the general-`k`
HasSum boundary (the integrability chain `hP` is the documented residue). -/
theorem cycleIntegral_eq_cycle2_pow {K : ℝ × ℝ → ℝ}
    (hP : ∀ n r : ℕ, Integrable (peelChainProd (n+2) (kchain n r K))
      (Measure.pi fun _ : Fin (n+2) => vol)) :
    cycleIntegral (n+2) K = cycle2 (compPowR n K) K := by
  have hkc : kchain n 0 K = fun _ => K := by
    funext j
    by_cases hj : j = Fin.last (n+1)
    · rw [hj, kchain, if_pos rfl]
      rfl
    · rw [kchain, if_neg hj]
  calc cycleIntegral (n+2) K
      = peelChainIntegral (n+2) (kchain n 0 K) := by rw [hkc, peelChainIntegral_eq_cycleIntegral]
    _ = cycle2 K (compPowR (n+0) K) := chainIntegral_kchain_eq K hP n 0
    _ = cycle2 K (compPowR n K) := by rw [Nat.add_zero]
    _ = cycle2 (compPowR n K) K := cycle2_symm K (compPowR n K)

end HS

end
