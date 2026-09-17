import Hurst.GeneralKPeelInduction
import Hurst.ChainIntegrabilityDischarge

/-!
# The unconditional general-`k` chain-integrability discharge

Discharges the documented residue of `Hurst.GeneralKPeelInduction` / `Hurst.GeneralKPeel`:
the *unconditional* chain-integrability `hP` instances for general `k`.

## Method

Everything is carried out in **nonnegative `lintegral` land**, where Tonelli
(`lintegral_prod`, `lintegral_prod_symm'`) is unconditional for *measurable* functions —
no section-integrability or section-measurability bookkeeping is ever needed.

* `pathLintegral_lt_top` — an open chain of `m` nonneg kernel factors over `vol^{m+1}`
  has finite lintegral, peeled one endpoint at a time (each peel costs the uniform
  section-`L¹` bound `D`).
* `chainLintegral_lt_top` — the `k = n+2` cycle: peel `z_0`; the wrap pair
  `|W 0 (a, w 0)| * |W (last) (w (last), a)|` is Cauchy–Schwarz-ed *in the single variable
  `a`* by AM–GM (`mul_le_half_sq_add_sq`), costing the uniform section-`L²` bounds `E`
  (`hE1` first-coordinate, `hE2` second-coordinate); the remaining open chain is
  discharged by the path lemma.  All bounds are uniform in the section parameters, so no
  section-function measurability is used anywhere.
* `chainProd_integrable_of_sectionBounds` — the master theorem: `chainProd k W` is
  integrable over `vol^k` for every `k ≥ 2`; subsumes the frozen-family case.

## Revision note (bound hypotheses of the master theorem)

The three section-bound hypotheses of `chainProd_integrable_of_sectionBounds` are stated
in **`lintegral`/`ofReal` form** (`∫⁻ a, ENNReal.ofReal |W i (a, y)|² ≤ ENNReal.ofReal E`,
etc.), not in Bochner-integral form.  Reason: the Bochner integral of a non-integrable
section is junk `0` in Mathlib (`integral` is `if Integrable f μ then … else 0`), so
Bochner-form bounds hold vacuously for kernels with non-integrable sections while the
conclusion fails — the Bochner form of the statement is *false*.  Consumers holding
genuine Bochner bounds for *integrable* sections can lift them with
`lintegral_ofReal_le_ofReal_of_integral_le`.
-/

open MeasureTheory Measure Real Set
open scoped Real

noncomputable section

namespace HS

/-! ### Elementary helpers -/

/-- AM–GM: `x * y ≤ (x² + y²)/2`. -/
theorem mul_le_half_sq_add_sq (x y : ℝ) : x * y ≤ (x * x + y * y) / 2 := by
  nlinarith [sq_nonneg (x - y)]

/-- Pointwise rewriting under the nonnegative integral. -/
theorem lintegral_congr_pt {α : Type} {m : MeasurableSpace α} {μ : Measure α}
    {f g : α → ENNReal} (h : ∀ x, f x = g x) :
    (∫⁻ x, f x ∂μ) = ∫⁻ x, g x ∂μ := by
  rw [lintegral_congr_ae (Filter.Eventually.of_forall h)]

/-- Integrability of a nonnegative measurable function from finiteness of the lintegral
of its `ofReal`-form (the `‖·‖ₑ = ofReal ‖·‖` bridge on `ℝ`). -/
theorem integrable_of_lintegral_ofReal_lt {f : ℝ → ℝ} (hf : Measurable f)
    (hnn : ∀ a, 0 ≤ f a) (hlt : (∫⁻ a, ENNReal.ofReal (f a) ∂vol) < (⊤ : ENNReal)) :
    Integrable f vol := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have h1 : ∫⁻ a, ‖f a‖ₑ ∂vol = ∫⁻ a, ENNReal.ofReal ‖f a‖ ∂vol :=
    lintegral_congr_pt (fun a => Real.enorm_eq_ofReal_abs _)
  rw [h1]
  have h2 : ∫⁻ a, ENNReal.ofReal ‖f a‖ ∂vol = ∫⁻ a, ENNReal.ofReal (f a) ∂vol :=
    lintegral_congr_pt (fun a => by
      show ENNReal.ofReal |f a| = ENNReal.ofReal (f a)
      rw [abs_of_nonneg (hnn a)])
  rw [h2]
  exact hlt

/-- Bridge from a genuine Bochner section bound to the `lintegral`/`ofReal` form used by
`chainLintegral_lt_top` and `chainProd_integrable_of_sectionBounds`: for an *integrable*
nonnegative section, `∫⁻ a, ofReal (f a) ≤ ofReal E` follows from `∫ a, f a ≤ E`.
(Without integrability the bridge fails — the Bochner integral is junk `0`.) -/
theorem lintegral_ofReal_le_ofReal_of_integral_le {f : ℝ → ℝ}
    (_hf : Measurable f) (hfint : Integrable f vol) (hnn : ∀ a, 0 ≤ f a) {E : ℝ}
    (hle : ∫ a : ℝ, f a ∂vol ≤ E) :
    (∫⁻ a : ℝ, ENNReal.ofReal (f a) ∂vol) ≤ ENNReal.ofReal E := by
  rw [← ofReal_integral_eq_lintegral_ofReal hfint (Filter.Eventually.of_forall hnn)]
  exact ENNReal.ofReal_le_ofReal hle

/-! ### The peel transport: Tonelli on `vol^{m+1}` via the cons insertion -/

/-- The cons insertion `p ↦ Fin.cons p.1 p.2` is measurable. -/
theorem measurable_cons_fin (n : ℕ) :
    Measurable (fun p : ℝ × (Fin (n+1) → ℝ) =>
      (Fin.cons p.1 p.2 : Fin (n+2) → ℝ)) := by
  have h := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+2) => ℝ)
    (0 : Fin (n+2))).measurable_invFun
  have heq : ∀ p : ℝ × (Fin (n+1) → ℝ),
      (Fin.cons p.1 p.2 : Fin (n+2) → ℝ)
        = (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+2) => ℝ) (0 : Fin (n+2))).symm p := by
    intro p
    exact (piFinSuccAbove_symm_apply_cons p).symm
  rw [show (fun p : ℝ × (Fin (n+1) → ℝ) => (Fin.cons p.1 p.2 : Fin (n+2) → ℝ))
      = fun p : ℝ × (Fin (n+1) → ℝ) =>
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+2) => ℝ) (0 : Fin (n+2))).symm p
    from funext heq]
  exact h

/-- Tonelli on `vol^{n+2}`: peel the first coordinate (no integrability hypotheses). -/
theorem lintegral_pi_cons (n : ℕ) (G : (Fin (n+2) → ℝ) → ENNReal) (hG : Measurable G) :
    (∫⁻ z, G z ∂(Measure.pi fun _ : Fin (n+2) => vol))
      = ∫⁻ a : ℝ, ∫⁻ w : Fin (n+1) → ℝ, G (Fin.cons a w)
          ∂(Measure.pi fun _ : Fin (n+1) => vol) ∂vol := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+2) => ℝ) (0 : Fin (n+2)) with he
  have hmp : MeasurePreserving (⇑e.symm) (vol.prod (Measure.pi fun _ : Fin (n+1) => vol))
      (Measure.pi fun _ : Fin (n+2) => vol) :=
    MeasurePreserving.symm (e := e)
      (measurePreserving_piFinSuccAbove (fun _ : Fin (n+2) => vol) 0)
  have hcons : (fun p : ℝ × (Fin (n+1) → ℝ) => G (Fin.cons p.1 p.2))
      = fun p : ℝ × (Fin (n+1) → ℝ) => G (⇑e.symm p) := by
    funext p
    exact congrArg G (piFinSuccAbove_symm_apply_cons p).symm
  rw [← hmp.map_eq, lintegral_map_equiv G e.symm, ← hcons,
    lintegral_prod (fun p : ℝ × (Fin (n+1) → ℝ) => G (Fin.cons p.1 p.2))
      (hG.comp (measurable_cons_fin n)).aemeasurable]

/-- Tonelli on `vol^{n+2}`, swapped iteration order. -/
theorem lintegral_pi_cons_swap (n : ℕ) (G : (Fin (n+2) → ℝ) → ENNReal) (hG : Measurable G) :
    (∫⁻ z, G z ∂(Measure.pi fun _ : Fin (n+2) => vol))
      = ∫⁻ w : Fin (n+1) → ℝ, ∫⁻ a : ℝ, G (Fin.cons a w) ∂vol
          ∂(Measure.pi fun _ : Fin (n+1) => vol) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+2) => ℝ) (0 : Fin (n+2)) with he
  have hmp : MeasurePreserving (⇑e.symm) (vol.prod (Measure.pi fun _ : Fin (n+1) => vol))
      (Measure.pi fun _ : Fin (n+2) => vol) :=
    MeasurePreserving.symm (e := e)
      (measurePreserving_piFinSuccAbove (fun _ : Fin (n+2) => vol) 0)
  have hcons : (fun p : ℝ × (Fin (n+1) → ℝ) => G (Fin.cons p.1 p.2))
      = fun p : ℝ × (Fin (n+1) → ℝ) => G (⇑e.symm p) := by
    funext p
    exact congrArg G (piFinSuccAbove_symm_apply_cons p).symm
  rw [← hmp.map_eq, lintegral_map_equiv G e.symm, ← hcons]
  exact lintegral_prod_symm' (fun p : ℝ × (Fin (n+1) → ℝ) => G (Fin.cons p.1 p.2))
    (hG.comp (measurable_cons_fin n))

/-! ### The open-chain (path) lemma -/

/-- The `m`-edge open chain product of the kernel family `V` (`m` kernels, `m+1` points),
in absolute value. -/
def pathProd (m : ℕ) (V : Fin m → ℝ × ℝ → ℝ) (w : Fin (m+1) → ℝ) : ℝ :=
  ∏ i : Fin m, |V i (w (Fin.castSucc i), w (Fin.succ i))|

/-- The path product is nonnegative. -/
theorem pathProd_nonneg {m : ℕ} {V : Fin m → ℝ × ℝ → ℝ} (w : Fin (m+1) → ℝ) :
    0 ≤ pathProd m V w := by
  unfold pathProd
  exact Finset.prod_nonneg fun i _ => abs_nonneg _

theorem measurable_pathProd {m : ℕ} {V : Fin m → ℝ × ℝ → ℝ} (hV : ∀ i, Measurable (V i)) :
    Measurable (pathProd m V) := by
  unfold pathProd
  refine Finset.measurable_prod _ fun i _ => ?_
  exact (hV i).abs.comp ((measurable_pi_apply (Fin.castSucc i)).prodMk
    (measurable_pi_apply (Fin.succ i)))

theorem measurable_ofReal_pathProd {m : ℕ} {V : Fin m → ℝ × ℝ → ℝ} (hV : ∀ i, Measurable (V i)) :
    Measurable (fun w : Fin (m+1) → ℝ => ENNReal.ofReal (pathProd m V w)) :=
  ENNReal.continuous_ofReal.measurable.comp (measurable_pathProd hV)

/-- Cons factorization of the path product: the `0`-edge splits off. -/
theorem pathProd_cons (m : ℕ) (V : Fin (m+1) → ℝ × ℝ → ℝ) (a : ℝ) (w : Fin (m+1) → ℝ) :
    pathProd (m+1) V (Fin.cons a w)
      = |V 0 (a, w 0)| * pathProd m (fun i : Fin m => V (Fin.succ i)) w := by
  unfold pathProd
  rw [Fin.prod_univ_succ]
  congr 1

/-- **The path lemma**: an open chain of measurable kernel factors with a uniform
section-`L¹` bound `D` has finite lintegral over `vol^{m+1}` — peeled one endpoint at a
time, each peel costing `D` (no sharpness tracked; only finiteness matters). -/
theorem pathLintegral_lt_top : ∀ (D : ℝ) (m : ℕ) (V : Fin m → ℝ × ℝ → ℝ),
    (∀ i, Measurable (V i)) →
    (∀ (i : Fin m) (y : ℝ), ∫⁻ a : ℝ, ENNReal.ofReal |V i (a, y)| ∂vol ≤ ENNReal.ofReal D) →
    (∫⁻ w, ENNReal.ofReal (pathProd m V w)
        ∂(Measure.pi fun _ : Fin (m+1) => vol)) < (⊤ : ENNReal) := by
  intro D m
  induction m with
  | zero =>
      intro V _ _
      rw [lintegral_congr_pt (fun w => by
        show ENNReal.ofReal (∏ _i : Fin 0, _) = ENNReal.ofReal 1
        simp)]
      rw [ENNReal.ofReal_one, lintegral_one]
      exact lt_top_iff_ne_top.mpr
        (measure_ne_top (Measure.pi fun _ : Fin 1 => vol) Set.univ)
  | succ m ih =>
      intro V hVm hVD
      have hPm := ih (fun i : Fin m => V (Fin.succ i)) (fun i => hVm (Fin.succ i))
        (fun i y => hVD (Fin.succ i) y)
      have hmeas := measurable_ofReal_pathProd hVm
      rw [lintegral_pi_cons_swap m _ hmeas]
      have hbound : ∀ w : Fin (m+1) → ℝ,
          ∫⁻ a : ℝ, ENNReal.ofReal (pathProd (m+1) V (Fin.cons a w)) ∂vol
            ≤ ENNReal.ofReal D * ENNReal.ofReal (pathProd m
                (fun i : Fin m => V (Fin.succ i)) w) := by
        intro w
        have hpt : ∀ a : ℝ, ENNReal.ofReal (pathProd (m+1) V (Fin.cons a w))
          = ENNReal.ofReal |V 0 (a, w 0)| * ENNReal.ofReal (pathProd m
              (fun i : Fin m => V (Fin.succ i)) w) := by
          intro a
          rw [pathProd_cons, ENNReal.ofReal_mul (abs_nonneg _)]
        have hsecM : Measurable (fun a : ℝ => ENNReal.ofReal |V 0 (a, w 0)|) :=
          ENNReal.continuous_ofReal.measurable.comp
            ((hVm 0).abs.comp (measurable_id.prodMk measurable_const))
        have hsec : (∫⁻ a : ℝ, ENNReal.ofReal |V 0 (a, w 0)| ∂vol)
            ≤ ENNReal.ofReal D :=
          hVD 0 (w 0)
        calc ∫⁻ a : ℝ, ENNReal.ofReal (pathProd (m+1) V (Fin.cons a w)) ∂vol
            = ∫⁻ a : ℝ, ENNReal.ofReal |V 0 (a, w 0)| * ENNReal.ofReal (pathProd m
                  (fun i : Fin m => V (Fin.succ i)) w) ∂vol :=
              lintegral_congr_pt hpt
          _ = (∫⁻ a : ℝ, ENNReal.ofReal |V 0 (a, w 0)| ∂vol) * ENNReal.ofReal (pathProd m
                  (fun i : Fin m => V (Fin.succ i)) w) :=
              lintegral_mul_const _ hsecM
          _ ≤ ENNReal.ofReal D * ENNReal.ofReal (pathProd m
                  (fun i : Fin m => V (Fin.succ i)) w) :=
                mul_le_mul' hsec le_rfl
      refine lt_of_le_of_lt (lintegral_mono hbound) ?_
      rw [lintegral_const_mul (ENNReal.ofReal D)
        (measurable_ofReal_pathProd (fun i => hVm (Fin.succ i)))]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hPm

/-! ### The cycle lemma and the master integrability theorem -/

/-- Absolute-value cons decomposition of the cycle product (from the landed
`chainProd_cons`), routed through the path product of the shifted family. -/
theorem chainAbs_cons (n : ℕ) (W : Fin (n+2) → ℝ × ℝ → ℝ) (a : ℝ) (w : Fin (n+1) → ℝ) :
    |chainProd (n+2) W (Fin.cons a w)|
      = |W 0 (a, w 0)| * |W (Fin.last (n+1)) (w (Fin.last n), a)|
        * pathProd n (fun i : Fin n => W ((Fin.castSucc i).succ)) w := by
  rw [chainProd_cons, abs_mul, abs_mul, Finset.abs_prod]
  have hpath : pathProd n (fun i : Fin n => W ((Fin.castSucc i).succ)) w
      = ∏ i : Fin n, |W ((Fin.castSucc i).succ) (w (Fin.castSucc i), w (Fin.succ i))| := rfl
  rw [hpath]
  ring

/-- Measurability of the cycle product's `ofReal`-absolute-value form. -/
theorem measurable_ofReal_abs_chainProd {k : ℕ} {W : Fin k → ℝ × ℝ → ℝ}
    (hWm : ∀ i, Measurable (W i)) :
    Measurable (fun z => ENNReal.ofReal |chainProd k W z|) :=
  ENNReal.continuous_ofReal.measurable.comp (measurable_chainProd hWm).abs

/-- **The cycle lemma**: the `k = n+2` cycle product of a measurable kernel family with
uniform section-`L²` bounds `E` (both coordinate forms) and uniform section-`L¹` bound `D`
has finite lintegral over `vol^{n+2}` — the general-`k` integrability engine. -/
theorem chainLintegral_lt_top (n : ℕ) (W : Fin (n+2) → ℝ × ℝ → ℝ)
    (hWm : ∀ i, Measurable (W i)) (E D : ℝ)
    (hE1 : ∀ (i : Fin (n+2)) (y : ℝ), ∫⁻ a : ℝ, ENNReal.ofReal |W i (a, y)| ^ 2 ∂vol ≤ ENNReal.ofReal E)
    (hE2 : ∀ (i : Fin (n+2)) (y : ℝ), ∫⁻ a : ℝ, ENNReal.ofReal |W i (y, a)| ^ 2 ∂vol ≤ ENNReal.ofReal E)
    (hD1 : ∀ (i : Fin (n+2)) (y : ℝ), ∫⁻ a : ℝ, ENNReal.ofReal |W i (a, y)| ∂vol ≤ ENNReal.ofReal D) :
    (∫⁻ z, ENNReal.ofReal |chainProd (n+2) W z|
        ∂(Measure.pi fun _ : Fin (n+2) => vol)) < (⊤ : ENNReal) := by
  classical
  have hmeas := measurable_ofReal_abs_chainProd hWm
  have hpath := pathLintegral_lt_top D n (fun i : Fin n => W ((Fin.castSucc i).succ))
    (fun i => hWm ((Fin.castSucc i).succ)) (fun i y => hD1 ((Fin.castSucc i).succ) y)
  have hpairL : ∀ w : Fin (n+1) → ℝ,
      ∫⁻ a : ℝ, ENNReal.ofReal (|W 0 (a, w 0)|
          * |W (Fin.last (n+1)) (w (Fin.last n), a)|) ∂vol
        ≤ ENNReal.ofReal E + ENNReal.ofReal E := by
    intro w
    have hA : Measurable (fun a : ℝ => |W 0 (a, w 0)|) :=
      (hWm 0).abs.comp (measurable_id.prodMk measurable_const)
    have hB : Measurable (fun a : ℝ => |W (Fin.last (n+1)) (w (Fin.last n), a)|) :=
      (hWm (Fin.last (n+1))).abs.comp (measurable_const.prodMk measurable_id)
    have hf2 : Measurable (fun a : ℝ => ENNReal.ofReal |W 0 (a, w 0)| ^ 2) :=
      (ENNReal.continuous_ofReal.measurable.comp hA).pow measurable_const
    have hg2 : Measurable (fun a : ℝ =>
        ENNReal.ofReal |W (Fin.last (n+1)) (w (Fin.last n), a)| ^ 2) :=
      (ENNReal.continuous_ofReal.measurable.comp hB).pow measurable_const
    have hamgm : ∀ a : ℝ, ENNReal.ofReal (|W 0 (a, w 0)|
        * |W (Fin.last (n+1)) (w (Fin.last n), a)|)
        ≤ ENNReal.ofReal |W 0 (a, w 0)| ^ 2
            + ENNReal.ofReal |W (Fin.last (n+1)) (w (Fin.last n), a)| ^ 2 := by
      intro a
      have h2a : ENNReal.ofReal |W 0 (a, w 0)| ^ 2
          = ENNReal.ofReal (|W 0 (a, w 0)| ^ 2) :=
        (ENNReal.ofReal_pow (abs_nonneg _) 2).symm
      have h2b : ENNReal.ofReal |W (Fin.last (n+1)) (w (Fin.last n), a)| ^ 2
          = ENNReal.ofReal (|W (Fin.last (n+1)) (w (Fin.last n), a)| ^ 2) :=
        (ENNReal.ofReal_pow (abs_nonneg _) 2).symm
      have hsplit : ENNReal.ofReal |W 0 (a, w 0)| ^ 2
          + ENNReal.ofReal |W (Fin.last (n+1)) (w (Fin.last n), a)| ^ 2
          = ENNReal.ofReal (|W 0 (a, w 0)| ^ 2
              + |W (Fin.last (n+1)) (w (Fin.last n), a)| ^ 2) := by
        rw [h2a, h2b, ← ENNReal.ofReal_add (pow_nonneg (abs_nonneg _) 2)
          (pow_nonneg (abs_nonneg _) 2)]
      rw [hsplit]
      refine ENNReal.ofReal_le_ofReal ?_
      nlinarith [sq_nonneg (|W 0 (a, w 0)| - |W (Fin.last (n+1)) (w (Fin.last n), a)|),
        sq_nonneg (|W 0 (a, w 0)|), sq_nonneg (|W (Fin.last (n+1)) (w (Fin.last n), a)|)]
    calc ∫⁻ a : ℝ, ENNReal.ofReal (|W 0 (a, w 0)|
            * |W (Fin.last (n+1)) (w (Fin.last n), a)|) ∂vol
        ≤ ∫⁻ a : ℝ, ENNReal.ofReal |W 0 (a, w 0)| ^ 2
              + ENNReal.ofReal |W (Fin.last (n+1)) (w (Fin.last n), a)| ^ 2 ∂vol :=
          lintegral_mono hamgm
      _ = ∫⁻ a : ℝ, ENNReal.ofReal |W 0 (a, w 0)| ^ 2 ∂vol
              + ∫⁻ a : ℝ, ENNReal.ofReal |W (Fin.last (n+1)) (w (Fin.last n), a)| ^ 2 ∂vol :=
          lintegral_add_left hf2 _
      _ ≤ ENNReal.ofReal E + ENNReal.ofReal E :=
          add_le_add (hE1 0 (w 0)) (hE2 (Fin.last (n+1)) (w (Fin.last n)))
  have hstep : ∀ w : Fin (n+1) → ℝ,
      (∫⁻ a : ℝ, ENNReal.ofReal |chainProd (n+2) W (Fin.cons a w)| ∂vol)
        ≤ (ENNReal.ofReal E + ENNReal.ofReal E) * ENNReal.ofReal
            (pathProd n (fun i : Fin n => W ((Fin.castSucc i).succ)) w) := by
    intro w
    have hA : Measurable (fun a : ℝ => |W 0 (a, w 0)|) :=
      (hWm 0).abs.comp (measurable_id.prodMk measurable_const)
    have hB : Measurable (fun a : ℝ => |W (Fin.last (n+1)) (w (Fin.last n), a)|) :=
      (hWm (Fin.last (n+1))).abs.comp (measurable_const.prodMk measurable_id)
    have hpairM : Measurable (fun a : ℝ => ENNReal.ofReal (|W 0 (a, w 0)|
        * |W (Fin.last (n+1)) (w (Fin.last n), a)|)) :=
      ENNReal.continuous_ofReal.measurable.comp (hA.mul hB)
    have hpt : ∀ a : ℝ, ENNReal.ofReal |chainProd (n+2) W (Fin.cons a w)|
        = ENNReal.ofReal (|W 0 (a, w 0)|
            * |W (Fin.last (n+1)) (w (Fin.last n), a)|) * ENNReal.ofReal
            (pathProd n (fun i : Fin n => W ((Fin.castSucc i).succ)) w) := by
      intro a
      rw [chainAbs_cons, ENNReal.ofReal_mul
        (mul_nonneg (abs_nonneg _) (abs_nonneg _))]
    calc ∫⁻ a : ℝ, ENNReal.ofReal |chainProd (n+2) W (Fin.cons a w)| ∂vol
        = ∫⁻ a : ℝ, ENNReal.ofReal (|W 0 (a, w 0)|
              * |W (Fin.last (n+1)) (w (Fin.last n), a)|) * ENNReal.ofReal
              (pathProd n (fun i : Fin n => W ((Fin.castSucc i).succ)) w) ∂vol :=
            lintegral_congr_pt hpt
      _ = (∫⁻ a : ℝ, ENNReal.ofReal (|W 0 (a, w 0)|
              * |W (Fin.last (n+1)) (w (Fin.last n), a)|) ∂vol) * ENNReal.ofReal
              (pathProd n (fun i : Fin n => W ((Fin.castSucc i).succ)) w) :=
            lintegral_mul_const _ hpairM
      _ ≤ (ENNReal.ofReal E + ENNReal.ofReal E) * ENNReal.ofReal
              (pathProd n (fun i : Fin n => W ((Fin.castSucc i).succ)) w) :=
            mul_le_mul' (hpairL w) le_rfl
  rw [lintegral_pi_cons_swap n _ hmeas]
  refine lt_of_le_of_lt (lintegral_mono hstep) ?_
  rw [lintegral_const_mul (ENNReal.ofReal E + ENNReal.ofReal E)
    (measurable_ofReal_pathProd (fun i => hWm ((Fin.castSucc i).succ)))]
  exact ENNReal.mul_lt_top
    (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩) hpath

/-- **The master theorem (item 2)**: the `k`-cycle product of a measurable kernel family
with uniform section-`L¹` bound `D` and uniform section-`L²` bounds `E` (both coordinate
forms) is integrable over `vol^k`, for every `k ≥ 2`.  This is the unconditional `hP`
discharge for general `k`.

The three section bounds are stated in **`lintegral`/`ofReal` form**.  (The earlier
Bochner-integral form `∫ a, |W i (a, y)|² ≤ E` was vacuous — Mathlib's Bochner integral of
a non-integrable section is junk `0`, so the Bochner form holds for kernels with
non-integrable sections while the conclusion fails.)  Consumers holding genuine Bochner
bounds for integrable sections can lift them via
`lintegral_ofReal_le_ofReal_of_integral_le`. -/
theorem chainProd_integrable_of_sectionBounds {k : ℕ} (hk : 2 ≤ k)
    (W : Fin k → ℝ × ℝ → ℝ) (hWm : ∀ i, Measurable (W i)) (E D : ℝ)
    (hE1 : ∀ (i : Fin k) (y : ℝ),
      ∫⁻ a : ℝ, ENNReal.ofReal |W i (a, y)| ^ 2 ∂vol ≤ ENNReal.ofReal E)
    (hE2 : ∀ (i : Fin k) (y : ℝ),
      ∫⁻ a : ℝ, ENNReal.ofReal |W i (y, a)| ^ 2 ∂vol ≤ ENNReal.ofReal E)
    (hD1 : ∀ (i : Fin k) (y : ℝ),
      ∫⁻ a : ℝ, ENNReal.ofReal |W i (a, y)| ∂vol ≤ ENNReal.ofReal D) :
    Integrable (chainProd k W) (Measure.pi fun _ : Fin k => vol) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  refine ⟨(measurable_chainProd hWm).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  rw [lintegral_congr_pt (fun z => Real.enorm_eq_ofReal_abs (chainProd (n + 2) W z))]
  exact chainLintegral_lt_top n W hWm E D hE1 hE2 hD1

end HS

end
