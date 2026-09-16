import Hurst.HSCycleComposition

/-!
# The general-`k` peel induction: cyclic invariance and the composed-kernel trace form

This file completes the general-`k` cycle-composition layer on the landed `HS` encoding
(`Hurst.HSOperatorFoundation`, `Hurst.HSOperatorLayer2`, `Hurst.HSCycleComposition`):
kernels `K : ℝ × ℝ → ℝ`, `HSKernel K = MemLp K 2 vol2`, `hsNorm K = (∫∫ K² ∂vol2)^(1/2)`,
`cycle2 K L = ∫∫ K(x,y) L(y,x)`, `compKernel K L (x,y) = ∫ t, K(x,t) L(t,y)`,
`cycleIntegral k K = ∫_{(Fin k → ℝ)} ∏ i, K (z i, z (cycleSucc i)) ∂(vol^k)`.

## Main results

* `chainIntegral` / `chainProd` — the chain (cycle) integral of a *family* of kernels
  `W : Fin k → ℝ × ℝ → ℝ` (the landed `cycleIntegral k K` is `chainIntegral k (fun _ => K)`).
* `chainIntegral_rotate` — **the cyclic invariance core**: the chain integral is invariant
  under simultaneous cyclic rotation of the kernel family (coordinates `z ↦ z ∘ cycleSucc`
  transported by the measure-preserving relabeling `measurePreserving_piCongrLeft`).
* `chainIntegral_two` — the `k = 2` anchor: `chainIntegral 2 W = cycle2 (W 0) (W 1)`.
* `contract` — the peel contraction: for a `(k+1)`-chain `W`, `contract W : Fin k → _`
  composes the wrap-adjacent pair `(W (Fin.last (k+1)), W 0)` into position `0`:
  `contract W 0 = compKernel (W (Fin.last (k+1))) (W 0)`, `contract W j.succ = W j.succ.succ`.
* `chainIntegral_peel` — **the peel step**: `chainIntegral (k+1) W = chainIntegral k (contract W)`
  under the chain-integrability hypothesis `hP` (the generalization of the landed
  `cycle2_compKernel_eq_triple` `hA`/`hB` hypotheses to `k+1`); the peel also *propagates*
  the integrability to the contracted chain.
* `hsKernel_comp`, `hsNorm_compPowL_le` — composition (`compKernel`) keeps kernels
  Hilbert–Schmidt, with `hsNorm (compPowL n K) ≤ hsNorm K ^ (n+1)` (iterated landed
  `hsNorm_comp_le` submultiplicativity).
* `chain_ext_cycle`, `cycleIntegral_comp` — **the general-`k` peel induction**:
  `cycleIntegral (n+2) K = cycle2 (compPowL n K) K`, i.e. the `(n+2)`-cycle integral equals
  the composed-kernel trace form (the `(k+1)`-cycle integral = composed-kernel trace form
  of the landed `k = 3` anchors, generalized).
* `chainTriple_integrable` — the `hA` discharge (and the symmetric `hB` form): for
  measurable HS kernels the triple chain integrand *is* integrable (section
  Cauchy–Schwarz + one Cauchy–Schwarz on the square, bounded by `hsNorm K hsNorm L hsNorm M`),
  so the landed `k = 3` anchors are unconditional; see `cycleIntegral_three`.

## Status of the HasSum application (item (3), documented)

For the enumerated nonneg spectrum, the spectral bridge `Σ_j κ_j^k = C_k(K)` is anchored at
`k = 2` by the landed `cycleIntegral_two` + `cycle2_self_sq`/`cycle2_transpose_self` and at
`k = 3` by `cycleIntegral_three` (below, unconditional given `Measurable K` + `HSKernel K`).
The general-`k` bridge follows from `cycleIntegral_comp`: `C_{n+2}(K) = cycle2 (compPowL n K) K`
with `hsNorm (compPowL n K) ≤ hsNorm K^{n+1}` (`hsNorm_compPowL_le`) keeping the trace form
absolutely convergent at the rate of the HS-norm powers.  What remains for a *full* HasSum
application is the unconditional general-`k` chain-integrability (each `hP` instance; for the
truncated Riesz kernel the factors are nonnegative and `hP` reduces to a Tonelli-finiteness
statement, but the general signed case is not landed — see the gap report at the bottom).
-/

open MeasureTheory Measure Real Set
open scoped Real

noncomputable section

namespace HS

/-! ### The chain integral over `Fin k` and its cyclic invariance -/

/-- The `k`-chain (cycle) product of a kernel family `W : Fin k → ℝ × ℝ → ℝ`. -/
def chainProd (k : ℕ) (W : Fin k → ℝ × ℝ → ℝ) (z : Fin k → ℝ) : ℝ :=
  ∏ i : Fin k, W i (z i, z (cycleSucc i))

/-- The `k`-chain (cycle) integral of a kernel family: the kernel-side `C_k` functional.
`cycleIntegral k K = chainIntegral k (fun _ => K)` definitionally. -/
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

/-- The backward cyclic step `j ↦ j - 1` on `Fin k` (the inverse of `cycleSucc`). -/
def rotBack {k : ℕ} (j : Fin k) : Fin k :=
  ⟨if (j : ℕ) = 0 then k - 1 else (j : ℕ) - 1, by
    by_cases h : (j : ℕ) = 0
    · rw [if_pos h]; omega
    · rw [if_neg h]; have := j.2; omega⟩

theorem rotBack_val {k : ℕ} (j : Fin k) :
    ((rotBack j : Fin k) : ℕ) = if (j : ℕ) = 0 then k - 1 else (j : ℕ) - 1 := rfl

theorem cycleSucc_val {k : ℕ} (i : Fin k) :
    ((cycleSucc i : Fin k) : ℕ) = if (i : ℕ) + 1 < k then (i : ℕ) + 1 else 0 := by
  unfold cycleSucc
  split <;> rfl

theorem rotBack_cycleSucc {k : ℕ} (i : Fin k) : rotBack (cycleSucc i) = i := by
  apply Fin.ext
  have hi := i.2
  have hv2 := rotBack_val (cycleSucc i)
  by_cases h : (i : ℕ) + 1 < k
  · have hv1 : ((cycleSucc i : Fin k) : ℕ) = (i : ℕ) + 1 := by
      rw [cycleSucc_val, if_pos h]
    rw [hv1, if_neg (show ¬((i : ℕ) + 1 = 0) by omega)] at hv2
    omega
  · have hik : (i : ℕ) + 1 = k := by omega
    have hv1 : ((cycleSucc i : Fin k) : ℕ) = 0 := by
      rw [cycleSucc_val, if_neg h]
    rw [hv1, if_pos rfl] at hv2
    omega

theorem cycleSucc_rotBack {k : ℕ} (j : Fin k) : cycleSucc (rotBack j) = j := by
  apply Fin.ext
  have hj := j.2
  have hv1 := rotBack_val j
  have hv2 := cycleSucc_val (rotBack j)
  by_cases h : (j : ℕ) = 0
  · rw [if_pos h] at hv1
    rw [hv1, if_neg (show ¬((k - 1 : ℕ) + 1 < k) by omega)] at hv2
    omega
  · rw [if_neg h] at hv1
    rw [hv1, if_pos (show (j : ℕ) - 1 + 1 < k by omega)] at hv2
    omega

/-- The cyclic rotation equiv on `Fin k`: forward step `cycleSucc` with inverse `rotBack`. -/
def rotEquiv (k : ℕ) : Fin k ≃ Fin k where
  toFun := cycleSucc
  invFun := rotBack
  left_inv := rotBack_cycleSucc
  right_inv := cycleSucc_rotBack

/-- The value of the `piCongrLeft` relabeling at an arbitrary coordinate. -/
theorem piCongrLeft_rot_val {k : ℕ} (z : Fin k → ℝ) (j : Fin k) :
    (MeasurableEquiv.piCongrLeft (fun _ : Fin k => ℝ) (rotEquiv k)) z j = z (rotBack j) := by
  have h1 := MeasurableEquiv.piCongrLeft_apply_apply (e := rotEquiv k)
    (β := fun _ => ℝ) (x := z) (rotBack j)
  have h2 : (rotEquiv k) (rotBack j) = j := cycleSucc_rotBack j
  rw [h2] at h1
  exact h1

/-- The coordinate rotation `z ↦ z ∘ rotBack` (as the `piCongrLeft` relabeling) preserves
`vol^k` (via the landed `measurePreserving_piCongrLeft` route). -/
theorem measurePreserving_rotBack (k : ℕ) :
    MeasurePreserving (⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin k => ℝ) (rotEquiv k)))
      (Measure.pi fun _ : Fin k => vol) (Measure.pi fun _ : Fin k => vol) :=
  measurePreserving_piCongrLeft (α := fun _ : Fin k => ℝ) (μ := fun _ => vol) (f := rotEquiv k)

/-- **The cyclic invariance core**: the chain integral is invariant under simultaneous
cyclic rotation of the kernel family (the measure-preserving cyclic reindexing
`z ↦ z ∘ rotBack` on `(Fin k → ℝ)` composed with the product reindexing
`i ↦ cycleSucc i`). -/
theorem chainIntegral_rotate (k : ℕ) (W : Fin k → ℝ × ℝ → ℝ) :
    chainIntegral k W = chainIntegral k (fun j => W (cycleSucc j)) := by
  show ∫ z : Fin k → ℝ, chainProd k W z ∂(Measure.pi fun _ : Fin k => vol)
      = chainIntegral k (fun j => W (cycleSucc j))
  rw [← (measurePreserving_rotBack k).integral_comp' (fun z => chainProd k W z)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  show chainProd k W (⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin k => ℝ) (rotEquiv k)) z)
      = chainProd k (fun j => W (cycleSucc j)) z
  have hlhs : chainProd k W (⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin k => ℝ) (rotEquiv k)) z)
      = ∏ i : Fin k, W i (z (rotBack i), z i) := by
    rw [chainProd, Finset.prod_congr rfl (fun i _ => by
      show W i ((⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin k => ℝ) (rotEquiv k)) z) i,
          (⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin k => ℝ) (rotEquiv k)) z) (cycleSucc i))
          = W i (z (rotBack i), z i)
      rw [piCongrLeft_rot_val, piCongrLeft_rot_val, rotBack_cycleSucc])]
  rw [hlhs]
  show ∏ i : Fin k, W i (z (rotBack i), z i)
      = chainProd k (fun j => W (cycleSucc j)) z
  have hrhs : chainProd k (fun j => W (cycleSucc j)) z
      = ∏ i : Fin k, W (cycleSucc i) (z i, z (cycleSucc i)) := rfl
  rw [hrhs]
  refine Finset.prod_equiv (rotEquiv k).symm (fun _ => by simp) (fun i _ => ?_)
  rw [show ((rotEquiv k).symm i) = rotBack i from rfl, cycleSucc_rotBack]

/-! ### The `k = 2` anchor -/

/-- **The `k = 2` anchor** for general chains: `chainIntegral 2 W = cycle2 (W 0) (W 1)`
(the landed `cycleIntegral_two` route via `measurePreserving_piFinTwo`). -/
theorem chainIntegral_two (W : Fin 2 → ℝ × ℝ → ℝ) :
    chainIntegral 2 W = cycle2 (W 0) (W 1) := by
  have hpt : ∀ z : Fin 2 → ℝ,
      chainProd 2 W z = (fun w : ℝ × ℝ => W 0 w * W 1 w.swap)
        (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ) z) := by
    intro z
    show (∏ i : Fin 2, W i (z i, z (cycleSucc i))) = W 0 (z 0, z 1) * W 1 (z 1, z 0)
    rw [Fin.prod_univ_two, cycleSucc_two_zero, cycleSucc_two_one]
  calc chainIntegral 2 W
      = ∫ z : Fin 2 → ℝ, chainProd 2 W z ∂(Measure.pi fun _ : Fin 2 => vol) := rfl
    _ = ∫ w : ℝ × ℝ, W 0 w * W 1 w.swap ∂(vol.prod vol) :=
        (integral_congr_ae (Filter.Eventually.of_forall hpt)).trans
          ((measurePreserving_piFinTwo (fun _ : Fin 2 => vol)).integral_comp'
            (fun w : ℝ × ℝ => W 0 w * W 1 w.swap))
    _ = cycle2 (W 0) (W 1) := rfl

/-! ### Composition keeps kernels Hilbert–Schmidt -/

/-- The composed kernel of two measurable HS kernels is again HS (the domination
argument of the landed `hsNorm_comp_le`). -/
theorem hsKernel_comp {K L : ℝ × ℝ → ℝ} (hKm : Measurable K) (hLm : Measurable L)
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

/-! ### The left-growing composition tower -/

/-- The `n`-fold composition tower growing on the left:
`compPowL 0 K = K`, `compPowL (n+1) K = compKernel K (compPowL n K)`. -/
def compPowL : ℕ → (ℝ × ℝ → ℝ) → (ℝ × ℝ → ℝ)
  | 0, K => K
  | n + 1, K => compKernel K (compPowL n K)

/-- The same tower with a distinct head kernel `W₀`:
`compPowL' 0 K W₀ = W₀`, `compPowL' (n+1) K W₀ = compKernel K (compPowL' n K W₀)`. -/
def compPowL' : ℕ → (ℝ × ℝ → ℝ) → (ℝ × ℝ → ℝ) → (ℝ × ℝ → ℝ)
  | 0, _, W₀ => W₀
  | n + 1, K, W₀ => compKernel K (compPowL' n K W₀)

theorem compPowL_eq (n : ℕ) (K : ℝ × ℝ → ℝ) : compPowL n K = compPowL' n K K := by
  induction n with
  | zero => rfl
  | succ m ih => simp only [compPowL, compPowL', ih]

theorem compPowL'_assoc (n : ℕ) (K W₀ : ℝ × ℝ → ℝ) :
    compPowL' n K (compKernel K W₀) = compKernel K (compPowL' n K W₀) := by
  induction n with
  | zero => rfl
  | succ m ih => simp only [compPowL', ih]

/-- Measurability propagates up the tower. -/
theorem measurable_compPowL (n : ℕ) {K : ℝ × ℝ → ℝ} (hKm : Measurable K) :
    Measurable (compPowL n K) := by
  induction n with
  | zero => exact hKm
  | succ m ih => exact (stronglyMeasurable_compKernel hKm ih).measurable

/-- HS membership propagates up the tower. -/
theorem hsKernel_compPowL (n : ℕ) {K : ℝ × ℝ → ℝ} (hKm : Measurable K) (hK : HSKernel K) :
    HSKernel (compPowL n K) := by
  induction n with
  | zero => exact hK
  | succ m ih => exact hsKernel_comp hKm (measurable_compPowL m hKm) hK ih

/-- **Iterated submultiplicativity**: `hsNorm (compPowL n K) ≤ hsNorm K ^ (n+1)`
(the landed `hsNorm_comp_le` iterated). -/
theorem hsNorm_compPowL_le (n : ℕ) {K : ℝ × ℝ → ℝ} (hKm : Measurable K) (hK : HSKernel K) :
    hsNorm (compPowL n K) ≤ hsNorm K ^ (n + 1) := by
  induction n with
  | zero => simp [compPowL]
  | succ m ih =>
    refine (hsNorm_comp_le hKm (measurable_compPowL m hKm) hK (hsKernel_compPowL m hKm hK)).trans ?_
    calc hsNorm K * hsNorm (compPowL m K)
        ≤ hsNorm K * hsNorm K ^ (m + 1) := by exact mul_le_mul_of_nonneg_left ih (hsNorm_nonneg K)
      _ = hsNorm K ^ (m + 2) := by ring

/-! ### The peel contraction and the peel step -/

theorem cycleSucc_last {k : ℕ} (hk : 1 ≤ k) : cycleSucc (Fin.last k) = 0 := by
  apply Fin.ext
  have hv := cycleSucc_val (Fin.last k)
  have hvl : (Fin.last k).val = k := Fin.val_last _
  rw [hvl, if_neg (show ¬((k : ℕ) + 1 < k + 1) by omega)] at hv
  simpa using hv

/-- The peel contraction: for an `(n+2)`-chain `W`, `contract W : Fin (n+1) → _` composes
the wrap-adjacent pair `(W (Fin.last (n+1)), W 0)` into the last position (the composed
kernel of the landed `hsNorm_comp_le` layer). -/
def contract {n : ℕ} (W : Fin (n+2) → ℝ × ℝ → ℝ) : Fin (n+1) → ℝ × ℝ → ℝ :=
  fun j => if j = Fin.last n then compKernel (W (Fin.last (n+1))) (W 0) else W j.succ

theorem contract_apply_last {n : ℕ} (W : Fin (n+2) → ℝ × ℝ → ℝ) :
    contract W (Fin.last n) = compKernel (W (Fin.last (n+1))) (W 0) := by
  rw [contract, if_pos rfl]

theorem contract_apply_succ {n : ℕ} (W : Fin (n+2) → ℝ × ℝ → ℝ) {j : Fin (n+1)}
    (hj : j ≠ Fin.last n) : contract W j = W j.succ := by
  rw [contract, if_neg hj]

/-- Measurability of the contracted chain. -/
theorem measurable_contract {n : ℕ} {W : Fin (n+2) → ℝ × ℝ → ℝ} (hWm : ∀ i, Measurable (W i))
    (j : Fin (n+1)) : Measurable (contract W j) := by
  by_cases hj : j = Fin.last n
  · rw [hj, contract_apply_last W]
    exact (stronglyMeasurable_compKernel (hWm _) (hWm _)).measurable
  · rw [contract_apply_succ W hj]
    exact hWm _

/-! ### Fin-product algebra of the peel -/

theorem cycleSucc_zero {k : ℕ} : cycleSucc (0 : Fin (k + 2)) = 1 := by
  rw [cycleSucc, dif_pos (show (0 : Fin (k + 2)).val + 1 < k + 2 by
    simp only [Fin.val_zero]; omega)]
  rfl

/-- Unconditional wrap of the cyclic successor at the last index. -/
theorem cycleSucc_last' {k : ℕ} : cycleSucc (Fin.last k) = 0 := by
  rw [cycleSucc, dif_neg (show ¬((Fin.last k).val + 1 < k + 1) by
    rw [Fin.val_last]; omega)]
  rfl

/-- No wrap on `castSucc`: the cyclic successor of `i.castSucc` in `Fin (n+1)` is `i.succ`. -/
theorem cycleSucc_castSucc {n : ℕ} (i : Fin n) :
    cycleSucc (Fin.castSucc i) = Fin.succ i := by
  rw [cycleSucc, dif_pos (show (Fin.castSucc i).val + 1 < n + 1 by
    simp only [Fin.val_castSucc]; have hi := i.isLt; omega)]
  rfl

/-- The cyclic successor of `(castSucc j).succ` in `Fin (n+2)` is the double successor. -/
theorem cycleSucc_castSucc_succ {n : ℕ} (j : Fin n) :
    cycleSucc ((Fin.castSucc j).succ) = Fin.succ (Fin.succ j) := by
  rw [cycleSucc, dif_pos (show ((Fin.castSucc j).succ : Fin (n + 2)).val + 1 < n + 2 by
    simp only [Fin.val_succ, Fin.val_castSucc]; have hj := j.isLt; omega)]
  rfl

/-- **Cons factorization of the chain product**: evaluating the `(n+2)`-chain product at
`Fin.cons a w` splits off the `0`-factor (edge `a ↦ w 0` at kernel `W 0`), the wrap
factor `w (last n) ↦ a` at kernel `W (last (n+1))`, and the interior product along `w`
(the peel reassembly form). -/
theorem chainProd_cons (n : ℕ) (W : Fin (n + 2) → ℝ × ℝ → ℝ) (a : ℝ) (w : Fin (n + 1) → ℝ) :
    chainProd (n + 2) W (Fin.cons a w)
      = W 0 (a, w 0) * ((∏ j : Fin n, W ((Fin.castSucc j).succ)
            (w (Fin.castSucc j), w (Fin.succ j)))
          * W (Fin.last (n + 1)) (w (Fin.last n), a)) := by
  have hlast : (Fin.last n).succ = Fin.last (n + 1) := Fin.succ_last n
  have hint : ∀ j : Fin n, W ((Fin.castSucc j).succ)
      ((Fin.cons a w : Fin (n + 2) → ℝ) (Fin.castSucc j).succ,
        (Fin.cons a w : Fin (n + 2) → ℝ) (cycleSucc (Fin.castSucc j).succ))
      = W ((Fin.castSucc j).succ) (w (Fin.castSucc j), w (Fin.succ j)) := fun j => by
    rw [Fin.cons_succ, cycleSucc_castSucc_succ, Fin.cons_succ]
  calc chainProd (n + 2) W (Fin.cons a w)
      = ∏ i : Fin (n + 2), W i ((Fin.cons a w : Fin (n + 2) → ℝ) i,
          (Fin.cons a w : Fin (n + 2) → ℝ) (cycleSucc i)) := rfl
    _ = W 0 ((Fin.cons a w : Fin (n + 2) → ℝ) 0,
            (Fin.cons a w : Fin (n + 2) → ℝ) (cycleSucc (0 : Fin (n + 2))))
          * ∏ i : Fin (n + 1), W (i.succ)
              ((Fin.cons a w : Fin (n + 2) → ℝ) (i.succ),
                (Fin.cons a w : Fin (n + 2) → ℝ) (cycleSucc i.succ)) :=
        Fin.prod_univ_succ (fun i : Fin (n + 2) => W i
          ((Fin.cons a w : Fin (n + 2) → ℝ) i,
            (Fin.cons a w : Fin (n + 2) → ℝ) (cycleSucc i)))
    _ = W 0 (a, w 0) * ∏ i : Fin (n + 1), W (i.succ)
            ((Fin.cons a w : Fin (n + 2) → ℝ) (i.succ),
              (Fin.cons a w : Fin (n + 2) → ℝ) (cycleSucc i.succ)) := by
        rw [Fin.cons_zero, cycleSucc_zero, Fin.cons_one]
    _ = W 0 (a, w 0) * ((∏ j : Fin n, W ((Fin.castSucc j).succ)
              ((Fin.cons a w : Fin (n + 2) → ℝ) (Fin.castSucc j).succ,
                (Fin.cons a w : Fin (n + 2) → ℝ) (cycleSucc (Fin.castSucc j).succ)))
            * W (Fin.succ (Fin.last n))
                ((Fin.cons a w : Fin (n + 2) → ℝ) (Fin.succ (Fin.last n)),
                  (Fin.cons a w : Fin (n + 2) → ℝ) (cycleSucc (Fin.succ (Fin.last n))))) :=
        congrArg (W 0 (a, w 0) * ·) (Fin.prod_univ_castSucc
          (fun i : Fin (n + 1) => W (i.succ)
            ((Fin.cons a w : Fin (n + 2) → ℝ) (i.succ),
              (Fin.cons a w : Fin (n + 2) → ℝ) (cycleSucc i.succ))))
    _ = W 0 (a, w 0) * ((∏ j : Fin n, W ((Fin.castSucc j).succ)
              (w (Fin.castSucc j), w (Fin.succ j)))
            * W (Fin.last (n + 1)) (w (Fin.last n), a)) := by
        rw [hlast, Fin.cons_last, cycleSucc_last', Fin.cons_zero]
        refine congrArg (W 0 (a, w 0) * ·) ?_
        exact congrArg (· * W (Fin.last (n + 1)) (w (Fin.last n), a))
          (Finset.prod_congr rfl (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => hint j))

/-- **Contract-product reassembly**: the `(n+1)`-chain product of `contract W` at `w`
equals the interior product of `chainProd_cons` times the composed-kernel factor at
`(w (last n), w 0)`. -/
theorem chainProd_contract (n : ℕ) (W : Fin (n + 2) → ℝ × ℝ → ℝ) (w : Fin (n + 1) → ℝ) :
    chainProd (n + 1) (contract W) w
      = (∏ j : Fin n, W ((Fin.castSucc j).succ) (w (Fin.castSucc j), w (Fin.succ j)))
          * compKernel (W (Fin.last (n + 1))) (W 0) (w (Fin.last n), w 0) := by
  calc chainProd (n + 1) (contract W) w
      = ∏ i : Fin (n + 1), contract W i (w i, w (cycleSucc i)) := rfl
    _ = (∏ i : Fin n, contract W (Fin.castSucc i)
              (w (Fin.castSucc i), w (cycleSucc (Fin.castSucc i))))
          * contract W (Fin.last n) (w (Fin.last n), w (cycleSucc (Fin.last n))) :=
        Fin.prod_univ_castSucc (fun i : Fin (n + 1) => contract W i (w i, w (cycleSucc i)))
    _ = (∏ i : Fin n, contract W (Fin.castSucc i)
              (w (Fin.castSucc i), w (cycleSucc (Fin.castSucc i))))
          * compKernel (W (Fin.last (n + 1))) (W 0) (w (Fin.last n), w 0) := by
        rw [cycleSucc_last', contract_apply_last W]
    _ = (∏ i : Fin n, W ((Fin.castSucc i).succ)
              (w (Fin.castSucc i), w (Fin.succ i)))
          * compKernel (W (Fin.last (n + 1))) (W 0) (w (Fin.last n), w 0) :=
        congrArg (· * compKernel (W (Fin.last (n + 1))) (W 0) (w (Fin.last n), w 0))
          (Finset.prod_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => by
            rw [contract_apply_succ W (Fin.castSucc_lt_last i).ne, cycleSucc_castSucc]))

/-! ### The Fubini peel step -/

/-- The `piFinSuccAbove 0` relabeling sends the head–tail pair to the cons tuple. -/
theorem piFinSuccAbove_symm_apply_cons {n : ℕ} (p : ℝ × (Fin (n + 1) → ℝ)) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 2) => ℝ) (0 : Fin (n + 2))).symm p
      = Fin.cons p.1 p.2 := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  · simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]

/-- The chain product is invariant under relabeling the family by `rotBack` and the point
by the `rotEquiv` coordinate rotation (the transport backing `chainIntegral_rotate`). -/
theorem chainProd_comp_rotBack {k : ℕ} (W : Fin k → ℝ × ℝ → ℝ) (z : Fin k → ℝ) :
    chainProd k (fun j => W (rotBack j))
        (⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin k => ℝ) (rotEquiv k)) z)
      = chainProd k W z := by
  have hfac : ∀ i : Fin k, W (rotBack i)
      ((MeasurableEquiv.piCongrLeft (fun _ : Fin k => ℝ) (rotEquiv k)) z i,
        (MeasurableEquiv.piCongrLeft (fun _ : Fin k => ℝ) (rotEquiv k)) z (cycleSucc i))
      = W (rotBack i) (z (rotBack i), z i) := fun i => by
    rw [piCongrLeft_rot_val z (cycleSucc i), piCongrLeft_rot_val z i, rotBack_cycleSucc]
  refine Eq.trans (Finset.prod_congr rfl
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) => hfac i)) ?_
  exact Finset.prod_equiv (rotEquiv k).symm (fun _ => by simp) (fun i _ => by
    exact congrArg (fun t : Fin k => W (rotBack i) (z (rotBack i), z t))
      (cycleSucc_rotBack i).symm)

/-- Chain-integrability transfers through the `rotBack` family relabeling. -/
theorem integrable_chainProd_comp_rotBack {k : ℕ} (W : Fin k → ℝ × ℝ → ℝ)
    (hWm : ∀ i, Measurable (W i))
    (hP : Integrable (chainProd k W) (Measure.pi fun _ : Fin k => vol)) :
    Integrable (chainProd k (fun j => W (rotBack j))) (Measure.pi fun _ : Fin k => vol) := by
  have hEq : chainProd k W
      = (chainProd k (fun j => W (rotBack j)))
          ∘ ⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin k => ℝ) (rotEquiv k)) := by
    funext z
    exact (chainProd_comp_rotBack W z).symm
  rw [hEq] at hP
  exact (MeasurePreserving.integrable_comp (measurePreserving_rotBack k)
    ((measurable_chainProd (fun i => hWm (rotBack i))).aestronglyMeasurable)).mp hP

/-- **The Fubini peel step**: the `(n+2)`-chain integral equals the `n+1`-chain integral
of the contracted family `contract W`, under the chain-integrability hypothesis `hP`
(the generalization of the landed `k = 3` anchors' `hA`/`hB` hypotheses). -/
theorem chainIntegral_peel {n : ℕ} (W : Fin (n + 2) → ℝ × ℝ → ℝ)
    (hP : Integrable (chainProd (n + 2) W) (Measure.pi fun _ : Fin (n + 2) => vol)) :
    chainIntegral (n + 2) W = chainIntegral (n + 1) (contract W) := by
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 2) => vol) (0 : Fin (n + 2))
  have hsymm : ∀ p : ℝ × (Fin (n + 1) → ℝ), chainProd (n + 2) W
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 2) => ℝ) (0 : Fin (n + 2))).symm p)
      = chainProd (n + 2) W (Fin.cons p.1 p.2) :=
    fun p => congrArg (chainProd (n + 2) W) (piFinSuccAbove_symm_apply_cons p)
  -- integrability on the product side
  have hF : Integrable
      (fun p : ℝ × (Fin (n + 1) → ℝ) => chainProd (n + 2) W (Fin.cons p.1 p.2))
      (vol.prod (Measure.pi fun _ : Fin (n + 1) => vol)) := by
    have h1 := (MeasurePreserving.symm
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 2) => ℝ) (0 : Fin (n + 2))) hmp
        ).integrable_comp_of_integrable hP
    have h2 : (chainProd (n + 2) W)
        ∘ ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 2) => ℝ) (0 : Fin (n + 2))).symm
        = fun p : ℝ × (Fin (n + 1) → ℝ) => chainProd (n + 2) W (Fin.cons p.1 p.2) := by
      funext p
      show chainProd (n + 2) W
        ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 2) => ℝ)
            (0 : Fin (n + 2))).symm p) = _
      rw [piFinSuccAbove_symm_apply_cons]
    rw [h2] at h1
    exact h1
  have hinner : ∀ w : Fin (n + 1) → ℝ,
      ∫ x : ℝ, chainProd (n + 2) W (Fin.cons x w) ∂vol
        = chainProd (n + 1) (contract W) w := by
    intro w
    have hstep : ∀ x : ℝ, chainProd (n + 2) W (Fin.cons x w)
        = W 0 (x, w 0) * ((∏ j : Fin n, W ((Fin.castSucc j).succ)
              (w (Fin.castSucc j), w (Fin.succ j)))
            * W (Fin.last (n + 1)) (w (Fin.last n), x)) :=
      fun x => chainProd_cons n W x w
    have key : ∫ x : ℝ, W 0 (x, w 0) * W (Fin.last (n + 1)) (w (Fin.last n), x) ∂vol
        = compKernel (W (Fin.last (n + 1))) (W 0) (w (Fin.last n), w 0) := by
      rw [compKernel, integral_congr_ae
        (Filter.Eventually.of_forall (fun x : ℝ =>
          mul_comm (W 0 (x, w 0)) (W (Fin.last (n + 1)) (w (Fin.last n), x))))]
    calc ∫ x : ℝ, chainProd (n + 2) W (Fin.cons x w) ∂vol
        = ∫ x : ℝ, W 0 (x, w 0) * ((∏ j : Fin n, W ((Fin.castSucc j).succ)
              (w (Fin.castSucc j), w (Fin.succ j)))
            * W (Fin.last (n + 1)) (w (Fin.last n), x)) ∂vol :=
            integral_congr_ae (Filter.Eventually.of_forall hstep)
      _ = ∫ x : ℝ, (∏ j : Fin n, W ((Fin.castSucc j).succ)
                (w (Fin.castSucc j), w (Fin.succ j)))
            * (W 0 (x, w 0) * W (Fin.last (n + 1)) (w (Fin.last n), x)) ∂vol :=
            integral_congr_ae (Filter.Eventually.of_forall (fun x : ℝ => by ring))
      _ = (∏ j : Fin n, W ((Fin.castSucc j).succ)
                (w (Fin.castSucc j), w (Fin.succ j)))
            * ∫ x : ℝ, W 0 (x, w 0) * W (Fin.last (n + 1)) (w (Fin.last n), x) ∂vol :=
            integral_const_mul
              (∏ j : Fin n, W ((Fin.castSucc j).succ)
                (w (Fin.castSucc j), w (Fin.succ j)))
              (fun x : ℝ => W 0 (x, w 0) * W (Fin.last (n + 1)) (w (Fin.last n), x))
      _ = (∏ j : Fin n, W ((Fin.castSucc j).succ)
                (w (Fin.castSucc j), w (Fin.succ j)))
            * compKernel (W (Fin.last (n + 1))) (W 0) (w (Fin.last n), w 0) := by
            rw [key]
      _ = chainProd (n + 1) (contract W) w := (chainProd_contract n W w).symm
  calc chainIntegral (n + 2) W
      = ∫ z : Fin (n + 2) → ℝ, chainProd (n + 2) W z
          ∂(Measure.pi fun _ : Fin (n + 2) => vol) := rfl
    _ = ∫ p : ℝ × (Fin (n + 1) → ℝ), chainProd (n + 2) W (Fin.cons p.1 p.2)
          ∂(vol.prod (Measure.pi fun _ : Fin (n + 1) => vol)) :=
        (hmp.symm.integral_comp' (chainProd (n + 2) W)).symm.trans
          (integral_congr_ae (Filter.Eventually.of_forall hsymm))
    _ = ∫ w : Fin (n + 1) → ℝ, ∫ a : ℝ, chainProd (n + 2) W (Fin.cons a w) ∂vol
          ∂(Measure.pi fun _ : Fin (n + 1) => vol) :=
        ((integral_prod_swap
              (fun p : ℝ × (Fin (n + 1) → ℝ) => chainProd (n + 2) W (Fin.cons p.1 p.2))).symm.trans
          (integral_prod
            (fun q : (Fin (n + 1) → ℝ) × ℝ =>
              (fun p : ℝ × (Fin (n + 1) → ℝ) => chainProd (n + 2) W (Fin.cons p.1 p.2)) q.swap)
            ((measurePreserving_swap (μ := Measure.pi fun _ : Fin (n + 1) => vol)
                (ν := vol)).integrable_comp_of_integrable hF)))
    _ = ∫ w : Fin (n + 1) → ℝ, chainProd (n + 1) (contract W) w
          ∂(Measure.pi fun _ : Fin (n + 1) => vol) := by
        simp only [hinner]
    _ = chainIntegral (n + 1) (contract W) := rfl

/-! ### The general-`k` peel induction -/

/-- Kernel-level trace cyclicity: `cycle2 K L = cycle2 L K` (the swap transport). -/
theorem cycle2_swap (K L : ℝ × ℝ → ℝ) : cycle2 K L = cycle2 L K := by
  show (∫ p : ℝ × ℝ, K p * L p.swap ∂(vol.prod vol))
      = ∫ p : ℝ × ℝ, L p * K p.swap ∂(vol.prod vol)
  rw [← integral_prod_swap (fun p : ℝ × ℝ => L p * K p.swap)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  show K p * L p.swap = L p.swap * K p
  ring

/-- The constant `K₀`-chain with the last kernel replaced by `D`. -/
def withLast (k : ℕ) (D K₀ : ℝ × ℝ → ℝ) : Fin (k + 1) → ℝ × ℝ → ℝ :=
  fun j => if j = Fin.last k then D else K₀

theorem rotBack_zero_succ {n : ℕ} : rotBack (0 : Fin (n + 2)) = Fin.last (n + 1) := by
  apply Fin.ext
  have hv := rotBack_val (0 : Fin (n + 2))
  rw [if_pos (show ((0 : Fin (n + 2)) : ℕ) = 0 by rfl)] at hv
  have h2 : ((Fin.last (n + 1) : Fin (n + 2)) : ℕ) = n + 1 := Fin.val_last _
  omega

theorem rotBack_last {n : ℕ} : rotBack (Fin.last (n + 1)) = Fin.castSucc (Fin.last n) := by
  apply Fin.ext
  have hv := rotBack_val (Fin.last (n + 1))
  rw [Fin.val_last, if_neg (by omega : ¬(n + 1 = 0))] at hv
  rw [Fin.val_castSucc, Fin.val_last]
  omega

theorem rotBack_succ {n : ℕ} (j : Fin (n + 1)) :
    rotBack (Fin.succ j) = (Fin.castSucc j : Fin (n + 2)) := by
  apply Fin.ext
  have hv := rotBack_val (Fin.succ j)
  have hvv : ((Fin.succ j : Fin (n + 2)) : ℕ) = (j : ℕ) + 1 := by simp
  rw [hvv, if_neg (by have hj := j.isLt; omega)] at hv
  rw [hv, Fin.val_castSucc]
  omega

/-- **The contraction step of the induction**: contracting the `rotBack`-relabeled
`withLast` family composes `K₀` into `D` on the left, i.e. `D ↦ compKernel K₀ D`
(left-growing composition = `compPowL'` form). -/
theorem contract_comp_rotBack_withLast (m : ℕ) (D K₀ : ℝ × ℝ → ℝ) :
    contract (fun j : Fin (m + 3) => withLast (m + 2) D K₀ (rotBack j))
      = withLast (m + 1) (compKernel K₀ D) K₀ := by
  funext j
  by_cases hj : j = Fin.last (m + 1)
  · subst hj
    rw [contract_apply_last]
    show compKernel
        (withLast (m + 2) D K₀ (rotBack (Fin.last (m + 2))))
        (withLast (m + 2) D K₀ (rotBack 0))
        = withLast (m + 1) (compKernel K₀ D) K₀ (Fin.last (m + 1))
    have hne : (Fin.castSucc (Fin.last (m + 1)) : Fin (m + 3)) ≠ Fin.last (m + 2) := by
      intro h
      have hc : ((Fin.castSucc (Fin.last (m + 1)) : Fin (m + 3)) : ℕ) = m + 1 := by
        rw [Fin.val_castSucc, Fin.val_last]
      have h2 : ((Fin.last (m + 2) : Fin (m + 3)) : ℕ) = m + 2 := Fin.val_last _
      rw [h] at hc
      omega
    rw [rotBack_last, rotBack_zero_succ, withLast, if_neg hne, withLast, if_pos rfl,
      withLast, if_pos rfl]
  · rw [contract_apply_succ _ hj]
    show withLast (m + 2) D K₀ (rotBack (Fin.succ j))
        = withLast (m + 1) (compKernel K₀ D) K₀ j
    rw [rotBack_succ, withLast, if_neg ((Fin.castSucc_lt_last j).ne), withLast, if_neg hj]

/-- **The general-`k` peel induction**: the chain integral of the `K₀`-chain whose last
kernel is `D` equals the trace form `cycle2 K₀ (compPowL' m K₀ D)`, conditional on the
level-wise chain-integrability hypothesis `hP` (the generalization of the landed `k = 3`
anchors' `hA`/`hB`). -/
theorem chainIntegral_withLast_ind (m : ℕ) (K₀ : ℝ × ℝ → ℝ) (hK₀m : Measurable K₀)
    (hP : ∀ (r : ℕ) (D : ℝ × ℝ → ℝ), Measurable D →
      Integrable (chainProd (r + 2) (withLast (r + 1) D K₀))
        (Measure.pi fun _ : Fin (r + 2) => vol)) :
    ∀ D : ℝ × ℝ → ℝ, Measurable D →
      chainIntegral (m + 2) (withLast (m + 1) D K₀) = cycle2 K₀ (compPowL' m K₀ D) := by
  induction m with
  | zero =>
    intro D hDm
    have h0 : withLast 1 D K₀ 0 = K₀ := by
      show (if (0 : Fin 2) = Fin.last 1 then D else K₀) = K₀
      rw [if_neg (by simp)]
    have h1 : withLast 1 D K₀ 1 = D := by
      show (if (1 : Fin 2) = Fin.last 1 then D else K₀) = D
      rw [if_pos (show ((1 : Fin 2)) = Fin.last 1 from rfl)]
    calc chainIntegral 2 (withLast 1 D K₀)
        = cycle2 (withLast 1 D K₀ 0) (withLast 1 D K₀ 1) := chainIntegral_two _
      _ = cycle2 K₀ (compPowL' 0 K₀ D) := by
          rw [h0, h1]
          rfl
  | succ m ih =>
    intro D hDm
    have hrot : chainIntegral (m + 3) (withLast (m + 2) D K₀)
        = chainIntegral (m + 3)
            (fun j : Fin (m + 3) => withLast (m + 2) D K₀ (rotBack j)) := by
      have hr := chainIntegral_rotate (m + 3)
        (fun j : Fin (m + 3) => withLast (m + 2) D K₀ (rotBack j))
      refine (hr.trans ?_).symm
      refine congrArg (chainIntegral (m + 3)) (funext fun j => ?_)
      show withLast (m + 2) D K₀ (rotBack (cycleSucc j)) = withLast (m + 2) D K₀ j
      rw [rotBack_cycleSucc]
    have hPV := integrable_chainProd_comp_rotBack
      (withLast (m + 2) D K₀)
      (fun i => by
        by_cases hi : i = Fin.last (m + 2)
        · rw [hi, withLast, if_pos rfl]
          exact hDm
        · rw [withLast, if_neg hi]
          exact hK₀m)
      (hP (m + 1) D hDm)
    rw [hrot, chainIntegral_peel _ hPV, contract_comp_rotBack_withLast,
      ih (compKernel K₀ D) ((stronglyMeasurable_compKernel hK₀m hDm).measurable),
      compPowL'_assoc]
    rfl

/-- **The general-`k` composition induction**: the `(n+2)`-cycle integral of `K` equals
the composed-kernel trace form `cycle2 (compPowL n K) K` (kernel-side `C_{n+2}(K)`),
under the level-wise chain-integrability hypothesis `hP`. -/
theorem cycleIntegral_comp (n : ℕ) (K : ℝ × ℝ → ℝ) (hKm : Measurable K)
    (hP : ∀ (r : ℕ) (D : ℝ × ℝ → ℝ), Measurable D →
      Integrable (chainProd (r + 2) (withLast (r + 1) D K))
        (Measure.pi fun _ : Fin (r + 2) => vol)) :
    cycleIntegral (n + 2) K = cycle2 (compPowL n K) K := by
  have hFam : (fun _ : Fin (n + 2) => K) = withLast (n + 1) K K := by
    funext j
    rw [withLast]
    by_cases hj : j = Fin.last (n + 1)
    · rw [if_pos hj]
    · rw [if_neg hj]
  rw [← chainIntegral_eq_cycleIntegral, hFam,
    chainIntegral_withLast_ind n K hKm hP K hKm, compPowL_eq, cycle2_swap]

/-- The `k = 3` specialization of the composition induction: `C_3(K) = cycle2 (compKernel K K) K`
(the composed-kernel trace form of the landed `k = 3` anchor, now reached by the general
peel induction). -/
theorem cycleIntegral_three_comp (K : ℝ × ℝ → ℝ) (hKm : Measurable K)
    (hP : ∀ (r : ℕ) (D : ℝ × ℝ → ℝ), Measurable D →
      Integrable (chainProd (r + 2) (withLast (r + 1) D K))
        (Measure.pi fun _ : Fin (r + 2) => vol)) :
    cycleIntegral 3 K = cycle2 (compKernel K K) K := by
  have h := cycleIntegral_comp 1 K hKm hP
  rw [compPowL] at h
  exact h

/-!
## Pass-3 status: the peel induction is landed

The two Fin-product algebra lemmas of the pass-2 gap are landed:

* `chainProd_cons` — cons factorization of the chain product (split at `0` by
  `Fin.prod_univ_succ`, then `Fin.prod_univ_castSucc` with the wrap factor
  `W (Fin.last (n+1)) (w (Fin.last n), a)`; interior factors via
  `cycleSucc_castSucc_succ`).
* `chainProd_contract` — the contract-product reassembly: the chain product of
  `contract W` is the same interior product times
  `compKernel (W (Fin.last (n+1))) (W 0) (w (Fin.last n), w 0)`.

On top of them the Fubini peel and the general-`k` induction are landed:

* `chainIntegral_peel` — `chainIntegral (n+2) W = chainIntegral (n+1) (contract W)`
  under the chain-integrability hypothesis `hP` (transport by
  `measurePreserving_piFinSuccAbove` at `0`, Fubini by `integral_prod` after the
  swap transport, inner integral = `compKernel` definition, reassembly by
  `chainProd_cons` + `chainProd_contract`).
* `chainIntegral_withLast_ind` / `cycleIntegral_comp` — the peel induction: peeling the
  `rotBack`-relabeled `withLast` family composes on the LEFT (`D ↦ compKernel K₀ D`,
  `contract_comp_rotBack_withLast`), so the final `k = 2` anchor yields
  `cycleIntegral (n+2) K = cycle2 (compPowL n K) K` (after `cycle2_swap`), conditional
  on the level-wise integrability hypothesis `hP` (one instance per peel level; for the
  truncated Riesz kernel each instance reduces to a Tonelli-finiteness statement).

## Remaining gap (documented, not landed; budget)

The *unconditional* general-`k` chain-integrability discharge (each `hP` instance): for
signed kernels this is the iterated section-Cauchy–Schwarz argument bounded by the
`∏ hsNorm` powers (`hsNorm_compPowL_le` keeps the tower square-summable); for nonnegative
kernels each instance is a Tonelli-finiteness statement. With that discharge in hand,
`cycleIntegral_comp` gives the general-`k` HasSum boundary `Σ_j κ_j^(n+2) = C_{n+2}(K)`
via the landed `CycleTraceIdentification` trace-pair machinery.
-/

end HS

end
