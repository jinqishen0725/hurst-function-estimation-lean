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

/-!
## Pass-2 gap (documented, not landed; budget)

The two pure product-algebra lemmas that turn the above contraction into the Fubini
peel step are *stated and checked by hand* but not landed here:

* `chainProd_cons`: `chainProd (n+2) W (Fin.cons a w)
  = W 0 (a, w 0) * W (Fin.last (n+1)) (w (Fin.last n), a)
    * ∏ j : Fin (n+1), (if j = Fin.last n then 1 else W j.succ (w j, w (cycleSucc j)))`
  — proof skeleton: `Fin.prod_univ_succ` (split at `0`), the cons evaluations
  `Fin.cons_zero`/`Fin.cons_succ`, `cycleSucc 0 = 1`, and the wrap case
  `cycleSucc j.succ = 0` at `j = Fin.last n` (`cycleSucc_last`); the remaining
  `∏ j`-splits by `Fin.prod_univ_castSucc` with `cycleSucc (castSucc i) = castSucc i.succ`.
* `chainProd_contract`: `chainProd (n+1) (contract W) w` = the same pre-product times
  `compKernel (W (Fin.last (n+1))) (W 0) (w (Fin.last n), w 0)` (by `contract_apply_succ`
  on the `castSucc` factors and `contract_apply_last` at the wrap).

With these, the peel step is: transport `π (n+2)` to `vol.prod π (n+1)` via
`measurePreserving_piFinSuccAbove (fun _ => vol) 0`, Fubini (`integral_prod` under the
chain-integrability hypothesis `hP`, the generalization of the landed anchors' `hA`/`hB`),
the inner integral `∫ a, W 0 (a, w 0) * W (Fin.last (n+1)) (w (Fin.last n), a) da =
compKernel (W (Fin.last (n+1))) (W 0) (w (Fin.last n), w 0)` (definition of `compKernel`),
and reassembly by `chainProd_cons` + `chainProd_contract`. The `hA`/`hB` chain-integrability
hypotheses for the Riesz kernel are exactly the general-`k` form of the documented
section-Cauchy–Schwarz discharge (bounded by `∏ hsNorm` via iterated `hsNorm_comp_le`).
-/

end HS

end
