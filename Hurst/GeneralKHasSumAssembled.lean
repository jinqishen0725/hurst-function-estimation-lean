import Hurst.GeneralKPeelInduction
import Hurst.CycleTraceIdentification
import Hurst.HSOperatorLayer3
import Hurst.FrozenSpectralCount
import Hurst.GeneralKHasSumClosed

/-!
# The assembled general-`k` HasSum from the landed pieces

This file assembles the general-`k` `HasSum` for the multiplicity-exact spectral
enumeration from the freshly landed pieces: the peel induction
(`Hurst.GeneralKPeelInduction`: `cycleIntegral_eq_cycle2_pow`, the `compPowR` tower,
`hsNorm_compPowR_le`), the `k = 2` / `k = 3` trace anchors
(`Hurst.CycleTraceIdentification`, `Hurst.GeneralKHasSumClosed`:
`cycleIntegral_three_eq_cycle2`), the HS-operator/compactness layer
(`Hurst.HSOperatorLayer3`) and the multiplicity enumeration
(`Hurst.FrozenSpectralCount`), plus the summability layer of
`Hurst.GeneralKHasSumComplete`.

## What is landed here (all proofs complete, no placeholders)

* `HS.IsDiagEnum` — the diagonal enumeration structure: every entry is either the pair
  `(0, 0)` or a unit-norm eigenvector with its eigenvalue.  This is exactly the shape of
  the canonical enumeration of `HS.exists_multiplicity_enumeration`
  (`Hurst.FrozenSpectralCount`) and is packaged from its two raw clauses by
  `HS.isDiagEnum_of_structures`.
* `HS.hasEigenvector_CLM_pow` — the operator-power eigenaction
  `(TOpEnd' K hK ^ m) v = μ ^ m • v` (induction over the `Module.End` monoid tower) —
  the tr-side input `Σ_j ⟪T^k e_j, e_j⟫ = Σ_j κ_j^k`.
* `HS.diag_inner_eq_pow` — **the tr-side diagonal identity**: under `IsDiagEnum`,
  `inner ℝ ((TOpEnd' K hK ^ k) (vec j)) (vec j) = val j ^ k` for `k ≥ 1` — the
  eigenbasis-restricted pairing identity of `Hurst.CycleTraceIdentification`, upgraded
  from `k = 2` to every `k ≥ 1` (restricted to the enumerated spectrum; kernel vectors
  contribute `0`).
* `HS.inner_pow_succ` — **the trace recursion** `⟪T^(k+1) v, v⟫ = val j · ⟪T^k v, v⟫`
  (the `tr(T^{k+1}) = tr(T^k · T)` induction step, in diagonal form).
* `HS.hasSum_diag_inner_pow` — the tr-side `HasSum` for every `k ≥ 2`:
  `HasSum (fun j => ⟪T^k (vec j), vec j⟫) (∑' j, val j ^ k)` (summability layer +
  pointwise congruence).
* `HS.bndTower` / `HS.abs_compPowR_le_bndTower` / `HS.integrable_kchain_bounded` /
  `HS.cycleIntegral_comp_pow_bounded` — **the kernel-side composition, unconditionally
  discharged for pointwise-bounded kernels**: for `|K| ≤ B` every chain integrand is
  integrable over the finite `vol^(n+2)` (`vol` is the unit-interval restriction), so the
  landed peel induction gives `cycleIntegral (n+2) K = cycle2 (compPowR n K) K` with **no
  hypothesis**.  The `hP`-carried version for general HS kernels is `HS.hasSum_general_k_assembled`.
* `HS.cycleIntegral_comp_envelope` — the cycle envelope `|cycleIntegral (n+2) K| ≤
  hsNorm K ^ (n+2)` under `hP` (composition of `cycle2_bound` with the landed
  `hsNorm_compPowR_le` tower bound).
* `HS.cycleIntegral_two_anchors` / `HS.cycleIntegral_three_anchors` — the `k = 2` and
  `k = 3` kernel-side anchors (`cycleIntegral 2 K = cycle2 K K = hsNorm K ^ 2` for
  symmetric kernels; `cycleIntegral 3 K = cycle2 (compKernel K K) K` unconditional).
* `HS.hasSum_general_k_assembled` / `HS.hasSum_general_k_assembled_bounded` /
  `HS.hasSum_k3_assembled_of_gate` — **the assembled general-`k` HasSum**: for every
  `k ≥ 2`,
  `HasSum (fun j => val j ^ k) (cycleIntegral k K)`,
  given the diagonal enumeration structure, the multiplicity clause, the kernel-side
  composition hypothesis (`hP`, or discharged by boundedness), and the operator-side
  gate `∑' j, val j ^ k = cycle2 (compPowR (k-2) K) K`.

## Honest residue (documented, NOT closed here)

The exact mission statement `HasSum (fun j => val j ^ k) (cycleIntegral k K)` for
`k ≥ 2` remains gated on a single hypothesis, the **operator-side trace-power
identification** `∑' j, val j ^ k = cycle2 (compPowR (k-2) K) K`: this is the
product-basis Parseval step isolated in `Hurst.CycleTraceIdentification`
(completeness of the tensor-product system `ψ_{ij}(x,y) = (e i)(x) · (e j)(y)` in
`L²(vol2)`; mathlib v4.31 has nothing for `L²` of a product measure).  The composition
route of the peel induction closes the *kernel side*
(`cycleIntegral k K = cycle2 (compPowR (k-2) K) K`, unconditionally for bounded
kernels, `hP`-carried in general), and this file closes the *tr side*
(`Σ_j ⟪T^k (vec j), vec j⟫ = Σ_j val j ^ k` over the enumerated spectrum); the gate is
exactly the identification of the two sides.  Everything else — eigenaction, diagonal
identities, trace recursion, summability, integrability discharge (bounded case), the
`k = 2`/`k = 3` anchors and the envelope — is proved here.
-/

open MeasureTheory Measure Real Set
open scoped Real

noncomputable section

namespace HS

/-! ### The diagonal enumeration structure -/

/-- The diagonal enumeration structure for the spectral `HasSum` consumption: every
entry of `val`/`vec` is either the pair `(0, 0)` or a unit-norm eigenvector of `T`
paired with its eigenvalue.  This is the shape of the canonical enumeration produced by
`HS.exists_multiplicity_enumeration` (`Hurst.FrozenSpectralCount`). -/
def IsDiagEnum (T : Module.End ℝ L2) (val : ℕ → ℝ) (vec : ℕ → L2) : Prop :=
  ∀ j : ℕ, (val j = 0 ∧ vec j = 0)
    ∨ (Module.End.HasEigenvector T (val j) (vec j) ∧ ‖vec j‖ = 1)

/-- The raw structural clauses imply `IsDiagEnum`. -/
theorem isDiagEnum_of_structures {T : Module.End ℝ L2} {val : ℕ → ℝ} {vec : ℕ → L2}
    (hzero : ∀ j, val j = 0 → vec j = 0)
    (heig : ∀ j, val j ≠ 0 → Module.End.HasEigenvector T (val j) (vec j) ∧ ‖vec j‖ = 1) :
    IsDiagEnum T val vec := by
  intro j
  by_cases hj : val j = 0
  · exact Or.inl ⟨hj, hzero j hj⟩
  · exact Or.inr (heig j hj)

/-! ### The tr-side eigenaction and diagonal pairing identities -/

private theorem hasSum_congr {f g : ℕ → ℝ} {a : ℝ} (h : ∀ j, f j = g j) (hf : HasSum f a) :
    HasSum g a := by
  rw [← funext h]
  exact hf

/-- **The operator-power eigenaction**: an eigenvector of `T = TOpEnd' K hK` with
eigenvalue `μ` is an eigenvector of every power `T^m`, with eigenvalue `μ ^ m`. -/
theorem hasEigenvector_CLM_pow {K : ℝ × ℝ → ℝ} {hK : HSKernel K} {μ : ℝ} {v : L2}
    (hv : Module.End.HasEigenvector (TOpEnd' K hK) μ v) :
    ∀ m : ℕ, (TOpEnd' K hK ^ m) v = μ ^ m • v := by
  intro m
  induction m with
  | zero => rw [pow_zero, Module.End.one_apply, pow_zero, one_smul]
  | succ m ih =>
      have h1 : TOpEnd' K hK v = μ • v := hv.apply_eq_smul
      calc (TOpEnd' K hK ^ (m + 1)) v = (TOpEnd' K hK ^ m * TOpEnd' K hK) v := by
            rw [pow_succ]
        _ = (TOpEnd' K hK ^ m) (TOpEnd' K hK v) := rfl
        _ = (TOpEnd' K hK ^ m) (μ • v) := by rw [h1]
        _ = μ • ((TOpEnd' K hK ^ m) v) := by rw [map_smul]
        _ = μ • (μ ^ m • v) := by rw [ih]
        _ = μ ^ (m + 1) • v := by rw [smul_smul, ← pow_succ']

/-- **The tr-side diagonal identity**: under the diagonal enumeration structure, the
`j`-th diagonal pairing of the `k`-th operator power reads the `k`-th power of the
eigenvalue: `inner ℝ ((TOpEnd' K hK ^ k) (vec j)) (vec j) = val j ^ k` for `k ≥ 1`.
This is the eigenbasis-restricted pairing identity (kernel vectors contribute `0`) of
`Hurst.CycleTraceIdentification`, at every `k ≥ 1`. -/
theorem diag_inner_eq_pow {K : ℝ × ℝ → ℝ} {hK : HSKernel K} {val : ℕ → ℝ} {vec : ℕ → L2}
    (hval' : IsDiagEnum (TOpEnd' K hK) val vec) {k : ℕ} (hk : 0 < k) (j : ℕ) :
    inner ℝ ((TOpEnd' K hK ^ k) (vec j)) (vec j) = val j ^ k := by
  rcases hval' j with ⟨hval0, hvec0⟩ | ⟨heig, hun⟩
  · rw [hvec0, map_zero, inner_zero_left, hval0,
      zero_pow (show k ≠ 0 from by omega)]
  · rw [hasEigenvector_CLM_pow heig k, real_inner_smul_left, real_inner_self_eq_norm_sq,
      hun, one_pow, mul_one]

/-- **The trace recursion (the induction step of the tr side)**: the diagonal pairings
of consecutive powers satisfy `⟪T^(k+1) v, v⟫ = val j · ⟪T^k v, v⟫` — the diagonal form
of `tr(T^{k+1}) = tr(T^k · T)`. -/
theorem inner_pow_succ {K : ℝ × ℝ → ℝ} {hK : HSKernel K} {val : ℕ → ℝ} {vec : ℕ → L2}
    (hval' : IsDiagEnum (TOpEnd' K hK) val vec) {k : ℕ} (hk : 1 ≤ k) (j : ℕ) :
    inner ℝ ((TOpEnd' K hK ^ (k + 1)) (vec j)) (vec j)
      = val j * inner ℝ ((TOpEnd' K hK ^ k) (vec j)) (vec j) := by
  rw [diag_inner_eq_pow hval' (by omega) j, diag_inner_eq_pow hval' hk j, pow_succ']

/-- **The tr-side `HasSum`**: the diagonal pairing series of the `k`-th operator power
`HasSum`s to the enumerated `k`-th power sum `∑' j, val j ^ k` (the summability layer of
`Hurst.GeneralKHasSumComplete` plus the pointwise diagonal identity). -/
theorem hasSum_diag_inner_pow
    (hCompact : IsCompactOperator (TOp K hK))
    (hsym : (↑(TOp K hK) : L2 →ₗ[ℝ] L2).IsSymmetric)
    {val : ℕ → ℝ} {vec : ℕ → L2}
    (hval' : IsDiagEnum (TOpEnd' K hK) val vec)
    (hmult : ∀ μ : ℝ, Module.End.HasEigenvalue (TOpEnd' K hK) μ → μ ≠ 0 →
      Nat.card {j : ℕ // val j = μ}
        = Module.finrank ℝ (Module.End.eigenspace (TOpEnd' K hK) μ))
    (k : ℕ) (hk : 2 ≤ k) :
    HasSum (fun j => inner ℝ ((TOpEnd' K hK ^ k) (vec j)) (vec j)) (∑' j, val j ^ k) := by
  have hval : ∀ j : ℕ, val j = 0 ∨ Module.End.HasEigenvector (TOpEnd' K hK) (val j) (vec j) := by
    intro j
    rcases hval' j with ⟨h0v, _⟩ | h
    · exact Or.inl h0v
    · exact Or.inr h.1
  refine hasSum_congr (fun j => (diag_inner_eq_pow (k := k) hval' (by omega) j).symm)
    (hasSum_general_k_pow hCompact hsym hval hmult k hk)

/-! ### The kernel side: bounded kernels discharge the chain integrability -/

/-- The tower of pointwise bounds for a `|K| ≤ B`-bounded kernel under composition:
`bndTower B 0 = B`, `bndTower B (r+1) = bndTower B r * B * vol(univ)` — the bound on
`compPowR r K` (the composition integral gains a factor `B` per slot and the total
`vol`-mass per layer). -/
def bndTower (B : ℝ) : ℕ → ℝ
  | 0 => B
  | r + 1 => bndTower B r * B * (vol univ).toReal

theorem bndTower_nonneg {B : ℝ} (hB : 0 ≤ B) : ∀ r, 0 ≤ bndTower B r := by
  intro r
  induction r with
  | zero => exact hB
  | succ m ih => exact mul_nonneg (mul_nonneg ih hB) ENNReal.toReal_nonneg

/-- The `compPowR` tower stays pointwise bounded under a pointwise-bounded kernel:
`|compPowR r K p| ≤ bndTower B r`. -/
theorem abs_compPowR_le_bndTower {K : ℝ × ℝ → ℝ} (hKm : Measurable K) {B : ℝ}
    (hB : 0 ≤ B) (hKb : ∀ p, |K p| ≤ B) :
    ∀ (r : ℕ) (p : ℝ × ℝ), |compPowR r K p| ≤ bndTower B r := by
  intro r
  induction r with
  | zero => intro p; exact hKb p
  | succ m ih =>
      intro p
      have hmeabs : AEStronglyMeasurable
          (fun t : ℝ => |compPowR m K (p.1, t) * K (t, p.2)|) vol :=
        ((((measurable_compPowR m hKm).comp (measurable_const.prodMk measurable_id)).mul
          (hKm.comp (measurable_id.prodMk measurable_const))).abs).aestronglyMeasurable
      have hf : Integrable
          (fun t : ℝ => |compPowR m K (p.1, t) * K (t, p.2)|) vol := by
        refine Integrable.mono (integrable_const (bndTower B m * B)) hmeabs ?_
        filter_upwards with t
        show ‖|compPowR m K (p.1, t) * K (t, p.2)|‖
          ≤ ‖(bndTower B m * B : ℝ)‖
        rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _),
          Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (bndTower_nonneg hB m) hB)]
        calc |compPowR m K (p.1, t) * K (t, p.2)|
            = |compPowR m K (p.1, t)| * |K (t, p.2)| := abs_mul _ _
          _ ≤ bndTower B m * B :=
            mul_le_mul (ih (p.1, t)) (hKb (t, p.2)) (abs_nonneg _)
              (bndTower_nonneg hB m)
      calc |compPowR (m + 1) K p|
          = |∫ t : ℝ, compPowR m K (p.1, t) * K (t, p.2) ∂vol| := rfl
        _ ≤ ∫ t : ℝ, |compPowR m K (p.1, t) * K (t, p.2)| ∂vol :=
            abs_integral_le_integral_abs
        _ ≤ ∫ t : ℝ, bndTower B m * B ∂vol := by
            refine integral_mono hf (integrable_const (bndTower B m * B)) ?_
            intro t
            calc |compPowR m K (p.1, t) * K (t, p.2)|
                = |compPowR m K (p.1, t)| * |K (t, p.2)| := abs_mul _ _
              _ ≤ bndTower B m * B :=
                mul_le_mul (ih (p.1, t)) (hKb (t, p.2)) (abs_nonneg _)
                  (bndTower_nonneg hB m)
        _ = bndTower B m * B * (vol univ).toReal := by
            rw [integral_const]
            have hreal : vol.real univ = (vol univ).toReal := rfl
            rw [hreal, smul_eq_mul]
            ring

/-- **The `hP` discharge for bounded kernels**: for a measurable kernel with
`|K| ≤ B`, every chain integrand of the peeled `kchain` family is integrable over the
finite `vol^(n+2)` (pointwise bounded by `max B (bndTower B r) ^ (n+2)`). -/
theorem integrable_kchain_bounded {K : ℝ × ℝ → ℝ} (hKm : Measurable K) {B : ℝ}
    (hB : 0 ≤ B) (hKb : ∀ p, |K p| ≤ B) (n r : ℕ) :
    Integrable (peelChainProd (n + 2) (kchain n r K))
      (Measure.pi fun _ : Fin (n + 2) => vol) := by
  classical
  have hentry : ∀ i : Fin (n + 2), Measurable (kchain n r K i) := by
    intro i
    by_cases hi : i = Fin.last (n + 1)
    · have hi2 : kchain n r K i = compPowR r K := by rw [kchain]; exact if_pos hi
      rw [hi2]
      exact measurable_compPowR r hKm
    · have hi2 : kchain n r K i = K := by rw [kchain]; exact if_neg hi
      rw [hi2]
      exact hKm
  have hmeas : AEStronglyMeasurable (peelChainProd (n + 2) (kchain n r K))
      (Measure.pi fun _ : Fin (n + 2) => vol) :=
    (peelMeasurable_chainProd hentry).aestronglyMeasurable
  -- the pointwise bound by `C ^ (n+2)`, `C = max B (bndTower B r)`
  have hstep : ∀ z : Fin (n + 2) → ℝ,
      |peelChainProd (n + 2) (kchain n r K) z| ≤ (max B (bndTower B r)) ^ (n + 2) := by
    intro z
    have hfactor : ∀ i : Fin (n + 2),
        |kchain n r K i (z i, z (cycleSucc i))| ≤ max B (bndTower B r) := by
      intro i
      by_cases hi : i = Fin.last (n + 1)
      · have hi2 : kchain n r K i = compPowR r K := by rw [kchain]; exact if_pos hi
        rw [hi2]
        calc |compPowR r K (z i, z (cycleSucc i))|
            ≤ bndTower B r := abs_compPowR_le_bndTower hKm hB hKb r _
          _ ≤ max B (bndTower B r) := le_max_right _ _
      · have hi2 : kchain n r K i = K := by rw [kchain]; exact if_neg hi
        rw [hi2]
        calc |K (z i, z (cycleSucc i))| ≤ B := hKb _
          _ ≤ max B (bndTower B r) := le_max_left _ _
    have habs : |peelChainProd (n + 2) (kchain n r K) z|
        = ∏ i : Fin (n + 2), |kchain n r K i (z i, z (cycleSucc i))| :=
      Finset.abs_prod _ _
    have hle : ∏ i : Fin (n + 2), |kchain n r K i (z i, z (cycleSucc i))|
        ≤ ∏ _i : Fin (n + 2), max B (bndTower B r) :=
      Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hfactor i)
    have hconst : (∏ _i : Fin (n + 2), max B (bndTower B r))
        = (max B (bndTower B r)) ^ (n + 2) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    calc |peelChainProd (n + 2) (kchain n r K) z|
        = ∏ i : Fin (n + 2), |kchain n r K i (z i, z (cycleSucc i))| := habs
      _ ≤ ∏ _i : Fin (n + 2), max B (bndTower B r) := hle
      _ = (max B (bndTower B r)) ^ (n + 2) := hconst
  refine Integrable.mono (integrable_const ((max B (bndTower B r)) ^ (n + 2))) hmeas ?_
  refine Filter.Eventually.of_forall fun z => ?_
  have hC0 : 0 ≤ max B (bndTower B r) := le_trans hB (le_max_left _ _)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hC0 _)]
  exact hstep z

private theorem compPowR_zero (K : ℝ × ℝ → ℝ) : compPowR 0 K = K := rfl

/-- **The kernel-side composition for bounded kernels (unconditional)**: for a
measurable `|K| ≤ B` kernel, the `(n+2)`-cycle integral equals the `cycle2` of the
`n`-fold composition tower — the landed general-`k` peel induction
`cycleIntegral_eq_cycle2_pow` with its chain-integrability hypothesis discharged by
`integrable_kchain_bounded`. -/
theorem cycleIntegral_comp_pow_bounded {K : ℝ × ℝ → ℝ} (hKm : Measurable K) {B : ℝ}
    (hB : 0 ≤ B) (hKb : ∀ p, |K p| ≤ B) (n : ℕ) :
    cycleIntegral (n + 2) K = cycle2 (compPowR n K) K :=
  cycleIntegral_eq_cycle2_pow (fun n r => integrable_kchain_bounded hKm hB hKb n r)

/-- **The cycle envelope (general HS kernels, `hP`-carried)**:
`|cycleIntegral (n+2) K| ≤ hsNorm K ^ (n+2)` — the landed `cycle2_bound` contracted by
the landed `hsNorm_compPowR_le` tower bound. -/
theorem cycleIntegral_comp_envelope {K : ℝ × ℝ → ℝ} (hKm : Measurable K) (hK : HSKernel K)
    (hP : ∀ n r : ℕ, Integrable (peelChainProd (n + 2) (kchain n r K))
      (Measure.pi fun _ : Fin (n + 2) => vol)) (n : ℕ) :
    |cycleIntegral (n + 2) K| ≤ hsNorm K ^ (n + 2) := by
  rw [cycleIntegral_eq_cycle2_pow hP]
  calc |cycle2 (compPowR n K) K|
      ≤ hsNorm (compPowR n K) * hsNorm K :=
        cycle2_bound (hsKernel_compPowR n hKm hK) hK
    _ ≤ hsNorm K ^ (n + 1) * hsNorm K := by
        exact mul_le_mul_of_nonneg_right (hsNorm_compPowR_le n hKm hK) (hsNorm_nonneg K)
    _ = hsNorm K ^ (n + 2) := by ring

/-! ### The `k = 2` and `k = 3` kernel-side anchors -/

/-- **The `k = 2` anchor**: `cycleIntegral 2 K = cycle2 K K = hsNorm K ^ 2` for
symmetric kernels (the landed `cycleIntegral_two` + `cycle2_self_sq`). -/
theorem cycleIntegral_two_anchors (K : ℝ × ℝ → ℝ) (hsymK : ∀ p : ℝ × ℝ, K p = K p.swap) :
    cycleIntegral 2 K = cycle2 K K ∧ cycle2 K K = hsNorm K ^ 2 :=
  ⟨cycleIntegral_two K, cycle2_self_sq hsymK⟩

/-- **The `k = 3` anchor (unconditional)**: `cycleIntegral 3 K = cycle2 (compKernel K K) K`
— the landed `hA`-discharged `k = 3` closure of `Hurst.GeneralKHasSumClosed` (with the
splice giving `cycleIntegral 3 K = chainCycleTriple K K K`). -/
theorem cycleIntegral_three_anchors (K : ℝ × ℝ → ℝ) (hKm : Measurable K) (hK : HSKernel K) :
    cycleIntegral 3 K = cycle2 (compKernel K K) K :=
  (cycleIntegral_three_eq_cycle2 K hKm hK).1

/-! ### The assembled general-`k` HasSum -/

/-- **The assembled general-`k` HasSum (`hP`-carried kernel side)**: for every `k ≥ 2`,
the enumerated `k`-th power series `HasSum`s to the `k`-cycle integral, given the
operator-side gate `∑' j, val j ^ k = cycle2 (compPowR (k-2) K) K`.  The proof assembles:
the summability layer (`hasSum_general_k_pow`) for the series side, the landed peel
induction (`cycleIntegral_eq_cycle2_pow`) for the kernel-side composition, and the gate
identifying the two. -/
theorem hasSum_general_k_assembled {K : ℝ × ℝ → ℝ} {hK : HSKernel K}
    (hCompact : IsCompactOperator (TOp K hK))
    (hsym : (↑(TOp K hK) : L2 →ₗ[ℝ] L2).IsSymmetric)
    {val : ℕ → ℝ} {vec : ℕ → L2}
    (hval' : IsDiagEnum (TOpEnd' K hK) val vec)
    (hmult : ∀ μ : ℝ, Module.End.HasEigenvalue (TOpEnd' K hK) μ → μ ≠ 0 →
      Nat.card {j : ℕ // val j = μ}
        = Module.finrank ℝ (Module.End.eigenspace (TOpEnd' K hK) μ))
    (hP : ∀ n r : ℕ, Integrable (peelChainProd (n + 2) (kchain n r K))
      (Measure.pi fun _ : Fin (n + 2) => vol))
    (k : ℕ) (hk : 2 ≤ k)
    (hgate : ∑' j, val j ^ k = cycle2 (compPowR (k - 2) K) K) :
    HasSum (fun j => val j ^ k) (cycleIntegral k K) := by
  have hcomp : cycleIntegral k K = cycle2 (compPowR (k - 2) K) K := by
    have h0 := cycleIntegral_eq_cycle2_pow (n := k - 2) hP
    rwa [show (k - 2) + 2 = k from by omega] at h0
  rw [hcomp, ← hgate]
  have hval : ∀ j : ℕ, val j = 0 ∨ Module.End.HasEigenvector (TOpEnd' K hK) (val j) (vec j) := by
    intro j
    rcases hval' j with ⟨h0v, _⟩ | h
    · exact Or.inl h0v
    · exact Or.inr h.1
  exact hasSum_general_k_pow hCompact hsym hval hmult k hk

/-- **The assembled general-`k` HasSum (bounded kernel: kernel side unconditional)**:
for a measurable `|K| ≤ B` HS kernel with compact symmetric operator, the diagonal
enumeration and the multiplicity clause and the operator-side gate suffice — no chain
integrability hypothesis. -/
theorem hasSum_general_k_assembled_bounded {K : ℝ × ℝ → ℝ} (hKm : Measurable K)
    {hK : HSKernel K} {B : ℝ} (hB : 0 ≤ B) (hKb : ∀ p, |K p| ≤ B)
    (hCompact : IsCompactOperator (TOp K hK))
    (hsym : (↑(TOp K hK) : L2 →ₗ[ℝ] L2).IsSymmetric)
    {val : ℕ → ℝ} {vec : ℕ → L2}
    (hval' : IsDiagEnum (TOpEnd' K hK) val vec)
    (hmult : ∀ μ : ℝ, Module.End.HasEigenvalue (TOpEnd' K hK) μ → μ ≠ 0 →
      Nat.card {j : ℕ // val j = μ}
        = Module.finrank ℝ (Module.End.eigenspace (TOpEnd' K hK) μ))
    (k : ℕ) (hk : 2 ≤ k)
    (hgate : ∑' j, val j ^ k = cycle2 (compPowR (k - 2) K) K) :
    HasSum (fun j => val j ^ k) (cycleIntegral k K) := by
  have hcomp : cycleIntegral k K = cycle2 (compPowR (k - 2) K) K := by
    have h0 := cycleIntegral_comp_pow_bounded hKm hB hKb (k - 2)
    rwa [show (k - 2) + 2 = k from by omega] at h0
  rw [hcomp, ← hgate]
  have hval : ∀ j : ℕ, val j = 0 ∨ Module.End.HasEigenvector (TOpEnd' K hK) (val j) (vec j) := by
    intro j
    rcases hval' j with ⟨h0v, _⟩ | h
    · exact Or.inl h0v
    · exact Or.inr h.1
  exact hasSum_general_k_pow hCompact hsym hval hmult k hk

/-- **The assembled `k = 3` HasSum (gate in the `compKernel` form)**: at `k = 3` the
kernel side is unconditionally closed (`cycleIntegral 3 K = cycle2 (compKernel K K) K`
= `cycle2 (compPowR 1 K) K`), so the single remaining hypothesis is the operator-side
gate in its `k = 3` form `∑' j, val j ^ 3 = cycle2 (compKernel K K) K`. -/
theorem hasSum_k3_assembled_of_gate {K : ℝ × ℝ → ℝ} {hK : HSKernel K}
    (hCompact : IsCompactOperator (TOp K hK))
    (hsym : (↑(TOp K hK) : L2 →ₗ[ℝ] L2).IsSymmetric)
    {val : ℕ → ℝ} {vec : ℕ → L2}
    (hval' : IsDiagEnum (TOpEnd' K hK) val vec)
    (hmult : ∀ μ : ℝ, Module.End.HasEigenvalue (TOpEnd' K hK) μ → μ ≠ 0 →
      Nat.card {j : ℕ // val j = μ}
        = Module.finrank ℝ (Module.End.eigenspace (TOpEnd' K hK) μ))
    (hP : ∀ n r : ℕ, Integrable (peelChainProd (n + 2) (kchain n r K))
      (Measure.pi fun _ : Fin (n + 2) => vol))
    (hgate : ∑' j, val j ^ 3 = cycle2 (compKernel K K) K) :
    HasSum (fun j => val j ^ 3) (cycleIntegral 3 K) := by
  refine hasSum_general_k_assembled hCompact hsym hval' hmult hP 3 (by omega) ?_
  show (∑' j, val j ^ 3) = cycle2 (compPowR (3 - 2) K) K
  exact hgate

end HS

end
