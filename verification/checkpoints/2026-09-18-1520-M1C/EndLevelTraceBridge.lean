import Hurst.EigenFamilySplice
import Hurst.TensorParsevalTracePair
import Hurst.GeneralKHasSumAssembled

/-!
# The end-level trace bridge: abstract compact self-adjoint operators

This file lifts the trace-class diagonal-sum bridge `HS.hBridge`
(`Hurst.EigenTraceBridge`, stated for kernel operators `TOp K hK`) to the ABSTRACT
operator level: a continuous linear map `T : L2 →L[ℝ] L2` that is self-adjoint and
compact, with NO kernel / `HSKernel` / `hconst` data whatsoever.  The proof of
`EigenTraceBridge.hBridge` used only the operator structure (complete eigenfamily via
`exists_complete_eigenfamily_of_symmetric`, absolute summability, basis-invariance by
Parseval along the eigenfamily, fiber-coupling evaluation); here that structure is
re-proved for the abstract `Module.End ℝ L2` form `↑T`.

## Main results

* `HS.exists_diag_enumeration_clm` — for ANY compact self-adjoint `T`, a
  multiplicity-exact diagonal enumeration `(val, vec)` exists: every entry is `(0, 0)`
  or a unit eigenvector with its eigenvalue (`IsDiagEnum`), every nonzero eigenvalue is
  enumerated exactly `finrank (eigenspace μ)` times, and every entry satisfies
  `val j = 0 ∨ |val j| ≤ ‖T‖`.  (Abstract generalization of
  `HS.exists_multiplicity_enumeration`, `Hurst.FrozenSpectralCount`.)
* `HS.hBridge_clm` — the trace-power bridge for the abstract operator.  Because
  compactness alone does NOT give a square-summable spectrum (diagonal operators with
  `κ n = 1/√(n+1)` are compact but `∑ κ² = ∞`), the statement carries an explicit
  Hilbert–Schmidt-type hypothesis `hTHS`: the matrix squares of `T` are summable over
  `ℕ × ℕ` with a basis-uniform bound (downstream, delivered for
  `B = S ∘ M_ω ∘ S` by the A7 estimate).  Conclusions: `Summable (fun m => val m ^ 2)`
  and `HasSum (fun i => ⟪T^j (e i), e i⟫) (∑' m, val m ^ j)` — the diagonal series is
  consumed as a genuine `HasSum` with proven summability, never as a junk tsum.
* `HS.hBridge_clm_tsum` — the same bridge in the bare tsum-equality form.

## Route (copy-adapt of `Hurst.EigenTraceBridge`)

1. **Complete ON eigenfamily** (`exists_complete_eigenfamily_of_symmetric` at the
   abstract `↑T`, fed by mathlib's compact-self-adjoint spectral theorem
   `ContinuousLinearMap.finite_dimensional_eigenspace` and
   `ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`).
2. **Square-summability from the HS-type input** (`summable_kappaSq_of_matrixSq`):
   Parseval along the given Hilbert basis shows `∑'_i ‖T (e i)‖²` is caught by the
   `hTHS` double sum; the abstract Bessel bound (`Orthonormal.sum_inner_products_le`)
   shows `∑_{l ∈ s} κ l² ≤ ∑'_i ‖T (e i)‖²` for every finite `s`.  `|κ l| ≤ ‖T‖` then
   interpolates to `Summable (fun l => |κ l| ^ j)` for `j ≥ 2`.
3. **Basis-invariance** (`tsum_diag_inner_pow_eq_tsum_kappaPow`): adaptation
   of the kernel-level proof (Parseval expansion + double-sum swap), with the
   diagonal-family summability extracted as an explicit conclusion.
4. **Fiber bookkeeping** (`natCard_kappaFiber_eq_finrank'`, `summable_val_of_summable_kappa`,
   `tsum_kappaPow_eq_tsum_valPow`): the `κ`-fiber cardinal identity and the coupling
   swap transfer power sums and summability between the eigenfamily and the
   enumeration, sign- and power-agnostically.
-/

set_option maxHeartbeats 1000000

noncomputable section

namespace HS

open MeasureTheory Measure Real Set Submodule
open scoped Real

/-! ### Small generic helpers (copied from `Hurst.EigenTraceBridge`) -/

/-- Powers of an eigenaction: `T w = μ • w` gives `T ^ m w = μ ^ m • w`. -/
private theorem end_pow_apply_eigenvector {T : L2 →ₗ[ℝ] L2} {μ : ℝ} {w : L2}
    (hw : T w = μ • w) : ∀ m : ℕ, (T ^ m) w = μ ^ m • w := by
  intro m
  induction m with
  | zero => rw [pow_zero, Module.End.one_apply, pow_zero, one_smul]
  | succ n ih =>
      calc (T ^ (n + 1)) w = (T ^ n) (T w) := by rw [pow_succ]; rfl
        _ = (T ^ n) (μ • w) := by rw [hw]
        _ = μ • ((T ^ n) w) := by rw [map_smul]
        _ = μ • (μ ^ n • w) := by rw [ih]
        _ = μ ^ (n + 1) • w := by rw [smul_smul, ← pow_succ']

/-- The cardinality of the `μ`-fiber of `val`, as a real number. -/
private def valFiberCard (val : ℕ → ℝ) (μ : ℝ) : ℝ :=
  ((Nat.card {m : ℕ // val m = μ} : ℕ) : ℝ)

/-- Absolute value of a real power times a square: `|r ^ n * x ^ 2| = |r| ^ n * x ^ 2`. -/
private theorem abs_rpow_mul_sq (r x : ℝ) (n : ℕ) : |r ^ n * x ^ 2| = |r| ^ n * x ^ 2 := by
  rw [abs_mul, abs_pow, abs_pow, sq_abs]

/-- **Finitely-supported fiber sums**: for a family supported on the level-fiber
`{b | g b = c}` (finite), the series of `if g b = c then a else 0` sums to
`a * fiber card`. -/
private theorem hasSum_fiber {β : Type*} {g : β → ℝ} {c a : ℝ}
    (hfin : ({b : β | g b = c} : Set β).Finite) :
    HasSum (fun b => (if g b = c then a else 0)) (a * (Nat.card {b : β // g b = c} : ℝ)) := by
  classical
  haveI : Fintype ↥({b : β | g b = c} : Set β) := hfin.fintype
  have hcard : hfin.toFinset.card = Nat.card {b : β // g b = c} :=
    hfin.card_toFinset.trans Nat.card_eq_fintype_card.symm
  have hsm : Summable (fun b : β => (if g b = c then a else 0)) := by
    refine summable_abs_iff.mp (summable_of_sum_le (c := hfin.toFinset.card * |a|)
      (fun b => abs_nonneg _) fun u => ?_)
    have hsub : u.filter (fun b => g b = c) ⊆ hfin.toFinset := fun x hx =>
      hfin.mem_toFinset.mpr (Finset.mem_filter.mp hx).2
    have h1 : ∑ b ∈ u.filter (fun b => g b = c), |(if g b = c then a else 0 : ℝ)|
        = ∑ b ∈ u, |(if g b = c then a else 0 : ℝ)| :=
      Finset.sum_subset (Finset.filter_subset _ u) (fun b hb hb' => by
        rw [if_neg (fun hc => hb' (Finset.mem_filter.mpr ⟨hb, hc⟩)), abs_zero])
    calc ∑ b ∈ u, |(if g b = c then a else 0 : ℝ)|
        = ∑ b ∈ u.filter (fun b => g b = c), |(if g b = c then a else 0 : ℝ)| := h1.symm
      _ = (u.filter (fun b => g b = c)).card * |a| := by
          rw [Finset.sum_congr rfl fun b hb => by
            rw [if_pos (show g b = c from (Finset.mem_filter.mp hb).2)],
            Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((hfin.toFinset.card : ℕ) : ℝ) * |a| :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card hsub))
            (abs_nonneg a)
  have hval : (∑' b : β, (if g b = c then a else 0)) = hfin.toFinset.card * a := by
    rw [tsum_eq_sum (s := hfin.toFinset) (fun b hb => by
      rw [if_neg (fun hc : g b = c => hb (hfin.mem_toFinset.mpr hc))]),
      Finset.sum_congr rfl fun b hb => by
        rw [if_pos (show g b = c from hfin.mem_toFinset.mp hb)],
      Finset.sum_const, nsmul_eq_mul]
  have hhs := hsm.hasSum
  rw [hval] at hhs
  rw [← hcard, mul_comm]
  exact hhs

/-- Finite fiber grouping of a level-weighted sum:
`∑ x ∈ t, w (g x) = ∑ μ ∈ t.image g, #{x ∈ t | μ = g x} · w μ`. -/
private theorem finset_sum_w_fiberGroup {α : Type*} [DecidableEq α]
    (t : Finset α) (g : α → ℝ) (w : ℝ → ℝ) :
    ∑ x ∈ t, w (g x)
      = ∑ μ ∈ t.image g, (t.filter (fun x => μ = g x)).card * w μ := by
  have step1 : ∑ x ∈ t, w (g x)
      = ∑ μ ∈ t.image g, ∑ x ∈ t, (if μ = g x then w (g x) else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hmem : g x ∈ t.image g := Finset.mem_image_of_mem _ hx
    have hsub : ∑ μ ∈ {g x}, (if μ = g x then w (g x) else 0)
        = ∑ μ ∈ t.image g, (if μ = g x then w (g x) else 0) := by
      refine Finset.sum_subset (Finset.singleton_subset_iff.mpr hmem) ?_
      intro a ha han
      rw [if_neg (fun heq => han (Finset.mem_singleton.mpr heq))]
    rw [← hsub, Finset.sum_singleton, if_pos rfl]
  refine step1.trans (Finset.sum_congr rfl fun μ _ => ?_)
  have hA : ∑ x ∈ t, (if μ = g x then w (g x) else 0)
      = ∑ x ∈ t, (if μ = g x then w μ else 0) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hm : μ = g x
    · rw [if_pos hm, if_pos hm, hm]
    · rw [if_neg hm, if_neg hm]
  have hB : ∑ x ∈ t, (if μ = g x then w μ else 0)
      = ∑ x ∈ t.filter (fun x => μ = g x), w μ := by
    have hB1 : ∑ x ∈ t.filter (fun x => μ = g x), (if μ = g x then w μ else 0)
        = ∑ x ∈ t, (if μ = g x then w μ else 0) :=
      Finset.sum_subset (Finset.filter_subset (fun x => μ = g x) t) (fun x hxmem hx' => by
        refine if_neg (fun hc => hx' ?_)
        exact Finset.mem_filter.mpr ⟨hxmem, hc⟩)
    refine hB1.symm.trans (Finset.sum_congr rfl fun x hx => ?_)
    exact if_pos (Finset.mem_filter.mp hx).2
  rw [hA, hB, Finset.sum_const, nsmul_eq_mul]

/-! ### Abstract compact self-adjoint spectral plumbing -/

/-- Distinct-eigenvalue eigenvectors of a symmetric operator are orthogonal. -/
private theorem innerEigenvectorEqZero {TE : Module.End ℝ L2} (hsym : TE.IsSymmetric)
    {μ ν : ℝ} {x y : L2}
    (hx : Module.End.HasEigenvector TE μ x) (hy : Module.End.HasEigenvector TE ν y)
    (hμν : μ ≠ ν) : inner ℝ x y = 0 := by
  have e0 : inner ℝ (TE x) y = inner ℝ x (TE y) := hsym x y
  rw [hx.apply_eq_smul, hy.apply_eq_smul, real_inner_smul_left,
    real_inner_smul_right] at e0
  have hzero : (μ - ν) * inner ℝ x y = 0 := by
    rw [sub_mul]
    linarith
  rcases mul_eq_zero.mp hzero with h | h
  · exact absurd (sub_eq_zero.mp h) hμν
  · exact h

/-- The unit rescaling of an eigenvector is a unit eigenvector. -/
private theorem hasEigenvector_norm_inv' {TE : Module.End ℝ L2} {μ : ℝ} {v : L2}
    (hv : Module.End.HasEigenvector TE μ v) :
    Module.End.HasEigenvector TE μ (‖v‖⁻¹ • v) ∧ ‖(‖v‖⁻¹ • v)‖ = 1 := by
  have hpos : (0:ℝ) < ‖v‖ := norm_pos_iff.mpr hv.2
  have hsmul : Module.End.HasEigenvector TE μ (‖v‖⁻¹ • v) := by
    refine ⟨?_, fun h => ?_⟩
    · show ‖v‖⁻¹ • v ∈ TE.eigenspace μ
      rw [Module.End.mem_eigenspace_iff, map_smul, hv.apply_eq_smul, smul_smul,
        smul_smul, mul_comm]
    · rcases smul_eq_zero.mp h with h' | h'
      · exact inv_ne_zero hpos.ne' h'
      · exact hv.2 h'
  refine ⟨hsmul, ?_⟩
  rw [norm_smul]
  have habs : ‖(‖v‖⁻¹ : ℝ)‖ = ‖v‖⁻¹ := by
    rw [Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v)]
  rw [habs, inv_mul_cancel₀ hpos.ne']

/-- A unit eigenvector for every eigenvalue. -/
private theorem exists_unit_hasEigenvector' {TE : Module.End ℝ L2} {μ : ℝ}
    (hμ : Module.End.HasEigenvalue TE μ) :
    ∃ e : L2, Module.End.HasEigenvector TE μ e ∧ ‖e‖ = 1 := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  exact ⟨‖v‖⁻¹ • v, (hasEigenvector_norm_inv' hv).1, (hasEigenvector_norm_inv' hv).2⟩

/-- Eigenvalue bound: an eigenvalue of a CLM is dominated by the operator norm. -/
private theorem abs_eigenvalue_le_norm' {T : L2 →L[ℝ] L2} {μ : ℝ} {v : L2}
    (hv : Module.End.HasEigenvector (T : L2 →ₗ[ℝ] L2) μ v) :
    |μ| ≤ ‖T‖ := by
  have h2 : (0:ℝ) < ‖v‖ := norm_pos_iff.mpr hv.2
  have h3 : ‖(T : L2 →ₗ[ℝ] L2) v‖ ≤ ‖T‖ * ‖v‖ :=
    ContinuousLinearMap.le_opNorm T v
  rw [hv.apply_eq_smul, norm_smul, Real.norm_eq_abs,
    mul_comm (|μ|) (‖v‖), mul_comm (‖T‖) (‖v‖)] at h3
  exact (mul_le_mul_iff_right₀ h2).mp h3

/-- There is no injective sequence of eigenvalues all of modulus `≥ ε` (`ε > 0`)
carrying unit eigenvectors (abstract compact self-adjoint form). -/
private theorem not_injective_eigenvalues_ge' {T : L2 →L[ℝ] L2}
    (hCompact : IsCompactOperator T)
    (hsym : (↑T : L2 →ₗ[ℝ] L2).IsSymmetric)
    {ε : ℝ} (hε : 0 < ε)
    (val : ℕ → ℝ) (e : ℕ → L2)
    (hevec : ∀ n, Module.End.HasEigenvector (T : L2 →ₗ[ℝ] L2) (val n) (e n))
    (hunit : ∀ n, ‖e n‖ = 1)
    (hbound : ∀ n, ε ≤ |val n|)
    (hinj : Function.Injective val) : False := by
  -- pairwise orthogonality of the unit eigenvectors
  have horth : ∀ i j, i ≠ j → inner ℝ (e i) (e j) = 0 := by
    intro i j hij
    refine innerEigenvectorEqZero hsym (hevec i) (hevec j) fun hμ => hij ?_
    exact hinj hμ
  -- the T-images live in the compact image of the unit ball
  obtain ⟨Kimg, hKcomp, hKsub⟩ := hCompact.image_closedBall_subset_compact (1 : ℝ)
  have hmem : ∀ n, T (e n) ∈ Kimg := by
    intro n
    refine hKsub (Set.mem_image_of_mem T ?_)
    rw [Metric.mem_closedBall, dist_zero_right, hunit n]
  obtain ⟨a, -, φ, hφmono, hφten⟩ := hKcomp.tendsto_subseq hmem
  -- separation: dist² = val i² + val j² ≥ 2 ε²
  have hsep : ∀ i j, i ≠ j → ε * ε ≤ dist (T (e i)) (T (e j)) ^ 2 := by
    intro i j hij
    have hne : i ≠ j := hij
    have key : dist (T (e i)) (T (e j))
        = ‖val i • e i - val j • e j‖ := by
      rw [dist_eq_norm, show T (e i) - T (e j)
          = ((T : L2 →ₗ[ℝ] L2)) (e i) - ((T : L2 →ₗ[ℝ] L2)) (e j) from rfl,
        (hevec i).apply_eq_smul, (hevec j).apply_eq_smul]
    have hexp : dist (T (e i)) (T (e j)) ^ 2
        = val i ^ 2 + val j ^ 2 := by
      rw [key, ← real_inner_self_eq_norm_sq, real_inner_sub_sub_self]
      simp only [real_inner_smul_left, real_inner_smul_right,
        real_inner_self_eq_norm_sq, hunit i, hunit j, horth i j hne,
        norm_smul, Real.norm_eq_abs, mul_one, sq_abs]
      ring
    calc ε * ε ≤ |val i| * |val j| :=
          mul_le_mul (hbound i) (hbound j) (le_of_lt hε) (abs_nonneg _)
      _ ≤ (|val i| * |val i| + |val j| * |val j|) / 2 := by
          nlinarith [sq_nonneg (|val i| - |val j|)]
      _ = (|val i| ^ 2 + |val j| ^ 2) / 2 := by ring
      _ ≤ val i ^ 2 + val j ^ 2 := by
          rw [sq_abs, sq_abs]
          linarith [sq_nonneg (val i), sq_nonneg (val j)]
      _ = dist (T (e i)) (T (e j)) ^ 2 := hexp.symm
  -- contradiction with the convergence of the subsequence
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hφten (ε / 2) (by positivity)
  simp only [Function.comp_apply] at hN
  have hd1 : dist (T (e (φ N))) a < ε / 2 := hN N (Nat.le_refl N)
  have hd2 : dist (T (e (φ (N + 1)))) a < ε / 2 := hN (N + 1) (Nat.le_succ N)
  have hlt : dist (T (e (φ N))) (T (e (φ (N + 1)))) < ε := by
    have h1 := dist_triangle (T (e (φ N))) a (T (e (φ (N + 1))))
    rw [dist_comm a] at h1
    calc dist (T (e (φ N))) (T (e (φ (N + 1))))
        ≤ dist (T (e (φ N))) a + dist (T (e (φ (N + 1)))) a := h1
      _ < ε := by linarith
  have hsq : ε * ε ≤ dist (T (e (φ N))) (T (e (φ (N + 1)))) ^ 2 :=
    hsep (φ N) (φ (N + 1)) (fun h => by
      have hlt := hφmono (Nat.lt_succ_self N)
      rw [h] at hlt
      exact Nat.lt_irrefl _ hlt)
  have hlt2 : dist (T (e (φ N))) (T (e (φ (N + 1)))) ^ 2 < ε * ε := by
    have hd := hlt
    have h1 : dist (T (e (φ N))) (T (e (φ (N + 1)))) ^ 2
        ≤ dist (T (e (φ N))) (T (e (φ (N + 1)))) * ε := by
      rw [pow_two]
      have hdnn : (0:ℝ) ≤ dist (T (e (φ N)))
          (T (e (φ (N + 1)))) := dist_nonneg
      exact mul_le_mul_of_nonneg_left hd.le hdnn
    exact lt_of_le_of_lt h1 (mul_lt_mul_of_pos_right hd hε)
  exact lt_irrefl _ (lt_of_le_of_lt hsq hlt2)

/-- **Finiteness**: for every `ε > 0`, the eigenvalues of the compact self-adjoint
operator of modulus `≥ ε` form a finite set. -/
private theorem eigenvalue_set_finite' {T : L2 →L[ℝ] L2}
    (hCompact : IsCompactOperator T)
    (hsym : (↑T : L2 →ₗ[ℝ] L2).IsSymmetric)
    {ε : ℝ} (hε : 0 < ε) :
    Set.Finite {μ : ℝ | Module.End.HasEigenvalue (T : L2 →ₗ[ℝ] L2) μ ∧ ε ≤ |μ|} := by
  by_contra hinf
  -- an injective eigenvalue sequence inside the set (embedding ℕ into the infinite set)
  obtain ⟨val, hmem, hinj⟩ :
      ∃ val : ℕ → ℝ,
        (∀ n, val n ∈ {μ : ℝ | Module.End.HasEigenvalue (T : L2 →ₗ[ℝ] L2) μ ∧ ε ≤ |μ|}) ∧
          Function.Injective val := by
    have f := Set.Infinite.natEmbedding
      {μ : ℝ | Module.End.HasEigenvalue (T : L2 →ₗ[ℝ] L2) μ ∧ ε ≤ |μ|} hinf
    exact ⟨fun n => (f n : ℝ), fun n => (f n).2,
      fun i j hij => f.injective (Subtype.ext hij)⟩
  -- unit eigenvectors, one per sequence entry
  have hpair : ∀ n : ℕ,
      Module.End.HasEigenvalue (T : L2 →ₗ[ℝ] L2) (val n) ∧ ε ≤ |val n| :=
    fun n => Set.mem_setOf.mp (hmem n)
  choose e he1 he2 using fun n : ℕ => exists_unit_hasEigenvector' (hpair n).1
  exact not_injective_eigenvalues_ge' hCompact hsym hε val e he1 he2
    (fun n => (hpair n).2) hinj

/-- **Countability**: the nonzero eigenvalues of the compact self-adjoint operator
form a countable set. -/
private theorem eigenvalue_set_countable' {T : L2 →L[ℝ] L2}
    (hCompact : IsCompactOperator T)
    (hsym : (↑T : L2 →ₗ[ℝ] L2).IsSymmetric) :
    Set.Countable {μ : ℝ | Module.End.HasEigenvalue (T : L2 →ₗ[ℝ] L2) μ ∧ μ ≠ 0} := by
  have hEq : {μ : ℝ | Module.End.HasEigenvalue (T : L2 →ₗ[ℝ] L2) μ ∧ μ ≠ 0}
      = ⋃ n : ℕ, {μ : ℝ | Module.End.HasEigenvalue (T : L2 →ₗ[ℝ] L2) μ ∧ 1 / (n + 1) ≤ |μ|} := by
    ext μ
    constructor
    · rintro ⟨hμ, hμ0⟩
      have habs : 0 < |μ| := abs_pos.mpr hμ0
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / |μ|)
      refine Set.mem_iUnion.mpr ⟨n, Set.mem_setOf.mpr ⟨hμ, ?_⟩⟩
      have hn' : (1:ℝ) / |μ| ≤ (n:ℝ) + 1 := by linarith
      have h2 : (1:ℝ) = |μ| * (1 / |μ|) := by
        rw [one_div]
        exact (mul_inv_cancel₀ (ne_of_gt habs)).symm
      have hkey : (1:ℝ) ≤ |μ| * ((n:ℝ) + 1) := by
        calc (1:ℝ) = |μ| * (1 / |μ|) := h2
          _ ≤ |μ| * ((n:ℝ) + 1) := mul_le_mul_of_nonneg_left hn' (abs_nonneg μ)
      exact (div_le_iff₀ (show (0:ℝ) < (n:ℝ) + 1 by positivity)).mpr hkey
    · intro hmem2
      obtain ⟨n, hmu2⟩ := Set.mem_iUnion.mp hmem2
      obtain ⟨hμe, hn⟩ := Set.mem_setOf.mp hmu2
      refine ⟨hμe, fun hzero => ?_⟩
      rw [hzero, abs_zero] at hn
      have hpos : 0 < (1:ℝ) / (n + 1) := by positivity
      linarith
  rw [hEq]
  exact Set.countable_iUnion fun n =>
    (eigenvalue_set_finite' hCompact hsym
      (show (0:ℝ) < 1 / (n + 1) by positivity)).countable

/-- Finite-dimensionality of the nonzero eigenspaces of a compact self-adjoint CLM
(mathlib's compact-spectral-theorem input, at the `Module.End` form). -/
private theorem finiteDimensional_eigenspace' {T : L2 →L[ℝ] L2}
    (hCompact : IsCompactOperator T) {μ : ℝ} (hμ0 : μ ≠ 0) :
    FiniteDimensional ℝ (Module.End.eigenspace (T : L2 →ₗ[ℝ] L2) μ) :=
  ContinuousLinearMap.finite_dimensional_eigenspace hCompact μ hμ0

/-- Positive dimension of the nonzero eigenspaces. -/
private theorem finrank_eigenspace_pos' {T : L2 →L[ℝ] L2}
    (hCompact : IsCompactOperator T)
    {μ : ℝ} (hμev : Module.End.HasEigenvalue (T : L2 →ₗ[ℝ] L2) μ) (hμ0 : μ ≠ 0) :
    0 < Module.finrank ℝ (Module.End.eigenspace (T : L2 →ₗ[ℝ] L2) μ) := by
  haveI hfd := finiteDimensional_eigenspace' hCompact hμ0
  obtain ⟨w, hw⟩ := hμev.exists_hasEigenvector
  haveI : Nontrivial ↥(Module.End.eigenspace (T : L2 →ₗ[ℝ] L2) μ) :=
    ⟨0, ⟨w, hw.1⟩, fun h => hw.2 (Subtype.ext_iff.mp h).symm⟩
  exact Module.finrank_pos

/-- The nonzero-`κ`-level fiber is finite (an infinite one would give a linearly
independent family in a finite-dimensional eigenspace indexed by `ℕ`). -/
private theorem kappaFiberFinite {T : L2 →L[ℝ] L2}
    (hCompact : IsCompactOperator T)
    {ι : Type} {v : ι → L2} {κ : ι → ℝ}
    (hv : Orthonormal ℝ v) (he : ∀ i, (T : L2 →ₗ[ℝ] L2) (v i) = κ i • v i)
    {μ : ℝ} (_hμev : Module.End.HasEigenvalue (T : L2 →ₗ[ℝ] L2) μ) (hμ0 : μ ≠ 0) :
    ({i : ι | κ i = μ} : Set ι).Finite := by
  by_contra hinf
  haveI hfd := finiteDimensional_eigenspace' hCompact hμ0
  haveI hI : ({i : ι | κ i = μ} : Set ι).Infinite := hinf
  obtain ⟨f, hf⟩ := hI.natEmbedding
  -- the composed family `v ∘ (coe ∘ f)` is orthonormal in L2 and lives in the eigenspace
  have hcoeinj : Function.Injective (fun n : ℕ => ((f n : {i : ι // κ i = μ}) : ι)) := by
    intro a b hab
    exact hf (Subtype.ext hab)
  have hON : Orthonormal ℝ (fun n : ℕ => v ((f n : {i : ι // κ i = μ}) : ι)) :=
    hv.comp _ hcoeinj
  have hwmem : ∀ n : ℕ,
      v ((f n : {i : ι // κ i = μ}) : ι)
        ∈ Module.End.eigenspace (T : L2 →ₗ[ℝ] L2) μ := by
    intro n
    refine Module.End.mem_eigenspace_iff.mpr ?_
    exact (he _).trans (congrArg (fun z : ℝ => z • v _) (Set.mem_setOf.mp (f n).2))
  have hLI2 : LinearIndependent ℝ
      (fun n : ℕ => (⟨v ((f n : {i : ι // κ i = μ}) : ι), hwmem n⟩ :
        ↥(Module.End.eigenspace (T : L2 →ₗ[ℝ] L2) μ))) := by
    refine LinearIndependent.of_comp
      (Module.End.eigenspace (T : L2 →ₗ[ℝ] L2) μ).subtype ?_
    have hfe : ((Module.End.eigenspace (T : L2 →ₗ[ℝ] L2) μ).subtype ∘
        fun n : ℕ => (⟨v ((f n : {i : ι // κ i = μ}) : ι), hwmem n⟩ :
          ↥(Module.End.eigenspace (T : L2 →ₗ[ℝ] L2) μ)))
        = (fun n : ℕ => v ((f n : {i : ι // κ i = μ}) : ι)) := by
      funext n; rfl
    rw [hfe]
    exact hON.linearIndependent
  exact absurd (LinearIndependent.cardinalMk_le_finrank (R := ℝ) hLI2)
    (by rw [Cardinal.mk_nat]; exact not_le.mpr Cardinal.natCast_lt_aleph0)

/-- **The `κ`-fiber cardinal identity** (abstract compact self-adjoint form): for the
complete orthonormal eigenfamily `(v, κ)` of `T`, each nonzero eigenvalue `μ` is
attained on EXACTLY `finrank (eigenspace μ)` indices:
`Nat.card {i // κ i = μ} = finrank (eigenspace μ)`. -/
private theorem natCard_kappaFiber_eq_finrank' {T : L2 →L[ℝ] L2}
    (hCompact : IsCompactOperator T)
    (hsym : (↑T : L2 →ₗ[ℝ] L2).IsSymmetric)
    {ι : Type} {v : ι → L2} {κ : ι → ℝ}
    (hv : Orthonormal ℝ v) (he : ∀ i, (T : L2 →ₗ[ℝ] L2) (v i) = κ i • v i)
    (hcomp : (span ℝ (Set.range v))ᗮ = ⊥)
    {μ : ℝ} (hμev : Module.End.HasEigenvalue (T : L2 →ₗ[ℝ] L2) μ) (hμ0 : μ ≠ 0) :
    Nat.card {i : ι // κ i = μ}
      = Module.finrank ℝ (Module.End.eigenspace (T : L2 →ₗ[ℝ] L2) μ) := by
  classical
  haveI hfd := finiteDimensional_eigenspace' hCompact hμ0
  set W := Module.End.eigenspace (T : L2 →ₗ[ℝ] L2) μ with hW
  have hvz : ∀ i : ι, v i ≠ 0 := fun i => norm_ne_zero_iff.mp (by rw [hv.1 i]; norm_num)
  have hve : ∀ i : ι,
      Module.End.HasEigenvector (T : L2 →ₗ[ℝ] L2) (κ i) (v i) := fun i =>
    Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr (he i), hvz i⟩
  have hwmem : ∀ x : {i : ι // κ i = μ}, v (x : ι) ∈ W := fun x => by
    refine Module.End.mem_eigenspace_iff.mpr ?_
    exact (he x.1).trans (congrArg (fun z : ℝ => z • v (x : ι)) x.2)
  set w : {i : ι // κ i = μ} → ↥W := fun x => ⟨v (x : ι), hwmem x⟩ with hwdef
  -- linear independence of the fiber family (in W)
  have hwON : Orthonormal ℝ (fun x : {i : ι // κ i = μ} => v (x : ι)) :=
    hv.comp Subtype.val Subtype.val_injective
  have hfe : (W.subtype ∘ w) = (fun x : {i : ι // κ i = μ} => v (x : ι)) := by
    funext x; rfl
  have hwLI : LinearIndependent ℝ w := by
    refine LinearIndependent.of_comp W.subtype ?_
    rw [hfe]
    exact hwON.linearIndependent
  -- finiteness of the fiber
  have hFfin : ({i : ι | κ i = μ} : Set ι).Finite :=
    kappaFiberFinite hCompact hv he hμev hμ0
  haveI hsubF : Finite {i : ι // κ i = μ} := hFfin.to_subtype
  haveI : Fintype {i : ι // κ i = μ} := Fintype.ofFinite _
  -- the fiber family spans W: a vector of W orthogonal to it is orthogonal to all of v
  have hspW : (span ℝ (Set.range w))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    by_cases hy0 : (y : L2) = 0
    · exact Subtype.ext hy0
    · have hyEV : Module.End.HasEigenvector (T : L2 →ₗ[ℝ] L2) μ (y : L2) :=
        Module.End.hasEigenvector_iff.mpr ⟨y.2, hy0⟩
      have hyall : ∀ i : ι, inner ℝ (v i) (y : L2) = 0 := by
        intro i
        by_cases himem : κ i = μ
        · have hmemrange : w ⟨i, himem⟩ ∈ span ℝ (Set.range w) :=
            Submodule.subset_span (Set.mem_range.mpr ⟨⟨i, himem⟩, rfl⟩)
          have h1 : inner ℝ (w ⟨i, himem⟩) y = 0 :=
            (Submodule.mem_orthogonal (span ℝ (Set.range w)) y).mp hy _ hmemrange
          have h2 : inner ℝ ((w ⟨i, himem⟩ : L2)) (y : L2)
              = inner ℝ (w ⟨i, himem⟩) y := (Submodule.coe_inner _ _ _).symm
          show inner ℝ ((w ⟨i, himem⟩ : L2)) (y : L2) = 0
          rw [h2]
          exact h1
        · exact (real_inner_comm (v i) (y : L2)).symm.trans
            (innerEigenvectorEqZero hsym hyEV (hve i)
              (fun h => himem h.symm))
      have hyOrtho : (y : L2) ∈ (span ℝ (Set.range v))ᗮ := by
        rw [Submodule.mem_orthogonal]
        intro z hz
        induction hz using Submodule.span_induction with
        | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hyall i
        | zero => simp
        | add x z _ _ hx hz2 => rw [inner_add_left, hx, hz2, add_zero]
        | smul c x _ hx => rw [real_inner_smul_left, hx, mul_zero]
      rw [hcomp] at hyOrtho
      rw [Submodule.mem_bot ℝ] at hyOrtho
      exact Subtype.ext hyOrtho
  -- conclude: the fiber family is a basis of W
  have htop : span ℝ (Set.range w) = ⊤ := Submodule.orthogonal_eq_bot_iff.mp hspW
  have hBasis : Module.Basis {i : ι // κ i = μ} ℝ ↥W :=
    Module.Basis.mk hwLI (le_of_eq htop.symm)
  calc Nat.card {i : ι // κ i = μ}
      = Fintype.card {i : ι // κ i = μ} := Nat.card_eq_fintype_card
    _ = Module.finrank ℝ ↥W := (Module.finrank_eq_card_basis hBasis).symm

/-! ### The matrix-square (Hilbert–Schmidt-type) input -/

set_option maxHeartbeats 4000000 in
/-- **Square-summability of the eigenvalues from the HS-type input**: if the matrix
squares of `T` are summable (with a uniform bound) over the Hilbert basis `e`, then the
eigenvalue family of the complete eigenfamily `(v, κ)` is square-summable. -/
private theorem summable_kappaSq_of_matrixSq {T : L2 →L[ℝ] L2}
    (hsym : (↑T : L2 →ₗ[ℝ] L2).IsSymmetric)
    (hTHS : ∃ C : ℝ, 0 ≤ C ∧ ∀ e : HilbertBasis ℕ ℝ L2,
      Summable (fun p : ℕ × ℕ => (inner ℝ (e p.1) (T (e p.2))) ^ 2) ∧
        (∑' p : ℕ × ℕ, (inner ℝ (e p.1) (T (e p.2))) ^ 2) ≤ C)
    {ι : Type} {v : ι → L2} {κ : ι → ℝ}
    (hv : Orthonormal ℝ v) (he : ∀ i, (T : L2 →ₗ[ℝ] L2) (v i) = κ i • v i)
    (e : HilbertBasis ℕ ℝ L2) :
    Summable (fun l : ι => κ l ^ 2) := by
  classical
  obtain ⟨C, hC0, heCl⟩ := hTHS
  obtain ⟨hSumE, hBoundE⟩ := heCl e
  -- the symmetry of T, at the CLM-application form (defeq to the End form)
  have hsymclm : ∀ (x y : L2), inner ℝ x (T y) = inner ℝ (T x) y := by
    intro x y
    have hcoe : ⇑((T : L2 →L[ℝ] L2) : L2 →ₗ[ℝ] L2) = ⇑T := ContinuousLinearMap.coe_coe T
    rw [← hcoe]
    exact (hsym x y).symm
  have hswapSum : Summable (fun q : ℕ × ℕ => inner ℝ (e q.2) (T (e q.1)) ^ 2) :=
    (Equiv.summable_iff (e := Equiv.prodComm ℕ ℕ)
      (f := fun q : ℕ × ℕ => inner ℝ (e q.1) (T (e q.2)) ^ 2)).mpr hSumE
  -- per-coordinate Parseval of the basis-vector images
  have hparse : ∀ i : ℕ, HasSum (fun j : ℕ => inner ℝ (e j) (T (e i)) * inner ℝ (e j) (T (e i)))
      (‖T (e i)‖ ^ 2) := by
    intro i
    have h1 := e.hasSum_inner_mul_inner (T (e i)) (T (e i))
    rw [real_inner_self_eq_norm_sq] at h1
    refine h1.congr_fun fun j => ?_
    rw [real_inner_comm (T (e i)) (e j)]
  have hparseSumm : ∀ i : ℕ, Summable (fun j : ℕ => inner ℝ (e j) (T (e i)) ^ 2) :=
    fun i => ((hparse i).congr_fun fun j => by ring).summable
  have hcolsum : Summable (fun i : ℕ => ∑' j : ℕ, inner ℝ (e j) (T (e i)) ^ 2) :=
    ((summable_prod_of_nonneg (fun _q : ℕ × ℕ => sq_nonneg _)).mp hswapSum).2
  have hnormSqSumm : Summable (fun i : ℕ => ‖T (e i)‖ ^ 2) := by
    have h : ∀ i : ℕ, (∑' j : ℕ, inner ℝ (e j) (T (e i)) ^ 2) = ‖T (e i)‖ ^ 2 :=
      fun i => ((hparse i).congr_fun fun j => pow_two (inner ℝ (e j) (T (e i)))).tsum_eq
    exact hcolsum.congr h
  -- ∑'_i ‖T (e i)‖² is caught by the hTHS double sum
  have hnormSqSum : (∑' i : ℕ, ‖T (e i)‖ ^ 2) ≤ C := by
    have h1 : (∑' i : ℕ, ‖T (e i)‖ ^ 2) = ∑' i : ℕ, ∑' j : ℕ, inner ℝ (e j) (T (e i)) ^ 2 :=
      tsum_congr fun i => ((hparse i).congr_fun fun j => by ring).tsum_eq.symm
    have h2 : (∑' i : ℕ, ∑' j : ℕ, inner ℝ (e j) (T (e i)) ^ 2)
        = ∑' p : ℕ × ℕ, inner ℝ (e p.2) (T (e p.1)) ^ 2 :=
      (Summable.tsum_prod' hswapSum (fun _i => hparseSumm _)).symm
    have h3 : (∑' p : ℕ × ℕ, inner ℝ (e p.2) (T (e p.1)) ^ 2)
        = (∑' p : ℕ × ℕ, inner ℝ (e p.1) (T (e p.2)) ^ 2) :=
      ((Equiv.prodComm ℕ ℕ).tsum_eq
        (fun q : ℕ × ℕ => inner ℝ (e q.1) (T (e q.2)) ^ 2))
    calc (∑' i : ℕ, ‖T (e i)‖ ^ 2) = ∑' i : ℕ, ∑' j : ℕ, inner ℝ (e j) (T (e i)) ^ 2 := h1
      _ = ∑' p : ℕ × ℕ, inner ℝ (e p.2) (T (e p.1)) ^ 2 := h2
      _ = ∑' p : ℕ × ℕ, inner ℝ (e p.1) (T (e p.2)) ^ 2 := h3
      _ ≤ C := hBoundE
  -- the per-eigenfamily-vector Parseval along the basis
  have hrowHas : ∀ l : ι, HasSum (fun i : ℕ => inner ℝ (v l) (T (e i)) ^ 2) (κ l ^ 2) := by
    intro l
    have h1 : ‖T (v l)‖ ^ 2 = κ l ^ 2 := by
      rw [show T (v l) = κ l • v l from he l, norm_smul, Real.norm_eq_abs, hv.1 l,
        mul_one, sq_abs]
    have h2 := e.hasSum_inner_mul_inner (T (v l)) (T (v l))
    rw [real_inner_self_eq_norm_sq, h1] at h2
    refine h2.congr_fun fun i => ?_
    have hB : inner ℝ (e i) (T (v l)) = inner ℝ (v l) (T (e i)) :=
      (hsymclm (e i) (v l)).trans (real_inner_comm (T (e i)) (v l)).symm
    have hA : inner ℝ (v l) (T (e i)) ^ 2
        = inner ℝ (v l) (T (e i)) * inner ℝ (v l) (T (e i)) := by ring
    rw [real_inner_comm (e i) (T (v l)), hB, hA]
  refine summable_of_sum_le (c := C) (fun l => sq_nonneg (κ l)) fun s => ?_
  have hBess : ∀ i : ℕ, ∑ l ∈ s, inner ℝ (v l) (T (e i)) ^ 2 ≤ ‖T (e i)‖ ^ 2 := by
    intro i
    have hb := hv.sum_inner_products_le (x := T (e i)) (s := s)
    have hsum : ∑ l ∈ s, inner ℝ (v l) (T (e i)) ^ 2
        = ∑ l ∈ s, ‖inner ℝ (v l) (T (e i))‖ ^ 2 := by
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Real.norm_eq_abs, sq_abs]
    rw [hsum]
    exact hb
  have hstep : ∀ i : ℕ,
      (∑' l : {x : ι // x ∈ s}, inner ℝ (v (l : ι)) (T (e i)) ^ 2)
        = ∑ l ∈ s, inner ℝ (v l) (T (e i)) ^ 2 := by
    intro i
    rw [tsum_fintype]
    exact Finset.sum_coe_sort s
      (fun l : ι => inner ℝ (v l) (T (e i)) ^ 2)
  have hswap : (∑' l : {x : ι // x ∈ s}, ∑' i : ℕ, inner ℝ (v (l : ι)) (T (e i)) ^ 2)
      = (∑' i : ℕ, ∑' l : {x : ι // x ∈ s}, inner ℝ (v (l : ι)) (T (e i)) ^ 2) :=
    (Summable.tsum_comm'
      ((summable_prod_of_nonneg (fun _q : {x : ι // x ∈ s} × ℕ => sq_nonneg _)).mpr
        ⟨fun l => ((hrowHas (l : ι)).congr_fun fun i => rfl).summable,
          Summable.of_finite.congr fun l => (hrowHas (l : ι)).tsum_eq.symm⟩)
      (fun l => ((hrowHas (l : ι)).congr_fun fun i => rfl).summable)
      (fun _i => Summable.of_finite)
      (f := fun (l : {x : ι // x ∈ s}) (i : ℕ) => inner ℝ (v (l : ι)) (T (e i)) ^ 2)).symm
  have hconv : (∑' i : ℕ, ∑' l : {x : ι // x ∈ s}, inner ℝ (v (l : ι)) (T (e i)) ^ 2)
      ≤ ∑' i : ℕ, ‖T (e i)‖ ^ 2 := by
    refine Real.tsum_le_of_sum_le (fun i => ?_) (fun u => ?_)
    · rw [hstep i]
      exact Finset.sum_nonneg fun _ _ => sq_nonneg _
    · refine le_trans (Finset.sum_le_sum fun i _ => ?_)
        (Summable.sum_le_tsum u (fun i _ => sq_nonneg (‖T (e i)‖)) hnormSqSumm)
      rw [hstep i]
      exact hBess i
  have hL : (∑ l ∈ s, ∑' i : ℕ, inner ℝ (v l) (T (e i)) ^ 2)
      = (∑' l : {x : ι // x ∈ s}, ∑' i : ℕ, inner ℝ (v (l : ι)) (T (e i)) ^ 2) := by
    refine Eq.trans (Finset.sum_coe_sort s
      (fun l : ι => ∑' i : ℕ, inner ℝ (v l) (T (e i)) ^ 2)).symm ?_
    exact (tsum_fintype (f := fun l : {x : ι // x ∈ s} =>
      ∑' i : ℕ, inner ℝ (v (l : ι)) (T (e i)) ^ 2)).symm
  calc ∑ l ∈ s, κ l ^ 2
      = ∑ l ∈ s, ∑' i : ℕ, inner ℝ (v l) (T (e i)) ^ 2 :=
        Finset.sum_congr rfl fun l _ => (hrowHas l).tsum_eq.symm
    _ = ∑' i : ℕ, ∑' l : {x : ι // x ∈ s}, inner ℝ (v (l : ι)) (T (e i)) ^ 2 := by
        rw [hL, hswap]
    _ ≤ ∑' i : ℕ, ‖T (e i)‖ ^ 2 := hconv
    _ ≤ C := hnormSqSum
/-! ### The multiplicity-exact enumeration for abstract compact self-adjoint T -/

/-- The multiplicity index type: a nonzero eigenvalue (as an element of `S`) together
with an index into its finite-dimensional eigenspace. -/
private abbrev multIdxE (TE : Module.End ℝ L2) (S : Set ℝ) : Type :=
  Σ a : ↥S, Fin (Module.finrank ℝ (Module.End.eigenspace TE a.val))

/-- Generic counting: the `μ'`-fiber of the multiplicity index type has the cardinality
of the `μ'`-eigenspace index type. -/
private theorem natCard_multIdx_fiberE (TE : Module.End ℝ L2) (S : Set ℝ) (μ' : ↥S) :
    Nat.card {σ : multIdxE TE S // σ.1.val = μ'.val}
      = Nat.card (Fin (Module.finrank ℝ (Module.End.eigenspace TE μ'.val))) :=
  Nat.card_congr
    { toFun := fun σ =>
        cast (congrArg (fun x : ℝ => Fin (Module.finrank ℝ (Module.End.eigenspace TE x))) σ.2)
          σ.1.2
      invFun := fun k => ⟨⟨μ', k⟩, rfl⟩
      left_inv := by
        rintro ⟨⟨⟨a, ha⟩, k⟩, hk⟩
        exact Subtype.ext (by
          rw [Sigma.mk.injEq]
          exact ⟨Subtype.ext hk.symm, cast_heq _ k⟩)
      right_inv := fun _ => rfl }

/-- The enumeration value map: entries over the range of the section `ρ` read off `fv`,
everything else is `0`. -/
private def enumValE {ι : Type} (ρ : ι → ℕ) (hρinj : Function.Injective ρ)
    (fv : ι → ℝ) (j : ℕ) : ℝ :=
  @dite _ (j ∈ Set.range ρ) (Classical.propDecidable _)
    (fun h => fv ((Equiv.ofInjective ρ hρinj).symm ⟨j, h⟩)) (fun _ => 0)

/-- The matching eigenvector map (same shape as `enumValE`). -/
private def enumVecE {ι : Type} (ρ : ι → ℕ) (hρinj : Function.Injective ρ)
    (w : ι → L2) (j : ℕ) : L2 :=
  @dite _ (j ∈ Set.range ρ) (Classical.propDecidable _)
    (fun h => w ((Equiv.ofInjective ρ hρinj).symm ⟨j, h⟩)) (fun _ => 0)

private theorem enumValE_of_mem {ι : Type} {ρ : ι → ℕ} (hρinj : Function.Injective ρ)
    {fv : ι → ℝ} {j : ℕ} (hj : j ∈ Set.range ρ) :
    enumValE ρ hρinj fv j = fv ((Equiv.ofInjective ρ hρinj).symm ⟨j, hj⟩) := dif_pos hj

private theorem enumValE_of_notMem {ι : Type} {ρ : ι → ℕ} (hρinj : Function.Injective ρ)
    {fv : ι → ℝ} {j : ℕ} (hj : j ∉ Set.range ρ) :
    enumValE ρ hρinj fv j = 0 := dif_neg hj

private theorem enumVecE_of_mem {ι : Type} {ρ : ι → ℕ} (hρinj : Function.Injective ρ)
    {w : ι → L2} {j : ℕ} (hj : j ∈ Set.range ρ) :
    enumVecE ρ hρinj w j = w ((Equiv.ofInjective ρ hρinj).symm ⟨j, hj⟩) := dif_pos hj

private theorem enumVecE_of_notMem {ι : Type} {ρ : ι → ℕ} (hρinj : Function.Injective ρ)
    {w : ι → L2} {j : ℕ} (hj : j ∉ Set.range ρ) :
    enumVecE ρ hρinj w j = 0 := dif_neg hj

set_option maxHeartbeats 4000000 in
/-- **Multiplicity-exact enumeration for any compact self-adjoint operator** (abstract
generalization of `HS.exists_multiplicity_enumeration`): there are `val : ℕ → ℝ` and
`vec : ℕ → L2` such that

* `(val, vec)` is a diagonal enumeration (`IsDiagEnum`: every entry is `(0, 0)` or a
  unit eigenvector with its eigenvalue);
* every nonzero eigenvalue `μ` is enumerated exactly
  `Module.finrank ℝ (eigenspace μ)` times;
* every entry satisfies `val j = 0 ∨ |val j| ≤ ‖T‖`. -/
theorem exists_diag_enumeration_clm {T : L2 →L[ℝ] L2}
    (hTsym : (↑T : L2 →ₗ[ℝ] L2).IsSymmetric) (hTcompact : IsCompactOperator T) :
    ∃ val : ℕ → ℝ, ∃ vec : ℕ → L2,
      IsDiagEnum (T : L2 →ₗ[ℝ] L2) val vec ∧
      (∀ μ : ℝ, Module.End.HasEigenvalue (T : L2 →ₗ[ℝ] L2) μ → μ ≠ 0 →
        Nat.card {m : ℕ // val m = μ}
          = Module.finrank ℝ (Module.End.eigenspace (T : L2 →ₗ[ℝ] L2) μ)) ∧
      (∀ j : ℕ, val j = 0 ∨ |val j| ≤ ‖T‖) := by
  classical
  set S : Set ℝ := {μ : ℝ | Module.End.HasEigenvalue (T : L2 →ₗ[ℝ] L2) μ ∧ μ ≠ 0} with hS
  have hScount : S.Countable := eigenvalue_set_countable' hTcompact hTsym
  haveI : Countable ↥S := hScount.to_subtype
  -- a unit eigenvector for each nonzero eigenvalue
  choose u hu1 hu2 using fun (a : ↥S) =>
    exists_unit_hasEigenvector'
      (show Module.End.HasEigenvalue (T : L2 →ₗ[ℝ] L2) a.val from a.2.1)
  -- nontrivial nonzero eigenspaces, hence positive finrank
  have hdimp : ∀ a : ↥S,
      0 < Module.finrank ℝ (Module.End.eigenspace (T : L2 →ₗ[ℝ] L2) a.val) := by
    intro a
    haveI : Module.Finite ℝ (Module.End.eigenspace (T : L2 →ₗ[ℝ] L2) a.val) :=
      finiteDimensional_eigenspace' hTcompact (show a.val ≠ 0 from a.2.2)
    haveI : Nontrivial (Module.End.eigenspace (T : L2 →ₗ[ℝ] L2) a.val) :=
      ⟨0, ⟨u a, (hu1 a).1⟩, fun h => (hu1 a).2 (Subtype.ext_iff.mp h).symm⟩
    exact Module.finrank_pos
  -- the multiplicity index type is countable (countable base, finite fibers)
  haveI : ∀ a : ↥S,
      Countable (Fin (Module.finrank ℝ
        (Module.End.eigenspace (T : L2 →ₗ[ℝ] L2) a.val))) := fun _ => inferInstance
  haveI : Countable (multIdxE (T : L2 →ₗ[ℝ] L2) S) := inferInstance
  rcases isEmpty_or_nonempty (multIdxE (T : L2 →ₗ[ℝ] L2) S) with hempty | hne
  · -- degenerate case: no nonzero eigenvalues — the identically-zero enumeration
    refine ⟨fun _ => 0, fun _ => 0, fun _ => Or.inl ⟨rfl, rfl⟩, ?_, fun j => Or.inl rfl⟩
    intro μ hμ hμ0
    exact (hempty.false
      (⟨⟨μ, hμ, hμ0⟩, ⟨0, hdimp ⟨μ, hμ, hμ0⟩⟩⟩ : multIdxE (T : L2 →ₗ[ℝ] L2) S)).elim
  · -- main case: enumerate the multiplicity index type via a section of a surjection
    haveI : Nonempty (multIdxE (T : L2 →ₗ[ℝ] L2) S) := hne
    obtain ⟨g, hg⟩ := exists_surjective_nat (multIdxE (T : L2 →ₗ[ℝ] L2) S)
    obtain ⟨ρ, hρ⟩ := hg.hasRightInverse
    have hρinj : Function.Injective ρ := hρ.injective
    refine ⟨enumValE ρ hρinj (fun σ : multIdxE (T : L2 →ₗ[ℝ] L2) S => σ.1.val),
      enumVecE ρ hρinj (fun σ => u σ.1), ?_, ?_, ?_⟩
    · -- (i) IsDiagEnum
      intro j
      by_cases hj : j ∈ Set.range ρ
      · rw [enumValE_of_mem hρinj hj, enumVecE_of_mem hρinj hj]
        refine Or.inr ⟨hu1 _, hu2 _⟩
      · rw [enumValE_of_notMem hρinj hj, enumVecE_of_notMem hρinj hj]
        exact Or.inl ⟨rfl, rfl⟩
    · -- (ii) fibers have exactly the eigenspace dimension
      intro μ hμ hμ0
      have heqsec : ∀ (j : ℕ) (hj : j ∈ Set.range ρ),
          ρ ((Equiv.ofInjective ρ hρinj).symm ⟨j, hj⟩) = j :=
        fun j hj => Equiv.apply_ofInjective_symm hρinj ⟨j, hj⟩
      have heq : ∀ q : {σ : multIdxE (T : L2 →ₗ[ℝ] L2) S // σ.1.val = μ},
          (Equiv.ofInjective ρ hρinj).symm ⟨ρ q.1, Set.mem_range_self q.1⟩ = q.1 := by
        intro q
        have hEq1 : Equiv.ofInjective ρ hρinj q.1 = ⟨ρ q.1, Set.mem_range_self q.1⟩ :=
          Subtype.ext rfl
        rw [← hEq1]
        exact Equiv.symm_apply_apply _ _
      have hp1 : ∀ p : {j : ℕ // enumValE ρ hρinj
          (fun σ : multIdxE (T : L2 →ₗ[ℝ] L2) S => σ.1.val) j = μ},
          p.1 ∈ Set.range ρ := by
        intro p
        have p2 : (if h : p.1 ∈ Set.range ρ then
            ((Equiv.ofInjective ρ hρinj).symm ⟨p.1, h⟩).1.val else (0:ℝ)) = μ := p.2
        by_contra hc
        rw [dif_neg hc] at p2
        exact absurd p2.symm hμ0
      have hp2 : ∀ p : {j : ℕ // enumValE ρ hρinj
          (fun σ : multIdxE (T : L2 →ₗ[ℝ] L2) S => σ.1.val) j = μ},
          ((Equiv.ofInjective ρ hρinj).symm ⟨p.1, hp1 p⟩).1.val = μ := fun p =>
        (enumValE_of_mem (fv := fun σ : multIdxE (T : L2 →ₗ[ℝ] L2) S => σ.1.val) hρinj
          (hp1 p)).symm.trans p.2
      have hE : Nat.card {j : ℕ // enumValE ρ hρinj
          (fun σ : multIdxE (T : L2 →ₗ[ℝ] L2) S => σ.1.val) j = μ}
          = Nat.card {σ : multIdxE (T : L2 →ₗ[ℝ] L2) S // σ.1.val = μ} := by
        refine Nat.card_congr ⟨fun p => ⟨(Equiv.ofInjective ρ hρinj).symm ⟨p.1, hp1 p⟩, hp2 p⟩,
          fun q => ⟨ρ q.1, ?_⟩, ?_, ?_⟩
        · have hm : ρ q.1 ∈ Set.range ρ := Set.mem_range_self q.1
          rw [enumValE_of_mem hρinj hm, heq q]
          exact q.2
        · intro p
          exact Subtype.ext (heqsec p.1 (hp1 p))
        · intro q
          exact Subtype.ext (heq q)
      refine Eq.trans hE ?_
      refine Eq.trans (natCard_multIdx_fiberE (T : L2 →ₗ[ℝ] L2) S ⟨μ, hμ, hμ0⟩) ?_
      exact Nat.card_fin _
    · -- (iii) every entry is `0` or dominated by the operator norm
      intro j
      by_cases hj : j ∈ Set.range ρ
      · rw [enumValE_of_mem hρinj hj]
        exact Or.inr (abs_eigenvalue_le_norm' (hu1 _))
      · rw [enumValE_of_notMem hρinj hj]
        exact Or.inl rfl

/-! ### Part (b): basis-invariance of the trace-class power pairing -/

set_option maxHeartbeats 8000000 in
/-- **Basis-invariance of the trace-class power pairing** (abstract form): for the
complete ON eigenfamily `(v, κ)` of the compact symmetric operator, the diagonal
pairing sum of `T^j` over ANY Hilbert basis `e` of `L2` equals the eigenvalue power
sum `∑' l, κ l ^ j`; moreover the diagonal family is summable. -/
private theorem tsum_diag_inner_pow_eq_tsum_kappaPow {TE : Module.End ℝ L2}
    (hsym : TE.IsSymmetric)
    {ι : Type} {v : ι → L2} {κ : ι → ℝ}
    (hv : Orthonormal ℝ v) (he : ∀ i, TE (v i) = κ i • v i)
    (hcomp : (span ℝ (Set.range v))ᗮ = ⊥)
    (j : ℕ) (_hj : 2 ≤ j)
    (hκabsj : Summable (fun l : ι => |κ l| ^ j))
    (e : HilbertBasis ℕ ℝ L2) :
    (∑' i : ℕ, inner ℝ ((TE ^ j) (e i)) (e i)) = ∑' l : ι, κ l ^ j ∧
      Summable (fun i : ℕ => inner ℝ ((TE ^ j) (e i)) (e i)) := by
  classical
  have hsymj := hsym.pow j
  have hpowE : ∀ l : ι, (TE ^ j) (v l) = κ l ^ j • v l :=
    fun l => end_pow_apply_eigenvector (he l) j
  -- per-fiber Parseval along `e` at the eigenfamily vector
  have hpars : ∀ l : ι, HasSum (fun i : ℕ => inner ℝ (v l) (e i) ^ 2)
      (inner ℝ (v l) (v l)) := by
    intro l
    have h1 := e.hasSum_inner_mul_inner (v l) (v l)
    refine h1.congr_fun fun i => ?_
    rw [real_inner_comm (e i) (v l), pow_two]
  have hself : ∀ l : ι, inner ℝ (v l) (v l) = 1 := by
    intro l
    rw [real_inner_self_eq_norm_sq, hv.1 l]
    norm_num
  -- per-basis-vector Parseval expansion of the diagonal pairing
  have hi : ∀ i : ℕ, HasSum
      (fun l : ι => κ l ^ j * inner ℝ (v l) (e i) ^ 2)
      (inner ℝ ((TE ^ j) (e i)) (e i)) := by
    intro i
    have h1 := (HilbertBasis.mkOfOrthogonalEqBot hv hcomp).hasSum_inner_mul_inner
      ((TE ^ j) (e i)) (e i)
    refine h1.congr_fun fun l => ?_
    simp only [HilbertBasis.coe_mkOfOrthogonalEqBot]
    calc κ l ^ j * inner ℝ (v l) (e i) ^ 2
        = inner ℝ (e i) ((TE ^ j) (v l)) * inner ℝ (v l) (e i) := by
          rw [hpowE l, real_inner_smul_right, real_inner_comm (e i) (v l)]
          ring
      _ = inner ℝ ((TE ^ j) (e i)) (v l) * inner ℝ (v l) (e i) := by
          rw [hsymj (e i) (v l)]
  -- fiberwise summability along `i`
  have h₂ : ∀ l : ι, Summable (fun i : ℕ => κ l ^ j * inner ℝ (v l) (e i) ^ 2) :=
    fun l => (summable_inner_sq_of_hilbertBasis e (v l)).const_smul (κ l ^ j)
  -- the double family is absolutely summable (per-fiber Bessel + row sums `|κ l|^j`)
  have hUncurryAbs : Summable
      (fun q : ι × ℕ => |κ q.1 ^ j * inner ℝ (v q.1) (e q.2) ^ 2|) := by
    have hD1 : ∀ l : ι, Summable (fun i : ℕ => |κ l ^ j * inner ℝ (v l) (e i) ^ 2|) :=
      fun l => ((summable_inner_sq_of_hilbertBasis e (v l)).const_smul (|κ l| ^ j)).congr
        fun i => (smul_eq_mul _ _).trans (abs_rpow_mul_sq _ _ _).symm
    have hrow : ∀ l : ι,
        HasSum (fun i : ℕ => |κ l ^ j * inner ℝ (v l) (e i) ^ 2|) (|κ l| ^ j) := by
      intro l
      have hx : HasSum (fun i : ℕ => |κ l| ^ j * inner ℝ (v l) (e i) ^ 2)
          (|κ l| ^ j * inner ℝ (v l) (v l)) := (hpars l).const_smul (|κ l| ^ j)
      rw [hself l, mul_one] at hx
      exact hx.congr_fun fun i => abs_rpow_mul_sq _ _ _
    have hD2 : Summable (fun l : ι => ∑' i : ℕ, |κ l ^ j * inner ℝ (v l) (e i) ^ 2|) :=
      hκabsj.congr fun l => (hrow l).tsum_eq.symm
    have hGabs : Summable
        (fun q : ι × ℕ => |κ q.1 ^ j * inner ℝ (v q.1) (e q.2) ^ 2|) :=
      (summable_prod_of_nonneg (fun q => abs_nonneg _)).mpr ⟨hD1, hD2⟩
    refine summable_abs_iff.mp (hGabs.of_norm_bounded fun q => ?_)
    simp only [Real.norm_eq_abs, abs_abs]
    exact le_refl _
  -- swap the two iterated sums
  have hUncurry : Summable (fun q : ι × ℕ => κ q.1 ^ j * inner ℝ (v q.1) (e q.2) ^ 2) :=
    summable_abs_iff.mp hUncurryAbs
  have hcomm : (∑' i : ℕ, ∑' l : ι, κ l ^ j * inner ℝ (v l) (e i) ^ 2)
      = (∑' l : ι, ∑' i : ℕ, κ l ^ j * inner ℝ (v l) (e i) ^ 2) :=
    Summable.tsum_comm' hUncurry h₂ (fun i => (hi i).summable)
      (f := fun (l : ι) (i : ℕ) => κ l ^ j * inner ℝ (v l) (e i) ^ 2)
  have hts : (∑' i : ℕ, inner ℝ ((TE ^ j) (e i)) (e i))
      = ∑' l : ι, κ l ^ j := by
    calc (∑' i : ℕ, inner ℝ ((TE ^ j) (e i)) (e i))
        = ∑' i : ℕ, ∑' l : ι, κ l ^ j * inner ℝ (v l) (e i) ^ 2 :=
          tsum_congr fun i => (hi i).tsum_eq.symm
      _ = ∑' l : ι, ∑' i : ℕ, κ l ^ j * inner ℝ (v l) (e i) ^ 2 := hcomm
      _ = ∑' l : ι, κ l ^ j * inner ℝ (v l) (v l) := by
          refine tsum_congr fun l => ?_
          have hx : HasSum (fun i : ℕ => κ l ^ j * inner ℝ (v l) (e i) ^ 2)
              (κ l ^ j * inner ℝ (v l) (v l)) := (hpars l).const_smul (κ l ^ j)
          exact hx.tsum_eq
      _ = ∑' l : ι, κ l ^ j := tsum_congr fun l => by rw [hself l, mul_one]
  refine ⟨hts, ?_⟩
  -- diagonal-family summability from the signed double family (column direction)
  have hColSigned : Summable (fun q : ℕ × ι => κ q.2 ^ j * inner ℝ (v q.2) (e q.1) ^ 2) :=
    hUncurry.prod_symm
  have hcol₂ : Summable (fun i : ℕ => ∑' l : ι, κ l ^ j * inner ℝ (v l) (e i) ^ 2) :=
    hColSigned.prod
  exact hcol₂.congr fun i => (hi i).tsum_eq

/-! ### Part (c): the eigenvalue power sum equals the enumerated power sum -/

/-- **The eigen-evaluation at power `j`** (fiber bookkeeping, power- and
sign-agnostic; abstract form): for the complete ON eigenfamily `(v, κ)` and the
multiplicity-exact enumeration `(val, vec)`, `∑' l, κ l ^ j = ∑' m, val m ^ j`. -/
private theorem tsum_kappaPow_eq_tsum_valPow {T : L2 →L[ℝ] L2}
    (hCompact : IsCompactOperator T)
    (hsym : (↑T : L2 →ₗ[ℝ] L2).IsSymmetric)
    {ι : Type} {v : ι → L2} {κ : ι → ℝ}
    (hv : Orthonormal ℝ v) (he : ∀ i, (T : L2 →ₗ[ℝ] L2) (v i) = κ i • v i)
    (hcomp : (span ℝ (Set.range v))ᗮ = ⊥)
    {val : ℕ → ℝ} {vec : ℕ → L2}
    (hdiag : IsDiagEnum (T : L2 →ₗ[ℝ] L2) val vec)
    (hmult : ∀ μ : ℝ, Module.End.HasEigenvalue (T : L2 →ₗ[ℝ] L2) μ → μ ≠ 0 →
      Nat.card {m : ℕ // val m = μ}
        = Module.finrank ℝ (Module.End.eigenspace (T : L2 →ₗ[ℝ] L2) μ))
    (j : ℕ) (hj : 2 ≤ j)
    (hκabsj : Summable (fun l : ι => |κ l| ^ j)) :
    (∑' l : ι, κ l ^ j) = (∑' m : ℕ, val m ^ j) := by
  classical
  have hvz : ∀ l : ι, v l ≠ 0 := fun l =>
    norm_ne_zero_iff.mp (by rw [hv.1 l]; norm_num)
  have hκev : ∀ l : ι, Module.End.HasEigenvalue (T : L2 →ₗ[ℝ] L2) (κ l) := fun l =>
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr (he l), hvz l⟩
  have hfrpos : ∀ {μ : ℝ}, Module.End.HasEigenvalue (T : L2 →ₗ[ℝ] L2) μ → μ ≠ 0 →
      0 < Module.finrank ℝ (Module.End.eigenspace (T : L2 →ₗ[ℝ] L2) μ) :=
    fun hμev hμ0 => finrank_eigenspace_pos' hCompact hμev hμ0
  -- the `val`-fiber at a nonzero eigenvalue is finite (it has positive cardinality)
  have hvalFfin : ∀ {μ : ℝ}, Module.End.HasEigenvalue (T : L2 →ₗ[ℝ] L2) μ → μ ≠ 0 →
      ({m : ℕ | val m = μ} : Set ℕ).Finite := by
    intro μ hμev hμ0
    by_contra hinf
    haveI hI : ({m : ℕ | val m = μ} : Set ℕ).Infinite := hinf
    haveI hsub : Infinite {m : ℕ // val m = μ} := hI.to_subtype
    have h0 : Nat.card {m : ℕ // val m = μ} = 0 := Nat.card_eq_zero.mpr (Or.inr hsub)
    rw [hmult μ hμev hμ0] at h0
    exact (hfrpos hμev hμ0).ne.symm h0
  have hκFfin : ∀ {μ : ℝ}, Module.End.HasEigenvalue (T : L2 →ₗ[ℝ] L2) μ → μ ≠ 0 →
      ({l : ι | κ l = μ} : Set ι).Finite := by
    intro μ hμev hμ0
    by_contra hinf
    haveI hI : ({l : ι | κ l = μ} : Set ι).Infinite := hinf
    haveI hsub : Infinite {l : ι // κ l = μ} := hI.to_subtype
    have h0 : Nat.card {l : ι // κ l = μ} = 0 := Nat.card_eq_zero.mpr (Or.inr hsub)
    rw [natCard_kappaFiber_eq_finrank' hCompact hsym hv he hcomp hμev hμ0] at h0
    exact (hfrpos hμev hμ0).ne.symm h0
  have hNmE : ∀ {μ : ℝ}, Module.End.HasEigenvalue (T : L2 →ₗ[ℝ] L2) μ → μ ≠ 0 →
      valFiberCard val μ
        = (Module.finrank ℝ (Module.End.eigenspace (T : L2 →ₗ[ℝ] L2) μ) : ℝ) := by
    intro μ hμev hμ0
    exact congrArg Nat.cast (hmult μ hμev hμ0)
  -- per-`κ`-level: the coupling family over `m` sums to `κ l ^ j`
  have hL : ∀ l : ι, HasSum
      (fun m : ℕ => (if val m = κ l then κ l ^ j / valFiberCard val (κ l) else 0))
      (κ l ^ j) := by
    intro l
    by_cases hzl : κ l = 0
    · have hz : κ l ^ j = 0 := by rw [hzl, zero_pow (by omega : (j:ℕ) ≠ 0)]
      have hfam : ∀ m : ℕ,
          (if val m = κ l then κ l ^ j / valFiberCard val (κ l) else 0) = 0 := by
        intro m
        by_cases heq : val m = κ l
        · rw [if_pos heq, hz, zero_div]
        · rw [if_neg heq]
      have h1 : HasSum (fun _ : ℕ => (0:ℝ)) (κ l ^ j) := by
        rw [hz]
        exact hasSum_zero
      exact h1.congr_fun fun m => hfam m
    · have hμev := hκev l
      have hfin := hvalFfin hμev hzl
      have h1 := hasSum_fiber (g := val) (c := κ l)
        (a := κ l ^ j / valFiberCard val (κ l)) hfin
      have hne : ((Module.finrank ℝ
          (Module.End.eigenspace (T : L2 →ₗ[ℝ] L2) (κ l)) : ℕ) : ℝ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (ne_of_gt (hfrpos hμev hzl))
      have hval2 : (κ l ^ j / valFiberCard val (κ l))
          * (Nat.card {m : ℕ // val m = κ l} : ℝ) = κ l ^ j := by
        show (κ l ^ j / ((Nat.card {m : ℕ // val m = κ l} : ℕ) : ℝ))
          * ((Nat.card {m : ℕ // val m = κ l} : ℕ) : ℝ) = κ l ^ j
        rw [hmult (κ l) hμev hzl, div_mul_eq_mul_div, mul_div_cancel_right₀ _ hne]
      rw [hval2] at h1
      exact h1
  -- per-`val`-level: the coupling family over `l` sums to `val m ^ j`
  have hR : ∀ m : ℕ, HasSum
      (fun l : ι => (if val m = κ l then κ l ^ j / valFiberCard val (κ l) else 0))
      (val m ^ j) := by
    intro m
    by_cases hzm : val m = 0
    · have hzf : val m ^ j = 0 := by rw [hzm, zero_pow (by omega : (j:ℕ) ≠ 0)]
      have hfam : ∀ l : ι,
          (if val m = κ l then κ l ^ j / valFiberCard val (κ l) else 0) = 0 := by
        intro l
        by_cases heq : val m = κ l
        · rw [if_pos heq, show κ l ^ j = 0 from by
            rw [show κ l = 0 from heq.symm.trans hzm, zero_pow (by omega : (j:ℕ) ≠ 0)],
            zero_div]
        · rw [if_neg heq]
      have h1 : HasSum (fun _ : ι => (0:ℝ)) (val m ^ j) := by
        rw [hzf]
        exact hasSum_zero
      exact h1.congr_fun fun l => hfam l
    · rcases hdiag m with ⟨hv0, _⟩ | hv0
      · exact absurd hv0 hzm
      · have hμev : Module.End.HasEigenvalue (T : L2 →ₗ[ℝ] L2) (val m) :=
          Module.End.hasEigenvalue_of_hasEigenvector hv0.1
        have hfinκ := hκFfin hμev hzm
        have h1 := hasSum_fiber (g := κ) (c := val m)
          (a := val m ^ j / valFiberCard val (val m)) hfinκ
        have hne : ((Module.finrank ℝ
            (Module.End.eigenspace (T : L2 →ₗ[ℝ] L2) (val m)) : ℕ) : ℝ) ≠ 0 :=
          Nat.cast_ne_zero.mpr (ne_of_gt (hfrpos hμev hzm))
        have hval2 : (val m ^ j / valFiberCard val (val m))
            * (Nat.card {l : ι // κ l = val m} : ℝ) = val m ^ j := by
          rw [hNmE hμev hzm,
            natCard_kappaFiber_eq_finrank' hCompact hsym hv he hcomp hμev hzm,
            div_mul_eq_mul_div, mul_div_cancel_right₀ _ hne]
        rw [hval2] at h1
        refine h1.congr_fun fun l => ?_
        by_cases h : val m = κ l
        · rw [if_pos h, if_pos h.symm, ← h]
        · rw [if_neg h, if_neg (fun hc => h hc.symm)]
  -- absolute summability of the coupling family over `ι × ℕ`
  have hUncurryAbs : Summable (fun q : ι × ℕ =>
      |(if val q.2 = κ q.1 then κ q.1 ^ j / valFiberCard val (κ q.1) else 0 : ℝ)|) := by
    have hD1 : ∀ l : ι, Summable (fun m : ℕ =>
        |(if val m = κ l then κ l ^ j / valFiberCard val (κ l) else 0 : ℝ)|) :=
      fun l => (hL l).summable.abs
    have hrow : ∀ l : ι, HasSum (fun m : ℕ =>
        |(if val m = κ l then κ l ^ j / valFiberCard val (κ l) else 0 : ℝ)|)
        (|κ l| ^ j) := by
        intro l
        by_cases hzl : κ l = 0
        · have hf : ∀ m : ℕ,
              |(if val m = κ l then κ l ^ j / valFiberCard val (κ l) else 0 : ℝ)| = 0 := by
            intro m
            by_cases heq : val m = κ l
            · rw [if_pos heq, show κ l ^ j = 0 from by
                rw [hzl, zero_pow (by omega : (j:ℕ) ≠ 0)], zero_div, abs_zero]
            · rw [if_neg heq, abs_zero]
          rw [show |κ l| ^ j = 0 from by
            rw [hzl, abs_zero, zero_pow (by omega : (j:ℕ) ≠ 0)]]
          exact hasSum_zero.congr_fun fun m => hf m
        · have hμev := hκev l
          have hfin := hvalFfin hμev hzl
          have h1 := hasSum_fiber (g := val) (c := κ l)
            (a := |κ l| ^ j / valFiberCard val (κ l)) hfin
          have hNnn : 0 ≤ valFiberCard val (κ l) := by
            show (0:ℝ) ≤ ((Nat.card {m : ℕ // val m = κ l} : ℕ) : ℝ)
            exact_mod_cast Nat.zero_le _
          have hne : ((Module.finrank ℝ
              (Module.End.eigenspace (T : L2 →ₗ[ℝ] L2) (κ l)) : ℕ) : ℝ) ≠ 0 :=
            Nat.cast_ne_zero.mpr (ne_of_gt (hfrpos hμev hzl))
          have hval2 : (|κ l| ^ j / valFiberCard val (κ l))
              * (Nat.card {m : ℕ // val m = κ l} : ℝ) = |κ l| ^ j := by
            show (|κ l| ^ j / ((Nat.card {m : ℕ // val m = κ l} : ℕ) : ℝ))
              * ((Nat.card {m : ℕ // val m = κ l} : ℕ) : ℝ) = |κ l| ^ j
            rw [hmult (κ l) hμev hzl, div_mul_eq_mul_div, mul_div_cancel_right₀ _ hne]
          rw [hval2] at h1
          refine h1.congr_fun fun m => ?_
          by_cases heq : val m = κ l
          · rw [if_pos heq, if_pos heq, abs_div, abs_pow, abs_of_nonneg hNnn]
          · rw [if_neg heq, if_neg heq, abs_zero]
    have hD2 : Summable (fun l : ι => ∑' m : ℕ,
        |(if val m = κ l then κ l ^ j / valFiberCard val (κ l) else 0 : ℝ)|) :=
      hκabsj.congr fun l => (hrow l).tsum_eq.symm
    exact (summable_prod_of_nonneg (fun q => abs_nonneg _)).mpr ⟨hD1, hD2⟩
  have hUncurry : Summable (fun q : ι × ℕ =>
      (if val q.2 = κ q.1 then κ q.1 ^ j / valFiberCard val (κ q.1) else 0)) :=
    summable_abs_iff.mp (hUncurryAbs.of_norm_bounded fun q => by
      rw [Real.norm_eq_abs]
      exact (abs_of_nonneg (abs_nonneg _)).le)
  -- swap the two iterated sums
  have hcomm : (∑' l : ι, ∑' i : ℕ,
        (if val i = κ l then κ l ^ j / valFiberCard val (κ l) else 0))
      = (∑' i : ℕ, ∑' l : ι,
        (if val i = κ l then κ l ^ j / valFiberCard val (κ l) else 0)) :=
    (Summable.tsum_comm' hUncurry (fun l => (hL l).summable) (fun i => (hR i).summable)
      (f := fun (l : ι) (i : ℕ) =>
        if val i = κ l then κ l ^ j / valFiberCard val (κ l) else 0)).symm
  calc (∑' l : ι, κ l ^ j)
      = ∑' l : ι, ∑' m : ℕ,
          (if val m = κ l then κ l ^ j / valFiberCard val (κ l) else 0) :=
        tsum_congr fun l => (hL l).tsum_eq.symm
    _ = ∑' m : ℕ, ∑' l : ι,
          (if val m = κ l then κ l ^ j / valFiberCard val (κ l) else 0) := hcomm
    _ = ∑' m : ℕ, val m ^ j := tsum_congr fun m => (hR m).tsum_eq

/-! ### Summability transfer between the eigenfamily and the enumeration -/

/-- **Weighted summability transfer** (generalized fiber bookkeeping): with the
level weight `w` (nonnegative, vanishing at `0`), summability of `w ∘ κ` over the
complete eigenfamily implies summability of `w ∘ val` over the enumeration. -/
private theorem summable_val_of_summable_kappa {T : L2 →L[ℝ] L2}
    (hCompact : IsCompactOperator T)
    (hsym : (↑T : L2 →ₗ[ℝ] L2).IsSymmetric)
    {ι : Type} {v : ι → L2} {κ : ι → ℝ}
    (hv : Orthonormal ℝ v) (he : ∀ i, (T : L2 →ₗ[ℝ] L2) (v i) = κ i • v i)
    (hcomp : (span ℝ (Set.range v))ᗮ = ⊥)
    {val : ℕ → ℝ} {vec : ℕ → L2}
    (hdiag : IsDiagEnum (T : L2 →ₗ[ℝ] L2) val vec)
    (hmult : ∀ μ : ℝ, Module.End.HasEigenvalue (T : L2 →ₗ[ℝ] L2) μ → μ ≠ 0 →
      Nat.card {m : ℕ // val m = μ}
        = Module.finrank ℝ (Module.End.eigenspace (T : L2 →ₗ[ℝ] L2) μ))
    {w : ℝ → ℝ} (hw0 : w 0 = 0) (hw : ∀ μ, 0 ≤ w μ)
    (hκ : Summable (fun l : ι => w (κ l))) :
    Summable (fun m : ℕ => w (val m)) := by
  classical
  have hvz : ∀ i : ι, v i ≠ 0 := fun i => norm_ne_zero_iff.mp (by rw [hv.1 i]; norm_num)
  have hve : ∀ i : ι, Module.End.HasEigenvector (T : L2 →ₗ[ℝ] L2) (κ i) (v i) := fun i =>
    Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr (he i), hvz i⟩
  have hfrPos : ∀ {μ : ℝ}, Module.End.HasEigenvalue (T : L2 →ₗ[ℝ] L2) μ → μ ≠ 0 →
      0 < Module.finrank ℝ (Module.End.eigenspace (T : L2 →ₗ[ℝ] L2) μ) :=
    fun hμev hμ0 => finrank_eigenspace_pos' hCompact hμev hμ0
  -- the val-side fiber set is finite (from the multiplicity identity)
  have hvalFfin : ∀ {μ : ℝ}, Module.End.HasEigenvalue (T : L2 →ₗ[ℝ] L2) μ → μ ≠ 0 →
      ({j : ℕ | val j = μ} : Set ℕ).Finite := by
    intro μ hμev hμ0
    by_contra hinf
    haveI hI : ({j : ℕ | val j = μ} : Set ℕ).Infinite := hinf
    haveI hsub : Infinite {j : ℕ // val j = μ} := hI.to_subtype
    have h0 : Nat.card {j : ℕ // val j = μ} = 0 := Nat.card_eq_zero.mpr (Or.inr hsub)
    have hnc := hmult μ hμev hμ0
    rw [h0] at hnc
    exact absurd hnc.symm (by linarith [hfrPos hμev hμ0])
  -- the κ-side fiber set is finite
  have hκFfin : ∀ {μ : ℝ}, Module.End.HasEigenvalue (T : L2 →ₗ[ℝ] L2) μ → μ ≠ 0 →
      ({i : ι | κ i = μ} : Set ι).Finite :=
    fun hμev hμ0 => kappaFiberFinite hCompact hv he hμev hμ0
  refine summable_of_sum_le (c := ∑' l : ι, w (κ l)) (fun m => hw (val m)) fun u => ?_
  set u' := u.filter (fun j => val j ≠ 0) with hu'
  have hdrop : ∑ j ∈ u, w (val j) = ∑ j ∈ u', w (val j) :=
    (Finset.sum_subset (Finset.filter_subset (fun j => val j ≠ 0) u) (fun j hj hj' => by
      have h0 : val j = 0 := by
        by_contra hne
        exact hj' (Finset.mem_filter.mpr ⟨hj, hne⟩)
      rw [h0, hw0])).symm
  set Lv : Finset ℝ := u'.image val with hLv
  have hLvE : ∀ μ ∈ Lv, Module.End.HasEigenvalue (T : L2 →ₗ[ℝ] L2) μ ∧ μ ≠ 0 := by
    intro μ hμ
    obtain ⟨j0, hj0u, hjμ⟩ := Finset.mem_image.mp hμ
    have hvj0 : val j0 ≠ 0 := (Finset.mem_filter.mp hj0u).2
    refine ⟨?_, ?_⟩
    · rcases hdiag j0 with ⟨h0, _⟩ | hv0
      · exact absurd h0 hvj0
      · exact Module.End.hasEigenvalue_of_hasEigenvector (by rw [← hjμ]; exact hv0.1)
    · rw [← hjμ]; exact hvj0
  -- the val-fiber inside u' is at most the full fiber
  have hcard : ∀ μ : ℝ, Module.End.HasEigenvalue (T : L2 →ₗ[ℝ] L2) μ → μ ≠ 0 →
      (u'.filter (fun j => val j = μ)).card ≤ Nat.card {j : ℕ // val j = μ} := by
    intro μ hμev hμ0
    haveI hfin : Fintype {j : ℕ // val j = μ} :=
      @Fintype.ofFinite {j : ℕ // val j = μ} (hvalFfin hμev hμ0).to_subtype
    have hinj : Function.Injective
        (fun m : {x : ℕ // x ∈ u'.filter (fun j => val j = μ)} =>
          (⟨m.1, (Finset.mem_filter.mp m.2).2⟩ : {j : ℕ // val j = μ})) := by
      intro m m' h
      exact Subtype.ext (by simpa using congrArg Subtype.val h)
    calc (u'.filter (fun j => val j = μ)).card
        = Fintype.card {x : ℕ // x ∈ u'.filter (fun j => val j = μ)} :=
          (Fintype.card_coe _).symm
      _ ≤ Fintype.card {j : ℕ // val j = μ} := Fintype.card_le_of_injective _ hinj
      _ = Nat.card {j : ℕ // val j = μ} := Nat.card_eq_fintype_card.symm
  -- per-level transport into the κ-fiber
  have hlevel : ∀ (μ : ℝ) (hμev : Module.End.HasEigenvalue (T : L2 →ₗ[ℝ] L2) μ)
      (hμ0 : μ ≠ 0), (u'.filter (fun j => val j = μ)).card * w μ
        ≤ ∑ i ∈ (hκFfin hμev hμ0).toFinset, w (κ i) := by
    intro μ hμev hμ0
    have hcard' := hcard μ hμev hμ0
    have hcard2 : Nat.card {j : ℕ // val j = μ}
        = Nat.card {i : ι // κ i = μ} := by
      rw [hmult μ hμev hμ0,
        natCard_kappaFiber_eq_finrank' hCompact hsym hv he hcomp hμev hμ0]
    have hκFfin := hκFfin hμev hμ0
    haveI : Fintype ↥({i : ι | κ i = μ} : Set ι) := hκFfin.fintype
    have hsumF : ∑ i ∈ hκFfin.toFinset, w (κ i) = hκFfin.toFinset.card * w μ := by
      have hall : ∀ i ∈ hκFfin.toFinset, κ i = μ := fun i hi =>
        hκFfin.mem_toFinset.mp hi
      calc ∑ i ∈ hκFfin.toFinset, w (κ i)
          = ∑ i ∈ hκFfin.toFinset, w μ :=
            Finset.sum_congr rfl fun i hi => by rw [hall i hi]
        _ = hκFfin.toFinset.card * w μ := by rw [Finset.sum_const, nsmul_eq_mul]
    have hcardF : hκFfin.toFinset.card = Nat.card {i : ι // κ i = μ} :=
      hκFfin.card_toFinset.trans Nat.card_eq_fintype_card.symm
    calc (u'.filter (fun j => val j = μ)).card * w μ
        ≤ Nat.card {j : ℕ // val j = μ} * w μ :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard') (hw μ)
      _ = Nat.card {i : ι // κ i = μ} * w μ := by rw [hcard2]
      _ = ∑ i ∈ hκFfin.toFinset, w (κ i) := by rw [hsumF, hcardF]
  -- assemble the level masses into the disjoint union of κ-fibers
  set U : Finset ι := Lv.attach.biUnion (fun p : {x : ℝ // x ∈ Lv} =>
    ((hκFfin (hLvE p.1 p.2).1 (hLvE p.1 p.2).2).toFinset)) with hUdef
  have hpd : Set.PairwiseDisjoint (↑Lv.attach : Set {x : ℝ // x ∈ Lv})
      fun p : {x : ℝ // x ∈ Lv} =>
        ((hκFfin (hLvE p.1 p.2).1 (hLvE p.1 p.2).2).toFinset) := by
    intro x _ y _ hxy
    refine Set.Finite.disjoint_toFinset.mpr ?_
    rw [Set.disjoint_left]
    intro i hi1 hi2
    exact hxy (Subtype.ext (hi1.symm.trans hi2))
  calc ∑ j ∈ u, w (val j)
      = ∑ μ ∈ Lv, (u'.filter (fun j => val j = μ)).card * w μ := by
        rw [hdrop, finset_sum_w_fiberGroup, ← hLv]
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [Finset.filter_congr (fun j (_ : j ∈ u') => eq_comm :
          ∀ j ∈ u', μ = val j ↔ val j = μ)]
    _ ≤ ∑ i ∈ U, w (κ i) := by
        rw [hUdef, Finset.sum_biUnion hpd, ← Finset.sum_attach]
        refine Finset.sum_le_sum fun p _hp => ?_
        exact hlevel p.1 (hLvE p.1 p.2).1 (hLvE p.1 p.2).2
    _ ≤ ∑' i, w (κ i) := Summable.sum_le_tsum _ (fun i _ => hw (κ i)) hκ

/-! ### The main bridge -/

set_option maxHeartbeats 4000000 in
/-- **hBridge_clm — the end-level trace bridge**: for a compact self-adjoint CLM
`T` whose matrix squares are summable with a basis-uniform bound (`hTHS`; the
abstract HS-type input, delivered downstream by the A7 estimate), and a
multiplicity-exact diagonal enumeration `(val, vec)`:

* the enumeration is square-summable: `Summable (fun m => val m ^ 2)`;
* for every power `j ≥ 2` and every Hilbert basis `e` of `L2`, the diagonal pairing
  series `fun i => ⟪T^j (e i), e i⟫` is a genuine `HasSum` to the enumerated power
  sum `∑' m, val m ^ j`. -/
theorem hBridge_clm {T : L2 →L[ℝ] L2}
    (hTsym : (↑T : L2 →ₗ[ℝ] L2).IsSymmetric) (hTcompact : IsCompactOperator T)
    (hTHS : ∃ C : ℝ, 0 ≤ C ∧ ∀ e : HilbertBasis ℕ ℝ L2,
      Summable (fun p : ℕ × ℕ => (inner ℝ (e p.1) (T (e p.2))) ^ 2) ∧
        (∑' p : ℕ × ℕ, (inner ℝ (e p.1) (T (e p.2))) ^ 2) ≤ C)
    {val : ℕ → ℝ} {vec : ℕ → L2}
    (hdiag : IsDiagEnum (T : L2 →ₗ[ℝ] L2) val vec)
    (hmult : ∀ μ : ℝ, Module.End.HasEigenvalue (T : L2 →ₗ[ℝ] L2) μ → μ ≠ 0 →
      Nat.card {m : ℕ // val m = μ}
        = Module.finrank ℝ (Module.End.eigenspace (T : L2 →ₗ[ℝ] L2) μ))
    (j : ℕ) (hj : 2 ≤ j) (e : HilbertBasis ℕ ℝ L2) :
    Summable (fun m : ℕ => val m ^ 2) ∧
    HasSum (fun i : ℕ => inner ℝ ((T ^ j) (e i)) (e i)) (∑' m : ℕ, val m ^ j) := by
  classical
  -- the complete ON eigenfamily of the abstract compact self-adjoint operator
  obtain ⟨ι, v, κ, hv, he, hcomp⟩ :=
    exists_complete_eigenfamily_of_symmetric (T := (T : L2 →ₗ[ℝ] L2)) hTsym
      (fun μ hμ => finiteDimensional_eigenspace' hTcompact hμ)
      (ContinuousLinearMap.isClosed_ker T)
      (ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hTcompact hTsym)
  have hvz : ∀ l : ι, v l ≠ 0 := fun l =>
    norm_ne_zero_iff.mp (by rw [hv.1 l]; norm_num)
  have hκvec : ∀ l : ι, Module.End.HasEigenvector (T : L2 →ₗ[ℝ] L2) (κ l) (v l) :=
    fun l => Module.End.hasEigenvector_iff.mpr
      ⟨Module.End.mem_eigenspace_iff.mpr (he l), hvz l⟩
  have hκabs : ∀ l : ι, |κ l| ≤ ‖T‖ := fun l => abs_eigenvalue_le_norm' (hκvec l)
  -- squared eigenvalues are summable (the matrix-square input on the basis `e`)
  have hκsq : Summable (fun l : ι => κ l ^ 2) :=
    summable_kappaSq_of_matrixSq hTsym hTHS hv he e
  -- the `j`-th absolute powers are summable (interpolation against the op norm)
  have hκabsj : Summable (fun l : ι => |κ l| ^ j) := by
    have key : ∀ l : ι, |κ l| ^ j ≤ ‖T‖ ^ (j - 2) * κ l ^ 2 := by
      intro l
      have h1 := hκabs l
      have h3 : |κ l| ^ j = |κ l| ^ (j - 2) * |κ l| ^ 2 := by
        rw [← pow_add (|κ l|) (j - 2) 2]
        exact congrArg (fun n : ℕ => |κ l| ^ n) (by omega)
      calc |κ l| ^ j = |κ l| ^ (j - 2) * |κ l| ^ 2 := h3
        _ = |κ l| ^ (j - 2) * κ l ^ 2 := by rw [sq_abs]
        _ ≤ ‖T‖ ^ (j - 2) * κ l ^ 2 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) h1 (j - 2))
            (sq_nonneg (κ l))
    have hcs : Summable (fun l : ι => ‖T‖ ^ (j - 2) * κ l ^ 2) :=
      hκsq.const_smul (‖T‖ ^ (j - 2))
    exact Summable.of_nonneg_of_le (fun l => pow_nonneg (abs_nonneg (κ l)) j) key hcs
  -- the diagonal expansion, with the diagonal family summable
  obtain ⟨hts, hdiagSumm⟩ :=
    tsum_diag_inner_pow_eq_tsum_kappaPow hTsym hv he hcomp j hj hκabsj e
  -- the enumeration side: square-summability and j-th absolute powers
  have hvalSum2 : Summable (fun m : ℕ => val m ^ 2) :=
    summable_val_of_summable_kappa hTcompact hTsym hv he hcomp hdiag hmult
      (by norm_num) (fun μ => sq_nonneg μ) hκsq
  have hvalAbsj : Summable (fun m : ℕ => |val m| ^ j) :=
    summable_val_of_summable_kappa (w := fun μ => |μ| ^ j) hTcompact hTsym hv he hcomp
      hdiag hmult (by rw [abs_zero, zero_pow (by omega)])
      (fun μ => pow_nonneg (abs_nonneg μ) j) hκabsj
  have hvalj : Summable (fun m : ℕ => val m ^ j) :=
    summable_abs_iff.mp (hvalAbsj.congr fun m => (abs_pow (val m) j).symm)
  -- convert the CLM-power to the End-power in the HasSum family
  have hpowconv : ∀ i : ℕ, ((T : L2 →ₗ[ℝ] L2) ^ j) (e i) = (T ^ j) (e i) :=
    fun i => DFunLike.congr_fun (ContinuousLinearMap.coe_pow T j).symm (e i)
  have hdiagSummCLM : Summable (fun i : ℕ => inner ℝ ((T ^ j) (e i)) (e i)) := by
    refine hdiagSumm.congr fun i => ?_
    show inner ℝ (((T : L2 →ₗ[ℝ] L2) ^ j) (e i)) (e i)
        = inner ℝ ((T ^ j) (e i)) (e i)
    rw [hpowconv i]
  have hEq : ∀ i : ℕ, inner ℝ ((T ^ j) (e i)) (e i)
      = inner ℝ (((T : L2 →ₗ[ℝ] L2) ^ j) (e i)) (e i) :=
    fun i => congrArg (fun x : L2 => inner ℝ x (e i)) (hpowconv i).symm
  have htsCLM : (∑' i : ℕ, inner ℝ ((T ^ j) (e i)) (e i)) = ∑' l : ι, κ l ^ j := by
    refine Eq.trans (tsum_congr fun i => ?_) hts
    exact hEq i
  have hkeq := tsum_kappaPow_eq_tsum_valPow hTcompact hTsym hv he hcomp hdiag hmult j hj
    hκabsj
  refine ⟨hvalSum2, ?_⟩
  have h1 : HasSum (fun i : ℕ => inner ℝ ((T ^ j) (e i)) (e i))
      (∑' i : ℕ, inner ℝ ((T ^ j) (e i)) (e i)) := hdiagSummCLM.hasSum
  rw [htsCLM, hkeq] at h1
  exact h1

/-- **The frozen tsum form of the end-level trace bridge**: the diagonal pairing
sum of `T^j` over every Hilbert basis equals the enumerated power sum
`∑' m, val m ^ j` (both sides are genuine convergent series, by `hBridge_clm`). -/
theorem hBridge_clm_tsum {T : L2 →L[ℝ] L2}
    (hTsym : (↑T : L2 →ₗ[ℝ] L2).IsSymmetric) (hTcompact : IsCompactOperator T)
    (hTHS : ∃ C : ℝ, 0 ≤ C ∧ ∀ e : HilbertBasis ℕ ℝ L2,
      Summable (fun p : ℕ × ℕ => (inner ℝ (e p.1) (T (e p.2))) ^ 2) ∧
        (∑' p : ℕ × ℕ, (inner ℝ (e p.1) (T (e p.2))) ^ 2) ≤ C)
    {val : ℕ → ℝ} {vec : ℕ → L2}
    (hdiag : IsDiagEnum (T : L2 →ₗ[ℝ] L2) val vec)
    (hmult : ∀ μ : ℝ, Module.End.HasEigenvalue (T : L2 →ₗ[ℝ] L2) μ → μ ≠ 0 →
      Nat.card {m : ℕ // val m = μ}
        = Module.finrank ℝ (Module.End.eigenspace (T : L2 →ₗ[ℝ] L2) μ))
    (j : ℕ) (hj : 2 ≤ j) (e : HilbertBasis ℕ ℝ L2) :
    (∑' i : ℕ, inner ℝ ((T ^ j) (e i)) (e i)) = ∑' m : ℕ, val m ^ j := by
  obtain ⟨-, h⟩ := hBridge_clm hTsym hTcompact hTHS hdiag hmult j hj e
  exact h.tsum_eq

end HS

end
