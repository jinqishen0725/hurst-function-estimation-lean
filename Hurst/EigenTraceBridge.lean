import Hurst.EigenFamilySplice
import Hurst.CapstoneV3Closed
import Hurst.TensorParsevalTracePair
import Hurst.HSNormIdentity
import Hurst.HSOperatorLayer4
import Hurst.SpectralEnumeration
import Hurst.GeneralKHasSumAssembled

/-!
# hBridge — trace-class diagonal-sum basis-invariance + eigen-evaluation

This file discharges the `hBridge` hypothesis consumed by
`Hurst.GeneralKHasSumFinal` (the operator-side bridge of spec §8): for a compact
symmetric kernel operator `T := TOpEnd' K hK`, a diagonal enumeration `(val, vec)`
with the multiplicity clause `hmult`, every power `j ≥ 2` and EVERY Hilbert basis
`e` of `L2`,

  `∑' i, ⟪T^j (e i), e i⟫ = ∑' m, val m ^ j`.

## Route (spec §8, reorganized)

1. **Complete ON eigenfamily** (`HS.exists_complete_eigenfamily_of_symmetric`,
   landed): eigenvectors `v l` with eigenvalues `κ l`, orthonormal, with trivially
   spanning orthocomplement; `κ²` is summable by the landed Bessel bound
   (`HS.sum_norm_TOp_sq_le`), and `|κ|^j` is summable by interpolation against the
   operator norm (`HS.abs_eigenvalue_le_norm`).
2. **Basis-invariance** (`HS.tsum_diag_inner_pow_eq_tsum_kappaPow`): expand each
   diagonal pairing `⟪T^j (e i), e i⟫` by Parseval along the eigenfamily (`T^j` is
   self-adjoint by the landed `LinearMap.IsSymmetric.pow`; eigen-action
   `T^j (v l) = κ l^j • v l`), get the double family `κ l^j · ⟪v l, e i⟫²`, swap the
   two sums by absolute convergence (`summable_prod_of_nonneg` +
   `Summable.tsum_comm'`), and collapse the inner Parseval
   `∑_i ⟪v l, e i⟫² = ‖v l‖² = 1`.  This works for ANY basis `e`.
3. **Eigen-evaluation** (`HS.tsum_kappaPow_eq_tsum_valPow`): splice the eigenfamily
   against the enumeration through the coupling double family
   `[val m = κ l] · κ l^j / valFiberCard val (κ l)`, swapped by absolute
   convergence.  On the `κ`-side each inner sum evaluates to `κ l^j` (a nonzero
   `κ l` occupies exactly `valFiberCard val (κ l) = finrank (eigenspace κ l)` slots
   of `val`, by `hmult`); on the `val`-side each inner sum evaluates to `val m^j`
   (the `κ`-fiber at `val m` has the same cardinality, by the landed power-agnostic
   `HS.natCard_kappaFiber_eq_finrank`).  This handles arbitrary (also negative)
   eigenvalues — no positivity hypothesis.
-/

set_option maxHeartbeats 1000000

noncomputable section

namespace HS

open MeasureTheory Measure Real Set Submodule
open scoped Real

variable {K : ℝ × ℝ → ℝ} {hK : HSKernel K}

/-! ### Small spectral helpers -/

/-- Nonzero eigenvalues of a compact kernel operator have positive-dimensional
eigenspaces. -/
private theorem finrank_eigenspace_pos (hCompact : IsCompactOperator (TOp K hK))
    {μ : ℝ} (hμev : Module.End.HasEigenvalue (TOpEnd' K hK) μ) (hμ0 : μ ≠ 0) :
    0 < Module.finrank ℝ (Module.End.eigenspace (TOpEnd' K hK) μ) := by
  haveI hfd := finiteDimensional_eigenspace_TOp hCompact hμ0
  obtain ⟨w, hw⟩ := hμev.exists_hasEigenvector
  haveI : Nontrivial ↥(Module.End.eigenspace (TOpEnd' K hK) μ) :=
    ⟨0, ⟨w, hw.1⟩, fun h => hw.2 (Subtype.ext_iff.mp h).symm⟩
  exact Module.finrank_pos

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

/-! ### Part (b): basis-invariance of the trace-class power pairing -/

/-- **Basis-invariance of the trace-class power pairing**: for the complete ON
eigenfamily `(v, κ)` of the compact symmetric kernel operator, the diagonal pairing
sum of `T^j` over ANY Hilbert basis `e` of `L2` equals the eigenvalue power sum
`∑' l, κ l ^ j`. -/
private theorem tsum_diag_inner_pow_eq_tsum_kappaPow
    (hsym : (↑(TOp K hK) : L2 →ₗ[ℝ] L2).IsSymmetric)
    {ι : Type} {v : ι → L2} {κ : ι → ℝ}
    (hv : Orthonormal ℝ v) (he : ∀ i, TOp K hK (v i) = κ i • v i)
    (hcomp : (span ℝ (Set.range v))ᗮ = ⊥)
    (j : ℕ) (_hj : 2 ≤ j)
    (hκabsj : Summable (fun l : ι => |κ l| ^ j))
    (e : HilbertBasis ℕ ℝ L2) :
    (∑' i : ℕ, inner ℝ ((TOpEnd' K hK ^ j) (e i)) (e i)) = ∑' l : ι, κ l ^ j := by
  classical
  have hsymj := hsym.pow j
  have hpowE : ∀ l : ι, (TOpEnd' K hK ^ j) (v l) = κ l ^ j • v l :=
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
      (inner ℝ ((TOpEnd' K hK ^ j) (e i)) (e i)) := by
    intro i
    have h1 := (HilbertBasis.mkOfOrthogonalEqBot hv hcomp).hasSum_inner_mul_inner
      ((TOpEnd' K hK ^ j) (e i)) (e i)
    refine h1.congr_fun fun l => ?_
    simp only [HilbertBasis.coe_mkOfOrthogonalEqBot]
    calc κ l ^ j * inner ℝ (v l) (e i) ^ 2
        = inner ℝ (e i) ((TOpEnd' K hK ^ j) (v l)) * inner ℝ (v l) (e i) := by
          rw [hpowE l, real_inner_smul_right, real_inner_comm (e i) (v l)]
          ring
      _ = inner ℝ ((TOpEnd' K hK ^ j) (e i)) (v l) * inner ℝ (v l) (e i) := by
          rw [hsymj (e i) (v l)]
  -- fiberwise summability along `i`
  have h₂ : ∀ l : ι, Summable (fun i : ℕ => κ l ^ j * inner ℝ (v l) (e i) ^ 2) :=
    fun l => (summable_inner_sq_of_hilbertBasis e (v l)).const_smul (κ l ^ j)
  -- the double family is absolutely summable (per-fiber Bessel + row sums `|κ l|^j`)
  have hUncurry : Summable (fun q : ι × ℕ => κ q.1 ^ j * inner ℝ (v q.1) (e q.2) ^ 2) := by
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
    rw [Real.norm_eq_abs]
    exact (abs_of_nonneg (abs_nonneg _)).le
  -- swap the two iterated sums
  have hcomm : (∑' i : ℕ, ∑' l : ι, κ l ^ j * inner ℝ (v l) (e i) ^ 2)
      = (∑' l : ι, ∑' i : ℕ, κ l ^ j * inner ℝ (v l) (e i) ^ 2) :=
    Summable.tsum_comm' hUncurry h₂ (fun i => (hi i).summable)
      (f := fun (l : ι) (i : ℕ) => κ l ^ j * inner ℝ (v l) (e i) ^ 2)
  calc (∑' i : ℕ, inner ℝ ((TOpEnd' K hK ^ j) (e i)) (e i))
      = ∑' i : ℕ, ∑' l : ι, κ l ^ j * inner ℝ (v l) (e i) ^ 2 :=
        tsum_congr fun i => (hi i).tsum_eq.symm
    _ = ∑' l : ι, ∑' i : ℕ, κ l ^ j * inner ℝ (v l) (e i) ^ 2 := hcomm
    _ = ∑' l : ι, κ l ^ j * inner ℝ (v l) (v l) := by
        refine tsum_congr fun l => ?_
        have hx : HasSum (fun i : ℕ => κ l ^ j * inner ℝ (v l) (e i) ^ 2)
            (κ l ^ j * inner ℝ (v l) (v l)) := (hpars l).const_smul (κ l ^ j)
        exact hx.tsum_eq
    _ = ∑' l : ι, κ l ^ j := tsum_congr fun l => by rw [hself l, mul_one]

/-! ### Part (c): the eigenvalue power sum equals the enumerated power sum -/

/-- **The eigen-evaluation at power `j`** (fiber bookkeeping, power- and
sign-agnostic): for the complete ON eigenfamily `(v, κ)` and the multiplicity-exact
enumeration `(val, vec)`, `∑' l, κ l ^ j = ∑' m, val m ^ j`. -/
private theorem tsum_kappaPow_eq_tsum_valPow
    (hCompact : IsCompactOperator (TOp K hK))
    (hsym : (↑(TOp K hK) : L2 →ₗ[ℝ] L2).IsSymmetric)
    {ι : Type} {v : ι → L2} {κ : ι → ℝ}
    (hv : Orthonormal ℝ v) (he : ∀ i, TOp K hK (v i) = κ i • v i)
    (hcomp : (span ℝ (Set.range v))ᗮ = ⊥)
    {val : ℕ → ℝ} {vec : ℕ → L2}
    (hdiag : IsDiagEnum (TOpEnd' K hK) val vec)
    (hmult : ∀ μ : ℝ, Module.End.HasEigenvalue (TOpEnd' K hK) μ → μ ≠ 0 →
      Nat.card {m : ℕ // val m = μ}
        = Module.finrank ℝ (Module.End.eigenspace (TOpEnd' K hK) μ))
    (j : ℕ) (hj : 2 ≤ j)
    (hκabsj : Summable (fun l : ι => |κ l| ^ j)) :
    (∑' l : ι, κ l ^ j) = (∑' m : ℕ, val m ^ j) := by
  classical
  have hvz : ∀ l : ι, v l ≠ 0 := fun l =>
    norm_ne_zero_iff.mp (by rw [hv.1 l]; norm_num)
  have hκev : ∀ l : ι, Module.End.HasEigenvalue (TOpEnd' K hK) (κ l) := fun l =>
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr (he l), hvz l⟩
  have hfrpos : ∀ {μ : ℝ}, Module.End.HasEigenvalue (TOpEnd' K hK) μ → μ ≠ 0 →
      0 < Module.finrank ℝ (Module.End.eigenspace (TOpEnd' K hK) μ) :=
    fun hμev hμ0 => finrank_eigenspace_pos hCompact hμev hμ0
  -- the `val`-fiber at a nonzero eigenvalue is finite (it has positive cardinality)
  have hvalFfin : ∀ {μ : ℝ}, Module.End.HasEigenvalue (TOpEnd' K hK) μ → μ ≠ 0 →
      ({m : ℕ | val m = μ} : Set ℕ).Finite := by
    intro μ hμev hμ0
    by_contra hinf
    haveI hI : ({m : ℕ | val m = μ} : Set ℕ).Infinite := hinf
    haveI hsub : Infinite {m : ℕ // val m = μ} := hI.to_subtype
    have h0 : Nat.card {m : ℕ // val m = μ} = 0 := Nat.card_eq_zero.mpr (Or.inr hsub)
    rw [hmult μ hμev hμ0] at h0
    exact (hfrpos hμev hμ0).ne.symm h0
  have hκFfin : ∀ {μ : ℝ}, Module.End.HasEigenvalue (TOpEnd' K hK) μ → μ ≠ 0 →
      ({l : ι | κ l = μ} : Set ι).Finite := by
    intro μ hμev hμ0
    by_contra hinf
    haveI hI : ({l : ι | κ l = μ} : Set ι).Infinite := hinf
    haveI hsub : Infinite {l : ι // κ l = μ} := hI.to_subtype
    have h0 : Nat.card {l : ι // κ l = μ} = 0 := Nat.card_eq_zero.mpr (Or.inr hsub)
    rw [natCard_kappaFiber_eq_finrank hCompact hsym hv he hcomp hμev hμ0] at h0
    exact (hfrpos hμev hμ0).ne.symm h0
  have hNmE : ∀ {μ : ℝ}, Module.End.HasEigenvalue (TOpEnd' K hK) μ → μ ≠ 0 →
      valFiberCard val μ
        = (Module.finrank ℝ (Module.End.eigenspace (TOpEnd' K hK) μ) : ℝ) := by
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
      have hne : ((Module.finrank ℝ (Module.End.eigenspace (TOpEnd' K hK) (κ l)) : ℕ) : ℝ) ≠ 0 :=
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
      · have hμev : Module.End.HasEigenvalue (TOpEnd' K hK) (val m) :=
          Module.End.hasEigenvalue_of_hasEigenvector hv0.1
        have hfinκ := hκFfin hμev hzm
        have h1 := hasSum_fiber (g := κ) (c := val m)
          (a := val m ^ j / valFiberCard val (val m)) hfinκ
        have hne : ((Module.finrank ℝ
            (Module.End.eigenspace (TOpEnd' K hK) (val m)) : ℕ) : ℝ) ≠ 0 :=
          Nat.cast_ne_zero.mpr (ne_of_gt (hfrpos hμev hzm))
        have hval2 : (val m ^ j / valFiberCard val (val m))
            * (Nat.card {l : ι // κ l = val m} : ℝ) = val m ^ j := by
          rw [hNmE hμev hzm,
            natCard_kappaFiber_eq_finrank hCompact hsym hv he hcomp hμev hzm,
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
          rw [show |κ l| ^ j = 0 from by rw [hzl, abs_zero, zero_pow (by omega : (j:ℕ) ≠ 0)]]
          exact hasSum_zero.congr_fun fun m => hf m
        · have hμev := hκev l
          have hfin := hvalFfin hμev hzl
          have h1 := hasSum_fiber (g := val) (c := κ l)
            (a := |κ l| ^ j / valFiberCard val (κ l)) hfin
          have hNnn : 0 ≤ valFiberCard val (κ l) := by
            show (0:ℝ) ≤ ((Nat.card {m : ℕ // val m = κ l} : ℕ) : ℝ)
            exact_mod_cast Nat.zero_le _
          have hne : ((Module.finrank ℝ
              (Module.End.eigenspace (TOpEnd' K hK) (κ l)) : ℕ) : ℝ) ≠ 0 :=
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

/-! ### The main bridge -/

/-- **hBridge — the trace-class diagonal invariance + eigen evaluation** (spec §8):
for a compact symmetric kernel operator, a diagonal enumeration with the
multiplicity clause, every power `j ≥ 2` and every Hilbert basis `e` of `L2`,
the diagonal pairing sum of `T^j` over `e` equals the enumerated power sum
`∑' m, val m ^ j`. -/
theorem hBridge {K : ℝ × ℝ → ℝ} (hK : HSKernel K)
    (hCompact : IsCompactOperator (TOp K hK))
    (hsym : (↑(TOp K hK) : L2 →ₗ[ℝ] L2).IsSymmetric)
    {val : ℕ → ℝ} {vec : ℕ → L2}
    (hdiag : IsDiagEnum (TOpEnd' K hK) val vec)
    (hmult : ∀ μ : ℝ, Module.End.HasEigenvalue (TOpEnd' K hK) μ → μ ≠ 0 →
      Nat.card {m : ℕ // val m = μ}
        = Module.finrank ℝ (Module.End.eigenspace (TOpEnd' K hK) μ))
    (j : ℕ) (hj : 2 ≤ j) (e : HilbertBasis ℕ ℝ L2) :
    (∑' i : ℕ, inner ℝ ((TOpEnd' K hK ^ j) (e i)) (e i)) = ∑' m : ℕ, val m ^ j := by
  obtain ⟨ι, v, κ, hv, he, hcomp⟩ :=
    exists_complete_eigenfamily_of_symmetric (T := (↑(TOp K hK) : L2 →ₗ[ℝ] L2)) hsym
      (fun μ hμ => finiteDimensional_eigenspace_TOp hCompact hμ)
      (ContinuousLinearMap.isClosed_ker (TOp K hK))
      (orthogonalComplement_iSup_eigenspaces_TOp hCompact hsym)
  have hvz : ∀ l : ι, v l ≠ 0 := fun l =>
    norm_ne_zero_iff.mp (by rw [hv.1 l]; norm_num)
  have hκev : ∀ l : ι, Module.End.HasEigenvalue (TOpEnd' K hK) (κ l) := fun l =>
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr (he l), hvz l⟩
  -- squared eigenvalues are summable (Bessel bound on the HS norm)
  have hκsq : Summable (fun l : ι => κ l ^ 2) := by
    refine summable_of_sum_le (c := hsNorm K ^ 2) (fun l => sq_nonneg _) fun u => ?_
    calc ∑ l ∈ u, κ l ^ 2 = ∑ l ∈ u, ‖TOp K hK (v l)‖ ^ 2 := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [show TOp K hK (v l) = κ l • v l from he l, norm_smul,
            Real.norm_eq_abs, hv.1 l, mul_one, sq_abs]
      _ ≤ hsNorm K ^ 2 := sum_norm_TOp_sq_le hv u
  -- the `j`-th absolute powers are summable (interpolation against the op norm)
  have hκabsj : Summable (fun l : ι => |κ l| ^ j) := by
    have key : ∀ l : ι, |κ l| ^ j ≤ ‖TOp K hK‖ ^ (j - 2) * κ l ^ 2 := by
      intro l
      have h1 := abs_eigenvalue_le_norm hK (hκev l)
      have h3 : |κ l| ^ j = |κ l| ^ (j - 2) * |κ l| ^ 2 := by
        rw [← pow_add (|κ l|) (j - 2) 2]
        exact congrArg (fun n : ℕ => |κ l| ^ n) (by omega)
      calc |κ l| ^ j = |κ l| ^ (j - 2) * |κ l| ^ 2 := h3
        _ = |κ l| ^ (j - 2) * κ l ^ 2 := by rw [sq_abs]
        _ ≤ ‖TOp K hK‖ ^ (j - 2) * κ l ^ 2 :=
          mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (abs_nonneg _) h1 (j - 2)) (sq_nonneg (κ l))
    have hcs : Summable (fun l : ι => ‖TOp K hK‖ ^ (j - 2) * κ l ^ 2) :=
      hκsq.const_smul (‖TOp K hK‖ ^ (j - 2))
    exact Summable.of_nonneg_of_le (fun l => pow_nonneg (abs_nonneg (κ l)) j) key hcs
  rw [tsum_diag_inner_pow_eq_tsum_kappaPow hsym hv he hcomp j hj hκabsj e,
    tsum_kappaPow_eq_tsum_valPow hCompact hsym hv he hcomp hdiag hmult j hj hκabsj]

end HS

end
