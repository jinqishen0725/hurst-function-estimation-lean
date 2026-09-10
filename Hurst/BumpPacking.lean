import Hurst.Corrections
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Support

noncomputable section
open Set Filter
open scoped Topology
namespace Hurst

theorem correctedBump_tsupport_subset : tsupport correctedBump ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have hx0 : correctedBump x ≠ 0 := hx
  constructor
  · by_contra h
    exact hx0 (correctedBump_zero x (Or.inl (le_of_not_ge h)))
  · by_contra h
    exact hx0 (correctedBump_zero x (Or.inr (le_of_not_ge h)))

theorem iteratedDeriv_tsupport_subset (f : ℝ → ℝ) (r : ℕ) : tsupport (iteratedDeriv r f) ⊆ tsupport f := by
  induction r with
  | zero => simp only [iteratedDeriv_zero, subset_refl]
  | succ r ih =>
    rw [iteratedDeriv_succ]
    exact tsupport_deriv_subset.trans ih

theorem correctedBump_derivative_support (r : ℕ) (x : ℝ) (hx : iteratedDeriv r correctedBump x ≠ 0) :
    x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) := by
  apply correctedBump_tsupport_subset
  apply iteratedDeriv_tsupport_subset correctedBump r
  exact subset_closure hx

theorem correctedBump_derivative_uniform_bound (r : ℕ) :
    ∃ C ≥ 0, ∀ x : ℝ, |iteratedDeriv r correctedBump x| ≤ C := by
  have hc := correctedBump_smooth.continuous_iteratedDeriv r (by exact_mod_cast (le_top : (r : ℕ∞) ≤ ⊤))
  obtain ⟨u, hu, humax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2)) hc.norm.continuousOn
  refine ⟨‖iteratedDeriv r correctedBump u‖, norm_nonneg _, ?_⟩
  intro x
  by_cases hx : iteratedDeriv r correctedBump x = 0
  · rw [hx, abs_zero]
    exact norm_nonneg _
  · simpa only [Real.norm_eq_abs, Set.mem_setOf_eq] using humax (correctedBump_derivative_support r x hx)

/-- Integer-indexed unit cells have overlap at most two, including their closed endpoints. -/
theorem finite_unit_window_card_bound (m : ℕ) (S : Finset (Fin m)) (x : ℝ)
    (hS : ∀ i ∈ S, (i.val : ℝ) ≤ x ∧ x ≤ i.val + 1) : S.card ≤ 2 := by
  classical
  have hmap : MapsTo (fun i : Fin m => (i.val : ℤ)) S ({Int.floor x, Int.floor x - 1} : Finset ℤ) := by
    intro i hi
    have h1 : (i.val : ℤ) ≤ Int.floor x := Int.le_floor.mpr (by exact_mod_cast (hS i hi).1)
    have h2R : (Int.floor x : ℝ) ≤ (i.val : ℝ) + 1 := (Int.floor_le x).trans (hS i hi).2
    have h2 : Int.floor x ≤ (i.val : ℤ) + 1 := by exact_mod_cast h2R
    have he : (i.val : ℤ) = Int.floor x ∨ (i.val : ℤ) = Int.floor x - 1 := by omega
    simpa only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] using he
  have hc := Finset.card_le_card_of_injOn (fun i : Fin m => (i.val : ℤ)) hmap
    (fun i _ j _ hij => Fin.ext (by dsimp only at hij; exact_mod_cast hij))
  exact hc.trans Finset.card_le_two

theorem finite_unit_window_sum_bound (m : ℕ) (f : Fin m → ℝ) (x C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ i, |f i| ≤ C) (hsupport : ∀ i, f i ≠ 0 → (i.val : ℝ) ≤ x ∧ x ≤ i.val + 1) :
    |∑ i, f i| ≤ 2 * C := by
  classical
  let S := Finset.univ.filter (fun i => f i ≠ 0)
  have hc : S.card ≤ 2 := finite_unit_window_card_bound m S x (fun i hi => hsupport i (Finset.mem_filter.mp hi).2)
  have hs : (∑ i, |f i|) = ∑ i ∈ S, |f i| := by
    dsimp only [S]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs with hi
    · rfl
    · simp only [not_not] at hi
      simp [hi]
  calc
    _ ≤ ∑ i, |f i| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := hs
    _ ≤ ∑ _i ∈ S, C := Finset.sum_le_sum (fun i _ => hbound i)
    _ = (S.card : ℝ) * C := by simp
    _ ≤ 2 * C := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hC

def binaryBumpSum (m : ℕ) (θ : Fin m → ℝ) (x : ℝ) : ℝ :=
  ∑ i, θ i * correctedBump ((m : ℝ) * x - i.val - 1 / 2)

theorem binaryBumpSum_smooth (m : ℕ) (θ : Fin m → ℝ) : ContDiff ℝ (⊤ : ℕ∞) (binaryBumpSum m θ) := by
  apply ContDiff.sum
  intro i _
  exact contDiff_const.mul (correctedBump_smooth.comp
    (((contDiff_const.mul contDiff_id).sub contDiff_const).sub contDiff_const))

theorem correctedBump_affine_derivative (m r : ℕ) (c x : ℝ) :
    iteratedDeriv r (fun y => correctedBump ((m : ℝ) * y + c)) x =
      (m : ℝ) ^ r * iteratedDeriv r correctedBump ((m : ℝ) * x + c) := by
  have hg : ContDiff ℝ r (fun y => correctedBump (y + c)) :=
    (correctedBump_smooth.comp (contDiff_id.add contDiff_const)).of_le (by exact_mod_cast (le_top : (r : ℕ∞) ≤ ⊤))
  have he := congrFun (iteratedDeriv_comp_const_mul hg (m : ℝ)) x
  rw [iteratedDeriv_comp_add_const] at he
  exact he

theorem binaryBumpSum_derivative (m r : ℕ) (θ : Fin m → ℝ) (x : ℝ) :
    iteratedDeriv r (binaryBumpSum m θ) x =
      (m : ℝ) ^ r * ∑ i, θ i * iteratedDeriv r correctedBump ((m : ℝ) * x - i.val - 1 / 2) := by
  unfold binaryBumpSum
  rw [iteratedDeriv_fun_sum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [iteratedDeriv_const_mul_field]
    have he : (fun y : ℝ => correctedBump ((m : ℝ) * y - i.val - 1 / 2)) =
        fun y => correctedBump ((m : ℝ) * y + (-(i.val : ℝ) - 1 / 2)) := by
      funext y
      congr 1
      ring
    rw [he, correctedBump_affine_derivative]
    have hx : (m : ℝ) * x + (-(i.val : ℝ) - 1 / 2) = (m : ℝ) * x - i.val - 1 / 2 := by ring
    rw [hx]
    ring
  · intro i _
    exact (contDiff_const.mul (correctedBump_smooth.comp
      (((contDiff_const.mul contDiff_id).sub contDiff_const).sub contDiff_const))).contDiffAt.of_le (by exact_mod_cast (le_top : (r : ℕ∞) ≤ ⊤))

theorem binaryBumpSum_derivative_uniform (r : ℕ) :
    ∃ C ≥ 0, ∀ m : ℕ, ∀ θ : Fin m → ℝ, (∀ i, |θ i| ≤ 1) → ∀ x : ℝ,
      |iteratedDeriv r (binaryBumpSum m θ) x| ≤ C * (m : ℝ) ^ r := by
  obtain ⟨C, hC, hc⟩ := correctedBump_derivative_uniform_bound r
  refine ⟨2 * C, by positivity, ?_⟩
  intro m θ hθ x
  have hs := finite_unit_window_sum_bound m
    (fun i => θ i * iteratedDeriv r correctedBump ((m : ℝ) * x - i.val - 1 / 2)) ((m : ℝ) * x) C hC
    (fun i => by
      rw [abs_mul]
      exact (mul_le_mul (hθ i) (hc _) (abs_nonneg _) (by norm_num)).trans_eq (one_mul C))
    (fun i hi => by
      have hd := correctedBump_derivative_support r ((m : ℝ) * x - i.val - 1 / 2) (right_ne_zero_of_mul hi)
      constructor <;> linarith [hd.1, hd.2])
  rw [binaryBumpSum_derivative, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (m : ℝ) ^ r)]
  exact (mul_le_mul_of_nonneg_left hs (by positivity)).trans_eq (by ring)

/-- Global interpolation avoids treating cross-cell Holder differences as if they were in one cell. -/
theorem scaled_holder_from_bounds (f : ℝ → ℝ) (m β A : ℝ) (hm : 0 < m)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hA : 0 ≤ A)
    (hbound : ∀ x, |f x| ≤ A * m ^ (-β))
    (hlip : ∀ x y, |f x - f y| ≤ (A * m ^ (1 - β)) * |x - y|) :
    ∀ x y, |f x - f y| ≤ (2 * A) * |x - y| ^ β := by
  intro x y
  by_cases hxy : x = y
  · subst y
    simp only [sub_self, abs_zero]
    positivity
  have hd : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
  by_cases hsmall : |x - y| ≤ 1 / m
  · have hmd : m * |x - y| ≤ 1 := by
      have he := (le_div_iff₀ hm).mp hsmall
      nlinarith
    have hp : (m * |x - y|) ^ (1 - β) ≤ 1 :=
      Real.rpow_le_one (by positivity) hmd (by linarith)
    have he : m ^ (1 - β) * |x - y| = (m * |x - y|) ^ (1 - β) * |x - y| ^ β := by
      rw [Real.mul_rpow hm.le hd.le, mul_assoc, ← Real.rpow_add hd,
        show 1 - β + β = 1 by ring, Real.rpow_one]
    have hrate : m ^ (1 - β) * |x - y| ≤ |x - y| ^ β := by
      rw [he]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hd.le β)
    have hmul := mul_le_mul_of_nonneg_left hrate hA
    have hpos : 0 ≤ A * |x - y| ^ β := by positivity
    nlinarith [hlip x y]
  · have hlarge : 1 / m ≤ |x - y| := le_of_lt (lt_of_not_ge hsmall)
    have hrate : m ^ (-β) ≤ |x - y| ^ β := by
      rw [Real.rpow_neg_eq_inv_rpow]
      exact Real.rpow_le_rpow (by positivity) (by simpa only [one_div] using hlarge) hβ0
    have ht := abs_sub (f x) (f y)
    have he := mul_le_mul_of_nonneg_left hrate hA
    linarith [hbound x, hbound y]

def bumpAlternative (m : ℕ) (p ε : ℝ) (θ : Fin m → ℝ) (x : ℝ) : ℝ :=
  1 / 2 + ε * (m : ℝ) ^ (-p) * binaryBumpSum m θ x

theorem bumpAlternative_smooth (m : ℕ) (p ε : ℝ) (θ : Fin m → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (bumpAlternative m p ε θ) :=
  contDiff_const.add (contDiff_const.mul (binaryBumpSum_smooth m θ))

theorem bumpAlternative_derivative_bound (r : ℕ) (hr : 0 < r) :
    ∃ C ≥ 0, ∀ m : ℕ, 0 < m → ∀ p ε : ℝ, 0 ≤ ε → ∀ θ : Fin m → ℝ,
      (∀ i, |θ i| ≤ 1) → ∀ x : ℝ,
      |iteratedDeriv r (bumpAlternative m p ε θ) x| ≤ C * ε * (m : ℝ) ^ ((r : ℝ) - p) := by
  obtain ⟨C, hC, hc⟩ := binaryBumpSum_derivative_uniform r
  refine ⟨C, hC, ?_⟩
  intro m hm p ε hε θ hθ x
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have he : (m : ℝ) ^ (-p) * (m : ℝ) ^ r = (m : ℝ) ^ ((r : ℝ) - p) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hmR]
    congr 1
    ring
  change |iteratedDeriv r (fun z => (1 / 2 : ℝ) + ε * (m : ℝ) ^ (-p) * binaryBumpSum m θ z) x| ≤ _
  rw [iteratedDeriv_const_add hr, iteratedDeriv_const_mul_field,
    abs_mul, abs_of_nonneg (by positivity : 0 ≤ ε * (m : ℝ) ^ (-p))]
  have hb := mul_le_mul_of_nonneg_left (hc m θ hθ x) (by positivity : 0 ≤ ε * (m : ℝ) ^ (-p))
  calc
    _ ≤ (ε * (m : ℝ) ^ (-p)) * (C * (m : ℝ) ^ r) := hb
    _ = (C * ε) * ((m : ℝ) ^ (-p) * (m : ℝ) ^ r) := by ring
    _ = _ := by rw [he]

theorem bumpAlternative_amplitude_bound :
    ∃ C ≥ 0, ∀ m : ℕ, ∀ p ε : ℝ, 0 ≤ ε → ∀ θ : Fin m → ℝ,
      (∀ i, |θ i| ≤ 1) → ∀ x : ℝ,
      |bumpAlternative m p ε θ x - 1 / 2| ≤ C * ε * (m : ℝ) ^ (-p) := by
  obtain ⟨C, hC, hc⟩ := binaryBumpSum_derivative_uniform 0
  refine ⟨C, hC, ?_⟩
  intro m p ε hε θ hθ x
  have hb := hc m θ hθ x
  simp only [iteratedDeriv_zero, pow_zero, mul_one] at hb
  rw [bumpAlternative, add_sub_cancel_left, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ ε * (m : ℝ) ^ (-p))]
  exact (mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq (by ring)

/-- Uniform global Holder seminorm, including points in different cells and integer exponents. -/
theorem bumpAlternative_holder_bound (r : ℕ) (hr : 0 < r) :
    ∃ C ≥ 0, ∀ m : ℕ, 0 < m → ∀ β ε : ℝ, 0 ≤ β → β ≤ 1 → 0 ≤ ε →
      ∀ θ : Fin m → ℝ, (∀ i, |θ i| ≤ 1) → ∀ x y : ℝ,
      |iteratedDeriv r (bumpAlternative m ((r : ℝ) + β) ε θ) x -
        iteratedDeriv r (bumpAlternative m ((r : ℝ) + β) ε θ) y| ≤
          (C * ε) * |x - y| ^ β := by
  obtain ⟨A, hA, ha⟩ := bumpAlternative_derivative_bound r hr
  obtain ⟨B, hB, hb⟩ := bumpAlternative_derivative_bound (r + 1) (by omega)
  let C := max A B
  have hC : 0 ≤ C := hA.trans (le_max_left _ _)
  refine ⟨2 * C, by positivity, ?_⟩
  intro m hm β ε hβ0 hβ1 hε θ hθ x y
  let f := bumpAlternative m ((r : ℝ) + β) ε θ
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hs : ∀ z, |iteratedDeriv r f z| ≤ (C * ε) * (m : ℝ) ^ (-β) := by
    intro z
    have he := ha m hm ((r : ℝ) + β) ε hε θ hθ z
    rw [show (r : ℝ) - ((r : ℝ) + β) = -β by ring] at he
    exact he.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left A B) hε) (Real.rpow_nonneg hmR.le _))
  have hd : ∀ z, HasDerivAt (iteratedDeriv r f) (iteratedDeriv (r + 1) f z) z := by
    intro z
    rw [iteratedDeriv_succ]
    exact ((bumpAlternative_smooth m ((r : ℝ) + β) ε θ).differentiable_iteratedDeriv r
      (by exact_mod_cast (WithTop.coe_lt_top r : (r : ℕ∞) < ⊤)) z).hasDerivAt
  have hdb : ∀ z, ‖iteratedDeriv (r + 1) f z‖ ≤ (C * ε) * (m : ℝ) ^ (1 - β) := by
    intro z
    have he := hb m hm ((r : ℝ) + β) ε hε θ hθ z
    rw [show ((r + 1 : ℕ) : ℝ) - ((r : ℝ) + β) = 1 - β by push_cast; ring] at he
    rw [Real.norm_eq_abs]
    exact he.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right A B) hε) (Real.rpow_nonneg hmR.le _))
  have hlip : ∀ u v, |iteratedDeriv r f u - iteratedDeriv r f v| ≤
      ((C * ε) * (m : ℝ) ^ (1 - β)) * |u - v| := by
    intro u v
    have he := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z (_ : z ∈ (univ : Set ℝ)) => (hd z).hasDerivWithinAt)
      (fun z _ => hdb z) convex_univ (mem_univ v) (mem_univ u)
    simpa only [Real.norm_eq_abs] using he
  have he := scaled_holder_from_bounds (iteratedDeriv r f) m β (C * ε) hmR hβ0 hβ1 (by positivity) hs hlip x y
  simpa only [mul_assoc] using he

theorem bumpAlternative_holder_floor_bound (p : ℝ) (hp : 1 ≤ p) :
    ∃ C ≥ 0, ∀ m : ℕ, 0 < m → ∀ ε : ℝ, 0 ≤ ε → ∀ θ : Fin m → ℝ,
      (∀ i, |θ i| ≤ 1) → ∀ x y : ℝ,
      |iteratedDeriv (Nat.floor p) (bumpAlternative m p ε θ) x -
        iteratedDeriv (Nat.floor p) (bumpAlternative m p ε θ) y| ≤
          (C * ε) * |x - y| ^ (p - (Nat.floor p : ℝ)) := by
  have hr : 0 < Nat.floor p := by have he := (Nat.one_le_floor_iff p).mpr hp; omega
  obtain ⟨C, hC, hc⟩ := bumpAlternative_holder_bound (Nat.floor p) hr
  refine ⟨C, hC, ?_⟩
  intro m hm ε hε θ hθ x y
  have hβ0 : 0 ≤ p - (Nat.floor p : ℝ) := sub_nonneg.mpr (Nat.floor_le (by linarith))
  have hβ1 : p - (Nat.floor p : ℝ) ≤ 1 := by linarith [Nat.lt_floor_add_one p]
  have he := hc m hm (p - (Nat.floor p : ℝ)) ε hβ0 hβ1 hε θ hθ x y
  rwa [add_sub_cancel] at he

def hurstHolderClass (p M : ℝ) : Set (ℝ → ℝ) := {H |
  MapsTo H (Ioo (0 : ℝ) 1) (Ioo (0 : ℝ) 1) ∧
  (∀ r : ℕ, r < Nat.floor p → ∀ x ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ (iteratedDeriv r H) x) ∧
  ∀ x ∈ Ioo (0 : ℝ) 1, ∀ y ∈ Ioo (0 : ℝ) 1,
    |iteratedDeriv (Nat.floor p) H x - iteratedDeriv (Nat.floor p) H y| ≤ M * |x - y| ^ (p - (Nat.floor p : ℝ))}

/-- Actual membership in the fixed original Holder class, uniform over all grid sizes and codewords. -/
theorem bumpAlternative_mem_hurstHolderClass (p M : ℝ) (hp : 1 ≤ p) (hM : 0 < M) :
    ∃ ε₀ > 0, ∀ ε : ℝ, 0 ≤ ε → ε ≤ ε₀ → ∀ m : ℕ, 0 < m →
      ∀ θ : Fin m → ℝ, (∀ i, |θ i| ≤ 1) → bumpAlternative m p ε θ ∈ hurstHolderClass p M := by
  obtain ⟨A, hA, ha⟩ := bumpAlternative_amplitude_bound
  obtain ⟨C, hC, hc⟩ := bumpAlternative_holder_floor_bound p hp
  let ε₀ := min (1 / (8 * (A + 1))) (M / (C + 1))
  have hε₀ : 0 < ε₀ := by dsimp only [ε₀]; positivity
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hεsmall m hm θ hθ
  have heA : ε * (8 * (A + 1)) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp (hεsmall.trans (min_le_left _ _))
  have heC : ε * (C + 1) ≤ M :=
    (le_div_iff₀ (by positivity)).mp (hεsmall.trans (min_le_right _ _))
  have hAε : A * ε ≤ 1 / 8 := by nlinarith
  have hCε : C * ε ≤ M := by nlinarith
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hpow : (m : ℝ) ^ (-p) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hm1 (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have he := (ha m p ε hε θ hθ x).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow (show 0 ≤ A * ε by positivity))
    have he' := abs_le.mp he
    constructor <;> linarith [he'.1, he'.2]
  · intro r hr x hx
    exact (bumpAlternative_smooth m p ε θ).differentiable_iteratedDeriv r
      (by exact_mod_cast (WithTop.coe_lt_top r : (r : ℕ∞) < ⊤)) x
  · intro x hx y hy
    exact (hc m hm ε hε θ hθ x y).trans
      (mul_le_mul_of_nonneg_right hCε (Real.rpow_nonneg (abs_nonneg _) _))

theorem binaryBumpSum_zero_outside (m : ℕ) (θ : Fin m → ℝ) (x : ℝ) (hx : x ≤ 0 ∨ 1 ≤ x) :
    binaryBumpSum m θ x = 0 := by
  unfold binaryBumpSum
  apply Finset.sum_eq_zero
  intro i _
  have hi0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
  have him : (i.val : ℝ) + 1 ≤ m := by exact_mod_cast Nat.succ_le_of_lt i.isLt
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have he : correctedBump ((m : ℝ) * x - i.val - 1 / 2) = 0 := by
    apply correctedBump_zero
    rcases hx with hx | hx
    · left
      have hm := mul_nonpos_of_nonneg_of_nonpos hm0 hx
      linarith
    · right
      have hm := mul_le_mul_of_nonneg_left hx hm0
      nlinarith
  rw [he, mul_zero]

end Hurst
