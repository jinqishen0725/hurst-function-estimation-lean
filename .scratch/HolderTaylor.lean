import Hurst.HurstExperiment
import Mathlib.Analysis.Calculus.Taylor

noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace Hurst

theorem iteratedDerivWithin_eq_of_mem_nhds (f : ℝ → ℝ) (r : ℕ) (S : Set ℝ) (x : ℝ) (hS : S ∈ 𝓝 x) :
    iteratedDerivWithin r f S x = iteratedDeriv r f x := by
  unfold iteratedDerivWithin iteratedDeriv
  rw [← iteratedFDerivWithin_univ]
  congr 1
  exact iteratedFDerivWithin_congr_set (Filter.eventuallyEq_univ.mpr hS) r

theorem contDiffOn_of_differentiable_iteratedDeriv_open (f : ℝ → ℝ) (n : ℕ) (U : Set ℝ) (hU : IsOpen U)
    (hf : ∀ k ≤ n, ∀ x ∈ U, DifferentiableAt ℝ (iteratedDeriv k f) x) : ContDiffOn ℝ n f U := by
  apply (contDiffOn_nat_iff_continuousOn_differentiableOn_deriv hU.uniqueDiffOn).mpr
  constructor
  · intro k hk
    have he := iteratedDerivWithin_of_isOpen (f := f) (n := k) hU
    have hd : DifferentiableOn ℝ (iteratedDeriv k f) U := fun x hx => (hf k hk x hx).differentiableWithinAt
    exact hd.continuousOn.congr he
  · intro k hk
    have he := iteratedDerivWithin_of_isOpen (f := f) (n := k) hU
    have hd : DifferentiableOn ℝ (iteratedDeriv k f) U := fun x hx => (hf k hk.le x hx).differentiableWithinAt
    exact hd.congr he

/-- Lagrange's remainder needs continuity only below the highest derivative. -/
theorem interval_taylor_lagrange (f : ℝ → ℝ) (n : ℕ)
    (hf : ∀ k ≤ n, ∀ x ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ (iteratedDeriv k f) x)
    (x y : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) (hxy : x ≠ y) :
    ∃ z ∈ uIoo x y,
      f y - (∑ k : Fin (n + 1), iteratedDeriv k.val f x * (y - x) ^ k.val / (k.val.factorial : ℝ)) =
        iteratedDeriv (n + 1) f z * (y - x) ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  have hU := contDiffOn_of_differentiable_iteratedDeriv_open f n _ isOpen_Ioo hf
  have hsub : uIcc x y ⊆ Ioo (0 : ℝ) 1 := by
    intro z hz
    exact ⟨(lt_min hx.1 hy.1).trans_le hz.1, hz.2.trans_lt (max_lt hx.2 hy.2)⟩
  have hd : DifferentiableOn ℝ (iteratedDerivWithin n f (uIcc x y)) (uIoo x y) := by
    have he : EqOn (iteratedDerivWithin n f (uIcc x y)) (iteratedDeriv n f) (uIoo x y) := by
      intro z hz
      exact iteratedDerivWithin_eq_of_mem_nhds f n _ z (Icc_mem_nhds hz.1 hz.2)
    have hdn : DifferentiableOn ℝ (iteratedDeriv n f) (uIoo x y) :=
      fun z hz => (hf n le_rfl z (hsub ⟨hz.1.le, hz.2.le⟩)).differentiableWithinAt
    exact hdn.congr he
  obtain ⟨z, hz, he⟩ := taylor_mean_remainder_lagrange hxy (hU.mono hsub) hd
  have huniq : UniqueDiffOn ℝ (uIcc x y) := uniqueDiffOn_Icc (min_lt_max.mpr hxy)
  have hcoeff : ∀ k ≤ n, iteratedDerivWithin k f (uIcc x y) x = iteratedDeriv k f x := by
    intro k hk
    apply iteratedDerivWithin_eq_iteratedDeriv huniq
    · exact (hU.of_le (by exact_mod_cast hk)).contDiffAt (isOpen_Ioo.mem_nhds hx)
    · exact left_mem_uIcc
  have heval : taylorWithinEval f n (uIcc x y) x y =
      ∑ k : Fin (n + 1), iteratedDeriv k.val f x * (y - x) ^ k.val / (k.val.factorial : ℝ) := by
    rw [taylor_within_apply, Fin.sum_univ_eq_sum_range
      (fun k : ℕ => iteratedDeriv k f x * (y - x) ^ k / (k.factorial : ℝ))]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hcoeff k (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk), smul_eq_mul]
    ring
  refine ⟨z, hz, ?_⟩
  rw [heval, iteratedDerivWithin_eq_of_mem_nhds f (n + 1) (uIcc x y) z (Icc_mem_nhds hz.1 hz.2)] at he
  exact he

def taylorJet (r : ℕ) (f : ℝ → ℝ) (x y : ℝ) : ℝ :=
  ∑ k : Fin (r + 1), iteratedDeriv k.val f x * (y - x) ^ k.val / (k.val.factorial : ℝ)

theorem taylorJet_self (r : ℕ) (f : ℝ → ℝ) (x : ℝ) : taylorJet r f x x = f x := by
  simp [taylorJet, Fin.sum_univ_succ]

theorem taylorJet_succ (r : ℕ) (f : ℝ → ℝ) (x y : ℝ) :
    taylorJet (r + 1) f x y = taylorJet r f x y +
      iteratedDeriv (r + 1) f x * (y - x) ^ (r + 1) / ((r + 1).factorial : ℝ) := by
  simp only [taylorJet, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]

theorem interval_distance_le (x y z : ℝ) (hz : z ∈ uIcc x y) : |z - x| ≤ |y - x| := by
  rcases le_total x y with hxy | hyx
  · rw [uIcc_of_le hxy] at hz
    rw [abs_of_nonneg (by linarith [hz.1]), abs_of_nonneg (by linarith)]
    linarith [hz.2]
  · rw [uIcc_of_ge hyx] at hz
    rw [abs_of_nonpos (by linarith [hz.2]), abs_of_nonpos (by linarith)]
    linarith [hz.1]

/-- Full Holder remainder, including integer exponents with no continuity assumption on the highest derivative. -/
theorem holder_taylor_remainder (f : ℝ → ℝ) (n : ℕ) (M β : ℝ) (hM : 0 ≤ M) (hβ : 0 ≤ β)
    (hf : ∀ k ≤ n, ∀ x ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ (iteratedDeriv k f) x)
    (hholder : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ y ∈ Ioo (0 : ℝ) 1,
      |iteratedDeriv (n + 1) f x - iteratedDeriv (n + 1) f y| ≤ M * |x - y| ^ β)
    (x y : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    |f y - taylorJet (n + 1) f x y| ≤
      (M / ((n + 1).factorial : ℝ)) * |y - x| ^ ((n + 1 : ℕ) + β) := by
  by_cases hxy : x = y
  · subst y
    rw [taylorJet_self, sub_self, abs_zero]
    positivity
  obtain ⟨z, hz, he⟩ := interval_taylor_lagrange f n hf x y hx hy hxy
  change f y - taylorJet n f x y = _ at he
  have hzU : z ∈ Ioo (0 : ℝ) 1 :=
    ⟨(lt_min hx.1 hy.1).trans hz.1, hz.2.trans (max_lt hx.2 hy.2)⟩
  have hdist := interval_distance_le x y z ⟨hz.1.le, hz.2.le⟩
  have hH := (hholder z hzU x hx).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (abs_nonneg _) hdist hβ) hM)
  have herr : f y - taylorJet (n + 1) f x y =
      (iteratedDeriv (n + 1) f z - iteratedDeriv (n + 1) f x) * (y - x) ^ (n + 1) /
        ((n + 1).factorial : ℝ) := by
    rw [taylorJet_succ, sub_add_eq_sub_sub, he]
    ring
  have hfact : (0 : ℝ) < (n + 1).factorial := by positivity
  have hdistpos : 0 < |y - x| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hxy))
  rw [herr, abs_div, abs_mul, abs_pow, abs_of_pos hfact]
  calc
    _ ≤ (M * |y - x| ^ β) * |y - x| ^ (n + 1) / ((n + 1).factorial : ℝ) := by gcongr
    _ = _ := by
      rw [Real.rpow_add hdistpos, Real.rpow_natCast]
      ring

end Hurst
