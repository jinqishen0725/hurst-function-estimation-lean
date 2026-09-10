import Hurst.HolderDerivativeBounds
import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section
open Set
namespace Hurst

theorem hurstHolder_floor_pos (p : ℝ) (hp : 1 ≤ p) : 1 ≤ Nat.floor p := by
  exact (Nat.le_floor_iff (by linarith : 0 ≤ p)).mpr (by exact_mod_cast hp)

theorem hurstHolder_taylor_remainder (p M : ℝ) (hp : 1 ≤ p) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (x y : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    |f y - taylorJet (Nat.floor p) f x y| ≤
      (M / ((Nat.floor p).factorial : ℝ)) * |y - x| ^ p := by
  have hr := hurstHolder_floor_pos p hp
  have he : Nat.floor p - 1 + 1 = Nat.floor p := by omega
  have hβ : 0 ≤ p - (Nat.floor p : ℝ) := sub_nonneg.mpr (Nat.floor_le (by linarith))
  have hd : ∀ k ≤ Nat.floor p - 1, ∀ z ∈ Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ (iteratedDeriv k f) z := by
    intro k hk z hz
    exact hf.2.1 k (by omega) z hz
  have hh : ∀ u ∈ Ioo (0 : ℝ) 1, ∀ v ∈ Ioo (0 : ℝ) 1,
      |iteratedDeriv (Nat.floor p - 1 + 1) f u - iteratedDeriv (Nat.floor p - 1 + 1) f v| ≤
        M * |u - v| ^ (p - (Nat.floor p : ℝ)) := by
    simpa only [he] using hf.2.2
  have h := holder_taylor_remainder f (Nat.floor p - 1) M (p - Nat.floor p) hM hβ hd hh x y hx hy
  rw [he] at h
  convert h using 1; congr 2; ring

theorem hurstHolder_taylor_error_le (p M : ℝ) (hp : 1 ≤ p) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (x y : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    |f y - taylorJet (Nat.floor p) f x y| ≤ M := by
  have hd : |y - x| ≤ 1 := abs_le.mpr ⟨by linarith [hx.1, hy.1, hx.2, hy.2], by linarith [hx.1, hy.1, hx.2, hy.2]⟩
  have hpow : |y - x| ^ p ≤ 1 := Real.rpow_le_one (abs_nonneg _) hd (by linarith)
  have hfact : (1 : ℝ) ≤ (Nat.floor p).factorial := by exact_mod_cast Nat.factorial_pos (Nat.floor p)
  calc
    _ ≤ (M / ((Nat.floor p).factorial : ℝ)) * |y - x| ^ p := hurstHolder_taylor_remainder p M hp hM f hf x y hx hy
    _ ≤ M * 1 := mul_le_mul ((div_le_iff₀ (by positivity)).mpr (by nlinarith)) hpow (Real.rpow_nonneg (abs_nonneg _) _) hM
    _ = M := mul_one M

theorem hurstHolder_uniform_derivative_bounds (p : ℝ) (hp : 1 ≤ p) :
    ∃ C > 0, ∀ M : ℝ, 0 ≤ M → ∀ f ∈ hurstHolderClass p M,
      ∀ x ∈ Ioo (0 : ℝ) 1, ∀ k ≤ Nat.floor p, |iteratedDeriv k f x| ≤ C * (1 + M) := by
  obtain ⟨C, hC, hbound⟩ := taylorJet_coefficient_uniform_bound (Nat.floor p)
  refine ⟨C, hC, ?_⟩
  intro M hM f hf x hx k hk
  apply hbound f M hM ?_ (fun u hu v hv => hurstHolder_taylor_error_le p M hp hM f hf u v hu hv) x hx ⟨k, by omega⟩
  intro z hz
  rw [abs_of_pos (hf.1 hz).1]
  exact (hf.1 hz).2.le

theorem hurstHolder_uniform_lower_derivative_lipschitz (p : ℝ) (hp : 1 ≤ p) :
    ∃ C > 0, ∀ M : ℝ, 0 ≤ M → ∀ f ∈ hurstHolderClass p M,
      ∀ k < Nat.floor p, ∀ x ∈ Ioo (0 : ℝ) 1, ∀ y ∈ Ioo (0 : ℝ) 1,
        |iteratedDeriv k f y - iteratedDeriv k f x| ≤ C * (1 + M) * |y - x| := by
  obtain ⟨C, hC, hbound⟩ := hurstHolder_uniform_derivative_bounds p hp
  refine ⟨C, hC, ?_⟩
  intro M hM f hf k hk x hx y hy
  have hb : ∀ z ∈ Ioo (0 : ℝ) 1, ‖deriv (iteratedDeriv k f) z‖ ≤ C * (1 + M) := by
    intro z hz
    simpa only [← iteratedDeriv_succ, Real.norm_eq_abs] using hbound M hM f hf z hz (k + 1) (by omega)
  simpa only [Real.norm_eq_abs] using
    (convex_Ioo (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le (hf.2.1 k hk) hb hx hy

theorem hurstHolder_uniform_lipschitz_extension (p : ℝ) (hp : 1 ≤ p) :
    ∃ C > 0, ∀ M : ℝ, 0 ≤ M → ∀ f ∈ hurstHolderClass p M,
      ∃ g : ℝ → ℝ, EqOn f g (Ioo (0 : ℝ) 1) ∧
        LipschitzWith (Real.toNNReal (C * (1 + M))) g ∧ MapsTo g (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) := by
  obtain ⟨C, hC, hbound⟩ := hurstHolder_uniform_lower_derivative_lipschitz p hp
  refine ⟨C, hC, ?_⟩
  intro M hM f hf
  have hnn : 0 ≤ C * (1 + M) := by positivity
  have hlip : LipschitzOnWith (Real.toNNReal (C * (1 + M))) f (Ioo (0 : ℝ) 1) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    simpa only [Real.dist_eq, Real.coe_toNNReal _ hnn, iteratedDeriv_zero] using
      hbound M hM f hf 0 (by have := hurstHolder_floor_pos p hp; omega) y hy x hx
  obtain ⟨g, hg, he⟩ := hlip.extend_real
  refine ⟨g, he, hg, ?_⟩
  have hmap : MapsTo g (Ioo (0 : ℝ) 1) (Ioo (0 : ℝ) 1) := by
    intro x hx
    rw [← he hx]
    exact hf.1 hx
  simpa only [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] using hmap.closure hg.continuous

theorem ceil_degree_cases (p : ℝ) (hp : 1 ≤ p) :
    (Nat.ceil p - 1 = Nat.floor p ∧ (Nat.floor p : ℝ) < p) ∨
      (p = (Nat.floor p : ℝ) ∧ Nat.ceil p - 1 + 1 = Nat.floor p) := by
  have hr := hurstHolder_floor_pos p hp
  have hfloor := Nat.floor_le (by linarith : 0 ≤ p)
  by_cases he : p = (Nat.floor p : ℝ)
  · right
    refine ⟨he, ?_⟩
    have hc : Nat.ceil p = Nat.floor p := (congrArg Nat.ceil he).trans (Nat.ceil_natCast _)
    omega
  · left
    have hlt : (Nat.floor p : ℝ) < p := lt_of_le_of_ne hfloor (Ne.symm he)
    have hc : Nat.ceil p = Nat.floor p + 1 := (Nat.ceil_eq_iff (by omega)).mpr
      ⟨by simpa using hlt, by simpa only [Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one p).le⟩
    exact ⟨by omega, hlt⟩

theorem hurstHolder_estimator_degree_remainder (p : ℝ) (hp : 1 ≤ p) :
    ∃ C > 0, ∀ M : ℝ, 0 ≤ M → ∀ f ∈ hurstHolderClass p M,
      ∀ x ∈ Ioo (0 : ℝ) 1, ∀ y ∈ Ioo (0 : ℝ) 1,
        |f y - taylorJet (Nat.ceil p - 1) f x y| ≤ C * (1 + M) * |y - x| ^ p := by
  obtain ⟨D, hD, hderiv⟩ := hurstHolder_uniform_derivative_bounds p hp
  refine ⟨max 1 D, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro M hM f hf x hx y hy
  rcases ceil_degree_cases p hp with ⟨he, hlt⟩ | ⟨he, hr⟩
  · rw [he]
    apply (hurstHolder_taylor_remainder p M hp hM f hf x y hx hy).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (abs_nonneg _) _)
    have hfact : (1 : ℝ) ≤ (Nat.floor p).factorial := by exact_mod_cast Nat.factorial_pos (Nat.floor p)
    have hfrac : M / ((Nat.floor p).factorial : ℝ) ≤ M := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
    apply hfrac.trans
    nlinarith [le_max_left (1 : ℝ) D]
  · by_cases hxy : x = y
    · subst y
      rw [taylorJet_self, sub_self, abs_zero]
      positivity
    obtain ⟨z, hz, hzEq⟩ := interval_taylor_lagrange f (Nat.ceil p - 1)
      (fun k hk u hu => hf.2.1 k (by omega) u hu) x y hx hy hxy
    change f y - taylorJet (Nat.ceil p - 1) f x y = _ at hzEq
    have hzU : z ∈ Ioo (0 : ℝ) 1 :=
      ⟨(lt_min hx.1 hy.1).trans hz.1, hz.2.trans (max_lt hx.2 hy.2)⟩
    have hd := hderiv M hM f hf z hzU (Nat.floor p) le_rfl
    rw [hzEq, hr, abs_div, abs_mul, abs_pow, abs_of_pos (by positivity : (0 : ℝ) < (Nat.floor p).factorial)]
    have hfact : (1 : ℝ) ≤ (Nat.floor p).factorial := by exact_mod_cast Nat.factorial_pos (Nat.floor p)
    have hnum : |iteratedDeriv (Nat.floor p) f z| * |y - x| ^ Nat.floor p ≤
        D * (1 + M) * |y - x| ^ Nat.floor p := mul_le_mul_of_nonneg_right hd (by positivity)
    calc
      _ ≤ D * (1 + M) * |y - x| ^ Nat.floor p :=
        (div_le_iff₀ (by positivity)).mpr (hnum.trans (by nlinarith [show 0 ≤ D * (1 + M) * |y - x| ^ Nat.floor p by positivity]))
      _ ≤ max 1 D * (1 + M) * |y - x| ^ Nat.floor p := by gcongr; exact le_max_right _ _
      _ = _ := by rw [he, Real.rpow_natCast, Nat.floor_natCast]

end Hurst
