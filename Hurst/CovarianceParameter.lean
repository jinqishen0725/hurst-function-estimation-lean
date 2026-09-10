import Hurst.FrozenEstimates

noncomputable section
open Set
namespace Hurst

def harmonizableCovCoeffSlope (h k : ℝ) : ℝ :=
  ((harmonizableD ((h + k) / 2) * harmonizableDSlope ((h + k) / 2)) *
      (2 * harmonizableD h * harmonizableD k) -
    harmonizableD ((h + k) / 2) ^ 2 * (2 * harmonizableD h * harmonizableDSlope k)) /
      (2 * harmonizableD h * harmonizableD k) ^ 2

theorem harmonizableCovCoeff_hasDerivAt (h k : ℝ) (hh : h ∈ Ioo (0 : ℝ) 1)
    (hk : k ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (harmonizableCovCoeff h) (harmonizableCovCoeffSlope h k) k := by
  have hmid : (h + k) / 2 ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [hh.1, hh.2, hk.1, hk.2]
  have hdmid := (harmonizableD_hasDerivAt _ hmid.1 hmid.2).comp k
    (((hasDerivAt_id k).const_add h).div_const 2)
  have hdnum := hdmid.pow 2
  have hdden := (harmonizableD_hasDerivAt k hk.1 hk.2).const_mul (2 * harmonizableD h)
  have hden : 2 * harmonizableD h * harmonizableD k ≠ 0 := ne_of_gt
    (mul_pos (mul_pos (by norm_num) (harmonizableD_pos h hh.1 hh.2)) (harmonizableD_pos k hk.1 hk.2))
  convert! hdnum.div hdden hden using 1
  simp only [harmonizableCovCoeffSlope, Function.comp_apply, id_eq, Pi.pow_apply,
    Nat.cast_ofNat, Nat.reduceSub, pow_one]
  congr 1
  ring

/-- The prefactor and its derivative are jointly uniform, not just pointwise in the frozen parameter. -/
theorem harmonizableCovCoeff_uniform_derivative_control (a b : ℝ) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) : ∃ C ≥ 0, ∀ h k : ℝ, h ∈ Icc a b → k ∈ Icc a b →
      |harmonizableCovCoeff h k| ≤ C ∧ |harmonizableCovCoeffSlope h k| ≤ C := by
  let S := Icc a b ×ˢ Icc a b
  have hfst : MapsTo (fun z : ℝ × ℝ => z.1) S (Ioo (0 : ℝ) 1) :=
    fun z hz => ⟨ha.trans_le hz.1.1, hz.1.2.trans_lt hb⟩
  have hsnd : MapsTo (fun z : ℝ × ℝ => z.2) S (Ioo (0 : ℝ) 1) :=
    fun z hz => ⟨ha.trans_le hz.2.1, hz.2.2.trans_lt hb⟩
  have hmid : MapsTo (fun z : ℝ × ℝ => (z.1 + z.2) / 2) S (Ioo (0 : ℝ) 1) := by
    intro z hz
    constructor <;> linarith [hz.1.1, hz.1.2, hz.2.1, hz.2.2]
  have hcmid : Continuous (fun z : ℝ × ℝ => (z.1 + z.2) / 2) := by fun_prop
  have hD₁ := harmonizableD_continuousOn.comp continuous_fst.continuousOn hfst
  have hD₂ := harmonizableD_continuousOn.comp continuous_snd.continuousOn hsnd
  have hDₘ := harmonizableD_continuousOn.comp hcmid.continuousOn hmid
  have hS₂ := harmonizableDSlope_continuousOn.comp continuous_snd.continuousOn hsnd
  have hSₘ := harmonizableDSlope_continuousOn.comp hcmid.continuousOn hmid
  have hd0 : ∀ z ∈ S, 2 * harmonizableD z.1 * harmonizableD z.2 ≠ 0 := by
    intro z hz
    exact ne_of_gt (mul_pos (mul_pos (by norm_num)
      (harmonizableD_pos z.1 (hfst hz).1 (hfst hz).2))
      (harmonizableD_pos z.2 (hsnd hz).1 (hsnd hz).2))
  have hB : ContinuousOn (fun z : ℝ × ℝ => harmonizableCovCoeff z.1 z.2) S :=
    (hDₘ.pow 2).div ((hD₁.const_mul 2).mul hD₂) hd0
  have hB' : ContinuousOn (fun z : ℝ × ℝ => harmonizableCovCoeffSlope z.1 z.2) S :=
    (((hDₘ.mul hSₘ).mul ((hD₁.const_mul 2).mul hD₂)).sub
      ((hDₘ.pow 2).mul ((hD₁.const_mul 2).mul hS₂))).div
      (((hD₁.const_mul 2).mul hD₂).pow 2) (fun z hz => pow_ne_zero 2 (hd0 z hz))
  have hcompact : IsCompact S := isCompact_Icc.prod isCompact_Icc
  have hnonempty : S.Nonempty := ⟨(a, a), ⟨⟨le_rfl, hab⟩, ⟨le_rfl, hab⟩⟩⟩
  obtain ⟨u, hu, humax⟩ := hcompact.exists_isMaxOn hnonempty (hB.norm.add hB'.norm)
  refine ⟨‖harmonizableCovCoeff u.1 u.2‖ + ‖harmonizableCovCoeffSlope u.1 u.2‖,
    add_nonneg (norm_nonneg _) (norm_nonneg _), ?_⟩
  intro h k hh hk
  have he := humax (show (h, k) ∈ S from ⟨hh, hk⟩)
  change ‖harmonizableCovCoeff h k‖ + ‖harmonizableCovCoeffSlope h k‖ ≤ _ at he
  simpa only [Real.norm_eq_abs, Pi.add_apply] using And.intro
    ((le_add_of_nonneg_right (norm_nonneg _)).trans he)
    ((le_add_of_nonneg_left (norm_nonneg _)).trans he)

end Hurst
