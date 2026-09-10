import Hurst.LinearizedDistribution
import Hurst.InverseL1Linearization

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Hurst

theorem linearCalibration_limit {Ω : ℕ → Type*} [∀ n,MeasurableSpace (Ω n)]
    {Ω' : Type*} [MeasurableSpace Ω']
    (P : ∀ n,Measure (Ω n)) [∀ n,IsProbabilityMeasure (P n)]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : ∀ n,Ω n → ℝ) (H μ : ℝ) (hH : H∈Ioo (0:ℝ) 1)
    (hXm : ∀ n,AEMeasurable (X n) (P n))
    (hX : ∀ᶠ n in atTop,MemLp (X n) 2 (P n))
    (A : ℕ → ℝ) (hA : ∀ᶠ n in atTop,0≤A n) (Z : Ω' → ℝ) (β : ℝ)
    (hCLT : TendstoInDistribution (fun n ω => A n*(X n ω-(∫ x,X n x ∂P n))) atTop Z P P')
    (hmean : Tendsto (fun n : ℕ => A n*((∫ x,X n x ∂P n)-calibrationOne (Real.log n) μ H)) atTop (𝓝 β))
    (hQ : Tendsto (fun n : ℕ => A n*(∫ x,(X n x-calibrationOne (Real.log n) μ H)^2 ∂P n)/Real.log n) atTop (𝓝 0)) :
    TendstoInDistribution (fun (n : ℕ) x => 2*A n*Real.log n*
      (boundedInverse (calibrationOne (Real.log n) μ) 0 1 (X n x)-H)) atTop
      (fun z => -Z z-β) P P' := by
  let T := fun (n : ℕ) ω => boundedInverse (calibrationOne (Real.log n) μ) 0 1 (X n ω)
  let d := min H (1-H)/2
  have hd : 0<d := by have := hH.1; have := hH.2; dsimp [d]; positivity
  have hHa : (0:ℝ)+d≤H := by have := min_le_left H (1-H); dsimp [d]; linarith [hH.1]
  have hHb : H+d≤1 := by have := min_le_right H (1-H); dsimp [d]; linarith [hH.2]
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hT : ∀ᶠ n in atTop,MemLp (T n) 2 (P n) := by
    filter_upwards [hX,hlog.eventually_gt_atTop 0] with n hn hl
    exact boundedInverse_memLp_two (P n) (X n) hn _ 0 1 (2*Real.log n) (by positivity) (by norm_num)
      (calibrationOne_continuous _ _).continuousOn (calibrationOne_strongDecrease _ _ _ _)
  apply linearized_distribution P P' _ _ Z
    (fun n : ℕ => A n*((∫ x,X n x ∂P n)-calibrationOne (Real.log n) μ H)) β hCLT
  · intro n
    by_cases hn : 1<n
    · have hl : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast hn)
      have hi := (boundedInverse_lipschitz (calibrationOne (Real.log n) μ) 0 1 (2*Real.log n)
        (by positivity) (by norm_num) (calibrationOne_continuous _ _).continuousOn
        (calibrationOne_strongDecrease _ _ _ _)).continuous.measurable
      exact (((hi.comp_aemeasurable (hXm n)).sub aemeasurable_const).const_mul _)
    · have hn' : n≤1 := by omega
      have hl : Real.log (n:ℝ)=0 := by interval_cases n <;> norm_num
      simp only [hl,mul_zero,zero_mul]
      exact aemeasurable_const
  · filter_upwards [hX,hT] with n hx ht
    exact (((ht.integrable (by norm_num)).sub (integrable_const H)).const_mul _).add
      (((hx.integrable (by norm_num)).sub (integrable_const _)).const_mul _)
  · exact hmean
  · apply squeeze_zero' (Eventually.of_forall (fun _ => integral_nonneg (fun _ => abs_nonneg _))) _
      (by simpa only [mul_zero] using hQ.const_mul (1/(2*d)))
    filter_upwards [hX,hA,hlog.eventually_gt_atTop 0] with n hx ha hl
    have hid : (fun z : ℝ => -(2*Real.log n)*z+0+μ)=calibrationOne (Real.log n) μ := by
      funext z; unfold calibrationOne; ring
    have he := boundedInverse_L1_linearization (P n) (X n) hx (fun _ => 0) 0 1 (2*Real.log n) μ H d 0
      (by positivity) hd (by norm_num) hHa hHb
      (by rw [hid]; exact (calibrationOne_continuous _ _).continuousOn)
      (by intro z hz; simp)
      (by rw [hid]; exact calibrationOne_strongDecrease _ _ _ _)
    have hval : -(2*Real.log n)*H+0+μ=calibrationOne (Real.log n) μ H := congrFun hid H
    simp only [hid,hval,zero_mul,zero_div,zero_add] at he
    have he' := mul_le_mul_of_nonneg_left he (show 0≤2*A n*Real.log n by positivity)
    have hid' (x : Ω n) : 2*A n*Real.log n*(T n x-H)+A n*(X n x-(∫ y,X n y ∂P n))+
        A n*((∫ y,X n y ∂P n)-calibrationOne (Real.log n) μ H)=
        (2*A n*Real.log n)*(T n x-H+(X n x-calibrationOne (Real.log n) μ H)/(2*Real.log n)) := by
      field_simp
      <;> ring
    change (∫ x,|2*A n*Real.log n*(T n x-H)+A n*(X n x-(∫ y,X n y ∂P n))+
      A n*((∫ y,X n y ∂P n)-calibrationOne (Real.log n) μ H)| ∂P n)≤_
    simp only [hid']
    have habs (z : ℝ) : |(2*A n*Real.log n)*z|=(2*A n*Real.log n)*|z| := by
      rw [abs_mul,abs_of_nonneg (by positivity : 0≤2*A n*Real.log n)]
    simp only [habs,integral_const_mul]
    convert he' using 1 <;> first | rfl | (field_simp <;> ring)

end Hurst
