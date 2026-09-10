import Hurst.InteriorDesignLimit

noncomputable section
open Set MeasureTheory
open scoped Topology
namespace Hurst

def equivalentKernel (r : ℕ) (x : ℝ) : ℝ :=
  localKernel x * ∑ j : Fin (r+1),(continuousKernelGram r (-1) 1)⁻¹ 0 j*x^j.val

theorem equivalentKernel_continuous (r : ℕ) : Continuous (equivalentKernel r) := by
  unfold equivalentKernel
  exact localKernel_smooth.continuous.mul (continuous_finsetSum _ (fun j _ => continuous_const.mul (continuous_id.pow _)))

theorem equivalentKernel_compactSupport (r : ℕ) : HasCompactSupport (equivalentKernel r) :=
  localKernel_compactSupport.mul_right

theorem equivalentKernel_integral_moment (r k : ℕ) :
    (∫ x in (-1:ℝ)..1,equivalentKernel r x*x^k)=equivalentKernelMoment r k := by
  have he (x : ℝ) : equivalentKernel r x*x^k =
      ∑ j : Fin (r+1),(continuousKernelGram r (-1) 1)⁻¹ 0 j*kernelMomentFunction (j.val+k) x := by
    simp only [equivalentKernel,kernelMomentFunction,pow_add,Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [he]
  have hi (j : Fin (r+1)) : IntervalIntegrable
      (fun x => (continuousKernelGram r (-1) 1)⁻¹ 0 j*kernelMomentFunction (j.val+k) x) volume (-1) 1 := by
    exact (continuous_const.mul (kernelMomentFunction_smooth _).continuous).intervalIntegrable _ _
  rw [intervalIntegral.integral_finsetSum (fun j _ => hi j)]
  simp only [intervalIntegral.integral_const_mul,equivalentKernelMoment,kernelMomentIntegral]

theorem equivalentKernelMoment_reproduces (r : ℕ) (k : Fin (r+1)) :
    equivalentKernelMoment r k.val=if k=0 then 1 else 0 := by
  have hd : IsUnit (continuousKernelGram r (-1) 1).det :=
    isUnit_iff_ne_zero.mpr (continuousKernelGram_posDef r (-1) 1 le_rfl le_rfl (by norm_num)).det_pos.ne'
  have he : equivalentKernelMoment r k.val=
      ((continuousKernelGram r (-1) 1)⁻¹*continuousKernelGram r (-1) 1) 0 k := by
    simp only [equivalentKernelMoment,Matrix.mul_apply,continuousKernelGram_moment,kernelMomentIntegral]
  rw [he,Matrix.nonsing_inv_mul _ hd]
  simp [Matrix.one_apply,eq_comm]

theorem equivalentKernel_integral (r : ℕ) : (∫ x in (-1:ℝ)..1,equivalentKernel r x)=1 := by
  have he := equivalentKernel_integral_moment r 0
  have hm : equivalentKernelMoment r 0=1 := by simpa using equivalentKernelMoment_reproduces r (0 : Fin (r+1))
  simpa only [pow_zero,mul_one,hm] using he

end Hurst
