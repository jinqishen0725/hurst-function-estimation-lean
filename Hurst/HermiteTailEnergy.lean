import Hurst.HermiteTruncation
import Hurst.GaussianLogResidual

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace Hurst

theorem hermiteTruncation_inner (f g : GaussianL2) (M : ℕ) :
    ⟪hermiteTruncation f M,g⟫ = ∑ n ∈ Finset.range M,⟪gaussianHermiteUnit n,f⟫*⟪gaussianHermiteUnit n,g⟫ := by
  simp only [hermiteTruncation,sum_inner,inner_smul_left,conj_trivial]

theorem hermiteTruncation_norm_sq (f : GaussianL2) (M : ℕ) :
    ‖hermiteTruncation f M‖^2 = ∑ n ∈ Finset.range M,⟪gaussianHermiteUnit n,f⟫^2 := by
  rw [← real_inner_self_eq_norm_sq,hermiteTruncation_inner]
  apply Finset.sum_congr rfl
  intro n hn
  rw [hermiteTruncation_coefficient,if_pos (Finset.mem_range.mp hn),pow_two]

theorem hermiteTail_norm_sq (f : GaussianL2) (M : ℕ) :
    ‖hermiteTail f M‖^2 = ‖f‖^2-∑ n ∈ Finset.range M,⟪gaussianHermiteUnit n,f⟫^2 := by
  rw [hermiteTail,norm_sub_sq_real,real_inner_comm (hermiteTruncation f M) f,
    hermiteTruncation_inner,hermiteTruncation_norm_sq]
  simp only [← pow_two]
  ring

theorem gaussianLog_hermiteTail_energy (M : ℕ) :
    ‖hermiteTail gaussianLogLp M‖^2 = gaussianLogSquareVariance-
      ∑ n ∈ Finset.range M,⟪gaussianHermiteUnit n,gaussianLogLp⟫^2 := by
  rw [hermiteTail_norm_sq,gaussianLogLp_norm_sq]

end Hurst
