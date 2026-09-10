import Hurst.GaussianHilbert
import Hurst.GaussianLogHermite

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

def hermiteTruncation (f : GaussianL2) (M : ℕ) : GaussianL2 :=
  ∑ n ∈ Finset.range M, ⟪gaussianHermiteUnit n,f⟫ • gaussianHermiteUnit n

def hermiteTail (f : GaussianL2) (M : ℕ) : GaussianL2 := f-hermiteTruncation f M

theorem hermiteTruncation_tendsto (f : GaussianL2) :
    Tendsto (hermiteTruncation f) atTop (𝓝 f) :=
  (gaussianHermite_expansion f).tendsto_sum_nat

theorem hermiteTail_tendsto (f : GaussianL2) : Tendsto (hermiteTail f) atTop (𝓝 0) := by
  change Tendsto (fun M => f-hermiteTruncation f M) atTop (𝓝 0)
  simpa only [sub_self] using (tendsto_const_nhds (x := f)).sub (hermiteTruncation_tendsto f)

theorem hermiteTail_norm_sq_tendsto (f : GaussianL2) :
    Tendsto (fun M => ‖hermiteTail f M‖^2) atTop (𝓝 0) := by
  simpa using (hermiteTail_tendsto f).norm.pow 2

theorem hermiteTruncation_coefficient (f : GaussianL2) (M n : ℕ) :
    ⟪gaussianHermiteUnit n,hermiteTruncation f M⟫ =
      if n<M then ⟪gaussianHermiteUnit n,f⟫ else 0 := by
  classical
  simp only [hermiteTruncation,inner_sum,inner_smul_right,
    orthonormal_iff_ite.mp gaussianHermiteUnit_orthonormal]
  simp [mul_ite,Finset.mem_range]

theorem hermiteTail_coefficient (f : GaussianL2) (M n : ℕ) :
    ⟪gaussianHermiteUnit n,hermiteTail f M⟫ =
      if n<M then 0 else ⟪gaussianHermiteUnit n,f⟫ := by
  rw [hermiteTail,inner_sub_right,hermiteTruncation_coefficient]
  split_ifs <;> ring

theorem hermiteTail_rank (f : GaussianL2) (M : ℕ) :
    ∀ n : ℕ,n<M → ⟪gaussianHermiteUnit n,hermiteTail f M⟫=0 := by
  intro n hn
  simp only [hermiteTail_coefficient,hn,if_true]

theorem hermiteTail_preserves_rank (f : GaussianL2) (M k : ℕ)
    (hk : ∀ n : ℕ,n<k → ⟪gaussianHermiteUnit n,f⟫=0) :
    ∀ n : ℕ,n<k → ⟪gaussianHermiteUnit n,hermiteTail f M⟫=0 := by
  intro n hn
  rw [hermiteTail_coefficient,hk n hn]
  simp

theorem gaussianLog_hermiteTail_rank_two (M : ℕ) :
    ∀ n : ℕ,n<2 → ⟪gaussianHermiteUnit n,hermiteTail gaussianLogLp M⟫=0 :=
  hermiteTail_preserves_rank gaussianLogLp M 2 gaussianLog_hermite_rank_at_least_two

end Hurst
