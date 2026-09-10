import Hurst.GaussianLogRank

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace Hurst

def gaussianLogResidual (x : ℝ) : ℝ := centeredGaussianLog x-(x^2-1)

def gaussianLogResidualLp : GaussianL2 := gaussianLogLp-gaussianHermiteLp 2

theorem gaussianLogResidualLp_ae : gaussianLogResidualLp =ᵐ[gaussianReal 0 1] gaussianLogResidual := by
  filter_upwards [Lp.coeFn_sub gaussianLogLp (gaussianHermiteLp 2),gaussianLogLp_ae,gaussianHermiteLp_ae 2]
    with x hx hf hh
  simpa only [gaussianLogResidualLp,gaussianLogResidual,Pi.sub_apply,hf,hh,gaussianHermite_two,
    Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_one] using hx

theorem gaussianHermiteUnit_inner_raw (n m : ℕ) :
    ⟪gaussianHermiteUnit n,gaussianHermiteLp m⟫ = if n=m then Real.sqrt (n.factorial:ℝ) else 0 := by
  rw [gaussianHermiteUnit,inner_smul_left,conj_trivial,gaussianHermiteLp_inner]
  split_ifs with h
  · have hp : 0 < (n.factorial:ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
    have hs : Real.sqrt (n.factorial:ℝ) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
    field_simp
    exact (Real.sq_sqrt hp.le).symm
  · ring

theorem gaussianLogResidual_rank_four :
    ∀ n : ℕ,n<4 → ⟪gaussianHermiteUnit n,gaussianLogResidualLp⟫=0 := by
  intro n hn
  rw [gaussianLogResidualLp,inner_sub_right,gaussianHermiteUnit_inner_raw]
  interval_cases n
  · simp [gaussianLog_hermite_coefficient_zero]
  · simp [gaussianLog_hermite_coefficient_odd 1 (by decide)]
  · simp [gaussianLog_hermite_coefficient_two]
  · simp [gaussianLog_hermite_coefficient_odd 3 (by decide)]

theorem gaussianLogLp_norm_sq : ‖gaussianLogLp‖^2=gaussianLogSquareVariance := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  unfold gaussianLogSquareVariance
  apply integral_congr_ae
  filter_upwards [gaussianLogLp_ae] with x hx
  simp only [hx,Real.inner_apply,pow_two]

theorem gaussianLogResidual_norm_sq : ‖gaussianLogResidualLp‖^2=gaussianLogSquareVariance-2 := by
  have hc : ⟪gaussianLogLp,gaussianHermiteLp 2⟫=2 := by
    rw [real_inner_comm,gaussianHermiteLp_inner_function]
    rw [← gaussianLog_second_hermite_integral]
    apply integral_congr_ae
    filter_upwards [gaussianLogLp_ae] with x hx
    rw [hx]
  have hh : ‖gaussianHermiteLp 2‖^2=2 := by
    rw [← real_inner_self_eq_norm_sq,gaussianHermiteLp_inner]
    norm_num
  rw [gaussianLogResidualLp,norm_sub_sq_real,gaussianLogLp_norm_sq,hc,hh]
  ring

theorem gaussianLogSquareVariance_ge_two : 2≤gaussianLogSquareVariance := by
  have he := sq_nonneg ‖gaussianLogResidualLp‖
  rw [gaussianLogResidual_norm_sq] at he
  linarith

end Hurst
