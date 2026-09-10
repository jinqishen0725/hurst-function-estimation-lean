import Hurst.JointHermite
import Hurst.GaussianPullback
import Hurst.HilbertDiagonal

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace Hurst

theorem jointGaussian_hermite_unit_inner {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ)
    (hXY : HasGaussianLaw (fun ω => (X ω,Y ω)) P)
    (hX : MeasurePreserving X P (gaussianReal 0 1))
    (hY : MeasurePreserving Y P (gaussianReal 0 1)) (n m : ℕ) :
    ⟪gaussianPullback P X hX (gaussianHermiteUnit n),gaussianPullback P Y hY (gaussianHermiteUnit m)⟫ =
      if n=m then cov[X,Y;P]^n else 0 := by
  have hXlaw : HasLaw X (gaussianReal 0 1) P := ⟨hX.measurable.aemeasurable,hX.map_eq⟩
  have hYlaw : HasLaw Y (gaussianReal 0 1) P := ⟨hY.measurable.aemeasurable,hY.map_eq⟩
  have hmX : (∫ ω,X ω ∂P)=0 := by rw [hXlaw.integral_eq,integral_id_gaussianReal]
  have hmY : (∫ ω,Y ω ∂P)=0 := by rw [hYlaw.integral_eq,integral_id_gaussianReal]
  have hvX : Var[X;P]=1 := by rw [hXlaw.variance_eq,variance_id_gaussianReal]; norm_num
  have hvY : Var[Y;P]=1 := by rw [hYlaw.variance_eq,variance_id_gaussianReal]; norm_num
  rw [L2.inner_def]
  have he : (∫ ω,⟪(gaussianPullback P X hX (gaussianHermiteUnit n)) ω,
        (gaussianPullback P Y hY (gaussianHermiteUnit m)) ω⟫ ∂P) =
      (Real.sqrt (n.factorial:ℝ))⁻¹*(Real.sqrt (m.factorial:ℝ))⁻¹*
        (∫ ω,(gaussianHermite n).eval (X ω)*(gaussianHermite m).eval (Y ω) ∂P) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [gaussianPullback_hermite_ae P X hX n,gaussianPullback_hermite_ae P Y hY m] with ω hn hm
    simp only [hn,hm,Real.inner_apply]
    ring
  rw [he,joint_standardGaussian_hermite P X Y hXY hmX hmY hvX hvY]
  split_ifs with hnm
  · subst m
    have hp : 0 < (n.factorial:ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
    have hs : Real.sqrt (n.factorial:ℝ) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
    have he := Real.sq_sqrt hp.le
    field_simp
    rw [he]
  · ring

theorem jointGaussian_hermite_covariance_expansion {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ)
    (hXY : HasGaussianLaw (fun ω => (X ω,Y ω)) P)
    (hX : MeasurePreserving X P (gaussianReal 0 1))
    (hY : MeasurePreserving Y P (gaussianReal 0 1)) (f g : GaussianL2) :
    HasSum (fun n => cov[X,Y;P]^n*⟪gaussianHermiteUnit n,f⟫*⟪gaussianHermiteUnit n,g⟫)
      (∫ ω,f (X ω)*g (Y ω) ∂P) := by
  have he := hilbert_diagonal_inner_expansion gaussianHermiteBasis
    (gaussianPullback P X hX) (gaussianPullback P Y hY) (fun n => cov[X,Y;P]^n)
    (by intro n m; simpa only [gaussianHermiteBasis_apply] using jointGaussian_hermite_unit_inner P X Y hXY hX hY n m) f g
  simpa only [gaussianHermiteBasis_apply,gaussianPullback_inner] using he

end Hurst
