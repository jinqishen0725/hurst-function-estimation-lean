import Hurst.GaussianHilbert

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace Hurst

def gaussianPullback {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ)
    (hX : MeasurePreserving X P (gaussianReal 0 1)) : GaussianL2 →L[ℝ] Lp ℝ 2 P :=
  (Lp.compMeasurePreservingₗᵢ ℝ X hX).toContinuousLinearMap

theorem gaussianPullback_ae {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ)
    (hX : MeasurePreserving X P (gaussianReal 0 1)) (f : GaussianL2) :
    gaussianPullback P X hX f =ᵐ[P] fun ω => f (X ω) :=
  Lp.coeFn_compMeasurePreserving f hX

theorem gaussianHermiteUnit_ae (n : ℕ) :
    gaussianHermiteUnit n =ᵐ[gaussianReal 0 1]
      fun x => (Real.sqrt (n.factorial:ℝ))⁻¹*(gaussianHermite n).eval x := by
  filter_upwards [Lp.coeFn_smul ((Real.sqrt (n.factorial:ℝ))⁻¹) (gaussianHermiteLp n),
    gaussianHermiteLp_ae n] with x hx hh
  simpa only [gaussianHermiteUnit,Pi.smul_apply,smul_eq_mul,hh] using hx

theorem gaussianPullback_hermite_ae {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ)
    (hX : MeasurePreserving X P (gaussianReal 0 1)) (n : ℕ) :
    gaussianPullback P X hX (gaussianHermiteUnit n) =ᵐ[P]
      fun ω => (Real.sqrt (n.factorial:ℝ))⁻¹*(gaussianHermite n).eval (X ω) := by
  filter_upwards [gaussianPullback_ae P X hX (gaussianHermiteUnit n),
    hX.quasiMeasurePreserving.ae (gaussianHermiteUnit_ae n)] with ω hω hn
  exact hω.trans hn

theorem gaussianPullback_inner {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X Y : Ω → ℝ)
    (hX : MeasurePreserving X P (gaussianReal 0 1)) (hY : MeasurePreserving Y P (gaussianReal 0 1))
    (f g : GaussianL2) :
    ⟪gaussianPullback P X hX f,gaussianPullback P Y hY g⟫ = ∫ ω,f (X ω)*g (Y ω) ∂P := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [gaussianPullback_ae P X hX f,gaussianPullback_ae P Y hY g] with ω hf hg
  simp only [hf,hg,Real.inner_apply]

end Hurst
