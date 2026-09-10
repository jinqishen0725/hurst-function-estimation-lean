import Hurst.ActualPilot
import Hurst.FirstPilot
import Hurst.FeatureHermiteTests

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace Hurst

def pilotJoinedWeights {κ : Type*} (w : κ → ℝ) : κ ⊕ κ → ℝ :=
  Sum.elim (fun i => -(w i)/(2*Real.log 2)) (fun i => w i/(2*Real.log 2))

theorem twoScalePilot_joined_statistic {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : κ → ℝ) (a b : κ → EuclideanSpace ℝ ι) :
    gaussianLogStatistic (pilotJoinedWeights w) (Sum.elim a b)=
      twoScalePilot (gaussianLogStatistic w a) (gaussianLogStatistic w b) := by
  funext x
  unfold gaussianLogStatistic pilotJoinedWeights twoScalePilot
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl,Sum.elim_inr]
  have h₁ (i : κ) : -(w i)/(2*Real.log 2)*Real.log (⟪a i,x⟫^2)=
    -(w i*Real.log (⟪a i,x⟫^2))/(2*Real.log 2) := by ring
  have h₂ (i : κ) : w i/(2*Real.log 2)*Real.log (⟪b i,x⟫^2)=
    (w i*Real.log (⟪b i,x⟫^2))/(2*Real.log 2) := by ring
  simp only [h₁,h₂,← Finset.sum_div,Finset.sum_neg_distrib]
  ring

def q1PilotJoinedCoefficients (n : ℕ) : Fin (n-2) ⊕ Fin (n-2) → EuclideanSpace ℝ (Fin n) :=
  Sum.elim (commonFirstStrideCoefficients n 1 2 (by norm_num)) (commonFirstStrideCoefficients n 2 2 (by norm_num))
def q2PilotJoinedCoefficients (n : ℕ) : Fin (n-4) ⊕ Fin (n-4) → EuclideanSpace ℝ (Fin n) :=
  Sum.elim (commonStrideCoefficients n 1 4 (by norm_num)) (commonStrideCoefficients n 2 4 (by norm_num))

theorem q1Pilot_joined_statistic (r n : ℕ) (δ t : ℝ) :
    gaussianLogStatistic (pilotJoinedWeights (localPolynomialWeights r n 2 δ t)) (q1PilotJoinedCoefficients n)=q1Pilot r n δ t :=
  twoScalePilot_joined_statistic _ _ _

theorem q2Pilot_joined_statistic (r n : ℕ) (δ t : ℝ) :
    gaussianLogStatistic (pilotJoinedWeights (localPolynomialWeights r n 4 δ t)) (q2PilotJoinedCoefficients n)=q2Pilot r n δ t :=
  twoScalePilot_joined_statistic _ _ _

end Hurst
