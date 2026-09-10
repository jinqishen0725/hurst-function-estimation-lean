import Hurst.ActualScaleVariance
import Hurst.ActualScaleBias
import Hurst.NonlinearScaleRisk
import Hurst.ScaleRiskTransfer

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst
set_option maxHeartbeats 1000000

/-- Complete unit-scale MSE of the actual spatial log-scale estimator. -/
theorem hurstHolder_q2_logScale_mse_unit (p a b M : ℝ) (hp : 2 ≤ p)
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M) :
    ∃ N₀ > 0, ∃ C ≥ 0, ∃ N : ℕ, 4 ≤ N ∧
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M, MapsTo f (Ioo (0:ℝ) 1) (Icc a b) →
      ∀ n : ℕ, N ≤ n → 1 ≤ Real.log n → ∀ m : ℕ, 0 < m →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1/2 → N₀ ≤ (n:ℝ)*δ → 1 ≤ (m:ℝ)*δ →
      (∫ x, (q2LogScaleEstimator a b (Nat.ceil p-1) n m δ x)^2
        ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) ≤
        C*((Real.log n*δ^p)^2+(Real.log n*gridCovarianceError (1/2) 1 n)^2+(Real.log n)^2/(n:ℝ)+1/((n:ℝ)*δ)) := by
  obtain ⟨Nb, hNb, Bl, hBl, El, hEl, Nb₀, hNb₀, hlinb⟩ := hurstHolder_q2_linearScale_bias p a b M hp ha hb hab hM
  obtain ⟨Nv, hNv, Vl, hVl, Nv₀, hNv₀, hlinv⟩ := hurstHolder_q2_linearScale_variance p a b M (Nat.ceil p-1) hp ha hb hab hM
  obtain ⟨Np, hNp, Bp, hBp, Ep, hEp, Vp, hVp, C, hC, Np₀, hNp₀, hnonlin⟩ := hurstHolder_q2_nonlinearScale_mse p a b M hp ha hb hab hM
  obtain ⟨K, hK, hrate⟩ := scale_component_rate_bound Bl El Vl Bp Ep Vp C hVl hVp
  let N₀ := max Nb (max Nv Np)
  let N := max Nb₀ (max Nv₀ Np₀)
  refine ⟨N₀, lt_of_lt_of_le hNb (le_max_left _ _), K, hK, N, hNb₀.trans (le_max_left _ _), ?_⟩
  intro f hf hF n hn hL m hm δ hδ hδhalf hnd hmd
  have hbn : Nb₀ ≤ n := (le_max_left _ _).trans hn
  have hvn : Nv₀ ≤ n := ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have hpn : Np₀ ≤ n := ((le_max_right _ _).trans (le_max_right _ _)).trans hn
  have hbδ : Nb ≤ (n:ℝ)*δ := (le_max_left _ _).trans hnd
  have hvδ : Nv ≤ (n:ℝ)*δ := ((le_max_left _ _).trans (le_max_right _ _)).trans hnd
  have hpδ : Np ≤ (n:ℝ)*δ := ((le_max_right _ _).trans (le_max_right _ _)).trans hnd
  have hmean := hlinb f hf hF n hbn hL m hm δ hδ hδhalf hbδ
  obtain ⟨hX, hvar⟩ := hlinv n hvn hL f hf hF m hm δ hδ hδhalf hvδ hmd
  obtain ⟨hY, hsq⟩ := hnonlin f hf hF n hpn m hm δ hδ hδhalf hpδ
  let μ := featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
  let X := q2LinearScale (Nat.ceil p-1) n m δ
  let Y := q2NonlinearScaleError a b (Nat.ceil p-1) n m δ f
  let θ := (∑ j : Fin m, (q2LogCorrection (f (grid m j.val))+gaussianLogSquareMean))/(m:ℝ)
  have he := scale_mse_from_components μ X Y θ
    (Bl*Real.log n*δ^p+Real.log n*gridCovarianceError (1/2) El n) (Vl*(Real.log n)^2/(n:ℝ))
    (C^2*(Vp/((n:ℝ)*δ)+2*(Bp*δ^p)^2+2*(gridCovarianceError (1/2) Ep n)^2)) hX hY hmean hvar hsq
  have hid : q2LogScaleEstimator a b (Nat.ceil p-1) n m δ = fun x => X x-θ-Y x := by
    funext x
    exact q2LogScaleEstimator_decomposition a b (Nat.ceil p-1) n m hm δ f x
  rw [hid]
  apply he.trans
  have heE : gridCovarianceError (1/2) El n = El*gridCovarianceError (1/2) 1 n := by unfold gridCovarianceError; ring
  have heP : gridCovarianceError (1/2) Ep n = Ep*gridCovarianceError (1/2) 1 n := by unfold gridCovarianceError; ring
  rw [heE, heP]
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hr := hrate (Real.log n) (δ^p) (gridCovarianceError (1/2) 1 n) (1/(n:ℝ)) (1/((n:ℝ)*δ)) hL (by positivity) (by positivity)
  have habsq : 2*(Bl*Real.log n*δ^p+Real.log n*(El*gridCovarianceError (1/2) 1 n))^2 ≤
      4*(Bl*Real.log n*δ^p)^2+4*(Real.log n*(El*gridCovarianceError (1/2) 1 n))^2 := by
    nlinarith [sq_nonneg (Bl*Real.log n*δ^p-Real.log n*(El*gridCovarianceError (1/2) 1 n))]
  simp only [div_eq_mul_inv, one_mul] at hr ⊢
  nlinarith

end Hurst
