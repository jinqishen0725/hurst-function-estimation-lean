import Hurst.ScaleAverage
import Hurst.ClippedSmooth
import Hurst.TransformMSE
import Hurst.SpatialRisk

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

def q2NonlinearScaleError (a b : ℝ) (r n m : ℕ) (δ : ℝ) (f : ℝ → ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (∑ j : Fin m, (q2LogCorrection (clip a b (q2Pilot r n δ (grid m j.val) x))-q2LogCorrection (f (grid m j.val))))/(m:ℝ)

theorem hurstHolder_q2_nonlinearScale_mse (p a b M : ℝ) (hp : 2 ≤ p)
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M) :
    ∃ N₀ > 0, ∃ B ≥ 0, ∃ E ≥ 0, ∃ V ≥ 0, ∃ C ≥ 1, ∃ N : ℕ, 4 ≤ N ∧
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M, MapsTo f (Ioo (0:ℝ) 1) (Icc a b) →
      ∀ n : ℕ, N ≤ n → ∀ m : ℕ, 0 < m → ∀ δ : ℝ, 0 < δ → δ ≤ 1/2 → N₀ ≤ (n:ℝ)*δ →
      MemLp (q2NonlinearScaleError a b (Nat.ceil p-1) n m δ f) 2 (featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) ∧
      (∫ x, (q2NonlinearScaleError a b (Nat.ceil p-1) n m δ f x)^2
        ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) ≤
      C^2*(V/((n:ℝ)*δ)+2*(B*δ^p)^2+2*(gridCovarianceError (1/2) E n)^2) := by
  obtain ⟨N₀, hN₀, B, hB, E, hE, V, hV, N, hN, hpilot⟩ := hurstHolder_q2_pilot_moments p a b M hp ha hb hab hM
  obtain ⟨C, hC, herr⟩ := smooth_clipped_error q2LogCorrection q2LogCorrection_smooth a b ha hb
  have hcont : Continuous (fun y => q2LogCorrection (clip a b y)) :=
    (q2LogCorrection_smooth.continuousOn.mono (fun y hy => ⟨ha.trans_le hy.1, hy.2.trans_lt hb⟩)).comp_continuous
      (clip_continuous a b) (fun y => clip_mem a b y hab)
  refine ⟨N₀, hN₀, B, hB, E, hE, V, hV, C, hC, N, hN, ?_⟩
  intro f hf hF n hn m hm δ hδ hδhalf hnd
  obtain ⟨g, hg, heq, hgb, hpm⟩ := hpilot f hf hF
  let μ := featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
  let X := fun j : Fin m => q2Pilot (Nat.ceil p-1) n δ (grid m j.val)
  let Y := fun j : Fin m => fun x => q2LogCorrection (clip a b (X j x))-q2LogCorrection (f (grid m j.val))
  let R := V/((n:ℝ)*δ)+2*(B*δ^p)^2+2*(gridCovarianceError (1/2) E n)^2
  have hj : ∀ j : Fin m, grid m j.val ∈ Ioo (0:ℝ) 1 := fun j => grid_mem m j.val hm j.isLt
  have hY : ∀ j, MemLp (Y j) 2 μ ∧ (∫ x, (Y j x)^2 ∂μ) ≤ C^2*R := by
    intro j
    obtain ⟨hmem, hmean, hvar⟩ := hpm n hn δ _ hδ hδhalf ⟨(hj j).1.le, (hj j).2.le⟩ hnd
    have hgval : g (grid m j.val) = f (grid m j.val) := (heq (hj j)).symm
    rw [hgval] at hmean
    have he := continuous_transform_mse μ (fun y => q2LogCorrection (clip a b y)) hcont
      (f (grid m j.val)) (q2LogCorrection (f (grid m j.val))) C (by linarith)
      (fun y => herr y _ (hF (hj j))) (X j) hmem
    refine ⟨he.1, he.2.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg C))⟩
    rw [mse_decomposition _ _ hmem]
    have hh := pow_le_pow_left₀ (abs_nonneg _) hmean 2
    rw [sq_abs] at hh
    dsimp [R]
    nlinarith [sq_nonneg (B*δ^p-gridCovarianceError (1/2) E n)]
  have hmY : MemLp (fun x => (∑ j, Y j x)/(m:ℝ)) 2 μ := by
    have he := (memLp_finsetSum Finset.univ (fun j _ => (hY j).1)).mul_const (m:ℝ)⁻¹
    simpa only [div_eq_mul_inv] using he
  exact ⟨hmY, finite_average_mse_bound μ m hm Y (C^2*R) (fun j => (hY j).1) (fun j => (hY j).2)⟩

end Hurst
