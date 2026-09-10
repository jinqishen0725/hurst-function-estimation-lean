import Hurst.ActualScaleEvenMoment
import Hurst.ActualScaleBias
import Hurst.FirstScaleBias
import Hurst.EvenMomentAlgebra

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace Topology
namespace Hurst

theorem linearScaleCombination_memLp_finite
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X Y : Ω → ℝ) (L s : ℝ) (hX : MemLp X (ENNReal.ofReal s) P)
    (hY : MemLp Y (ENNReal.ofReal s) P) :
    MemLp (linearScaleCombination L X Y) (ENNReal.ofReal s) P := by
  unfold linearScaleCombination
  exact (hX.const_mul _).add (hY.const_mul _)

theorem hurstHolder_q1_scale_raw_evenMoment
    (hBS : BardetSurgailisLemmaOneScalar) (k : ℕ) (hk : 1 ≤ k)
    (p a b M : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 3 / 4)
    (hab : a ≤ b) (hM : 0 ≤ M) :
    ∃ N₀ > 0, ∃ C > 0, ∃ E ≥ 0, ∃ N : ℕ, 2 ≤ N ∧
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) →
      ∀ n : ℕ, N ≤ n → 1 ≤ Real.log n → ∀ m : ℕ, 0 < m →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → N₀ ≤ (n : ℝ) * δ →
      1 ≤ (m : ℝ) * δ →
      (∫ x, |q1LogScaleEstimator (Nat.ceil p - 1) n m δ x| ^ (2 * k)
        ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) ≤
        2 ^ (2 * k - 1) *
          (C * (Real.log n) ^ (2 * k) / (n : ℝ) ^ k +
            (Real.log n * gridCovarianceError b E n) ^ (2 * k)) := by
  obtain ⟨Nm, hNm, C, hC, hmom⟩ := hurstHolder_q1_linearScale_centered_evenMoment
    hBS k hk p a b M hp ha hb hab hM (Nat.ceil p - 1)
  obtain ⟨Nb, hNb, E, hE, NbN, hNbN, hbias⟩ := hurstHolder_q1_linearScale_bias
    p a b M (Nat.ceil p - 1) hp ha hb hab hM
  obtain ⟨_, _, hz₁⟩ := hurstHolder_common_first_stride_log_mean
    p a b M 1 2 hp ha (by linarith) hab hM (by omega) (by omega)
  obtain ⟨_, _, hz₂⟩ := hurstHolder_common_first_stride_log_mean
    p a b M 2 2 hp ha (by linarith) hab hM (by omega) (by omega)
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hmom.and (hz₁.and hz₂))
  let N₀ := max Nm Nb
  let N := max (max K NbN) 2
  refine ⟨N₀, hNm.trans_le (le_max_left _ _), C, hC, E, hE, N,
    le_max_right _ _, ?_⟩
  intro f hf hF n hn hlog m hm δ hδ hδhalf hnδ hmδ
  obtain ⟨hcenter, hnz1, hnz2⟩ := hK n
    ((le_max_left K NbN).trans ((le_max_left _ 2).trans hn))
  have hb := hbias n ((le_max_right K NbN).trans ((le_max_left _ 2).trans hn))
    hlog f hf hF m hm δ hδ hδhalf ((le_max_right Nm Nb).trans hnδ) hmδ
  let P := featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
  let v := gridObservationFeatures n (midpointSampleHurst f hf.1 n)
  let w := averagedLocalWeights (Nat.ceil p - 1) n 2 m δ
  let a₁ := commonFirstStrideCoefficients n 1 2 (by omega)
  let a₂ := commonFirstStrideCoefficients n 2 2 (by omega)
  let X := q1LinearScale (Nat.ceil p - 1) n m δ
  have hfeat₁ : ∀ i, ∑ j, a₁ i j • v j ≠ 0 := fun i => (hnz1 f hf hF i).1
  have hfeat₂ : ∀ i, ∑ j, a₂ i j • v j ≠ 0 := fun i => (hnz2 f hf hF i).1
  have hXmem : MemLp X (ENNReal.ofReal (2 * k : ℝ)) P :=
    linearScaleCombination_memLp_finite P _ _ (Real.log n) (2 * k : ℝ)
      (gaussianLogStatistic_memLp_finite v w a₁ hfeat₁ _) 
      (gaussianLogStatistic_memLp_finite v w a₂ hfeat₂ _)
  have hXi : Integrable X P := hXmem.integrable (by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by exact_mod_cast (show 1 ≤ 2 * k by omega)))
  have hXcenter : Integrable (fun x => |X x - ∫ y, X y ∂P| ^ (2 * k)) P := by
    have hc := hXmem.sub (memLp_const (c := ∫ y, X y ∂P))
    have hi := hc.integrable_norm_rpow'
    rw [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * k),
      show (2 : ℝ) * k = ((2 * k : ℕ) : ℝ) by norm_num] at hi
    simpa only [Pi.sub_apply, Real.norm_eq_abs, Real.rpow_natCast] using hi
  have hraw := evenMoment_le_centered_add_bias P X gaussianLogSquareMean k hk hXi hXcenter
  change (∫ x, |X x - gaussianLogSquareMean| ^ (2 * k) ∂P) ≤ _
  apply hraw.trans
  have hb' : |(∫ y, X y ∂P) - gaussianLogSquareMean| ≤
      Real.log n * gridCovarianceError b E n := by simpa only [X, P] using hb
  calc
    2 ^ (2 * k - 1) *
        ((∫ x, |X x - ∫ y, X y ∂P| ^ (2 * k) ∂P) +
          |(∫ y, X y ∂P) - gaussianLogSquareMean| ^ (2 * k)) ≤
      2 ^ (2 * k - 1) *
        (C * (Real.log n) ^ (2 * k) / (n : ℝ) ^ k +
          (Real.log n * gridCovarianceError b E n) ^ (2 * k)) := by
      gcongr
      exact hcenter hlog f hf hF m hm δ hδ hδhalf
        ((le_max_left Nm Nb).trans hnδ) hmδ

theorem hurstHolder_q2_linear_raw_evenMoment
    (hBS : BardetSurgailisLemmaOneScalar) (k : ℕ) (hk : 1 ≤ k)
    (p a b M : ℝ) (hp : 2 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M) :
    ∃ N₀ > 0, ∃ C > 0, ∃ B ≥ 0, ∃ E ≥ 0, ∃ N : ℕ, 4 ≤ N ∧
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) →
      ∀ n : ℕ, N ≤ n → 1 ≤ Real.log n → ∀ m : ℕ, 0 < m →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → N₀ ≤ (n : ℝ) * δ →
      1 ≤ (m : ℝ) * δ →
      (∫ x, |q2LinearScale (Nat.ceil p - 1) n m δ x -
          (∑ j : Fin m, (q2LogCorrection (f (grid m j.val)) +
            gaussianLogSquareMean)) / (m : ℝ)| ^ (2 * k)
        ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) ≤
        2 ^ (2 * k - 1) *
          (C * (Real.log n) ^ (2 * k) / (n : ℝ) ^ k +
            (B * Real.log n * δ ^ p +
              Real.log n * gridCovarianceError (1 / 2) E n) ^ (2 * k)) := by
  obtain ⟨Nm, hNm, C, hC, hmom⟩ := hurstHolder_q2_linearScale_centered_evenMoment
    hBS k hk p a b M hp ha hb hab hM (Nat.ceil p - 1)
  obtain ⟨Nb, hNb, B, hB, E, hE, NbN, hNbN, hbias⟩ :=
    hurstHolder_q2_linearScale_bias p a b M hp ha hb hab hM
  obtain ⟨_, _, hz₁⟩ := hurstHolder_common_stride_log_mean
    p a b M 1 4 hp ha hb hab hM (by omega) (by omega)
  obtain ⟨_, _, hz₂⟩ := hurstHolder_common_stride_log_mean
    p a b M 2 4 hp ha hb hab hM (by omega) (by omega)
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hmom.and (hz₁.and hz₂))
  let N₀ := max Nm Nb
  let N := max (max K NbN) 4
  refine ⟨N₀, hNm.trans_le (le_max_left _ _), C, hC, B, hB, E, hE, N,
    le_max_right _ _, ?_⟩
  intro f hf hF n hn hlog m hm δ hδ hδhalf hnδ hmδ
  obtain ⟨hcenter, hnz1, hnz2⟩ := hK n
    ((le_max_left K NbN).trans ((le_max_left _ 4).trans hn))
  have hbiasn := hbias f hf hF n
    ((le_max_right K NbN).trans ((le_max_left _ 4).trans hn)) hlog m hm δ hδ hδhalf
    ((le_max_right Nm Nb).trans hnδ)
  let P := featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
  let v := gridObservationFeatures n (midpointSampleHurst f hf.1 n)
  let w := averagedLocalWeights (Nat.ceil p - 1) n 4 m δ
  let a₁ := commonStrideCoefficients n 1 4 (by omega)
  let a₂ := commonStrideCoefficients n 2 4 (by omega)
  let X := q2LinearScale (Nat.ceil p - 1) n m δ
  let θ := (∑ j : Fin m, (q2LogCorrection (f (grid m j.val)) +
    gaussianLogSquareMean)) / (m : ℝ)
  have hfeat₁ : ∀ i, ∑ j, a₁ i j • v j ≠ 0 := fun i => (hnz1 f hf hF i).1
  have hfeat₂ : ∀ i, ∑ j, a₂ i j • v j ≠ 0 := fun i => (hnz2 f hf hF i).1
  have hXmem : MemLp X (ENNReal.ofReal (2 * k : ℝ)) P :=
    linearScaleCombination_memLp_finite P _ _ (Real.log n) (2 * k : ℝ)
      (gaussianLogStatistic_memLp_finite v w a₁ hfeat₁ _)
      (gaussianLogStatistic_memLp_finite v w a₂ hfeat₂ _)
  have hXi : Integrable X P := hXmem.integrable (by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by exact_mod_cast (show 1 ≤ 2 * k by omega)))
  have hXcenter : Integrable (fun x => |X x - ∫ y, X y ∂P| ^ (2 * k)) P := by
    have hc := hXmem.sub (memLp_const (c := ∫ y, X y ∂P))
    have hi := hc.integrable_norm_rpow'
    rw [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * k),
      show (2 : ℝ) * k = ((2 * k : ℕ) : ℝ) by norm_num] at hi
    simpa only [Pi.sub_apply, Real.norm_eq_abs, Real.rpow_natCast] using hi
  have hraw := evenMoment_le_centered_add_bias P X θ k hk hXi hXcenter
  apply hraw.trans
  have hb' : |(∫ y, X y ∂P) - θ| ≤
      B * Real.log n * δ ^ p + Real.log n * gridCovarianceError (1 / 2) E n := by
    simpa only [X, P, θ] using hbiasn
  calc
    2 ^ (2 * k - 1) *
        ((∫ x, |X x - ∫ y, X y ∂P| ^ (2 * k) ∂P) +
          |(∫ y, X y ∂P) - θ| ^ (2 * k)) ≤
      2 ^ (2 * k - 1) *
        (C * (Real.log n) ^ (2 * k) / (n : ℝ) ^ k +
          (B * Real.log n * δ ^ p +
            Real.log n * gridCovarianceError (1 / 2) E n) ^ (2 * k)) := by
      gcongr
      exact hcenter hlog f hf hF m hm δ hδ hδhalf
        ((le_max_left Nm Nb).trans hnδ) hmδ

end Hurst
