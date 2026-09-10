import Hurst.ActualCommonCutoffAveragedMoment
import Hurst.EvenMomentAlgebra
import Hurst.FirstScale
import Hurst.ScaleAverage
import Hurst.CommonFirstMean
import Hurst.CommonStrideMean

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace Topology
namespace Hurst

theorem hurstHolder_q1_linearScale_centered_evenMoment
    (hBS : BardetSurgailisLemmaOneScalar) (k : ℕ) (hk : 1 ≤ k)
    (p a b M : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 3 / 4)
    (hab : a ≤ b) (hM : 0 ≤ M) (r : ℕ) :
    ∃ N₀ > 0, ∃ C > 0, ∀ᶠ n : ℕ in atTop,
      1 ≤ Real.log n → ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) →
      ∀ m : ℕ, 0 < m → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
      N₀ ≤ (n : ℝ) * δ → 1 ≤ (m : ℝ) * δ →
      (∫ x, |q1LinearScale r n m δ x -
          (∫ y, q1LinearScale r n m δ y
            ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))| ^
            (2 * k)
        ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) ≤
        C * (Real.log n) ^ (2 * k) / (n : ℝ) ^ k := by
  obtain ⟨N₁, hN₁, C₁, hC₁, hm₁⟩ :=
    hurstHolder_commonFirstStride_averaged_evenMoment
      hBS k hk p a b M hp ha hb hab hM r 1 2 (by omega) (by omega)
  obtain ⟨N₂, hN₂, C₂, hC₂, hm₂⟩ :=
    hurstHolder_commonFirstStride_averaged_evenMoment
      hBS k hk p a b M hp ha hb hab hM r 2 2 (by omega) (by omega)
  obtain ⟨_, _, hz₁⟩ := hurstHolder_common_first_stride_log_mean
    p a b M 1 2 hp ha (by linarith) hab hM (by omega) (by omega)
  obtain ⟨_, _, hz₂⟩ := hurstHolder_common_first_stride_log_mean
    p a b M 2 2 hp ha (by linarith) hab hM (by omega) (by omega)
  let B : ℝ := 1 + 1 / Real.log 2
  have hB : 0 < B := by dsimp only [B]; positivity
  let C : ℝ := 2 ^ (2 * k - 1) * B ^ (2 * k) * (C₁ + C₂)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨max N₁ N₂, lt_of_lt_of_le hN₁ (le_max_left _ _), C, hC, ?_⟩
  filter_upwards [hm₁, hm₂, hz₁, hz₂] with n hm1 hm2 hnz1 hnz2
  intro hlog f hf hF m hm δ hδ hδhalf hnδ hmδ
  let P := featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
  let v := gridObservationFeatures n (midpointSampleHurst f hf.1 n)
  let w := averagedLocalWeights r n 2 m δ
  let a₁ := commonFirstStrideCoefficients n 1 2 (by omega)
  let a₂ := commonFirstStrideCoefficients n 2 2 (by omega)
  let X := gaussianLogStatistic w a₁
  let Y := gaussianLogStatistic w a₂
  have hM₁ := hm1 f hf hF m hm δ hδ hδhalf ((le_max_left _ _).trans hnδ) hmδ
  have hM₂ := hm2 f hf hF m hm δ hδ hδhalf ((le_max_right _ _).trans hnδ) hmδ
  have hfeat₁ : ∀ i, ∑ j, a₁ i j • v j ≠ 0 := fun i => (hnz1 f hf hF i).1
  have hfeat₂ : ∀ i, ∑ j, a₂ i j • v j ≠ 0 := fun i => (hnz2 f hf hF i).1
  have hXtwo := gaussianLogStatistic_memLp_two v w a₁ hfeat₁
  have hYtwo := gaussianLogStatistic_memLp_two v w a₂ hfeat₂
  have hX : Integrable X P := hXtwo.integrable one_le_two
  have hY : Integrable Y P := hYtwo.integrable one_le_two
  have hXp : Integrable (fun x => |X x - ∫ y, X y ∂P| ^ (2 * k)) P := by
    have hfinite := (gaussianLogStatistic_memLp_finite v w a₁ hfeat₁ (2 * k : ℝ)).sub
      (memLp_const (c := ∫ y, X y ∂P))
    have hi := hfinite.integrable_norm_rpow'
    rw [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * k),
      show (2 : ℝ) * k = ((2 * k : ℕ) : ℝ) by norm_num] at hi
    simpa only [X, P, Pi.sub_apply, Real.norm_eq_abs, Real.rpow_natCast] using hi
  have hYp : Integrable (fun x => |Y x - ∫ y, Y y ∂P| ^ (2 * k)) P := by
    have hfinite := (gaussianLogStatistic_memLp_finite v w a₂ hfeat₂ (2 * k : ℝ)).sub
      (memLp_const (c := ∫ y, Y y ∂P))
    have hi := hfinite.integrable_norm_rpow'
    rw [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * k),
      show (2 : ℝ) * k = ((2 * k : ℕ) : ℝ) by norm_num] at hi
    simpa only [Y, P, Pi.sub_apply, Real.norm_eq_abs, Real.rpow_natCast] using hi
  let L := Real.log n
  let α := 1 - L / Real.log 2
  let β := L / Real.log 2
  have hα : |α| ≤ B * L := by
    calc
      |α| ≤ 1 + |L / Real.log 2| := by
        dsimp only [α]
        simpa only [abs_one] using abs_sub (1 : ℝ) (L / Real.log 2)
      _ = 1 + L / Real.log 2 := by
        rw [abs_of_nonneg (div_nonneg (by dsimp only [L]; linarith) (Real.log_pos (by norm_num)).le)]
      _ ≤ B * L := by
        dsimp only [B]
        have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
        field_simp
        nlinarith
  have hβ : |β| ≤ B * L := by
    rw [abs_of_nonneg (div_nonneg (by dsimp only [L]; linarith)
      (Real.log_pos (by norm_num)).le)]
    dsimp only [β, B]
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    field_simp
    nlinarith
  have hcomb := centered_linear_combination_evenMoment_le P X Y α β k hk hX hY hXp hYp
  change (∫ x, |q1LinearScale r n m δ x - ∫ y, q1LinearScale r n m δ y ∂P| ^
    (2 * k) ∂P) ≤ _
  change (∫ x, |(α * X x + β * Y x) - ∫ y, α * X y + β * Y y ∂P| ^
    (2 * k) ∂P) ≤ _
  apply hcomb.trans
  have hαp := pow_le_pow_left₀ (abs_nonneg α) hα (2 * k)
  have hβp := pow_le_pow_left₀ (abs_nonneg β) hβ (2 * k)
  calc
    2 ^ (2 * k - 1) *
        (|α| ^ (2 * k) * (∫ x, |X x - ∫ y, X y ∂P| ^ (2 * k) ∂P) +
         |β| ^ (2 * k) * (∫ x, |Y x - ∫ y, Y y ∂P| ^ (2 * k) ∂P)) ≤
      2 ^ (2 * k - 1) *
        ((B * L) ^ (2 * k) * (C₁ / (n : ℝ) ^ k) +
         (B * L) ^ (2 * k) * (C₂ / (n : ℝ) ^ k)) := by
      gcongr
    _ = C * L ^ (2 * k) / (n : ℝ) ^ k := by
      dsimp only [C]
      rw [mul_pow]
      ring

theorem hurstHolder_q2_linearScale_centered_evenMoment
    (hBS : BardetSurgailisLemmaOneScalar) (k : ℕ) (hk : 1 ≤ k)
    (p a b M : ℝ) (hp : 2 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M) (r : ℕ) :
    ∃ N₀ > 0, ∃ C > 0, ∀ᶠ n : ℕ in atTop,
      1 ≤ Real.log n → ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) →
      ∀ m : ℕ, 0 < m → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
      N₀ ≤ (n : ℝ) * δ → 1 ≤ (m : ℝ) * δ →
      (∫ x, |q2LinearScale r n m δ x -
          (∫ y, q2LinearScale r n m δ y
            ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))| ^
            (2 * k)
        ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) ≤
        C * (Real.log n) ^ (2 * k) / (n : ℝ) ^ k := by
  obtain ⟨N₁, hN₁, C₁, hC₁, hm₁⟩ :=
    hurstHolder_commonStride_averaged_evenMoment
      hBS k hk p a b M hp ha hb hab hM r 1 4 (by omega) (by omega)
  obtain ⟨N₂, hN₂, C₂, hC₂, hm₂⟩ :=
    hurstHolder_commonStride_averaged_evenMoment
      hBS k hk p a b M hp ha hb hab hM r 2 4 (by omega) (by omega)
  obtain ⟨_, _, hz₁⟩ := hurstHolder_common_stride_log_mean
    p a b M 1 4 hp ha hb hab hM (by omega) (by omega)
  obtain ⟨_, _, hz₂⟩ := hurstHolder_common_stride_log_mean
    p a b M 2 4 hp ha hb hab hM (by omega) (by omega)
  let B : ℝ := 1 + 1 / Real.log 2
  have hB : 0 < B := by dsimp only [B]; positivity
  let C : ℝ := 2 ^ (2 * k - 1) * B ^ (2 * k) * (C₁ + C₂)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨max N₁ N₂, lt_of_lt_of_le hN₁ (le_max_left _ _), C, hC, ?_⟩
  filter_upwards [hm₁, hm₂, hz₁, hz₂] with n hm1 hm2 hnz1 hnz2
  intro hlog f hf hF m hm δ hδ hδhalf hnδ hmδ
  let P := featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
  let v := gridObservationFeatures n (midpointSampleHurst f hf.1 n)
  let w := averagedLocalWeights r n 4 m δ
  let a₁ := commonStrideCoefficients n 1 4 (by omega)
  let a₂ := commonStrideCoefficients n 2 4 (by omega)
  let X := gaussianLogStatistic w a₁
  let Y := gaussianLogStatistic w a₂
  have hM₁ := hm1 f hf hF m hm δ hδ hδhalf ((le_max_left _ _).trans hnδ) hmδ
  have hM₂ := hm2 f hf hF m hm δ hδ hδhalf ((le_max_right _ _).trans hnδ) hmδ
  have hfeat₁ : ∀ i, ∑ j, a₁ i j • v j ≠ 0 := fun i => (hnz1 f hf hF i).1
  have hfeat₂ : ∀ i, ∑ j, a₂ i j • v j ≠ 0 := fun i => (hnz2 f hf hF i).1
  have hXtwo := gaussianLogStatistic_memLp_two v w a₁ hfeat₁
  have hYtwo := gaussianLogStatistic_memLp_two v w a₂ hfeat₂
  have hX : Integrable X P := hXtwo.integrable one_le_two
  have hY : Integrable Y P := hYtwo.integrable one_le_two
  have hXp : Integrable (fun x => |X x - ∫ y, X y ∂P| ^ (2 * k)) P := by
    have hfinite := (gaussianLogStatistic_memLp_finite v w a₁ hfeat₁ (2 * k : ℝ)).sub
      (memLp_const (c := ∫ y, X y ∂P))
    have hi := hfinite.integrable_norm_rpow'
    rw [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * k),
      show (2 : ℝ) * k = ((2 * k : ℕ) : ℝ) by norm_num] at hi
    simpa only [X, P, Pi.sub_apply, Real.norm_eq_abs, Real.rpow_natCast] using hi
  have hYp : Integrable (fun x => |Y x - ∫ y, Y y ∂P| ^ (2 * k)) P := by
    have hfinite := (gaussianLogStatistic_memLp_finite v w a₂ hfeat₂ (2 * k : ℝ)).sub
      (memLp_const (c := ∫ y, Y y ∂P))
    have hi := hfinite.integrable_norm_rpow'
    rw [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * k),
      show (2 : ℝ) * k = ((2 * k : ℕ) : ℝ) by norm_num] at hi
    simpa only [Y, P, Pi.sub_apply, Real.norm_eq_abs, Real.rpow_natCast] using hi
  let L := Real.log n
  let α := 1 - L / Real.log 2
  let β := L / Real.log 2
  have hα : |α| ≤ B * L := by
    calc
      |α| ≤ 1 + |L / Real.log 2| := by
        dsimp only [α]
        simpa only [abs_one] using abs_sub (1 : ℝ) (L / Real.log 2)
      _ = 1 + L / Real.log 2 := by
        rw [abs_of_nonneg (div_nonneg (by dsimp only [L]; linarith) (Real.log_pos (by norm_num)).le)]
      _ ≤ B * L := by
        dsimp only [B]
        have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
        field_simp
        nlinarith
  have hβ : |β| ≤ B * L := by
    rw [abs_of_nonneg (div_nonneg (by dsimp only [L]; linarith)
      (Real.log_pos (by norm_num)).le)]
    dsimp only [β, B]
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    field_simp
    nlinarith
  have hcomb := centered_linear_combination_evenMoment_le P X Y α β k hk hX hY hXp hYp
  change (∫ x, |q2LinearScale r n m δ x - ∫ y, q2LinearScale r n m δ y ∂P| ^
    (2 * k) ∂P) ≤ _
  change (∫ x, |(α * X x + β * Y x) - ∫ y, α * X y + β * Y y ∂P| ^
    (2 * k) ∂P) ≤ _
  apply hcomb.trans
  have hαp := pow_le_pow_left₀ (abs_nonneg α) hα (2 * k)
  have hβp := pow_le_pow_left₀ (abs_nonneg β) hβ (2 * k)
  calc
    2 ^ (2 * k - 1) *
        (|α| ^ (2 * k) * (∫ x, |X x - ∫ y, X y ∂P| ^ (2 * k) ∂P) +
         |β| ^ (2 * k) * (∫ x, |Y x - ∫ y, Y y ∂P| ^ (2 * k) ∂P)) ≤
      2 ^ (2 * k - 1) *
        ((B * L) ^ (2 * k) * (C₁ / (n : ℝ) ^ k) +
         (B * L) ^ (2 * k) * (C₂ / (n : ℝ) ^ k)) := by
      gcongr
    _ = C * L ^ (2 * k) / (n : ℝ) ^ k := by
      dsimp only [C]
      rw [mul_pow]
      ring

end Hurst
