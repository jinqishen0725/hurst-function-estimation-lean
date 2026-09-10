import Hurst.ActualLocalRawEvenMoment
import Hurst.ActualScaleRawEvenMoment
import Hurst.ActualNonlinearScaleEvenMoment
import Hurst.EvenMomentAlgebra

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace Topology
namespace Hurst

/-- Complete unit-scale raw `2k` moment decomposition for the first estimator,
before specializing the bandwidth and spatial averaging resolution. -/
theorem hurstHolder_q1_combined_raw_evenMoment
    (hBS : BardetSurgailisLemmaOneScalar) (k : ℕ) (hk : 1 ≤ k)
    (p a b M : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 3 / 4)
    (hab : a ≤ b) (hM : 0 ≤ M) :
    ∃ N₀ > 0, ∃ Cl > 0, ∃ Cb > 0, ∃ D > 0, ∃ El ≥ 0,
      ∃ Cs > 0, ∃ Es ≥ 0, ∃ N : ℕ, 2 ≤ N ∧
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) →
      ∃ g : ℝ → ℝ, Continuous g ∧ EqOn f g (Ioo (0 : ℝ) 1) ∧
        MapsTo g (Icc (0 : ℝ) 1) (Icc a b) ∧
      ∀ n : ℕ, N ≤ n → 1 ≤ Real.log n → ∀ m : ℕ, 0 < m →
      ∀ δ t : ℝ, 0 < δ → δ ≤ 1 / 2 → t ∈ Icc (0 : ℝ) 1 →
      N₀ ≤ (n : ℝ) * δ → 1 ≤ (m : ℝ) * δ →
      (∫ x, |(gaussianLogStatistic
          (localPolynomialWeights (Nat.ceil p - 1) n 1 δ t)
          (gridDifferenceCoefficients n) x -
          q1LogScaleEstimator (Nat.ceil p - 1) n m δ x) -
          calibrationOne (Real.log n) gaussianLogSquareMean (g t)| ^ (2 * k)
        ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) ≤
      2 ^ (2 * k - 1) *
        (2 ^ (2 * k - 1) *
          (Cl / ((n : ℝ) * δ) ^ k +
            (2 * Real.log n * (Cb * δ ^ p) +
              2 * D * gridCovarianceError b El n) ^ (2 * k)) +
         2 ^ (2 * k - 1) *
          (Cs * (Real.log n) ^ (2 * k) / (n : ℝ) ^ k +
            (Real.log n * gridCovarianceError b Es n) ^ (2 * k))) := by
  obtain ⟨Nl, hNl, Cl, hCl, Cb, hCb, D, hD, El, hEl, Nln, hNln, hlocal⟩ :=
    hurstHolder_q1_local_raw_evenMoment hBS k hk p a b M hp ha hb hab hM
  obtain ⟨Ns, hNs, Cs, hCs, Es, hEs, Nsn, hNsn, hscale⟩ :=
    hurstHolder_q1_scale_raw_evenMoment hBS k hk p a b M hp ha hb hab hM
  obtain ⟨_, _, _, _, hzlocal⟩ := hurstHolder_stride_first_correlation_decay
    p a b M hp ha hb hab hM 1 (by omega)
  obtain ⟨_, _, hz₁⟩ := hurstHolder_common_first_stride_log_mean
    p a b M 1 2 hp ha (by linarith) hab hM (by omega) (by omega)
  obtain ⟨_, _, hz₂⟩ := hurstHolder_common_first_stride_log_mean
    p a b M 2 2 hp ha (by linarith) hab hM (by omega) (by omega)
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hzlocal.and (hz₁.and hz₂))
  let N₀ := max Nl Ns
  let N := max (max Nln Nsn) (max K 2)
  refine ⟨N₀, hNl.trans_le (le_max_left _ _), Cl, hCl, Cb, hCb, D, hD,
    El, hEl, Cs, hCs, Es, hEs, N,
    (le_max_right K 2).trans (le_max_right _ _), ?_⟩
  intro f hf hF
  obtain ⟨g, hg, heq, hgmap, hloc⟩ := hlocal f hf hF
  refine ⟨g, hg, heq, hgmap, ?_⟩
  intro n hn hlog m hm δ t hδ hδhalf ht hnδ hmδ
  obtain ⟨hnzlocal, hnz1, hnz2⟩ := hK n
    ((le_max_left K 2).trans ((le_max_right _ _).trans hn))
  have hl := hloc n ((le_max_left Nln Nsn).trans ((le_max_left _ _).trans hn))
    δ t hδ hδhalf ht ((le_max_left Nl Ns).trans hnδ)
  have hs := hscale f hf hF n
    ((le_max_right Nln Nsn).trans ((le_max_left _ _).trans hn)) hlog m hm δ hδ hδhalf
    ((le_max_right Nl Ns).trans hnδ) hmδ
  let P := featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
  let v := gridObservationFeatures n (midpointSampleHurst f hf.1 n)
  let A := fun x => gaussianLogStatistic
    (localPolynomialWeights (Nat.ceil p - 1) n 1 δ t) (gridDifferenceCoefficients n) x -
    calibrationOne (Real.log n) gaussianLogSquareMean (g t)
  let S := q1LogScaleEstimator (Nat.ceil p - 1) n m δ
  have hn0 : 0 < n := by omega
  have hfeat0 : ∀ i, ∑ j, gridDifferenceCoefficients n i j • v j ≠ 0 := by
    intro i
    dsimp only [v]
    change ∑ j, gridStrideFirstCoefficients n 1 i j •
      gridObservationFeatures n (midpointSampleHurst f hf.1 n) j ≠ 0
    rw [gridStrideFirst_feature_identity n 1 hn0 (by omega)
      (midpointSampleHurst f hf.1 n) i]
    exact smul_ne_zero (Real.rpow_pos_of_pos (by positivity) _).ne'
      ((hnzlocal f hf hF).1 i)
  let w := averagedLocalWeights (Nat.ceil p - 1) n 2 m δ
  let a₁ := commonFirstStrideCoefficients n 1 2 (by omega)
  let a₂ := commonFirstStrideCoefficients n 2 2 (by omega)
  have hfeat₁ : ∀ i, ∑ j, a₁ i j • v j ≠ 0 := fun i => (hnz1 f hf hF i).1
  have hfeat₂ : ∀ i, ∑ j, a₂ i j • v j ≠ 0 := fun i => (hnz2 f hf hF i).1
  have hA_mem : MemLp A (ENNReal.ofReal (2 * k : ℝ)) P :=
    (gaussianLogStatistic_memLp_finite v _ _ hfeat0 _).sub (memLp_const _)
  have hS_mem : MemLp S (ENNReal.ofReal (2 * k : ℝ)) P :=
    (linearScaleCombination_memLp_finite P _ _ (Real.log n) (2 * k : ℝ)
      (gaussianLogStatistic_memLp_finite v w a₁ hfeat₁ _)
      (gaussianLogStatistic_memLp_finite v w a₂ hfeat₂ _)).sub (memLp_const _)
  have hAint : Integrable (fun x => |A x| ^ (2 * k)) P := by
    have hi := hA_mem.integrable_norm_rpow'
    rw [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * k),
      show (2 : ℝ) * k = ((2 * k : ℕ) : ℝ) by norm_num] at hi
    simpa only [Real.norm_eq_abs, Real.rpow_natCast] using hi
  have hSint : Integrable (fun x => |-S x| ^ (2 * k)) P := by
    have hi := hS_mem.integrable_norm_rpow'
    rw [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * k),
      show (2 : ℝ) * k = ((2 * k : ℕ) : ℝ) by norm_num] at hi
    simpa only [Real.norm_eq_abs, Real.rpow_natCast, abs_neg] using hi
  have hadd := evenMoment_add_le P A (fun x => -S x) k hk
    hA_mem.aestronglyMeasurable hS_mem.neg.aestronglyMeasurable hAint hSint
  have hrewrite : ∀ x, (gaussianLogStatistic
      (localPolynomialWeights (Nat.ceil p - 1) n 1 δ t) (gridDifferenceCoefficients n) x -
      q1LogScaleEstimator (Nat.ceil p - 1) n m δ x) -
      calibrationOne (Real.log n) gaussianLogSquareMean (g t) = A x + -S x := by
    intro x
    dsimp only [A, S]
    ring
  simp_rw [hrewrite]
  have hs' : (∫ x, |-S x| ^ (2 * k) ∂P) ≤
      2 ^ (2 * k - 1) *
        (Cs * (Real.log n) ^ (2 * k) / (n : ℝ) ^ k +
          (Real.log n * gridCovarianceError b Es n) ^ (2 * k)) := by
    simpa only [S, P, abs_neg] using hs
  exact hadd.trans (mul_le_mul_of_nonneg_left (add_le_add hl hs') (by positivity))

/-- Complete unit-scale raw `2k` moment decomposition for the second estimator,
before specializing the bandwidth and spatial averaging resolution. -/
theorem hurstHolder_q2_combined_raw_evenMoment
    (hBS : BardetSurgailisLemmaOneScalar) (k : ℕ) (hk : 1 ≤ k)
    (p a b M : ℝ) (hp : 2 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M) :
    ∃ N₀ > 0, ∃ Cl > 0, ∃ Cb ≥ 0, ∃ D > 0, ∃ El ≥ 0,
      ∃ Cs > 0, ∃ Bs ≥ 0, ∃ Es ≥ 0,
      ∃ Cp > 0, ∃ Bp ≥ 0, ∃ Ep ≥ 0, ∃ L ≥ 1,
      ∃ N : ℕ, 4 ≤ N ∧
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) →
      ∃ g : ℝ → ℝ, Continuous g ∧ EqOn f g (Ioo (0 : ℝ) 1) ∧
        MapsTo g (Icc (0 : ℝ) 1) (Icc a b) ∧
      ∀ n : ℕ, N ≤ n → 1 ≤ Real.log n → ∀ m : ℕ, 0 < m →
      ∀ δ t : ℝ, 0 < δ → δ ≤ 1 / 2 → t ∈ Icc (0 : ℝ) 1 →
      N₀ ≤ (n : ℝ) * δ → 1 ≤ (m : ℝ) * δ →
      (∫ x, |(gaussianLogStatistic
          (localPolynomialWeights (Nat.ceil p - 1) n 2 δ t)
          (gridSecondCoefficients n) x -
          q2LogScaleEstimator a b (Nat.ceil p - 1) n m δ x) -
          calibrationTwo (Real.log n) gaussianLogSquareMean (g t)| ^ (2 * k)
        ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) ≤
      2 ^ (2 * k - 1) *
        (2 ^ (2 * k - 1) *
          (Cl / ((n : ℝ) * δ) ^ k +
            (2 * Real.log n * (Cb * δ ^ p) +
              D * gridCovarianceError (1 / 2) El n) ^ (2 * k)) +
         2 ^ (2 * k - 1) *
          (2 ^ (2 * k - 1) *
            (Cs * (Real.log n) ^ (2 * k) / (n : ℝ) ^ k +
              (Bs * Real.log n * δ ^ p +
                Real.log n * gridCovarianceError (1 / 2) Es n) ^ (2 * k)) +
           L ^ (2 * k) * 2 ^ (2 * k - 1) *
            (Cp / ((n : ℝ) * δ) ^ k +
              (Bp * δ ^ p + gridCovarianceError (1 / 2) Ep n) ^ (2 * k)))) := by
  obtain ⟨Nl, hNl, Cl, hCl, Cb, hCb, D, hD, El, hEl, Nln, hNln, hlocal⟩ :=
    hurstHolder_q2_local_raw_evenMoment hBS k hk p a b M hp ha hb hab hM
  obtain ⟨Ns, hNs, Cs, hCs, Bs, hBs, Es, hEs, Nsn, hNsn, hscale⟩ :=
    hurstHolder_q2_linear_raw_evenMoment hBS k hk p a b M hp ha hb hab hM
  obtain ⟨Np, hNp, Cp, hCp, Bp, hBp, Ep, hEp, L, hL, Npn, hNpn, hnonlin⟩ :=
    hurstHolder_q2_nonlinearScale_evenMoment hBS k hk p a b M hp ha hb hab hM
  obtain ⟨_, _, _, _, hzlocal⟩ := hurstHolder_stride_second_correlation_decay
    p a b M hp ha hb hab hM 1 (by omega)
  obtain ⟨_, _, hz₁⟩ := hurstHolder_common_stride_log_mean
    p a b M 1 4 hp ha hb hab hM (by omega) (by omega)
  obtain ⟨_, _, hz₂⟩ := hurstHolder_common_stride_log_mean
    p a b M 2 4 hp ha hb hab hM (by omega) (by omega)
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hzlocal.and (hz₁.and hz₂))
  let N₀ := max Nl (max Ns Np)
  let N := max (max Nln (max Nsn Npn)) (max K 4)
  refine ⟨N₀, hNl.trans_le (le_max_left _ _), Cl, hCl, Cb, hCb, D, hD,
    El, hEl, Cs, hCs, Bs, hBs, Es, hEs, Cp, hCp, Bp, hBp, Ep, hEp, L, hL,
    N, (le_max_right K 4).trans (le_max_right _ _), ?_⟩
  intro f hf hF
  obtain ⟨g, hg, heq, hgmap, hloc⟩ := hlocal f hf hF
  refine ⟨g, hg, heq, hgmap, ?_⟩
  intro n hn hlog m hm δ t hδ hδhalf ht hnδ hmδ
  obtain ⟨hnzlocal, hnz1, hnz2⟩ := hK n
    ((le_max_left K 4).trans ((le_max_right _ _).trans hn))
  have hl := hloc n ((le_max_left Nln _).trans ((le_max_left _ _).trans hn))
    δ t hδ hδhalf ht ((le_max_left Nl _).trans hnδ)
  have hs := hscale f hf hF n
    ((le_max_left Nsn Npn).trans ((le_max_right Nln _).trans ((le_max_left _ _).trans hn)))
    hlog m hm δ hδ hδhalf ((le_max_left Ns Np).trans ((le_max_right Nl _).trans hnδ)) hmδ
  have hpilot := hnonlin f hf hF n
    ((le_max_right Nsn Npn).trans ((le_max_right Nln _).trans ((le_max_left _ _).trans hn)))
    m hm δ hδ hδhalf ((le_max_right Ns Np).trans ((le_max_right Nl _).trans hnδ))
  let P := featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
  let v := gridObservationFeatures n (midpointSampleHurst f hf.1 n)
  let A := fun x => gaussianLogStatistic
    (localPolynomialWeights (Nat.ceil p - 1) n 2 δ t) (gridSecondCoefficients n) x -
    calibrationTwo (Real.log n) gaussianLogSquareMean (g t)
  let T := fun x => q2LinearScale (Nat.ceil p - 1) n m δ x -
    (∑ j : Fin m, (q2LogCorrection (f (grid m j.val)) + gaussianLogSquareMean)) / (m : ℝ)
  let U := q2NonlinearScaleError a b (Nat.ceil p - 1) n m δ f
  have hn0 : 0 < n := by omega
  have hfeat0 : ∀ i, ∑ j, gridSecondCoefficients n i j • v j ≠ 0 := by
    intro i
    dsimp only [v]
    change ∑ j, gridStrideSecondCoefficients n 1 i j •
      gridObservationFeatures n (midpointSampleHurst f hf.1 n) j ≠ 0
    rw [gridStrideSecond_feature_identity n 1 hn0 (by omega)
      (midpointSampleHurst f hf.1 n) i]
    exact smul_ne_zero (Real.rpow_pos_of_pos (by positivity) _).ne'
      ((hnzlocal f hf hF).1 i)
  let w := averagedLocalWeights (Nat.ceil p - 1) n 4 m δ
  let a₁ := commonStrideCoefficients n 1 4 (by omega)
  let a₂ := commonStrideCoefficients n 2 4 (by omega)
  have hfeat₁ : ∀ i, ∑ j, a₁ i j • v j ≠ 0 := fun i => (hnz1 f hf hF i).1
  have hfeat₂ : ∀ i, ∑ j, a₂ i j • v j ≠ 0 := fun i => (hnz2 f hf hF i).1
  have hA_mem : MemLp A (ENNReal.ofReal (2 * k : ℝ)) P :=
    (gaussianLogStatistic_memLp_finite v _ _ hfeat0 _).sub (memLp_const _)
  have hT_mem : MemLp T (ENNReal.ofReal (2 * k : ℝ)) P :=
    (linearScaleCombination_memLp_finite P _ _ (Real.log n) (2 * k : ℝ)
      (gaussianLogStatistic_memLp_finite v w a₁ hfeat₁ _)
      (gaussianLogStatistic_memLp_finite v w a₂ hfeat₂ _)).sub (memLp_const _)
  have hAint : Integrable (fun x => |A x| ^ (2 * k)) P := by
    have hi := hA_mem.integrable_norm_rpow'
    rw [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * k),
      show (2 : ℝ) * k = ((2 * k : ℕ) : ℝ) by norm_num] at hi
    simpa only [Real.norm_eq_abs, Real.rpow_natCast] using hi
  have hTint : Integrable (fun x => |-T x| ^ (2 * k)) P := by
    have hi := hT_mem.integrable_norm_rpow'
    rw [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * k),
      show (2 : ℝ) * k = ((2 * k : ℕ) : ℝ) by norm_num] at hi
    simpa only [Real.norm_eq_abs, Real.rpow_natCast, abs_neg] using hi
  have hUm : Measurable U := by
    dsimp only [U]
    unfold q2NonlinearScaleError
    have hp : ∀ j : Fin m, Measurable
        (q2Pilot (Nat.ceil p - 1) n δ (grid m j.val)) := fun j =>
      q2Pilot_measurable _ _ _ _
    have hphi : Measurable q2LogCorrection := by unfold q2LogCorrection; fun_prop
    have hclip := (clip_continuous a b).measurable
    fun_prop
  have hTU := evenMoment_add_le P (fun x => -T x) U k hk
    hT_mem.neg.aestronglyMeasurable
    hUm.aestronglyMeasurable
    hTint hpilot.1
  have hTU_int : Integrable (fun x => |-T x + U x| ^ (2 * k)) P := by
    let G : EuclideanSpace ℝ (Fin n) → ℝ := fun x => 2 ^ (2 * k - 1) *
      (|-T x| ^ (2 * k) + |U x| ^ (2 * k))
    have hGi : Integrable G P := (hTint.add hpilot.1).const_mul _
    apply hGi.mono'
    · exact (hT_mem.neg.aestronglyMeasurable.add
        hUm.aestronglyMeasurable).norm.pow _
    · filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
      dsimp only [G]
      calc
        |-T x + U x| ^ (2 * k) ≤ (|-T x| + |U x|) ^ (2 * k) :=
          pow_le_pow_left₀ (abs_nonneg _) (abs_add_le _ _) _
        _ ≤ _ := add_pow_le (abs_nonneg _) (abs_nonneg _) _
  have hfull := evenMoment_add_le P A (fun x => -T x + U x) k hk
    hA_mem.aestronglyMeasurable
    (hT_mem.neg.aestronglyMeasurable.add
      hUm.aestronglyMeasurable)
    hAint hTU_int
  have hdecomp : ∀ x, (gaussianLogStatistic
      (localPolynomialWeights (Nat.ceil p - 1) n 2 δ t) (gridSecondCoefficients n) x -
      q2LogScaleEstimator a b (Nat.ceil p - 1) n m δ x) -
      calibrationTwo (Real.log n) gaussianLogSquareMean (g t) = A x + (-T x + U x) := by
    intro x
    rw [q2LogScaleEstimator_decomposition a b (Nat.ceil p - 1) n m hm δ f x]
    dsimp only [A, T, U, q2NonlinearScaleError]
    ring
  simp_rw [hdecomp]
  apply hfull.trans
  apply mul_le_mul_of_nonneg_left (add_le_add hl ?_) (by positivity)
  have hs' : (∫ x, |-T x| ^ (2 * k) ∂P) ≤
      2 ^ (2 * k - 1) *
        (Cs * (Real.log n) ^ (2 * k) / (n : ℝ) ^ k +
          (Bs * Real.log n * δ ^ p +
            Real.log n * gridCovarianceError (1 / 2) Es n) ^ (2 * k)) := by
    simpa only [T, P, abs_neg] using hs
  exact hTU.trans (mul_le_mul_of_nonneg_left (add_le_add hs' hpilot.2) (by positivity))

end Hurst
