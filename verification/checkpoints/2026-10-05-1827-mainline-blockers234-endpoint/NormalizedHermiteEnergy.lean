import Hurst.FirstLongRealScaleHilbertSchmidt
import Hurst.FeatureQuadraticLimit

/-! Normalized unweighted energy and the absolute-weight fourth-order remainder.
The hypotheses bound `S^(2ψ-2) ∑ ρ²`, never the unnormalised sum. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology RealInnerProductSpace
namespace Hurst

/-- The exact normalization of the unweighted correlation kernel. -/
theorem realScaleMeshEnergy_scaled_eq {m : ℕ} (S ψ : ℝ) (hS : 0 < S)
    (ρ : Fin m → Fin m → ℝ) :
    realScaleMeshEnergy S (fun i j => S ^ ψ * ρ i j) =
      S ^ (2 * ψ - 2) * ∑ i, ∑ j, ρ i j ^ 2 := by
  have hscalar : S⁻¹ ^ 2 * (S ^ ψ) ^ 2 = S ^ (2 * ψ - 2) := by
    rw [show S⁻¹ = S ^ (-1 : ℝ) by rw [Real.rpow_neg_one],
      ← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul hS.le, ← Real.rpow_mul hS.le, ← Real.rpow_add hS]
    congr 1
    norm_num
    ring
  simp only [realScaleMeshEnergy, mul_pow, ← Finset.mul_sum]
  rw [← mul_assoc, hscalar]

/-- Splitting near and far pairs retains absolute weights, allowing signed
local-polynomial weights. `ε` is a uniform bound on the far correlations. -/
theorem weighted_fourth_le_band_add_energy {m R : ℕ}
    (ρ : Fin m → Fin m → ℝ) (u : Fin m → ℝ) (U ε : ℝ)
    (hU : 0 ≤ U) (hu : ∀ i, |u i| ≤ U)
    (hρ : ∀ i j, |ρ i j| ≤ 1)
    (hε : 0 ≤ ε)
    (hfar : ∀ i j, R < Nat.dist j.val i.val → |ρ i j| ≤ ε) :
    (∑ i, ∑ j, |u i * u j| * |ρ i j| ^ 4) ≤
      U ^ 2 * ((∑ i, ∑ j ∈ Finset.univ.filter
        (fun j : Fin m => Nat.dist j.val i.val ≤ R), ρ i j ^ 2) +
        ε ^ 2 * ∑ i, ∑ j, ρ i j ^ 2) := by
  classical
  have hpoint : ∀ i j,
      |u i * u j| * |ρ i j| ^ 4 ≤ U ^ 2 *
        ((if Nat.dist j.val i.val ≤ R then ρ i j ^ 2 else 0) +
          ε ^ 2 * ρ i j ^ 2) := by
    intro i j
    have hw : |u i * u j| ≤ U ^ 2 := by
      rw [abs_mul, pow_two]
      exact mul_le_mul (hu i) (hu j) (abs_nonneg _) hU
    have hsq : |ρ i j| ^ 2 = ρ i j ^ 2 := sq_abs _
    apply (mul_le_mul_of_nonneg_right hw (by positivity)).trans
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg U)
    split_ifs with hn
    · have hp := pow_le_pow_left₀ (abs_nonneg (ρ i j)) (hρ i j) 2
      have hm := mul_le_mul_of_nonneg_right hp (sq_nonneg (ρ i j))
      nlinarith [sq_nonneg ε, mul_nonneg (sq_nonneg ε) (sq_nonneg (ρ i j))]
    · have hp := pow_le_pow_left₀ (abs_nonneg (ρ i j))
        (hfar i j (Nat.lt_of_not_ge hn)) 2
      have hm := mul_le_mul_of_nonneg_right hp (sq_nonneg (ρ i j))
      nlinarith
  calc
    _ ≤ ∑ i, ∑ j, U ^ 2 *
        ((if Nat.dist j.val i.val ≤ R then ρ i j ^ 2 else 0) +
          ε ^ 2 * ρ i j ^ 2) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpoint i j
    _ = _ := by simp only [← Finset.mul_sum, Finset.sum_add_distrib,
      ← Finset.sum_filter]

/-- Quantitative E3 bound, in terms of scaled weights `u = S w`. -/
theorem normalized_weighted_fourth_le {m R : ℕ}
    (S ψ : ℝ) (hS : 0 < S) (ρ : Fin m → Fin m → ℝ)
    (u : Fin m → ℝ) (U ε C : ℝ) (hU : 0 ≤ U)
    (hu : ∀ i, |u i| ≤ U) (hρ : ∀ i j, |ρ i j| ≤ 1)
    (hε : 0 ≤ ε)
    (hfar : ∀ i j, R < Nat.dist j.val i.val → |ρ i j| ≤ ε)
    (hE : S ^ (2 * ψ - 2) * ∑ i, ∑ j, ρ i j ^ 2 ≤ C) :
    S ^ (2 * ψ - 2) * (∑ i, ∑ j, |u i * u j| * |ρ i j| ^ 4) ≤
      U ^ 2 * (S ^ (2 * ψ - 2) * (m : ℝ) * (2 * (R : ℝ) + 1) +
        ε ^ 2 * C) := by
  have hb := realScaleMeshBandEnergy_scaled_le S ψ hS ρ hρ (R := R)
  have hscalar := realScaleMeshEnergy_scaled_eq S ψ hS ρ
  have hband : realScaleMeshBandEnergy S R (fun i j => S ^ ψ * ρ i j) =
      S ^ (2 * ψ - 2) * (∑ i, ∑ j ∈ Finset.univ.filter
        (fun j : Fin m => Nat.dist j.val i.val ≤ R), ρ i j ^ 2) := by
    have hs : S⁻¹ ^ 2 * (S ^ ψ) ^ 2 = S ^ (2 * ψ - 2) := by
      rw [show S⁻¹ = S ^ (-1 : ℝ) by rw [Real.rpow_neg_one],
        ← Real.rpow_natCast, ← Real.rpow_natCast,
        ← Real.rpow_mul hS.le, ← Real.rpow_mul hS.le, ← Real.rpow_add hS]
      congr 1
      norm_num
      ring
    simp only [realScaleMeshBandEnergy, mul_pow, ← Finset.mul_sum]
    rw [← mul_assoc, hs]
  rw [hband] at hb
  have hf := mul_le_mul_of_nonneg_left
    (weighted_fourth_le_band_add_energy (R := R) ρ u U ε hU hu hρ hε hfar)
    (Real.rpow_nonneg hS.le (2 * ψ - 2))
  have he := mul_le_mul_of_nonneg_left hE (sq_nonneg ε)
  calc
    _ ≤ U ^ 2 * (S ^ (2 * ψ - 2) * (∑ i, ∑ j ∈ Finset.univ.filter
        (fun j : Fin m => Nat.dist j.val i.val ≤ R), ρ i j ^ 2) +
        ε ^ 2 * (S ^ (2 * ψ - 2) * ∑ i, ∑ j, ρ i j ^ 2)) := by
      convert hf using 1 <;> first | rfl | ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hb he) (sq_nonneg U)

/-- W8/E3 convergence from a vanishing near-band count, a vanishing far
correlation envelope, and a bounded normalized second energy. -/
theorem normalized_weighted_fourth_tendsto_zero
    (m R : ℕ → ℕ) (S ε : ℕ → ℝ) (ψ U C : ℝ)
    (ρ : ∀ n, Fin (m n) → Fin (m n) → ℝ)
    (u : ∀ n, Fin (m n) → ℝ)
    (hS : ∀ᶠ n in atTop, 0 < S n) (hU : 0 ≤ U)
    (hu : ∀ᶠ n in atTop, ∀ i, |u n i| ≤ U)
    (hρ : ∀ᶠ n in atTop, ∀ i j, |ρ n i j| ≤ 1)
    (hε : ∀ᶠ n in atTop, 0 ≤ ε n)
    (hfar : ∀ᶠ n in atTop, ∀ i j,
      R n < Nat.dist j.val i.val → |ρ n i j| ≤ ε n)
    (hE : ∀ᶠ n in atTop,
      S n ^ (2 * ψ - 2) * ∑ i, ∑ j, ρ n i j ^ 2 ≤ C)
    (hcut : Tendsto (fun n => S n ^ (2 * ψ - 2) *
      (m n : ℝ) * (2 * (R n : ℝ) + 1)) atTop (𝓝 0))
    (hε0 : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => S n ^ (2 * ψ - 2) *
      (∑ i, ∑ j, |u n i * u n j| * |ρ n i j| ^ 4)) atTop (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards [hS] with n hn
    exact mul_nonneg (Real.rpow_nonneg hn.le _) (Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (by positivity))
  · filter_upwards [hS, hu, hρ, hε, hfar, hE] with n hn hUn hρn hεn hfn hEn
    exact normalized_weighted_fourth_le (S n) ψ hn (ρ n) (u n) U (ε n) C
      hU hUn hρn hεn hfn hEn
  · simpa using (hcut.add ((hε0.pow 2).mul_const C)).const_mul (U ^ 2)

/-- The normalized second energy is bounded from kernel approximation and
reference energy. This works before inserting any signed weights. -/
theorem realScaleMeshEnergy_le_error_add_reference {m : ℕ}
    (S : ℝ) (A B : Fin m → Fin m → ℝ) :
    realScaleMeshEnergy S A ≤
      2 * realScaleMeshEnergy S (fun i j => A i j - B i j) +
      2 * realScaleMeshEnergy S B := by
  have hp : ∀ i j, A i j ^ 2 ≤ 2 * (A i j - B i j) ^ 2 + 2 * B i j ^ 2 := by
    intro i j
    nlinarith [sq_nonneg (A i j - 2 * B i j)]
  have hs := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) fun j _ => hp i j
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  unfold realScaleMeshEnergy
  nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg S⁻¹)]

/-- Hilbert-space proof of the absolute weighted covariance bound, retaining
pairwise correlations instead of replacing them by a row-sum maximum. -/
theorem gaussian_array_rank_second_moment_double_sum
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (hX : ∀ i, MeasurePreserving (X i) P (gaussianReal 0 1))
    (hpair : ∀ i j, HasGaussianLaw (fun ω => (X i ω, X j ω)) P)
    (w : ι → ℝ) (f : GaussianL2) (k : ℕ)
    (hk : ∀ n : ℕ, n < k → ⟪gaussianHermiteUnit n, f⟫ = 0) :
    (∫ ω, (∑ i, w i * f (X i ω)) ^ 2 ∂P) ≤
      ‖f‖ ^ 2 * ∑ i, ∑ j, |w i * w j| * |cov[X i, X j; P]| ^ k := by
  rw [gaussianArrayPullback_second_moment P X hX w f]
  have he : gaussianArrayPullback P X hX w f =
      ∑ i, w i • gaussianPullback P (X i) (hX i) f := by
    simp [gaussianArrayPullback]
  rw [he, ← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    conj_trivial, Finset.mul_sum]
  calc
    _ ≤ ∑ i, ∑ j, ‖f‖ ^ 2 * (|w i * w j| * |cov[X i, X j; P]| ^ k) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      have hb := jointGaussian_hermite_rank_bound P (X i) (X j)
        (hpair i j) (hX i) (hX j) f k hk
      rw [real_inner_comm, gaussianPullback_inner]
      have hm := mul_le_mul_of_nonneg_left hb (abs_nonneg (w i * w j))
      calc
        _ ≤ |w i * w j| * |∫ ω, f (X i ω) * f (X j ω) ∂P| := by
          rw [← abs_mul]
          convert le_abs_self (w i * w j * ∫ ω, f (X i ω) * f (X j ω) ∂P) using 1 <;> first | rfl | ring
        _ ≤ _ := by convert hm using 1 <;> first | rfl | ring
    _ = _ := by simp only [← Finset.mul_sum]

theorem featureGaussian_log_quadratic_error_double_sum {ι κ E : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (w : κ → ℝ) (a : κ → EuclideanSpace ℝ ι)
    (ha : ∀ j,∑ i,a j i • v i≠0) :
    (∫ x,(gaussianLogStatistic w a x-(∫ y,gaussianLogStatistic w a y ∂featureGaussian v)-
      gaussianLogQuadraticStatistic v w a x)^2 ∂featureGaussian v) ≤
      (gaussianLogSquareVariance-2) * ∑ i, ∑ j,
        |w i * w j| * |featureCorrelation v (a i) (a j)| ^ 4 := by
  have he := gaussian_array_rank_second_moment_double_sum (featureGaussian v)
    (fun i => standardizedFeatureObservation v (a i))
    (fun i => standardizedFeatureObservation_law v (a i) (ha i))
    (fun i j => standardizedFeatureObservation_pair v (a i) (a j)) w gaussianLogResidualLp 4 gaussianLogResidual_rank_four
  simp only [gaussianLogResidual_norm_sq, standardizedFeatureObservation_covariance] at he
  apply le_trans (le_of_eq ?_) he
  apply integral_congr_ae
  filter_upwards [gaussianLogStatistic_centered_standardized v w a ha,
    ae_all_iff.mpr (fun i => (standardizedFeatureObservation_law v (a i) (ha i)).quasiMeasurePreserving.ae
      gaussianLogResidualLp_ae)] with x hx hres
  rw [hx,gaussianLogQuadraticStatistic,← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [hres i]
  unfold gaussianLogResidual
  ring


theorem featureGaussian_log_limit_of_quadratic_limit_double_sum
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (m : ℕ → ℕ) (v : ∀ n,Fin n → E)
    (w : ∀ n,Fin (m n) → ℝ) (a : ∀ n,Fin (m n) → EuclideanSpace ℝ (Fin n))
    (c : ℕ → ℝ) (Z : Ω' → ℝ)
    (ha : ∀ᶠ n in atTop,∀ j,∑ i,a n j i • v n i≠0)
    (hW : Tendsto (fun n => (c n)^2*(∑ i, ∑ j, |w n i * w n j| * |featureCorrelation (v n) (a n i) (a n j)| ^ 4)) atTop (𝓝 0))
    (hquad : TendstoInDistribution
      (fun n x => c n*gaussianLogQuadraticStatistic (v n) (w n) (a n) x) atTop Z
      (fun n => featureGaussian (v n)) P') :
    TendstoInDistribution (fun n x => c n*(gaussianLogStatistic (w n) (a n) x-
      (∫ y,gaussianLogStatistic (w n) (a n) y ∂featureGaussian (v n)))) atTop Z
      (fun n => featureGaussian (v n)) P' := by
  let X := fun n x => c n*(gaussianLogStatistic (w n) (a n) x-
      (∫ y,gaussianLogStatistic (w n) (a n) y ∂featureGaussian (v n)))
  let Y := fun n x => c n*gaussianLogQuadraticStatistic (v n) (w n) (a n) x
  have he : ∀ᶠ n in atTop,MemLp (fun x => X n x-Y n x) 2 (featureGaussian (v n)) ∧
      (∫ x,(X n x-Y n x)^2 ∂featureGaussian (v n))≤
      (gaussianLogSquareVariance-2)*((c n)^2*(∑ i, ∑ j, |w n i * w n j| * |featureCorrelation (v n) (a n i) (a n j)| ^ 4)) := by
    filter_upwards [ha] with n hn
    have hX := ((gaussianLogStatistic_memLp_two (v n) (w n) (a n) hn).sub (memLp_const (∫ y,gaussianLogStatistic (w n) (a n) y ∂featureGaussian (v n)))).const_mul (c n)
    have hY := (gaussianLogQuadraticStatistic_memLp_two (v n) (w n) (a n)).const_mul (c n)
    refine ⟨hX.sub hY,?_⟩
    have hid : (∫ x,(X n x-Y n x)^2 ∂featureGaussian (v n))=
        (c n)^2*(∫ x,(gaussianLogStatistic (w n) (a n) x-(∫ y,gaussianLogStatistic (w n) (a n) y ∂featureGaussian (v n))-
          gaussianLogQuadraticStatistic (v n) (w n) (a n) x)^2 ∂featureGaussian (v n)) := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall (fun x => by dsimp [X,Y]; ring))
    rw [hid]
    convert mul_le_mul_of_nonneg_left (featureGaussian_log_quadratic_error_double_sum (v n) (w n) (a n) hn) (sq_nonneg (c n)) using 1 <;> first | rfl | ring
  apply triangular_L1_distribution_transfer (fun n => featureGaussian (v n)) P' Y X Z hquad
    (fun n => by dsimp [X]; unfold gaussianLogStatistic; fun_prop) (he.mono (fun _ hn => hn.1.integrable (by norm_num)))
  have hz : Tendsto (fun n => (gaussianLogSquareVariance-2)*((c n)^2*(∑ i, ∑ j, |w n i * w n j| * |featureCorrelation (v n) (a n i) (a n j)| ^ 4))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hW.const_mul (gaussianLogSquareVariance-2)
  have hs : Tendsto (fun n => Real.sqrt ((gaussianLogSquareVariance-2)*((c n)^2*(∑ i, ∑ j, |w n i * w n j| * |featureCorrelation (v n) (a n i) (a n j)| ^ 4)))) atTop (𝓝 0) := by
    convert Real.continuous_sqrt.continuousAt.tendsto.comp hz using 1 <;> first | rfl | simp only [Real.sqrt_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => integral_nonneg (fun _ => abs_nonneg _))) _ hs
  filter_upwards [he] with n hn
  exact (integral_abs_le_sqrt_second_moment (featureGaussian (v n)) _ hn.1).trans (Real.sqrt_le_sqrt hn.2)


/-- Converts scaled local weights `u = S w` to the normalization used by the
Gaussian statistic, whose multiplier is `S^ψ`. -/
theorem normalized_weighted_fourth_eq_original {m : ℕ}
    (S ψ : ℝ) (hS : 0 < S) (w : Fin m → ℝ) (ρ : Fin m → Fin m → ℝ) :
    S ^ (2 * ψ - 2) * (∑ i, ∑ j,
      |(S * w i) * (S * w j)| * |ρ i j| ^ 4) =
      (S ^ ψ) ^ 2 * (∑ i, ∑ j, |w i * w j| * |ρ i j| ^ 4) := by
  have hs : S ^ (2 * ψ - 2) * S ^ (2 : ℕ) = (S ^ ψ) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hS,
      ← Real.rpow_natCast, ← Real.rpow_mul hS.le]
    congr 1
    norm_num
    ring
  have hp : ∀ i j, |(S * w i) * (S * w j)| * |ρ i j| ^ 4 =
      S ^ 2 * (|w i * w j| * |ρ i j| ^ 4) := by
    intro i j
    rw [show (S * w i) * (S * w j) = S ^ 2 * (w i * w j) by ring,
      abs_mul, abs_of_nonneg (sq_nonneg S)]
    ring
  simp_rw [hp, ← Finset.mul_sum]
  rw [← mul_assoc, hs]

/-- The finite-row normalized energy is eventually bounded whenever its
unweighted kernel converges in squared mesh norm to an energy-bounded reference. -/
theorem realScaleMeshEnergy_eventually_bounded_of_approximation
    (m : ℕ → ℕ) (S : ℕ → ℝ)
    (A B : ∀ n, Fin (m n) → Fin (m n) → ℝ) (C : ℝ)
    (herror : Tendsto (fun n => realScaleMeshEnergy (S n)
      (fun i j => A n i j - B n i j)) atTop (𝓝 0))
    (hB : ∀ᶠ n in atTop, realScaleMeshEnergy (S n) (B n) ≤ C) :
    ∀ᶠ n in atTop, realScaleMeshEnergy (S n) (A n) ≤ 2 + 2 * C := by
  have he : ∀ᶠ n in atTop, realScaleMeshEnergy (S n)
      (fun i j => A n i j - B n i j) < 1 :=
    herror.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [he, hB] with n hn hBn
  have hb := realScaleMeshEnergy_le_error_add_reference (S n) (A n) (B n)
  linarith

/-- A scaled-correlation tail estimate supplies the vanishing far envelope
used above. Absolute values on both constants avoid a hidden sign assumption. -/
theorem correlation_le_of_scaled_tail (d R ψ c η r : ℝ)
    (hR : 0 < R) (hRd : R ≤ d) (hψ : 0 ≤ ψ)
    (htail : |d ^ ψ * r - c| ≤ η) :
    |r| ≤ (|c| + |η|) * R ^ (-ψ) := by
  have hd : 0 < d := hR.trans_le hRd
  have hpow : 0 < d ^ ψ := Real.rpow_pos_of_pos hd _
  have hbound : d ^ ψ * |r| ≤ |c| + |η| := by
    calc
      _ = |d ^ ψ * r| := by rw [abs_mul, abs_of_pos hpow]
      _ = |(d ^ ψ * r - c) + c| := by congr 1; ring
      _ ≤ |d ^ ψ * r - c| + |c| := abs_add_le _ _
      _ ≤ |c| + |η| := by linarith [le_abs_self η]
  have hinv : (d ^ ψ)⁻¹ ≤ (R ^ ψ)⁻¹ :=
    (inv_le_inv₀ (Real.rpow_pos_of_pos hd _) (Real.rpow_pos_of_pos hR _)).2
      (Real.rpow_le_rpow hR.le hRd hψ)
  calc
    |r| ≤ (|c| + |η|) / d ^ ψ := (le_div_iff₀ hpow).2 (by simpa [mul_comm] using hbound)
    _ ≤ (|c| + |η|) * (R ^ ψ)⁻¹ :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = _ := by rw [Real.rpow_neg hR.le]

/-- The far envelope tends to zero from `R → ∞` and the actual scaled tail
error `η → 0`; it is not a disguised fourth-moment convergence hypothesis. -/
theorem scaled_tail_envelope_tendsto_zero (R η : ℕ → ℝ) (ψ c : ℝ)
    (hψ : 0 < ψ) (hR : Tendsto R atTop atTop)
    (hη : Tendsto η atTop (𝓝 0)) :
    Tendsto (fun n => (|c| + |η n|) * R n ^ (-ψ)) atTop (𝓝 0) := by
  have hh := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => |c|) atTop (𝓝 |c|)).add hη.abs).mul
    ((tendsto_rpow_neg_atTop hψ).comp hR)
  simpa only [abs_zero, add_zero, mul_zero, Function.comp_def] using hh

end Hurst

#print axioms Hurst.normalized_weighted_fourth_tendsto_zero
#print axioms Hurst.featureGaussian_log_quadratic_error_double_sum
#print axioms Hurst.featureGaussian_log_limit_of_quadratic_limit_double_sum
#print axioms Hurst.realScaleMeshEnergy_eventually_bounded_of_approximation
#print axioms Hurst.correlation_le_of_scaled_tail
#print axioms Hurst.scaled_tail_envelope_tendsto_zero
