import Hurst.TruncatedVarianceFormula
import Hurst.ShiftedWeightEnergy

noncomputable section
open Filter
open scoped Topology
namespace Hurst

/-- A finite Hermite covariance truncation is a polynomial, hence continuous
in the correlation parameter. -/
theorem continuous_gaussianLogTruncationCovariance (K : ℕ) :
    Continuous (gaussianLogTruncationCovariance K) := by
  unfold gaussianLogTruncationCovariance
  fun_prop

/-- The rank-two property survives every finite truncation.  On the correlation
interval `[-1,1]`, its absolute value is bounded by `|ρ|²` times the finite
coefficient energy. -/
theorem gaussianLogTruncationCovariance_abs_le_square
    (K : ℕ) (ρ : ℝ) (hρ : |ρ| ≤ 1) :
    |gaussianLogTruncationCovariance K ρ| ≤
      |ρ| ^ 2 * ∑ n ∈ Finset.range K, gaussianLogHermiteCoefficient n ^ 2 := by
  unfold gaussianLogTruncationCovariance
  calc
    |∑ n ∈ Finset.range K,
        gaussianLogHermiteCoefficient n ^ 2 * ρ ^ n| ≤
        ∑ n ∈ Finset.range K,
          |gaussianLogHermiteCoefficient n ^ 2 * ρ ^ n| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.range K,
        |ρ| ^ 2 * gaussianLogHermiteCoefficient n ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      rw [abs_mul, abs_sq, abs_pow]
      by_cases hn2 : n < 2
      · have hz : gaussianLogHermiteCoefficient n = 0 := by
          exact gaussianLog_hermite_rank_at_least_two n hn2
        rw [hz]
        simp
      · have hp := pow_le_pow_of_le_one (abs_nonneg ρ) hρ
          (Nat.le_of_not_gt hn2)
        simpa only [mul_comm] using
          (mul_le_mul_of_nonneg_right hp
            (sq_nonneg (gaussianLogHermiteCoefficient n)))
    _ = _ := by rw [Finset.mul_sum]

/-- Transfer a fixed-lag weight-energy limit through a uniformly convergent
finite Hermite covariance profile.  The absolute product-mass hypothesis is
the exact deterministic input needed to sum the uniform approximation error. -/
theorem weighted_fixedLag_truncationCovariance_tendsto
    (m : ℕ → ℕ) (s : ℕ → ℝ)
    (w u : ∀ n, Fin (m n) → ℝ) (corr : ∀ n, Fin (m n) → ℝ)
    (K : ℕ) (ρ E B : ℝ) (_hB : 0 ≤ B)
    (henergy : Tendsto (fun n => s n * ∑ i, w n i * u n i)
      atTop (nhds E))
    (eps : ℕ → ℝ) (heps : Tendsto eps atTop (nhds 0))
    (heps0 : ∀ᶠ n in atTop, 0 ≤ eps n)
    (huniform : ∀ᶠ n in atTop, ∀ i, w n i * u n i ≠ 0 →
      |gaussianLogTruncationCovariance K (corr n i) -
        gaussianLogTruncationCovariance K ρ| ≤ eps n)
    (hmass : ∀ᶠ n in atTop,
      |s n| * ∑ i, |w n i * u n i| ≤ B) :
    Tendsto (fun n => s n * ∑ i, w n i * u n i *
      gaussianLogTruncationCovariance K (corr n i)) atTop
      (nhds (E * gaussianLogTruncationCovariance K ρ)) := by
  let C := gaussianLogTruncationCovariance K ρ
  have herr : Tendsto (fun n => s n * ∑ i, w n i * u n i *
      (gaussianLogTruncationCovariance K (corr n i) - C)) atTop (nhds 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero, Real.norm_eq_abs]
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall (fun n => abs_nonneg _)
    · filter_upwards [huniform, hmass, heps0] with n hn hmassn hepsn
      calc
        |s n * ∑ i, w n i * u n i *
              (gaussianLogTruncationCovariance K (corr n i) - C)|
            = |s n| * |∑ i, w n i * u n i *
              (gaussianLogTruncationCovariance K (corr n i) - C)| := by
          rw [abs_mul]
        _ ≤ |s n| * ∑ i, |w n i * u n i *
              (gaussianLogTruncationCovariance K (corr n i) - C)| := by
          gcongr
          exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ |s n| * ∑ i, |w n i * u n i| * eps n := by
          gcongr with i
          by_cases hwu : w n i * u n i = 0
          · simp [hwu, hepsn]
          · rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (hn i hwu) (abs_nonneg _)
        _ = (|s n| * ∑ i, |w n i * u n i|) * eps n := by
          rw [← Finset.sum_mul]
          ring
        _ ≤ B * eps n := mul_le_mul_of_nonneg_right hmassn hepsn
    · simpa only [mul_zero] using heps.const_mul B
  have hmain := henergy.const_mul C
  have hsum := herr.add hmain
  convert hsum using 1
  · funext n
    dsimp only [C]
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  · simp only [C]
    ring

/-- A finite collection of fixed-lag limits can be summed without any tail
assumption.  This is the finite-cutoff layer of the actual variance argument. -/
theorem tendsto_sum_fixed_lags {R : ℕ} (f : ℕ → Fin R → ℝ)
    (g : Fin R → ℝ)
    (h : ∀ k, Tendsto (fun n => f n k) atTop (nhds (g k))) :
    Tendsto (fun n => ∑ k, f n k) atTop (nhds (∑ k, g k)) := by
  exact tendsto_finsetSum Finset.univ (fun k _ => h k)

/-- The scaled absolute product mass of a fixed shift of actual local
polynomial weights is eventually bounded. -/
theorem localPolynomialWeights_fixedShift_abs_mass
    (r q k : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ : Tendsto δ atTop (nhds 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop) :
    ∃ C > 0, ∀ᶠ n : ℕ in atTop,
      |(n : ℝ) * δ n| * ∑ i,
        |localPolynomialWeights r n q (δ n) t i *
          finZeroExtendedShift k
            (localPolynomialWeights r n q (δ n) t) i| ≤ C := by
  obtain ⟨N₀, hN₀, C, hC, hw⟩ := localPolynomialWeights_uniform_stability r q
  refine ⟨C ^ 2, sq_pos_of_pos hC, ?_⟩
  filter_upwards [hδpos,
      hδ.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
      hN.eventually_ge_atTop N₀, eventually_ge_atTop (q + 1)] with
      n hnδ hnδhalf hnN hnq
  have hn0 : 0 < n := by omega
  obtain ⟨_, hmax, hl1, _⟩ :=
    hw n hn0 (by omega) (δ n) t hnδ hnδhalf.le ht hnN
  have hshift (i : Fin (n - q)) :
      |finZeroExtendedShift k
        (localPolynomialWeights r n q (δ n) t) i| ≤
          C / ((n : ℝ) * δ n) := by
    unfold finZeroExtendedShift
    split_ifs with hi
    · exact hmax _
    · simp
      positivity
  have hsum : (∑ i,
      |localPolynomialWeights r n q (δ n) t i *
        finZeroExtendedShift k
          (localPolynomialWeights r n q (δ n) t) i|) ≤
      (C / ((n : ℝ) * δ n)) * C := by
    calc
      _ = ∑ i, |localPolynomialWeights r n q (δ n) t i| *
          |finZeroExtendedShift k
            (localPolynomialWeights r n q (δ n) t) i| := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [abs_mul]
      _ ≤ ∑ i, |localPolynomialWeights r n q (δ n) t i| *
          (C / ((n : ℝ) * δ n)) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hshift i) (abs_nonneg _)
      _ = (C / ((n : ℝ) * δ n)) *
          ∑ i, |localPolynomialWeights r n q (δ n) t i| := by
        rw [← Finset.sum_mul]
        ring
      _ ≤ (C / ((n : ℝ) * δ n)) * C := by
        exact mul_le_mul_of_nonneg_left hl1 (by positivity)
  rw [abs_of_pos (mul_pos (by exact_mod_cast hn0) hnδ)]
  have hmul := mul_le_mul_of_nonneg_left hsum
    (mul_nonneg (Nat.cast_nonneg n) hnδ.le)
  calc
    (n : ℝ) * δ n * ∑ i,
        |localPolynomialWeights r n q (δ n) t i *
          finZeroExtendedShift k
            (localPolynomialWeights r n q (δ n) t) i|
        ≤ (n : ℝ) * δ n *
          ((C / ((n : ℝ) * δ n)) * C) := hmul
    _ = C ^ 2 := by field_simp

/-- Fixed-lag covariance limit for actual local-polynomial weights, once a
uniform covariance-profile approximation at that lag has been supplied. -/
theorem localPolynomialWeights_fixedShift_truncationCovariance_tendsto
    (r q k K : ℕ) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ : Tendsto δ atTop (nhds 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (corr : ∀ n, Fin (n - q) → ℝ) (ρ : ℝ)
    (eps : ℕ → ℝ) (heps : Tendsto eps atTop (nhds 0))
    (heps0 : ∀ᶠ n in atTop, 0 ≤ eps n)
    (huniform : ∀ᶠ n in atTop, ∀ i,
      localPolynomialWeights r n q (δ n) t i *
        finZeroExtendedShift k
          (localPolynomialWeights r n q (δ n) t) i ≠ 0 →
      |gaussianLogTruncationCovariance K (corr n i) -
        gaussianLogTruncationCovariance K ρ| ≤ eps n) :
    Tendsto (fun n : ℕ => (n : ℝ) * δ n * ∑ i,
      localPolynomialWeights r n q (δ n) t i *
        finZeroExtendedShift k
          (localPolynomialWeights r n q (δ n) t) i *
            gaussianLogTruncationCovariance K (corr n i)) atTop
      (nhds ((∫ x in (-1 : ℝ)..1, equivalentKernel r x ^ 2) *
        gaussianLogTruncationCovariance K ρ)) := by
  obtain ⟨C, hC, hmass⟩ := localPolynomialWeights_fixedShift_abs_mass
    r q k t ⟨ht.1.le, ht.2.le⟩ δ hδpos hδ hN
  exact weighted_fixedLag_truncationCovariance_tendsto
    (fun n => n - q) (fun n => (n : ℝ) * δ n)
    (fun n => localPolynomialWeights r n q (δ n) t)
    (fun n => finZeroExtendedShift k
      (localPolynomialWeights r n q (δ n) t)) corr K ρ
    (∫ x in (-1 : ℝ)..1, equivalentKernel r x ^ 2) C hC.le
    (localPolynomialWeights_fixedShift_energy_tendsto
      r q k t ht δ hδpos hδ hN)
    eps heps heps0 huniform hmass

/-- The same transfer stated with the natural epsilon formulation of uniform
convergence.  This avoids choosing an explicit rate for the correlation
approximation. -/
theorem weighted_fixedLag_truncationCovariance_tendsto_of_uniform
    (m : ℕ → ℕ) (s : ℕ → ℝ)
    (w u : ∀ n, Fin (m n) → ℝ) (corr : ∀ n, Fin (m n) → ℝ)
    (K : ℕ) (ρ E B : ℝ) (hB : 0 ≤ B)
    (henergy : Tendsto (fun n => s n * ∑ i, w n i * u n i)
      atTop (nhds E))
    (huniform : ∀ ε > 0, ∀ᶠ n in atTop, ∀ i, w n i * u n i ≠ 0 →
      |gaussianLogTruncationCovariance K (corr n i) -
        gaussianLogTruncationCovariance K ρ| < ε)
    (hmass : ∀ᶠ n in atTop,
      |s n| * ∑ i, |w n i * u n i| ≤ B) :
    Tendsto (fun n => s n * ∑ i, w n i * u n i *
      gaussianLogTruncationCovariance K (corr n i)) atTop
      (nhds (E * gaussianLogTruncationCovariance K ρ)) := by
  let C := gaussianLogTruncationCovariance K ρ
  have herr : Tendsto (fun n => s n * ∑ i, w n i * u n i *
      (gaussianLogTruncationCovariance K (corr n i) - C)) atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hden : 0 < B + 1 := by linarith
    have hsmall := huniform (ε / (B + 1)) (div_pos hε hden)
    obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 hmass
    obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 hsmall
    refine ⟨max N₁ N₂, fun n hn ↦ ?_⟩
    have hmassn := hN₁ n (le_trans (le_max_left _ _) hn)
    have hnunif := hN₂ n (le_trans (le_max_right _ _) hn)
    rw [Real.dist_eq, sub_zero]
    calc
      |s n * ∑ i, w n i * u n i *
          (gaussianLogTruncationCovariance K (corr n i) - C)|
          ≤ |s n| * ∑ i, |w n i * u n i| * (ε / (B + 1)) := by
        rw [abs_mul]
        gcongr
        calc
          |∑ i, w n i * u n i *
              (gaussianLogTruncationCovariance K (corr n i) - C)|
              ≤ ∑ i, |w n i * u n i *
                (gaussianLogTruncationCovariance K (corr n i) - C)| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i, |w n i * u n i| * (ε / (B + 1)) := by
            apply Finset.sum_le_sum
            intro i hi
            by_cases hwu : w n i * u n i = 0
            · simp [hwu]
            · rw [abs_mul]
              exact mul_le_mul_of_nonneg_left (le_of_lt (hnunif i hwu)) (abs_nonneg _)
      _ = (|s n| * ∑ i, |w n i * u n i|) * (ε / (B + 1)) := by
        rw [← Finset.sum_mul]
        ring
      _ ≤ B * (ε / (B + 1)) := by
        exact mul_le_mul_of_nonneg_right hmassn (div_nonneg hε.le hden.le)
      _ < ε := by
        calc
          B * (ε / (B + 1)) = ε * (B / (B + 1)) := by ring
          _ < ε * 1 := mul_lt_mul_of_pos_left
            ((div_lt_one hden).2 (by linarith)) hε
          _ = ε := mul_one _
  have hmain := henergy.const_mul C
  have hsum := herr.add hmain
  convert hsum using 1
  · funext n
    dsimp only [C]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  · simp only [C]
    ring

/-- Local-polynomial specialization of the epsilon-form fixed-lag transfer. -/
theorem localPolynomialWeights_fixedShift_truncationCovariance_tendsto_of_uniform
    (r q k K : ℕ) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ : Tendsto δ atTop (nhds 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (corr : ∀ n, Fin (n - q) → ℝ) (ρ : ℝ)
    (huniform : ∀ ε > 0, ∀ᶠ n in atTop, ∀ i,
      localPolynomialWeights r n q (δ n) t i *
        finZeroExtendedShift k
          (localPolynomialWeights r n q (δ n) t) i ≠ 0 →
      |gaussianLogTruncationCovariance K (corr n i) -
        gaussianLogTruncationCovariance K ρ| < ε) :
    Tendsto (fun n : ℕ => (n : ℝ) * δ n * ∑ i,
      localPolynomialWeights r n q (δ n) t i *
        finZeroExtendedShift k
          (localPolynomialWeights r n q (δ n) t) i *
            gaussianLogTruncationCovariance K (corr n i)) atTop
      (nhds ((∫ x in (-1 : ℝ)..1, equivalentKernel r x ^ 2) *
        gaussianLogTruncationCovariance K ρ)) := by
  obtain ⟨C, hC, hmass⟩ := localPolynomialWeights_fixedShift_abs_mass
    r q k t ⟨ht.1.le, ht.2.le⟩ δ hδpos hδ hN
  exact weighted_fixedLag_truncationCovariance_tendsto_of_uniform
    (fun n => n - q) (fun n => (n : ℝ) * δ n)
    (fun n => localPolynomialWeights r n q (δ n) t)
    (fun n => finZeroExtendedShift k
      (localPolynomialWeights r n q (δ n) t)) corr K ρ
    (∫ x in (-1 : ℝ)..1, equivalentKernel r x ^ 2) C hC.le
    (localPolynomialWeights_fixedShift_energy_tendsto
      r q k t ht δ hδpos hδ hN) huniform hmass

end Hurst
