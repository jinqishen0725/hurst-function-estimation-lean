import Hurst.TruncatedVarianceTail
import Hurst.WeightedCorrelationTail

noncomputable section
namespace Hurst

/-- A finite double sum splits exactly into pairs below a distance cutoff and
the complementary tail. -/
theorem finite_double_sum_sub_distance_lt_eq_tail
    (m R : ℕ) (F : Fin m → Fin m → ℝ) :
    (∑ i, ∑ j, F i j) -
        (∑ i, ∑ j, if Nat.dist i.val j.val < R then F i j else 0) =
      ∑ i, ∑ j, if R ≤ Nat.dist i.val j.val then F i j else 0 := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : Nat.dist i.val j.val < R
  · simp [h, Nat.not_le.mpr h]
  · simp [h, Nat.le_of_not_gt h]

/-- Same split in the strict-tail convention used by correlation row-tail
bounds. -/
theorem finite_double_sum_sub_distance_lt_succ_eq_tail
    (m R : ℕ) (F : Fin m → Fin m → ℝ) :
    (∑ i, ∑ j, F i j) -
        (∑ i, ∑ j, if Nat.dist i.val j.val < R + 1 then F i j else 0) =
      ∑ i, ∑ j, if R < Nat.dist i.val j.val then F i j else 0 := by
  rw [finite_double_sum_sub_distance_lt_eq_tail]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : R < Nat.dist i.val j.val
  · simp [h]
  · have hn : ¬ R + 1 ≤ Nat.dist i.val j.val := by omega
    simp [h, hn]

/-- Max-weight and L1 stability turn a uniform square-correlation row tail
into a uniformly negligible scaled truncated-covariance tail. -/
theorem weighted_truncationCovariance_uniform_tail
    (m : ℕ → ℕ) (M : ℕ) (scale : ℕ → ℝ)
    (w : ∀ n, Fin (m n) → ℝ)
    (corr : ∀ n, Fin (m n) → Fin (m n) → ℝ)
    (D B : ℝ) (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hscale : ∀ᶠ n in Filter.atTop, 0 < scale n)
    (hwmax : ∀ᶠ n in Filter.atTop, ∀ i, |w n i| ≤ D / scale n)
    (hwmass : ∀ᶠ n in Filter.atTop, ∑ i, |w n i| ≤ B)
    (hcorr : ∀ n i j, |corr n i j| ≤ 1)
    (htail : ∀ ε > 0, ∃ R : ℕ, ∀ᶠ n in Filter.atTop, ∀ i,
      ∑ j, (if R < Nat.dist j.val i.val then |corr n i j| ^ 2 else 0) ≤ ε) :
    ∀ ε > 0, ∀ᶠ R : ℕ in Filter.atTop, ∀ᶠ n : ℕ in Filter.atTop,
      scale n * |∑ i, ∑ j, if R < Nat.dist j.val i.val then
        w n i * w n j * gaussianLogTruncationCovariance M (corr n i j)
      else 0| < ε := by
  intro ε hε
  let E : ℝ := ∑ k ∈ Finset.range M, gaussianLogHermiteCoefficient k ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg (fun k _ => sq_nonneg _)
  let C : ℝ := D * B * E
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hden : 0 < C + 1 := by linarith
  obtain ⟨R₀, hR₀⟩ := htail (ε / (C + 1)) (div_pos hε hden)
  filter_upwards [Filter.eventually_ge_atTop R₀] with R hRR
  filter_upwards [hscale, hwmax, hwmass, hR₀] with n hn hmax hmass hrow
  have hrow' : ∀ i, ∑ j,
      (if R < Nat.dist j.val i.val then |corr n i j| ^ 2 else 0) ≤
        ε / (C + 1) := by
    intro i
    apply le_trans (Finset.sum_le_sum (fun j _ => ?_)) (hrow i)
    by_cases hj : R < Nat.dist j.val i.val
    · have hj₀ : R₀ < Nat.dist j.val i.val := lt_of_le_of_lt hRR hj
      simp [hj, hj₀]
    · simp only [hj, if_false]
      split_ifs <;> positivity
  have hb := weighted_truncationCovariance_tail_le
    (m n) R M (scale n) D B (ε / (C + 1)) hn hD hB
    (div_nonneg hε.le hden.le) (w n) (corr n) hmax hmass
    (hcorr n) (fun i => by simpa only [sq_abs] using hrow' i)
  change scale n * |∑ i, ∑ j, if R < Nat.dist j.val i.val then
      w n i * w n j * gaussianLogTruncationCovariance M (corr n i j)
    else 0| < ε
  calc
    _ ≤ D * B * E * (ε / (C + 1)) := by simpa only [E] using hb
    _ = C * (ε / (C + 1)) := by rfl
    _ < ε := by
      have hquot : C * ε / (C + 1) < ε := by
        rw [div_lt_iff₀ hden]
        nlinarith
      convert hquot using 1 <;> ring

/-- Actual local-polynomial weights satisfy the hypotheses of the generic
weighted tail theorem whenever the bandwidth shrinks and `n * δ n` diverges. -/
theorem localPolynomialWeights_truncationCovariance_uniform_tail
    (r q M : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in Filter.atTop, 0 < δ n)
    (hδ : Filter.Tendsto δ Filter.atTop (nhds 0))
    (hN : Filter.Tendsto (fun n : ℕ => (n : ℝ) * δ n)
      Filter.atTop Filter.atTop)
    (corr : ∀ n, Fin (n - q) → Fin (n - q) → ℝ)
    (hcorr : ∀ n i j, |corr n i j| ≤ 1)
    (htail : ∀ ε > 0, ∃ R : ℕ, ∀ᶠ n in Filter.atTop, ∀ i,
      ∑ j, (if R < Nat.dist j.val i.val then |corr n i j| ^ 2 else 0) ≤ ε) :
    ∀ ε > 0, ∀ᶠ R : ℕ in Filter.atTop, ∀ᶠ n : ℕ in Filter.atTop,
      ((n : ℝ) * δ n) * |∑ i, ∑ j, if R < Nat.dist j.val i.val then
        localPolynomialWeights r n q (δ n) t i *
          localPolynomialWeights r n q (δ n) t j *
            gaussianLogTruncationCovariance M (corr n i j)
      else 0| < ε := by
  obtain ⟨N₀, hN₀, D, hD, hw⟩ := localPolynomialWeights_uniform_stability r q
  apply weighted_truncationCovariance_uniform_tail
    (fun n => n - q) M (fun n => (n : ℝ) * δ n)
    (fun n => localPolynomialWeights r n q (δ n) t) corr D D hD.le hD.le
  · filter_upwards [hδpos, Filter.eventually_ge_atTop 1] with n hnδ hn
    positivity
  · filter_upwards [hδpos,
      hδ.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
      hN.eventually_ge_atTop N₀, Filter.eventually_ge_atTop (q + 1)] with
      n hnδ hnδhalf hnN hnq
    have hn0 : 0 < n := by omega
    exact (hw n hn0 (by omega) (δ n) t hnδ hnδhalf.le ht hnN).2.1
  · filter_upwards [hδpos,
      hδ.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
      hN.eventually_ge_atTop N₀, Filter.eventually_ge_atTop (q + 1)] with
      n hnδ hnδhalf hnN hnq
    have hn0 : 0 < n := by omega
    exact (hw n hn0 (by omega) (δ n) t hnδ hnδhalf.le ht hnN).2.2.1
  · exact hcorr
  · exact htail

end Hurst
