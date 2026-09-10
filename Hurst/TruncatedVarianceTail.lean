import Hurst.ActualCorrelationRowTail
import Hurst.TruncatedCovarianceLimit
import Hurst.WeightedRowEnergy

noncomputable section
open Set Filter
open scoped Topology RealInnerProductSpace
namespace Hurst

theorem featureCorrelation_abs_le_one_unconditional
    {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (a b : EuclideanSpace ℝ ι) :
    |featureCorrelation v a b| ≤ 1 := by
  simpa only [featureCorrelation] using
    abs_real_inner_div_norm_mul_norm_le_one
      (∑ i, a i • v i) (∑ i, b i • v i)

/-- A rank-two truncated covariance turns a uniform square-correlation row
tail into a weighted double-sum tail bound. -/
theorem weighted_truncatedCovariance_tail_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (val : ι → ℕ) (w : ι → ℝ) (corr : ι → ι → ℝ)
    (K cutoff : ℕ) (W L T : ℝ)
    (hW0 : 0 ≤ W) (hL0 : 0 ≤ L) (hT0 : 0 ≤ T)
    (hW : ∀ i, |w i| ≤ W) (hL : ∑ i, |w i| ≤ L)
    (hcorr : ∀ i j, |corr i j| ≤ 1)
    (hrow : ∀ i, ∑ j, (if cutoff < Nat.dist (val j) (val i) then
      |corr i j| ^ 2 else 0) ≤ T) :
    |∑ i, ∑ j, if cutoff < Nat.dist (val j) (val i) then
      w i * w j * gaussianLogTruncationCovariance K (corr i j) else 0| ≤
      (∑ n ∈ Finset.range K, gaussianLogHermiteCoefficient n ^ 2) *
        (W * L * T) := by
  let Q := ∑ n ∈ Finset.range K, gaussianLogHermiteCoefficient n ^ 2
  let A : ι → ι → ℝ := fun i j =>
    if cutoff < Nat.dist (val j) (val i) then |corr i j| ^ 2 else 0
  have hA0 : ∀ i j, 0 ≤ A i j := by
    intro i j
    dsimp only [A]
    split_ifs <;> positivity
  have hweighted := weighted_double_sum_le_max_l1_row w A W L T
    hW0 hL0 hT0 hW hL hA0 hrow
  calc
    |∑ i, ∑ j, if cutoff < Nat.dist (val j) (val i) then
        w i * w j * gaussianLogTruncationCovariance K (corr i j) else 0|
        ≤ ∑ i, ∑ j, |if cutoff < Nat.dist (val j) (val i) then
          w i * w j * gaussianLogTruncationCovariance K (corr i j) else 0| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun i hi => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ i, ∑ j, Q * (|w i| * |w j| * A i j) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      by_cases hd : cutoff < Nat.dist (val j) (val i)
      · simp only [hd, if_true, A, Q]
        have hc := gaussianLogTruncationCovariance_abs_le_square K (corr i j) (hcorr i j)
        rw [abs_mul, abs_mul]
        calc
          |w i| * |w j| * |gaussianLogTruncationCovariance K (corr i j)| ≤
              |w i| * |w j| * (|corr i j| ^ 2 *
                ∑ n ∈ Finset.range K, gaussianLogHermiteCoefficient n ^ 2) :=
            mul_le_mul_of_nonneg_left hc
              (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          _ = (∑ n ∈ Finset.range K, gaussianLogHermiteCoefficient n ^ 2) *
              (|w i| * |w j| * |corr i j| ^ 2) := by ring
      · simp [hd, A]
    _ = Q * (∑ i, ∑ j, |w i| * |w j| * A i j) := by
      simp only [Finset.mul_sum]
    _ ≤ Q * (W * L * T) := by
      exact mul_le_mul_of_nonneg_left hweighted
        (Finset.sum_nonneg (fun n hn => sq_nonneg _))
    _ = _ := rfl

/-- Standard epsilon/three argument: convergence of every fixed cutoff plus a
uniformly negligible tail and convergence of the cutoff limits imply
convergence of the full rows. -/
theorem tendsto_of_finiteCutoff_and_uniformTail
    (full : ℕ → ℝ) (approx : ℕ → ℕ → ℝ)
    (limit : ℕ → ℝ) (V : ℝ)
    (hpartial : ∀ R, Tendsto (fun n => approx R n) atTop (nhds (limit R)))
    (htail : ∀ ε > 0, ∀ᶠ R in atTop,
      ∀ᶠ n in atTop, |full n - approx R n| < ε)
    (hlimit : Tendsto limit atTop (nhds V)) :
    Tendsto full atTop (nhds V) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hRtail := htail (ε / 3) (by linarith)
  have hRlimit : ∀ᶠ R in atTop, |limit R - V| < ε / 3 := by
    have := hlimit.eventually
      (Metric.ball_mem_nhds V (ε := ε / 3) (by linarith))
    simpa only [Metric.mem_ball, Real.dist_eq] using this
  obtain ⟨R, htailR, hlimitR⟩ := (hRtail.and hRlimit).exists
  have hpartialR : ∀ᶠ n in atTop, |approx R n - limit R| < ε / 3 := by
    have := (hpartial R).eventually
      (Metric.ball_mem_nhds (limit R) (ε := ε / 3) (by linarith))
    simpa only [Metric.mem_ball, Real.dist_eq] using this
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 htailR
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 hpartialR
  refine ⟨max N₁ N₂, fun n hn ↦ ?_⟩
  have h₁ := hN₁ n (le_trans (le_max_left _ _) hn)
  have h₂ := hN₂ n (le_trans (le_max_right _ _) hn)
  rw [Real.dist_eq]
  calc
    |full n - V| ≤ |full n - approx R n| +
        |approx R n - limit R| + |limit R - V| := by
      calc
        |full n - V| = |(full n - approx R n) +
            (approx R n - limit R) + (limit R - V)| := by ring
        _ ≤ |full n - approx R n| + |approx R n - limit R| +
            |limit R - V| := (abs_add_le _ _).trans
              (add_le_add (abs_add_le _ _) le_rfl)
    _ < ε := by linarith

end Hurst
