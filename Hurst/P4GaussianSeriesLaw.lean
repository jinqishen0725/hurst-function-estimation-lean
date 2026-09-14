import Hurst.SecondChaosSeriesL2
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration

/-!
# P4: A constructed probability space carrying the Gaussian second-chaos series

This file discharges the "assumed probability space" gap of
`IsSecondChaosSeriesLaw` (file 23, step C1) by *constructing* the space:

* `Ω := ℕ → ℝ` with `gaussianSeqMeasure := Measure.infinitePi
  (fun _ : ℕ => gaussianReal 0 1)`;
* the coordinate evaluations `gaussianSeqVar j x = x j` form a mutually
  independent sequence, each with law `gaussianReal 0 1`
  (`gaussianSeqMeasure_map_var`, `gaussianSeq_iIndepFun`);
* for every square-summable coefficient sequence `lambda` the partial sums
  `∑ j ∈ range K, lambda j (x j² − 1)` are Cauchy in `L²`, converge to an
  explicitly existing `L²`-limit `Q`, every `Q − S_K` is in `L²` and the
  squared error integral tends to zero
  (`exists_gaussSeries_L2limit`; file 23, step C2).

The remaining field of `IsSecondChaosSeriesLaw` (full-sequence a.s.
convergence of `S_K` to `Q`, file 23 step C3) is **not** discharged in
this revision: it requires the maximal inequality of file 23 C3 (or an
L¹-bounded martingale construction on the cylinder filtration).  Note that
mathlib's `MeasureTheory.ae_tendsto_of_cauchy_eLpNorm'` does **not** close
it as stated: its Cauchy bound `B` must satisfy `∑' B i ≠ ∞`, which for
`S_K` would need `∑_N √(2·tail_N) < ∞` — false for general square-summable
`lambda` — so it only yields a.s. convergence along a sparse subsequence.
This is reported as the open gap.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal
namespace Hurst

/-! ### The constructed iid standard Gaussian sequence space -/

/-- The countable product of standard Gaussian laws on `ℕ → ℝ`. -/
def gaussianSeqMeasure : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)

instance : IsProbabilityMeasure gaussianSeqMeasure := by
  unfold gaussianSeqMeasure
  infer_instance

/-- The `j`-th coordinate random variable on the Gaussian sequence space. -/
def gaussianSeqVar (j : ℕ) : (ℕ → ℝ) → ℝ := fun x => x j

theorem gaussianSeqVar_measurable (j : ℕ) : Measurable (gaussianSeqVar j) := by
  exact measurable_pi_apply j

/-- The law of the `j`-th coordinate is the standard Gaussian. -/
theorem gaussianSeqMeasure_map_var (j : ℕ) :
    gaussianSeqMeasure.map (gaussianSeqVar j) = gaussianReal 0 1 :=
  (measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) j).map_eq

/-- The coordinate evaluations are mutually independent under the Gaussian
product measure (mathlib `iIndepFun_infinitePi` on the constructed
product). -/
theorem gaussianSeq_iIndepFun :
    iIndepFun (fun (j : ℕ) (x : ℕ → ℝ) => x j) gaussianSeqMeasure :=
  iIndepFun_infinitePi (fun _ => measurable_id)

/-- The iid package of `Hurst.SecondChaosSeriesL2` instantiated on the
constructed space: exact finite-sum `L²` isometry. -/
theorem gaussianSeq_centeredSquare_finset_L2 (lambda : ℕ → ℝ) (s : Finset ℕ) :
    (∫ x, (∑ j ∈ s, lambda j * ((x j) ^ 2 - 1)) ^ 2 ∂gaussianSeqMeasure) =
      2 * ∑ j ∈ s, (lambda j) ^ 2 :=
  iid_standardGaussian_centeredSquare_finset_L2 gaussianSeqMeasure gaussianSeqVar
    (fun j => (gaussianSeqVar_measurable j).aemeasurable) gaussianSeq_iIndepFun
    gaussianSeqMeasure_map_var lambda s

/-! ### Partial sums, their `L²` membership and exact tail variance -/

/-- The `K`-th partial sum of the Gaussian second-chaos series on the
constructed space. -/
def gaussPartial (lambda : ℕ → ℝ) (K : ℕ) : (ℕ → ℝ) → ℝ :=
  fun x => ∑ j ∈ Finset.range K, lambda j * ((x j) ^ 2 - 1)

theorem gaussPartial_memLp (lambda : ℕ → ℝ) (K : ℕ) :
    MemLp (gaussPartial lambda K) 2 gaussianSeqMeasure := by
  have h : MemLp (fun x => ∑ j ∈ Finset.range K, lambda j * ((x j) ^ 2 - 1)) 2
      gaussianSeqMeasure := by
    refine memLp_finsetSum _ (fun j _ => ?_)
    exact (iid_standardGaussian_centeredSquare_memLp gaussianSeqMeasure gaussianSeqVar
      (fun j => (gaussianSeqVar_measurable j).aemeasurable) gaussianSeqMeasure_map_var
      j).const_mul _
  exact h

/-- Exact squared `L²` distance between the partial sums with cutoffs
`N ≤ M`. -/
theorem gaussPartial_L2 (lambda : ℕ → ℝ) (M N : ℕ) (hMN : N ≤ M) :
    (∫ x, (gaussPartial lambda M x - gaussPartial lambda N x) ^ 2 ∂gaussianSeqMeasure)
      = 2 * ∑ j ∈ Finset.range M \ Finset.range N, (lambda j) ^ 2 := by
  have hrangesub : Finset.range N ⊆ Finset.range M := by
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  obtain ⟨_, hint⟩ := iid_standardGaussian_centeredSquare_finset_difference_L2
    gaussianSeqMeasure gaussianSeqVar
    (fun j => (gaussianSeqVar_measurable j).aemeasurable) gaussianSeq_iIndepFun
    gaussianSeqMeasure_map_var lambda (Finset.range M) (Finset.range N)
    hrangesub
  convert hint using 3
  all_goals rfl

/-- For an `L²` function into `ℝ`, the squared `eLpNorm` computed via the
ordinary integral of the square. -/
theorem memLp_integral_sq_eq_eLpNorm {f : (ℕ → ℝ) → ℝ}
    (hf : MemLp f 2 gaussianSeqMeasure) :
    (∫ x, f x ^ 2 ∂gaussianSeqMeasure) = (eLpNorm f 2 gaussianSeqMeasure).toReal ^ 2 := by
  have hint : (0:ℝ) ≤ ∫ x, f x ^ 2 ∂gaussianSeqMeasure :=
    integral_nonneg fun x => sq_nonneg _
  have hexp : ((2:ℝ≥0∞) : ℝ≥0∞).toReal = (2:ℝ) := by norm_num
  have hinv : (2:ℝ)⁻¹ = (1/2:ℝ) := by norm_num
  have hnorm : (∫ x, ‖f x‖ ^ (2:ℝ) ∂gaussianSeqMeasure)
      = ∫ x, f x ^ 2 ∂gaussianSeqMeasure := by
    congr 1
    funext x
    simp [Real.norm_eq_abs, sq_abs]
  have hpow : (0:ℝ) ≤ (∫ x, f x ^ 2 ∂gaussianSeqMeasure) ^ (1/2:ℝ) :=
    Real.rpow_nonneg hint _
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp), hexp, hnorm, hinv,
    ENNReal.toReal_ofReal hpow, ← Real.sqrt_eq_rpow, Real.sq_sqrt hint]

/-! ### The `L²` limit of the series -/

/-- Existence of the `L²` limit of the Gaussian second-chaos series with
square-summable coefficients on the constructed space: every tail
`Q − S_K` is in `L²` and its squared error integral tends to zero. -/
theorem exists_gaussSeries_L2limit (lambda : ℕ → ℝ)
    (hlambda : Summable (fun j => (lambda j) ^ 2)) :
    ∃ Q : (ℕ → ℝ) → ℝ,
      MemLp Q 2 gaussianSeqMeasure ∧
      (∀ K : ℕ, MemLp (fun x => Q x - gaussPartial lambda K x) 2 gaussianSeqMeasure) ∧
      Tendsto (fun K : ℕ =>
        ∫ x, (Q x - gaussPartial lambda K x) ^ 2 ∂gaussianSeqMeasure) atTop (𝓝 0) := by
  classical
  set S : ℕ → Lp ℝ 2 gaussianSeqMeasure := fun K =>
    MemLp.toLp (gaussPartial lambda K) (gaussPartial_memLp lambda K) with hS
  have hcoecoe : ∀ K : ℕ,
      (S K : (ℕ → ℝ) → ℝ) =ᵐ[gaussianSeqMeasure] gaussPartial lambda K :=
    fun K => (gaussPartial_memLp lambda K).coeFn_toLp
  have hSdist : ∀ M N : ℕ, dist (S M) (S N) =
      (eLpNorm (fun x => gaussPartial lambda M x - gaussPartial lambda N x) 2
        gaussianSeqMeasure).toReal := by
    intro M N
    rw [Lp.dist_def, eLpNorm_congr_ae ((hcoecoe M).sub (hcoecoe N))]
    rfl
  have htotal : HasSum (fun j => (lambda j) ^ 2) (∑' j, (lambda j) ^ 2) :=
    hlambda.hasSum
  have hsub : ∀ M : ℕ, ∀ N : ℕ, N ≤ M →
      (∑ j ∈ Finset.range M \ Finset.range N, (lambda j) ^ 2)
        ≤ (∑' j, (lambda j) ^ 2) - ∑ j ∈ Finset.range N, (lambda j) ^ 2 := by
    intro M N hMN
    have hrangesub : Finset.range N ⊆ Finset.range M := by
      intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    have hsplit0 := Finset.sum_sdiff hrangesub (f := fun j : ℕ => (lambda j) ^ 2)
    have hsplit : (∑ j ∈ Finset.range M, (lambda j) ^ 2)
        = (∑ j ∈ Finset.range N, (lambda j) ^ 2)
          + (∑ j ∈ Finset.range M \ Finset.range N, (lambda j) ^ 2) := by linarith
    have hle : (∑ j ∈ Finset.range M, (lambda j) ^ 2)
        ≤ ∑' j, (lambda j) ^ 2 :=
      hlambda.sum_le_tsum (Finset.range M) (fun j _ => sq_nonneg _)
    linarith
  have hCauchy : CauchySeq S := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    have htail : Tendsto (fun N : ℕ =>
        (∑' j, (lambda j) ^ 2) - ∑ j ∈ Finset.range N, (lambda j) ^ 2) atTop (𝓝 0) := by
      have h1 : Tendsto (fun N : ℕ => ∑ j ∈ Finset.range N, (lambda j) ^ 2) atTop
          (𝓝 (∑' j, (lambda j) ^ 2)) := htotal.tendsto_sum_nat
      exact (h1.const_sub (∑' j, (lambda j) ^ 2)).trans_eq (by simp)
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 htail (ε ^ 2 / 2) (by positivity)
    have key : ∀ M : ℕ, N ≤ M → dist (S M) (S N) < ε := by
      intro M hMN
      have hbound : (eLpNorm (fun x => gaussPartial lambda M x -
          gaussPartial lambda N x) 2 gaussianSeqMeasure).toReal ^ 2 < ε ^ 2 := by
        rw [← memLp_integral_sq_eq_eLpNorm
          (show MemLp (fun x => gaussPartial lambda M x - gaussPartial lambda N x) 2
            gaussianSeqMeasure from
            (gaussPartial_memLp lambda M).sub (gaussPartial_memLp lambda N)),
          gaussPartial_L2 lambda M N hMN]
        calc (2:ℝ) * ∑ j ∈ Finset.range M \ Finset.range N, (lambda j) ^ 2
            ≤ (2:ℝ) * ((∑' j, (lambda j) ^ 2)
              - ∑ j ∈ Finset.range N, (lambda j) ^ 2) := by
              nlinarith [hsub M N hMN]
          _ < ε ^ 2 := by
              have hN' := hN N (le_refl N)
              rw [Real.dist_0_eq_abs, abs_lt] at hN'
              nlinarith [hsub M N hMN, hN'.1, hN'.2]
      have hnonneg : (0:ℝ) ≤ (eLpNorm (fun x => gaussPartial lambda M x -
          gaussPartial lambda N x) 2 gaussianSeqMeasure).toReal :=
        ENNReal.toReal_nonneg
      rw [hSdist M N]
      nlinarith [hbound, hε, hnonneg, sq_nonneg ε]
    exact ⟨N, fun m hm => key m hm⟩
  set Q : Lp ℝ 2 gaussianSeqMeasure := atTop.limUnder S with hQdef
  have hQtend : Tendsto S atTop (𝓝 Q) := hCauchy.tendsto_limUnder
  have hdist0 : Tendsto (fun K : ℕ => dist (S K) Q) atTop (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.1 hQtend
  have hQdist : ∀ K : ℕ, dist (S K) Q =
      (eLpNorm (fun x => ⇑Q x - gaussPartial lambda K x) 2 gaussianSeqMeasure).toReal := by
    intro K
    have hfun : (⇑(S K) - ⇑Q) =ᵐ[gaussianSeqMeasure] -(⇑Q - gaussPartial lambda K) := by
      filter_upwards [hcoecoe K] with x hx
      show ⇑(S K) x - ⇑Q x = -(⇑Q x - gaussPartial lambda K x)
      rw [hx]
      ring
    rw [Lp.dist_def, eLpNorm_congr_ae hfun, eLpNorm_neg]
    rfl
  have h2 : Tendsto (fun K : ℕ => (dist (S K) Q) ^ 2) atTop (𝓝 0) := by
    simpa using hdist0.pow 2
  have hfinal : ∀ K : ℕ,
      (∫ x, (⇑Q x - gaussPartial lambda K x) ^ 2 ∂gaussianSeqMeasure)
        = (dist (S K) Q) ^ 2 := by
    intro K
    rw [hQdist K, ← memLp_integral_sq_eq_eLpNorm
      (show MemLp (fun x => ⇑Q x - gaussPartial lambda K x) 2 gaussianSeqMeasure from
        (Lp.memLp Q).sub (gaussPartial_memLp lambda K))]
  refine ⟨Q, Lp.memLp Q, ?_, ?_⟩
  · intro K
    exact (Lp.memLp Q).sub (gaussPartial_memLp lambda K)
  · refine Tendsto.congr' (Filter.Eventually.of_forall fun K => (hfinal K).symm) h2

/-- Interface packaging on the constructed space: everything
`IsSecondChaosSeriesLaw` needs except the a.s.-convergence field. -/
theorem exists_gaussSeries_L2limit_fields (lambda : ℕ → ℝ)
    (hlambda : Summable (fun j => (lambda j) ^ 2)) :
    ∃ Q : (ℕ → ℝ) → ℝ,
      AEMeasurable Q gaussianSeqMeasure ∧
      (∀ K : ℕ, MemLp (fun x => Q x - ∑ j ∈ Finset.range K,
        lambda j * ((x j) ^ 2 - 1)) 2 gaussianSeqMeasure) ∧
      Tendsto (fun K : ℕ =>
        ∫ x, (Q x - ∑ j ∈ Finset.range K,
          lambda j * ((x j) ^ 2 - 1)) ^ 2 ∂gaussianSeqMeasure) atTop (𝓝 0) := by
  obtain ⟨Q, hQ, hmem, htail⟩ := exists_gaussSeries_L2limit lambda hlambda
  exact ⟨Q, hQ.aemeasurable, hmem, htail⟩

end Hurst
