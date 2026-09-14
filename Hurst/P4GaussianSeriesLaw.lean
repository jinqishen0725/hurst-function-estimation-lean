import Hurst.SecondChaosSeriesL2
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

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
convergence of `S_K` to `Q`, file 23 step C3) **is discharged** in this
revision via the martingale route: the partial sums form an `L¹`-bounded
martingale for the cylinder filtration
(`gaussPartial_martingale`, proved through
`MeasureTheory.condExp_indep_eq` on the coordinate/block σ-algebras), so
`Submartingale.exists_ae_tendsto_of_bdd` gives a.e. convergence of the full
sequence to some limit, and the `L²` limit `Q` is identified with that
a.e. limit by extracting an a.e.-convergent subsequence from the `L²`
convergence (`TendstoInMeasure.exists_seq_tendsto_ae`).  The full
`IsSecondChaosSeriesLaw gaussianSeqMeasure Q lambda` is assembled in
`exists_isSecondChaosSeriesLaw_gaussSeq` (file 23 step D2 existence form).
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

/-! ### The cylinder filtration and the martingale property

The partial sums `S_K = ∑_{j<K} λ_j (Z_j² − 1)` form an `L²`-bounded martingale
for the cylinder filtration `𝓕_K := σ(Z_j : j < K)`: for `m ≤ n` the tail block
`S_n − S_m` depends only on coordinates `j ∈ [m, n)`, which are independent of
`𝓕_m` and centered, hence `E[S_n | 𝓕_m] = S_m` by `condExp_indep_eq`.  The
`L¹`-bounded martingale convergence theorem
(`Submartingale.exists_ae_tendsto_of_bdd`) then gives a.s. convergence of the
full sequence `S_K`; the a.s. limit is identified with the `L²`-limit `Q` by
extracting an a.e.-convergent subsequence from `L²` convergence. -/

/-- One centered square has mean zero on the constructed space. -/
theorem gaussianSeq_centeredSquare_mean (j : ℕ) :
    (∫ x, (gaussianSeqVar j x) ^ 2 - 1 ∂gaussianSeqMeasure) = 0 := by
  have hLaw : HasLaw (gaussianSeqVar j) (gaussianReal 0 1) gaussianSeqMeasure :=
    ⟨(gaussianSeqVar_measurable j).aemeasurable, gaussianSeqMeasure_map_var j⟩
  have hf : AEStronglyMeasurable (fun z : ℝ => z ^ 2 - 1) (gaussianReal 0 1) :=
    (show Continuous fun z : ℝ => z ^ 2 - 1 by fun_prop).aestronglyMeasurable
  have hmap := hLaw.integral_comp hf
  change ∫ x, (fun z : ℝ => z ^ 2 - 1) (gaussianSeqVar j x) ∂gaussianSeqMeasure = 0
  rw [show (∫ x, (fun z : ℝ => z ^ 2 - 1) (gaussianSeqVar j x) ∂gaussianSeqMeasure)
      = ∫ z, (fun z : ℝ => z ^ 2 - 1) z ∂gaussianReal 0 1 by
      simpa [Function.comp_def] using hmap]
  simpa [gaussianHermite_two] using standardGaussian_hermite_mean_succ 1

theorem gaussianSeqVar_sq_memLp (j : ℕ) :
    MemLp (fun x : ℕ → ℝ => (x j) ^ 2 - 1) 2 gaussianSeqMeasure :=
  iid_standardGaussian_centeredSquare_memLp gaussianSeqMeasure gaussianSeqVar
    (fun j => (gaussianSeqVar_measurable j).aemeasurable) gaussianSeqMeasure_map_var j

/-- `L²` on the probability space `gaussianSeqMeasure` implies integrability. -/
theorem integrable_of_memLp_two {f : (ℕ → ℝ) → ℝ}
    (hf : MemLp f 2 gaussianSeqMeasure) : Integrable f gaussianSeqMeasure := by
  have h1 : MemLp f 1 gaussianSeqMeasure :=
    ⟨hf.aestronglyMeasurable, lt_of_le_of_lt
      (eLpNorm_le_eLpNorm_of_exponent_le (μ := gaussianSeqMeasure) (p := 1) (q := 2)
        (by norm_num) hf.aestronglyMeasurable) hf.eLpNorm_lt_top⟩
  exact memLp_one_iff_integrable.1 h1

/-! ### The cylinder and block σ-algebras -/

/-- `Finset.range i ⊆ Finset.range j` for `i ≤ j` (stated directly to avoid
version-dependent `Finset.range_subset` argument order). -/
theorem rangeNle_subset {i j : ℕ} (hij : i ≤ j) : Finset.range i ⊆ Finset.range j :=
  fun x hx => Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hx) hij)

/-- The σ-algebra generated by the coordinates of a finite block `s`. -/
@[reducible]
def gaussBlockMeas (s : Finset ℕ) : MeasurableSpace (ℕ → ℝ) :=
  ⨆ i ∈ (s : Set ℕ), MeasurableSpace.comap (fun x : ℕ → ℝ => x i) (borel ℝ)

/-- The cylinder σ-algebra generated by the coordinates `j < n`. -/
@[reducible]
def gaussCylMeas (n : ℕ) : MeasurableSpace (ℕ → ℝ) := gaussBlockMeas (Finset.range n)

theorem gaussBlockMeas_mono {t s : Finset ℕ} (h : t ⊆ s) : gaussBlockMeas t ≤ gaussBlockMeas s :=
  iSup₂_le fun j hj => le_iSup₂_of_le j (h hj) le_rfl

theorem gaussBlockMeas_le (s : Finset ℕ) :
    gaussBlockMeas s ≤ (inferInstance : MeasurableSpace (ℕ → ℝ)) :=
  iSup₂_le fun j _ => Measurable.comap_le (measurable_pi_apply j)

/-- The trimmed measure along any block σ-algebra of the Gaussian sequence
space is finite (the space has total mass one). -/
instance isFiniteMeasure_trim_of_gaussBlock {s : Finset ℕ}
    (h : gaussBlockMeas s ≤ (inferInstance : MeasurableSpace (ℕ → ℝ))) :
    IsFiniteMeasure (gaussianSeqMeasure.trim h) where
  measure_univ_lt_top := by
    rw [MeasureTheory.trim_measurableSet_eq h MeasurableSet.univ]
    exact lt_of_eq_of_lt measure_univ ENNReal.one_lt_top

/-- The cylinder filtration on the Gaussian sequence space. -/
def gaussFiltration : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → ℝ)) where
  seq := gaussCylMeas
  mono' := fun i j hij =>
    gaussBlockMeas_mono (t := Finset.range i) (s := Finset.range j) (rangeNle_subset hij)
  le' := fun i => gaussBlockMeas_le (Finset.range i)

theorem measurable_coord_comap (j : ℕ) :
    @Measurable (ℕ → ℝ) ℝ (MeasurableSpace.comap (fun x : ℕ → ℝ => x j) (borel ℝ)) (borel ℝ)
      (fun x : ℕ → ℝ => x j) := fun _ hs => ⟨_, hs, rfl⟩

theorem stronglyMeasurable_coord_sq_sub_one (j : ℕ) :
    StronglyMeasurable[MeasurableSpace.comap (fun x : ℕ → ℝ => x j) (borel ℝ)]
      (fun x : ℕ → ℝ => (x j) ^ 2 - 1) := by
  have hmeas : Measurable (fun t : ℝ => t ^ 2 - 1) :=
    (show Continuous fun t : ℝ => t ^ 2 - 1 by fun_prop).measurable
  exact Measurable.stronglyMeasurable (Measurable.comp hmeas (measurable_coord_comap j))

theorem stronglyMeasurable_coord_mul (lambda : ℕ → ℝ) {j : ℕ} {s : Finset ℕ} (hj : j ∈ s) :
    StronglyMeasurable[gaussBlockMeas s] (fun x : ℕ → ℝ => lambda j * ((x j) ^ 2 - 1)) :=
  ((stronglyMeasurable_coord_sq_sub_one j).mono
    (le_iSup₂_of_le j hj le_rfl)).const_mul (lambda j)

theorem stronglyMeasurable_finsetSum_of {s : Finset ℕ} {m : MeasurableSpace (ℕ → ℝ)}
    (F : ℕ → (ℕ → ℝ) → ℝ) (hF : ∀ j ∈ s, StronglyMeasurable[m] (F j)) :
    StronglyMeasurable[m] (fun x => ∑ j ∈ s, F j x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using stronglyMeasurable_const
  | insert k s hk ih =>
    have key : StronglyMeasurable[m] (fun x => F k x + ∑ j ∈ s, F j x) :=
      StronglyMeasurable.add (hF k (Finset.mem_insert_self k s))
        (ih (fun j hj => hF j (Finset.mem_insert_of_mem hj)))
    simpa [Finset.sum_insert hk] using key

theorem gaussPartial_stronglyMeasurable (lambda : ℕ → ℝ) (K : ℕ) :
    StronglyMeasurable[gaussCylMeas K] (gaussPartial lambda K) := by
  have h : StronglyMeasurable[gaussCylMeas K]
      (fun x => ∑ j ∈ Finset.range K, lambda j * ((x j) ^ 2 - 1)) :=
    stronglyMeasurable_finsetSum_of (fun j x => lambda j * ((x j) ^ 2 - 1))
      (fun j hj => stronglyMeasurable_coord_mul lambda hj)
  exact h

/-! ### Independence of cylinder and block σ-algebras -/

set_option maxHeartbeats 1000000 in
theorem gaussianSeq_iIndep_comap :
    iIndep (fun i : ℕ => MeasurableSpace.comap (fun x : ℕ → ℝ => x i) (borel ℝ))
      gaussianSeqMeasure :=
  (iIndepFun_iff_iIndep (fun _ : ℕ => (borel ℝ)) (fun (j : ℕ) (x : ℕ → ℝ) => x j)
    gaussianSeqMeasure).1 gaussianSeq_iIndepFun

set_option maxHeartbeats 1000000 in
theorem gaussBlock_indep (s t : Finset ℕ) (hst : Disjoint s t) :
    Indep (gaussBlockMeas s) (gaussBlockMeas t) gaussianSeqMeasure := by
  have hcoe : Disjoint (s : Set ℕ) (t : Set ℕ) := by simpa using hst
  exact ProbabilityTheory.indep_iSup_of_disjoint
    (fun i => Measurable.comap_le (measurable_pi_apply i)) gaussianSeq_iIndep_comap hcoe

/-! ### The martingale property of the partial sums -/

set_option maxHeartbeats 20000000 in
/-- The conditional expectation of a block sum against an independent
block σ-algebra is the constant mean (zero here). -/
theorem gaussBlockMeas_condExp_block (lambda : ℕ → ℝ) (d e : Finset ℕ) (hde : Disjoint d e) :
    (condExp (gaussBlockMeas e) gaussianSeqMeasure
        (fun x => ∑ j ∈ d, lambda j * ((x j) ^ 2 - 1))) =ᵐ[gaussianSeqMeasure]
      fun _ : ℕ → ℝ => (0 : ℝ) := by
  haveI hsf : SigmaFinite (gaussianSeqMeasure.trim (gaussBlockMeas_le e)) := inferInstance
  have hTzero : (∫ x, ∑ j ∈ d, lambda j * ((x j) ^ 2 - 1) ∂gaussianSeqMeasure) = 0 := by
    have hint : ∀ j : ℕ, j ∈ d → Integrable (fun x : ℕ → ℝ => lambda j * ((x j) ^ 2 - 1))
        gaussianSeqMeasure := fun j _ =>
      integrable_of_memLp_two ((gaussianSeqVar_sq_memLp j).const_mul (lambda j))
    rw [integral_finsetSum d hint]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [integral_const_mul,
      show (∫ x : ℕ → ℝ, (x j) ^ 2 - 1 ∂gaussianSeqMeasure) = 0
        from gaussianSeq_centeredSquare_mean j, mul_zero]
  have hInd : Indep (gaussBlockMeas d) (gaussBlockMeas e) gaussianSeqMeasure :=
    gaussBlock_indep d e hde
  have hTmeas : StronglyMeasurable[gaussBlockMeas d]
      (fun x => ∑ j ∈ d, lambda j * ((x j) ^ 2 - 1)) :=
    stronglyMeasurable_finsetSum_of (m := gaussBlockMeas d) (s := d)
      (fun j x => lambda j * ((x j) ^ 2 - 1)) (fun j hj => stronglyMeasurable_coord_mul lambda hj)
  have h := condExp_indep_eq (gaussBlockMeas_le d) (gaussBlockMeas_le e) hTmeas hInd
  rw [hTzero] at h
  exact h

set_option maxHeartbeats 20000000 in
/-- The partial sums form a martingale for the cylinder filtration:
`E[S_n | 𝓕_m] = S_m` for `m ≤ n`. -/
theorem gaussPartial_condExp (lambda : ℕ → ℝ) {m n : ℕ} (hmn : m ≤ n) :
    (condExp (gaussCylMeas m) gaussianSeqMeasure (gaussPartial lambda n)) =ᵐ[gaussianSeqMeasure]
      gaussPartial lambda m := by
  classical
  have hsub : Finset.range m ⊆ Finset.range n := rangeNle_subset hmn
  set d : Finset ℕ := Finset.range n \ Finset.range m with hd
  have hIntS : Integrable (gaussPartial lambda m) gaussianSeqMeasure :=
    integrable_of_memLp_two (gaussPartial_memLp lambda m)
  have hIntT : Integrable (fun x : ℕ → ℝ => ∑ j ∈ d, lambda j * ((x j) ^ 2 - 1))
      gaussianSeqMeasure := by
    refine integrable_of_memLp_two (memLp_finsetSum d fun j _ => ?_)
    exact (gaussianSeqVar_sq_memLp j).const_mul _
  have hfunEq : gaussPartial lambda n
      = gaussPartial lambda m + fun x => ∑ j ∈ d, lambda j * ((x j) ^ 2 - 1) := by
    funext x
    have h := Finset.sum_sdiff (s₁ := Finset.range m) (s₂ := Finset.range n) hsub
      (f := fun j : ℕ => lambda j * ((x j) ^ 2 - 1))
    show ∑ j ∈ Finset.range n, lambda j * ((x j) ^ 2 - 1)
        = ∑ j ∈ Finset.range m, lambda j * ((x j) ^ 2 - 1)
          + ∑ j ∈ Finset.range n \ Finset.range m, lambda j * ((x j) ^ 2 - 1)
    linarith [h]
  have hInd : Disjoint d (Finset.range m) := by
    rw [Finset.disjoint_left]
    intro a ha1 ha2
    simp only [hd, Finset.mem_sdiff] at ha1
    exact ha1.2 ha2
  have e2 : (condExp (gaussCylMeas m) gaussianSeqMeasure
      (gaussPartial lambda m)) =ᵐ[gaussianSeqMeasure] gaussPartial lambda m := by
    have h2 := condExp_of_stronglyMeasurable (gaussBlockMeas_le (Finset.range m))
      (gaussPartial_stronglyMeasurable lambda m) hIntS
    exact Eventually.of_forall fun x => congrFun h2 x
  have e3 : (condExp (gaussCylMeas m) gaussianSeqMeasure
      (fun x => ∑ j ∈ d, lambda j * ((x j) ^ 2 - 1))) =ᵐ[gaussianSeqMeasure]
      (fun _ : ℕ → ℝ => (0 : ℝ)) :=
    gaussBlockMeas_condExp_block lambda d (Finset.range m) hInd
  have step1 : (condExp (gaussCylMeas m) gaussianSeqMeasure (gaussPartial lambda n))
      =ᵐ[gaussianSeqMeasure] condExp (gaussCylMeas m) gaussianSeqMeasure
          (gaussPartial lambda m + fun x => ∑ j ∈ d, lambda j * ((x j) ^ 2 - 1)) :=
    condExp_congr_ae (Eventually.of_forall fun x => congrFun hfunEq x)
  have step2 : (condExp (gaussCylMeas m) gaussianSeqMeasure
      (gaussPartial lambda m + fun x => ∑ j ∈ d, lambda j * ((x j) ^ 2 - 1)))
      =ᵐ[gaussianSeqMeasure] condExp (gaussCylMeas m) gaussianSeqMeasure (gaussPartial lambda m)
          + condExp (gaussCylMeas m) gaussianSeqMeasure
            (fun x => ∑ j ∈ d, lambda j * ((x j) ^ 2 - 1)) :=
    condExp_add hIntS hIntT (gaussCylMeas m)
  calc condExp (gaussCylMeas m) gaussianSeqMeasure (gaussPartial lambda n)
      =ᵐ[gaussianSeqMeasure] condExp (gaussCylMeas m) gaussianSeqMeasure
          (gaussPartial lambda m + fun x => ∑ j ∈ d, lambda j * ((x j) ^ 2 - 1)) := step1
    _ =ᵐ[gaussianSeqMeasure] condExp (gaussCylMeas m) gaussianSeqMeasure (gaussPartial lambda m)
          + condExp (gaussCylMeas m) gaussianSeqMeasure
            (fun x => ∑ j ∈ d, lambda j * ((x j) ^ 2 - 1)) := step2
    _ =ᵐ[gaussianSeqMeasure] gaussPartial lambda m + fun _ : ℕ → ℝ => (0 : ℝ) := e2.add e3
    _ =ᵐ[gaussianSeqMeasure] gaussPartial lambda m := by
        filter_upwards with x
        simp

theorem gaussPartial_martingale (lambda : ℕ → ℝ) :
    Martingale (fun K => gaussPartial lambda K) gaussFiltration gaussianSeqMeasure :=
  ⟨fun K => gaussPartial_stronglyMeasurable lambda K,
    fun m n hmn => gaussPartial_condExp lambda hmn⟩

/-! ### Full-sequence a.s. convergence -/

/-- The partial sums of the Gaussian second-chaos series converge almost
surely (full sequence) to the `L²` limit `Q`. -/
theorem exists_gaussSeries_ae_convergence (lambda : ℕ → ℝ)
    (hlambda : Summable fun j => (lambda j) ^ 2) :
    ∃ Q : (ℕ → ℝ) → ℝ,
      MemLp Q 2 gaussianSeqMeasure ∧
      (∀ K : ℕ, MemLp (fun x => Q x - gaussPartial lambda K x) 2 gaussianSeqMeasure) ∧
      Tendsto (fun K : ℕ =>
        ∫ x, (Q x - gaussPartial lambda K x) ^ 2 ∂gaussianSeqMeasure) atTop (𝓝 0) ∧
      ∀ᵐ x ∂gaussianSeqMeasure,
        Tendsto (fun K : ℕ => gaussPartial lambda K x) atTop (𝓝 (Q x)) := by
  obtain ⟨Q, hQ, hmem, htail⟩ := exists_gaussSeries_L2limit lambda hlambda
  -- `L¹` boundedness of the partial sums from the exact `L²` norms
  have hbound : ∀ K : ℕ, eLpNorm (gaussPartial lambda K) 1 gaussianSeqMeasure
      ≤ ENNReal.ofReal (Real.sqrt (2 * ∑' j, (lambda j) ^ 2) + 1) := by
    intro K
    have hsq : (eLpNorm (gaussPartial lambda K) 2 gaussianSeqMeasure).toReal
        = Real.sqrt (2 * ∑ j ∈ Finset.range K, (lambda j) ^ 2) := by
      have h0 : gaussPartial lambda 0 = fun _ : ℕ → ℝ => (0 : ℝ) := by
        funext x; simp [gaussPartial]
      have h0' := gaussPartial_L2 lambda K 0 (Nat.zero_le K)
      rw [h0] at h0'
      simp only [sub_zero] at h0'
      rw [memLp_integral_sq_eq_eLpNorm (gaussPartial_memLp lambda K)] at h0'
      simp only [Finset.range_zero, Finset.sdiff_empty] at h0'
      have hnn : (0:ℝ) ≤ (eLpNorm (gaussPartial lambda K) 2 gaussianSeqMeasure).toReal :=
        ENNReal.toReal_nonneg
      calc (eLpNorm (gaussPartial lambda K) 2 gaussianSeqMeasure).toReal
          = Real.sqrt ((eLpNorm (gaussPartial lambda K) 2 gaussianSeqMeasure).toReal ^ 2) :=
            (Real.sqrt_sq hnn).symm
        _ = Real.sqrt (2 * ∑ j ∈ Finset.range K, (lambda j) ^ 2) := by rw [h0']
    refine le_trans (eLpNorm_le_eLpNorm_of_exponent_le (μ := gaussianSeqMeasure)
      (p := 1) (q := 2) (by norm_num) (gaussPartial_memLp lambda K).aestronglyMeasurable) ?_
    refine (ENNReal.le_ofReal_iff_toReal_le
      (gaussPartial_memLp lambda K).eLpNorm_lt_top.ne
      (add_nonneg (Real.sqrt_nonneg _) zero_le_one)).2 ?_
    rw [hsq]
    have hmono : 2 * ∑ j ∈ Finset.range K, (lambda j) ^ 2 ≤ 2 * ∑' j, (lambda j) ^ 2 := by
      nlinarith [hlambda.sum_le_tsum (Finset.range K) (fun j _ => sq_nonneg _)]
    calc Real.sqrt (2 * ∑ j ∈ Finset.range K, (lambda j) ^ 2)
        ≤ Real.sqrt (2 * ∑' j, (lambda j) ^ 2) := Real.sqrt_le_sqrt hmono
      _ ≤ Real.sqrt (2 * ∑' j, (lambda j) ^ 2) + 1 :=
        by linarith [Real.sqrt_nonneg (2 * ∑' j, (lambda j) ^ 2)]
  -- a.s. convergence of the martingale to *some* limit
  have hsub := (gaussPartial_martingale lambda).submartingale
  have hae := hsub.exists_ae_tendsto_of_bdd hbound
  -- `L²` convergence gives convergence in measure to `Q`, hence an a.e.
  -- convergent subsequence; the a.e. limits must agree
  have hAE : ∀ K : ℕ, AEStronglyMeasurable (gaussPartial lambda K) gaussianSeqMeasure :=
    fun K => (gaussPartial_memLp lambda K).aestronglyMeasurable
  have hint : Tendsto (fun K : ℕ =>
      ∫ x, (gaussPartial lambda K x - Q x) ^ 2 ∂gaussianSeqMeasure) atTop (𝓝 0) := by
    have hEq : (fun K : ℕ => ∫ x, (gaussPartial lambda K x - Q x) ^ 2 ∂gaussianSeqMeasure)
        = (fun K : ℕ => ∫ x, (Q x - gaussPartial lambda K x) ^ 2 ∂gaussianSeqMeasure) := by
      funext K
      exact integral_congr_ae (Eventually.of_forall fun x => by ring)
    rw [hEq]; exact htail
  have hnorm : Tendsto (fun K : ℕ => eLpNorm (fun x => gaussPartial lambda K x - Q x) 2
      gaussianSeqMeasure) atTop (𝓝 0) := by
    have htarget : Tendsto (fun K : ℕ => ENNReal.ofReal (Real.sqrt
        (∫ x, (gaussPartial lambda K x - Q x) ^ 2 ∂gaussianSeqMeasure))) atTop (𝓝 0) := by
      have h2 := ENNReal.continuous_ofReal.tendsto (Real.sqrt (0:ℝ))
      have h3 := h2.comp hint.sqrt
      rw [Real.sqrt_zero, ENNReal.ofReal_zero] at h3
      exact h3
    have hbound2 : ∀ K : ℕ,
        eLpNorm (fun x => gaussPartial lambda K x - Q x) 2 gaussianSeqMeasure
        ≤ ENNReal.ofReal (Real.sqrt
          (∫ x, (gaussPartial lambda K x - Q x) ^ 2 ∂gaussianSeqMeasure)) := by
      intro K
      have hsq := memLp_integral_sq_eq_eLpNorm ((gaussPartial_memLp lambda K).sub hQ)
      have hsq2 : (∫ x, (gaussPartial lambda K x - Q x) ^ 2 ∂gaussianSeqMeasure)
          = (eLpNorm (fun x => gaussPartial lambda K x - Q x) 2
            gaussianSeqMeasure).toReal ^ 2 := hsq
      have hnn : (0:ℝ) ≤ (eLpNorm (fun x => gaussPartial lambda K x - Q x) 2
          gaussianSeqMeasure).toReal := ENNReal.toReal_nonneg
      have hfin : eLpNorm (fun x => gaussPartial lambda K x - Q x) 2 gaussianSeqMeasure ≠ ∞ :=
        ((gaussPartial_memLp lambda K).sub hQ).eLpNorm_lt_top.ne
      refine (ENNReal.le_ofReal_iff_toReal_le hfin
        (Real.sqrt_nonneg
          (∫ x, (gaussPartial lambda K x - Q x) ^ 2 ∂gaussianSeqMeasure))).2 ?_
      rw [hsq2, Real.sqrt_sq hnn]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htarget
      (fun _ => zero_le) hbound2
  obtain ⟨u, hu, huae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm
    (p := (2:ℝ≥0∞)) (by norm_num) hAE hQ.aestronglyMeasurable hnorm).exists_seq_tendsto_ae
  refine ⟨Q, hQ, hmem, htail, ?_⟩
  filter_upwards [hae, huae] with x hx hx'
  obtain ⟨c, hc⟩ := hx
  have hsu : Tendsto (fun i => gaussPartial lambda (u i) x) atTop (𝓝 c) :=
    hc.comp hu.tendsto_atTop
  have hEqc : c = Q x := tendsto_nhds_unique hsu hx'
  rw [hEqc] at hc
  exact hc

/-- The D2-existence form on the constructed space: for every square-summable
coefficient sequence there is a random variable carrying the Gaussian
second-chaos series law, including full-sequence a.s. convergence of the
partial sums. -/
theorem exists_isSecondChaosSeriesLaw_gaussSeq (lambda : ℕ → ℝ)
    (hlambda : Summable fun j => (lambda j) ^ 2) :
    ∃ Q : (ℕ → ℝ) → ℝ, IsSecondChaosSeriesLaw gaussianSeqMeasure Q lambda := by
  obtain ⟨Q, hQ, hmem, htail, hae⟩ := exists_gaussSeries_ae_convergence lambda hlambda
  refine ⟨Q, hQ.aemeasurable, hlambda, gaussianSeqVar,
    fun j => (gaussianSeqVar_measurable j).aemeasurable, gaussianSeq_iIndepFun,
    gaussianSeqMeasure_map_var, hmem, htail, hae⟩

end Hurst
