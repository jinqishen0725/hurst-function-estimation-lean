import Hurst.P5LogHLayers
import Hurst.FirstScaleLongL1
import Hurst.FirstScaleLongRates
import Hurst.FirstScaleEquivariance
import Hurst.NormalizedInverseMeasurability

/-!
# P7 optional endpoint: unknown-scale conditional layers (file 24, E6–E8)

This module lands the unknown-scale conditional layers of the q1 long-memory
chain, downstream of the P5 conditional log/H layers (`Hurst.P5LogHLayers`).
All distributional statements remain CONDITIONAL on the quadratic/log-statistic
limits: the upstream hypotheses (`hPow`, `hane`, `hNegMass`, `hQ`, `hlam`, `hm`
of `actualQ1LongStatistic_tendsto_secondChaos_signed`) are never discharged
here.

## Contents

1. E6 layer: the truncated q1 calibration inverse is 1-Lipschitz
   (`p5Trunc01_abs_sub_le`); the unknown/known-scale estimators satisfy the
   pointwise contraction `|H_n^u - H_n^o| ≤ |Ŝ_n - s_σ| / (2 log n)` (file 24
   E6) and hence the L¹ transfer `2 A log n E|H_n^u - H_n^o| ≤ A E|Ŝ_n - s_σ|`
   (written (E5)) with its centered corollary — with NO independence between
   the pilot `Ŝ_n` and the main statistic `G_n`.
2. σ-L¹ bound (E6 concrete): `p7_q1LogScale_L1_sigma_eq_unit` (the actual
   `q1LogScaleEstimator`'s L¹ error at scale σ equals the unit-scale L¹ error)
   and `p7_q1LogScale_L1_sigma_bound` (combined with the landed long-L1 bound
   `hurstHolder_q1_logScale_L1_lt_one`).  The weight-reproduction and
   stride-nondegeneracy premises remain explicit ordinary hypotheses.
3. E8 layer: the generic weighted log-statistic a.e. scale shift and the a.e.
   scale EQUIVARIANCE of the unknown-scale estimator (both the main statistic
   and the pilot shift by `log σ²`, so the difference is invariant); plus the
   conditional distribution-inheritance transports (expectation-centered and
   truth-centered) from a known-scale endpoint via the L¹ smallness.
4. E7 layer (conservative rates): building blocks
   (`p7_alpha_log_rpow_tendsto`, `p7_alpha_loglog_rpow_tendsto`), the explicit
   row-bound split `p7_firstStrideLongRowBound_div_n_le`, the conditional rate
   `p7_unknownScale_scale_L1_rate_of_mesh_bound` (the rate condition
   `(1-γ)ψ < 1-b` as an explicit ordinary hypothesis), and the conservative
   `s = 1` bandwidth window `p7_conservative_window_s_one`.

## Known gaps (documented)

* The upstream conditional hypotheses are not discharged (by design).
* The concrete dischargers of `hw`/`h₁`/`h₂` (weight reproduction
  `∑ averagedLocalWeights = 1`, stride nondegeneracy) are upstream obligations.
* `ψ` is kept as an abstract positive parameter; the endpoint instance is
  `ψ = 2 - 2 * f t` with `3/4 < f t`.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace

namespace Hurst

/-! ## E6 layer: the truncated-inverse contraction and the L¹ transfer -/

private theorem clip_sub_add_le (z e : ℝ) (he : 0 ≤ e) :
    p5Trunc01 (z + e) ≤ p5Trunc01 z + e := by
  have h1 : max 0 (z + e) ≤ max 0 z + e := by
    refine max_le ?_ ?_
    · linarith [le_max_left (0 : ℝ) z]
    · linarith [le_max_right (0 : ℝ) z]
  have h2 : min 1 (max 0 z + e) ≤ min 1 (max 0 z) + e := by
    rcases min_cases 1 (max 0 z) with hm | hm
    · rw [hm.1]
      exact le_trans (min_le_left 1 (max 0 z + e)) (by linarith)
    · rcases min_cases 1 (max 0 z + e) with hm2 | hm2
      · rw [hm2.1, hm.1]
        linarith
      · rw [hm2.1, hm.1]
  show min 1 (max 0 (z + e)) ≤ min 1 (max 0 z) + e
  calc min 1 (max 0 (z + e)) ≤ min 1 (max 0 z + e) := min_le_min (le_refl 1) h1
    _ ≤ min 1 (max 0 z) + e := h2

/-- **E6, step 1.** The truncated q1 calibration inverse `p5Trunc01` is
1-Lipschitz: clipping to `[0, 1]` cannot expand distances. -/
theorem p5Trunc01_abs_sub_le (x y : ℝ) : |p5Trunc01 x - p5Trunc01 y| ≤ |x - y| := by
  rcases le_total x y with h | h
  · have hmono : p5Trunc01 x ≤ p5Trunc01 y := p5Trunc01_mono h
    rw [abs_of_nonpos (sub_nonpos.mpr hmono), abs_of_nonpos (sub_nonpos.mpr h),
      neg_sub, neg_sub]
    have hshift := clip_sub_add_le x (y - x) (sub_nonneg.mpr h)
    have hxy : x + (y - x) = y := by ring
    calc p5Trunc01 y - p5Trunc01 x
        = p5Trunc01 (x + (y - x)) - p5Trunc01 x := by rw [hxy]
      _ ≤ p5Trunc01 x + (y - x) - p5Trunc01 x := by linarith
      _ = y - x := by ring
  · have hmono : p5Trunc01 y ≤ p5Trunc01 x := p5Trunc01_mono h
    rw [abs_of_nonneg (sub_nonneg.mpr hmono), abs_of_nonneg (sub_nonneg.mpr h)]
    have hshift := clip_sub_add_le y (x - y) (sub_nonneg.mpr h)
    have hyx : y + (x - y) = x := by ring
    calc p5Trunc01 x - p5Trunc01 y
        = p5Trunc01 (y + (x - y)) - p5Trunc01 y := by rw [hyx]
      _ ≤ p5Trunc01 y + (x - y) - p5Trunc01 y := by linarith
      _ = x - y := by ring

/-- The untruncated unknown-scale H transform `(c - (G - S)) / (2 log n)`:
file 24 E6's `T_n (G_n - Ŝ_n)` before truncation, with `c` the calibration
center. -/
def p7UnknownScaleHtilde (n : ℕ) (c : ℝ) (G S : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ := (c - (G x - S x)) / (2 * Real.log n)

/-- The unknown-scale H estimator `H_n^u = T_n (G_n - Ŝ_n)` (file 24 E6). -/
def p7UnknownScaleEstimator (n : ℕ) (c : ℝ) (G S : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ := p5Trunc01 (p7UnknownScaleHtilde n c G S x)

/-- The known-scale comparison estimator `H_n^o = T_n (G_n - s)`, with the true
log-scale `s` in place of the pilot (file 24 E6). -/
def p7KnownScaleEstimator (n : ℕ) (c s : ℝ) (G : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ := p5Trunc01 ((c - (G x - s)) / (2 * Real.log n))

/-- **E6, step 2 (pointwise contraction).** `|H_n^u - H_n^o| ≤ |Ŝ_n - s| / (2 log n)`
for `1 < n`: the calibration slope is `2 log n` and truncation does not expand. -/
theorem p7_unknown_known_pointwise_le (n : ℕ) (hn : 1 < n) (c s : ℝ)
    (G S : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    |p7UnknownScaleEstimator n c G S x - p7KnownScaleEstimator n c s G x|
      ≤ |S x - s| / (2 * Real.log n) := by
  have hlog : 0 < 2 * Real.log (n : ℝ) := by
    have h0 : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
    positivity
  have htilde : p7UnknownScaleHtilde n c G S x - (c - (G x - s)) / (2 * Real.log n)
      = (S x - s) / (2 * Real.log n) := by
    unfold p7UnknownScaleHtilde
    ring
  calc |p7UnknownScaleEstimator n c G S x - p7KnownScaleEstimator n c s G x|
      = |p5Trunc01 (p7UnknownScaleHtilde n c G S x)
          - p5Trunc01 ((c - (G x - s)) / (2 * Real.log n))| := rfl
    _ ≤ |p7UnknownScaleHtilde n c G S x - (c - (G x - s)) / (2 * Real.log n)| :=
        p5Trunc01_abs_sub_le _ _
    _ = |S x - s| / (2 * Real.log n) := by rw [htilde, abs_div, abs_of_pos hlog]

/-- **E6, step 3 (written (E5), no independence).** For any probability space:
if the unknown/known pair `(U, O)` satisfies the pointwise E6 contraction
`|U x - O x| ≤ |S x - s| / L` (with `L = 2 log n` the truncated-q1 slope), then
the normalization `A · L` gives `A L · E|U - O| ≤ A · E|S - s|`.  Only L¹
control of the pilot error enters; `S` and the main statistic need not be
independent. -/
theorem p7_L1_transfer_of_pointwise {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A L s : ℝ) (hL : 0 < L) (hA : 0 ≤ A) (U O S : Ω → ℝ)
    (hpt : ∀ x : Ω, |U x - O x| ≤ |S x - s| / L)
    (hYmeas : AEMeasurable U μ) (hOmeas : AEMeasurable O μ)
    (hS : MemLp S 1 μ) :
    ∫ x, |A * L * (U x - O x)| ∂μ ≤ A * ∫ x, |S x - s| ∂μ := by
  have hintR : Integrable (fun x : Ω => |S x - s|) μ :=
    ((hS.sub (memLp_const s)).integrable le_rfl).abs
  have hdom : Integrable (fun x : Ω => A * |S x - s|) μ := hintR.const_mul A
  have hsub : AEStronglyMeasurable (fun x : Ω => A * L * (U x - O x)) μ :=
    ((hYmeas.sub hOmeas).const_mul _).aestronglyMeasurable
  have hpt2 : ∀ x : Ω, ‖A * L * (U x - O x)‖ ≤ A * |S x - s| := by
    intro x
    have h := hpt x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg hA hL.le)]
    calc A * L * |U x - O x| ≤ A * L * (|S x - s| / L) :=
          mul_le_mul_of_nonneg_left h (mul_nonneg hA hL.le)
      _ = A * |S x - s| := by field_simp
  have hintL : Integrable (fun x : Ω => |A * L * (U x - O x)|) μ :=
    (hdom.mono' hsub (Eventually.of_forall hpt2)).abs
  calc ∫ x, |A * L * (U x - O x)| ∂μ
      ≤ ∫ x, A * |S x - s| ∂μ := integral_mono hintL hdom (by
        intro x
        simpa only [Real.norm_eq_abs] using hpt2 x)
    _ = A * ∫ x, |S x - s| ∂μ := integral_const_mul _ _

/-- **E6, step 3 concrete:** the transfer for the actual truncated q1
unknown/known pair on the feature sample space, slope `L = 2 log n`: the
normalization `2 A log n` gives `2 A log n · E|H_n^u - H_n^o| ≤ A · E|S - s|`
(file 24 E6, written (E5)). -/
theorem p7_unknownScale_L1_transfer (n : ℕ) (hn : 1 < n) (A : ℝ) (hA : 0 ≤ A) (c s : ℝ)
    (G S : EuclideanSpace ℝ (Fin n) → ℝ)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hS : MemLp S 1 μ)
    (hYmeas : AEMeasurable (p7UnknownScaleEstimator n c G S) μ)
    (hOmeas : AEMeasurable (p7KnownScaleEstimator n c s G) μ) :
    ∫ x, |2 * A * Real.log n * (p7UnknownScaleEstimator n c G S x
        - p7KnownScaleEstimator n c s G x)| ∂μ
      ≤ A * ∫ x, |S x - s| ∂μ := by
  have hlog : 0 < 2 * Real.log (n : ℝ) := by
    have h0 : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
    positivity
  have hcore := p7_L1_transfer_of_pointwise μ A (2 * Real.log n) s hlog hA
    (p7UnknownScaleEstimator n c G S) (p7KnownScaleEstimator n c s G) S
    (fun x => p7_unknown_known_pointwise_le n hn c s G S x) hYmeas hOmeas hS
  have hnorm : (2 : ℝ) * A * Real.log n = A * (2 * Real.log n) := by ring
  rw [hnorm]
  exact hcore

/-- **E6, step 4 (centered corollary).** For any probability space, the
centered L¹ distance between `U` and `O` is at most twice their raw L¹
distance (file 24 E6 tail). -/
theorem p7_centered_L1_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U O : Ω → ℝ)
    (hU : MemLp U 1 μ) (hO : MemLp O 1 μ) :
    ∫ x, |(U x - (∫ y, U y ∂μ)) - (O x - (∫ y, O y ∂μ))| ∂μ
      ≤ 2 * ∫ x, |U x - O x| ∂μ := by
  have hUO : Integrable (fun x : Ω => U x - O x) μ :=
    (hU.integrable le_rfl).sub (hO.integrable le_rfl)
  have hsub : AEStronglyMeasurable (fun x : Ω =>
      (U x - (∫ y, U y ∂μ)) - (O x - (∫ y, O y ∂μ))) μ :=
    (hU.1.sub aestronglyMeasurable_const).sub
      (hO.1.sub aestronglyMeasurable_const)
  have hmean : |(∫ y, O y ∂μ) - (∫ y, U y ∂μ)|
      ≤ ∫ x, |U x - O x| ∂μ := by
    have h := norm_integral_le_integral_norm (μ := μ) (fun x : Ω => U x - O x)
    rw [integral_sub (hU.integrable le_rfl) (hO.integrable le_rfl)] at h
    simpa only [Real.norm_eq_abs, abs_sub_comm] using h
  have hdom : Integrable (fun x : Ω => |U x - O x|
      + |(∫ y, O y ∂μ) - (∫ y, U y ∂μ)|) μ := hUO.abs.add (integrable_const _)
  have hpt : ∀ x : Ω, ‖(U x - (∫ y, U y ∂μ)) - (O x - (∫ y, O y ∂μ))‖
      ≤ ‖U x - O x‖ + ‖(∫ y, O y ∂μ) - (∫ y, U y ∂μ)‖ := by
    intro x
    have habs := abs_add_le (U x - O x) ((∫ y, O y ∂μ) - (∫ y, U y ∂μ))
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 : (U x - (∫ y : Ω, U y ∂μ)) - (O x - (∫ y : Ω, O y ∂μ))
        = (U x - O x) + ((∫ y : Ω, O y ∂μ) - (∫ y : Ω, U y ∂μ)) := by ring
    rw [h1]
    simpa using habs
  have hint : Integrable (fun x : Ω =>
      |(U x - (∫ y, U y ∂μ)) - (O x - (∫ y, O y ∂μ))|) μ :=
    (hdom.mono' hsub (Eventually.of_forall hpt)).abs
  have hint2 : Integrable (fun x : Ω => (|U x - O x|
      + |(∫ y, O y ∂μ) - (∫ y, U y ∂μ)|)) μ := hdom
  have hmono2 : ∀ x : Ω, |(U x - (∫ y, U y ∂μ)) - (O x - (∫ y, O y ∂μ))|
      ≤ |U x - O x| + |(∫ y, O y ∂μ) - (∫ y, U y ∂μ)| := by
    intro x
    have hx := hpt x
    simpa only [Real.norm_eq_abs] using hx
  calc ∫ x, |(U x - (∫ y, U y ∂μ)) - (O x - (∫ y, O y ∂μ))| ∂μ
    ≤ ∫ x, (|U x - O x| + |(∫ y, O y ∂μ) - (∫ y, U y ∂μ)|) ∂μ :=
      integral_mono hint hint2 hmono2
  _ = (∫ x, |U x - O x| ∂μ) + |(∫ y, O y ∂μ) - (∫ y, U y ∂μ)| := by
      rw [integral_add hUO.abs (integrable_const _), integral_const,
        probReal_univ, one_smul]
  _ ≤ 2 * ∫ x, |U x - O x| ∂μ := by linarith

/-! ## σ-L¹ identity and bound for the actual q1 scale estimator -/

/-- **E6/E8 (σ-identity).** The actual q1 scale estimator's L¹ error at scale
σ equals the unit-scale L¹ error: `E_σ|ŝ_n - log σ²| = E_1|ŝ_n|`, obtained from
the landed scale-equivariance integral identity with `Φ = |·|`. -/
theorem p7_q1LogScale_L1_sigma_eq_unit {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V]
    (r n m : ℕ) (δ : ℝ) (v : Fin n → V)
    (hw : ∑ i, averagedLocalWeights r n 2 m δ i = 1)
    (h₁ : ∀ i, ∑ j, commonFirstStrideCoefficients n 1 2 (by norm_num) i j • v j ≠ 0)
    (h₂ : ∀ i, ∑ j, commonFirstStrideCoefficients n 2 2 (by norm_num) i j • v j ≠ 0)
    (σ : ℝ) (hσ : σ ≠ 0) :
    (∫ x, |q1LogScaleEstimator r n m δ x - Real.log (σ ^ 2)|
        ∂featureGaussian (fun i => σ • v i))
      = ∫ x, |q1LogScaleEstimator r n m δ x| ∂featureGaussian v :=
  q1LogScaleEstimator_scale_integral r n m δ v hw h₁ h₂ σ hσ (fun y => |y|)

/-- **E6 concrete (the actual q1 scale estimator's σ-scale L¹ bound).**  Under
the weight-reproduction and stride-nondegeneracy premises (explicit ordinary
hypotheses; their concrete dischargers are upstream), the eventual long-L1
bound of `hurstHolder_q1_logScale_L1_lt_one` holds VERBATIM for the σ-scaled
data.  This is the feasible-bandwidth L¹ smallness of the scale error
`E_σ|ŝ_n - s_σ|` used by the E7 rate layer.  (The σ-side Lp measurability
transfers through `featureGaussian_map_smul` + `memLp_map_measure_iff` and is
not restated here.) -/
theorem p7_q1LogScale_L1_sigma_bound
    (p a b M : ℝ) (r : ℕ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (σ : ℝ) (hσ : σ ≠ 0)
    (hw : ∀ n m : ℕ, ∀ δ : ℝ, ∑ i, averagedLocalWeights r n 2 m δ i = 1)
    (h₁ : ∀ n : ℕ, ∀ i, ∑ j, commonFirstStrideCoefficients n 1 2 (by norm_num) i j •
      gridObservationFeatures n (midpointSampleHurst f hf.1 n) j ≠ 0)
    (h₂ : ∀ n : ℕ, ∀ i, ∑ j, commonFirstStrideCoefficients n 2 2 (by norm_num) i j •
      gridObservationFeatures n (midpointSampleHurst f hf.1 n) j ≠ 0) :
    ∃ N₀ > 0,
    ∃ A₁ ≥ 1, ∃ C₁ ≥ 0, ∃ D₁ ≥ 0,
    ∃ A₂ ≥ 1, ∃ C₂ ≥ 0, ∃ D₂ ≥ 0,
    ∃ Ew ≥ 0, ∃ N : ℕ, 2 ≤ N ∧
      ∀ n : ℕ, N ≤ n → 1 ≤ Real.log n →
      ∀ m : ℕ, 0 < m → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
      N₀ ≤ (n : ℝ) * δ → 1 ≤ (m : ℝ) * δ →
      (∫ x, |q1LogScaleEstimator r n m δ x - Real.log (σ ^ 2)|
        ∂featureGaussian
          (fun i => σ • gridObservationFeatures n (midpointSampleHurst f hf.1 n) i)) ≤
        Real.sqrt
          ((4 + 4 / (Real.log 2) ^ 2) * (Real.log n) ^ 2 *
            (D₁ / (n : ℝ) * firstStrideLongRowBound b C₁ A₁ 1 n +
             D₂ / (n : ℝ) * firstStrideLongRowBound b C₂ A₂ 2 n)) +
        Real.log n * gridCovarianceError b Ew n := by
  obtain ⟨N₀, hN₀, A₁, hA₁, C₁, hC₁, D₁, hD₁, A₂, hA₂, C₂, hC₂, D₂, hD₂,
      Ew, hEw, N, hN, hunit⟩ :=
    hurstHolder_q1_logScale_L1_lt_one p a b M r hp ha hb hab hM
  refine ⟨N₀, hN₀, A₁, hA₁, C₁, hC₁, D₁, hD₁, A₂, hA₂, C₂, hC₂, D₂, hD₂,
    Ew, hEw, N, hN, ?_⟩
  intro n hn hlog m hm δ hδ hδhalf hnd hmd
  obtain ⟨_, hXbound⟩ :=
    hunit n hn hlog f hf hF m hm δ hδ hδhalf hnd hmd
  have hidsig := p7_q1LogScale_L1_sigma_eq_unit r n m δ
    (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
    (hw n m δ) (h₁ n) (h₂ n) σ hσ
  rw [hidsig]
  exact hXbound

/-! ## E8 layer: scale equivariance and conditional inheritance -/

/-- Generic weighted log-statistic a.e. shift under a common scale
(`gaussianLogStatistic_smul` made a.e. on the feature-Gaussian space). -/
theorem p7_gaussianLogStatistic_scale_ae {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V]
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (v : ι → V) (w : κ → ℝ) (a : κ → EuclideanSpace ℝ ι)
    (h : ∀ j, ∑ i, a j i • v i ≠ 0) (σ : ℝ) (hσ : σ ≠ 0) :
    ∀ᵐ x ∂featureGaussian v,
      gaussianLogStatistic w a (σ • x)
        = Real.log (σ ^ 2) * (∑ i, w i) + gaussianLogStatistic w a x := by
  have hz : ∀ᵐ x ∂featureGaussian v, ∀ j, ⟪a j, x⟫ ≠ 0 :=
    ae_all_iff.mpr (fun j => featureGaussian_linear_ae_ne_zero v (a j) (h j))
  filter_upwards [hz] with x hx
  exact gaussianLogStatistic_smul w a x σ hσ hx

/-- **E8 (scale equivariance of the unknown-scale estimator).**  If BOTH the
main statistic and the pilot log-scale estimator shift by `log σ²` under
`x ↦ σ • x` (each a.e.; for the pilot this is `q1LogScaleEstimator_scale_ae`,
for a genuine weighted log statistic `p7_gaussianLogStatistic_scale_ae` with
unit-sum weights), then the unknown-scale estimator is a.e. INVARIANT under
the scaling: the two shifts cancel before the truncated inverse.  No
independence is used. -/
theorem p7_unknownScale_estimator_scale_ae
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {n : ℕ} (v : Fin n → V) (σ : ℝ) (hσ : σ ≠ 0)
    (c s : ℝ) (G S : EuclideanSpace ℝ (Fin n) → ℝ)
    (hG : ∀ᵐ x ∂featureGaussian v, G (σ • x) = G x + Real.log (σ ^ 2))
    (hS : ∀ᵐ x ∂featureGaussian v, S (σ • x) = S x + Real.log (σ ^ 2)) :
    ∀ᵐ x ∂featureGaussian v,
      p7UnknownScaleEstimator n c G S (σ • x) = p7UnknownScaleEstimator n c G S x := by
  filter_upwards [hG, hS] with x hxG hxS
  have hden : G (σ • x) - S (σ • x) = G x - S x := by rw [hxG, hxS]; ring
  show p5Trunc01 ((c - (G (σ • x) - S (σ • x))) / (2 * Real.log n))
      = p5Trunc01 ((c - (G x - S x)) / (2 * Real.log n))
  rw [hden]

/-- **E8, expectation-centered conditional inheritance.**  If the KNOWN-scale
expectation-centered limit holds (the D3-shaped conditional endpoint of the
upstream chain) and the normalized unknown-vs-known L¹ distance tends to 0 —
exactly the E6 output `2 A n log n · E|H^u - H^o| ≤ A n E|Ŝ - s_σ|` made
small — then the UNKNOWN-scale expectation-centered limit holds. -/
theorem p7_unknownScale_expectationCentered_of_known
    {Pn : ∀ n : ℕ, Measure (EuclideanSpace ℝ (Fin n))}
    [∀ n : ℕ, IsProbabilityMeasure (Pn n)]
    {Theta : Type*} [MeasurableSpace Theta]
    {P' : Measure Theta} [IsProbabilityMeasure P'] {Z : Theta → ℝ}
    (G S : ∀ n, EuclideanSpace ℝ (Fin n) → ℝ) (c s : ℕ → ℝ) (A L : ℕ → ℝ)
    (hknown : TendstoInDistribution (fun n x => 2 * A n * L n *
        (p7KnownScaleEstimator n (c n) (s n) (G n) x -
          (∫ y, p7KnownScaleEstimator n (c n) (s n) (G n) y ∂Pn n))) atTop Z Pn P')
    (hL1 : Tendsto (fun n => ∫ x, |2 * A n * L n *
          (p7UnknownScaleEstimator n (c n) (G n) (S n) x -
            (∫ y, p7UnknownScaleEstimator n (c n) (G n) (S n) y ∂Pn n))
        - 2 * A n * L n * (p7KnownScaleEstimator n (c n) (s n) (G n) x -
            (∫ y, p7KnownScaleEstimator n (c n) (s n) (G n) y ∂Pn n))| ∂Pn n)
      atTop (𝓝 0))
    (hYmeas : ∀ n, AEMeasurable (fun x => 2 * A n * L n *
        (p7UnknownScaleEstimator n (c n) (G n) (S n) x -
          (∫ y, p7UnknownScaleEstimator n (c n) (G n) (S n) y ∂Pn n))) (Pn n))
    (hDint : ∀ᶠ n in atTop, Integrable (fun x =>
      2 * A n * L n * (p7UnknownScaleEstimator n (c n) (G n) (S n) x -
          (∫ y, p7UnknownScaleEstimator n (c n) (G n) (S n) y ∂Pn n))
      - 2 * A n * L n * (p7KnownScaleEstimator n (c n) (s n) (G n) x -
          (∫ y, p7KnownScaleEstimator n (c n) (s n) (G n) y ∂Pn n))) (Pn n)) :
    TendstoInDistribution (fun n x => 2 * A n * L n *
        (p7UnknownScaleEstimator n (c n) (G n) (S n) x -
          (∫ y, p7UnknownScaleEstimator n (c n) (G n) (S n) y ∂Pn n))) atTop Z Pn P' :=
  triangular_L1_distribution_transfer Pn P' _ _ Z hknown hYmeas hDint hL1

/-- **E8, truth-centered conditional inheritance.**  Same as
`p7_unknownScale_expectationCentered_of_known` but at the truth center `h`:
the unknown-vs-known L¹ difference of the truth-centered statistics is
EXACTLY `2 A n log n (H^u - H^o)` (the `h - c` terms cancel), so the E6 L¹
smallness transports a known-scale truth-centered limit to the unknown scale. -/
theorem p7_unknownScale_truthCentered_of_known
    {Pn : ∀ n : ℕ, Measure (EuclideanSpace ℝ (Fin n))}
    [∀ n : ℕ, IsProbabilityMeasure (Pn n)]
    {Theta : Type*} [MeasurableSpace Theta]
    {P' : Measure Theta} [IsProbabilityMeasure P'] {Z : Theta → ℝ}
    (G S : ∀ n, EuclideanSpace ℝ (Fin n) → ℝ) (c s : ℕ → ℝ) (A L : ℕ → ℝ)
    (h : ℝ)
    (hknown : TendstoInDistribution (fun n x => 2 * A n * L n *
        (p7KnownScaleEstimator n (c n) (s n) (G n) x - h)) atTop Z Pn P')
    (hL1 : Tendsto (fun n => ∫ x, |2 * A n * L n *
          (p7UnknownScaleEstimator n (c n) (G n) (S n) x - h)
        - 2 * A n * L n * (p7KnownScaleEstimator n (c n) (s n) (G n) x - h)| ∂Pn n)
      atTop (𝓝 0))
    (hYmeas : ∀ n, AEMeasurable (fun x => 2 * A n * L n *
        (p7UnknownScaleEstimator n (c n) (G n) (S n) x - h)) (Pn n))
    (hDint : ∀ᶠ n in atTop, Integrable (fun x =>
      2 * A n * L n * (p7UnknownScaleEstimator n (c n) (G n) (S n) x - h)
      - 2 * A n * L n * (p7KnownScaleEstimator n (c n) (s n) (G n) x - h)) (Pn n)) :
    TendstoInDistribution (fun n x => 2 * A n * L n *
        (p7UnknownScaleEstimator n (c n) (G n) (S n) x - h)) atTop Z Pn P' :=
  triangular_L1_distribution_transfer Pn P' _ _ Z hknown hYmeas hDint hL1

/-! ## E7 layer: conservative rates -/

theorem p7_gridCovarianceError_nonneg (b C : ℝ) (hC : 0 ≤ C) (n : ℕ) :
    0 ≤ gridCovarianceError b C n := by
  have hlog : (0:ℝ) ≤ 1 + Real.log (2 * (n:ℝ)) := by
    rcases n with _ | m
    · simp
    · have h2 := Real.log_nonneg (show (1:ℝ) ≤ 2 * (((m:ℕ) + 1 : ℕ) : ℝ) by
        norm_cast
        omega)
      linarith
  unfold gridCovarianceError
  exact mul_nonneg (mul_nonneg hC hlog) (add_nonneg
    (Real.rpow_nonneg (Nat.cast_nonneg n) _) (Real.rpow_nonneg (Nat.cast_nonneg n) _))

/-- **E7 building block.** `(1-γ)ψ`-normalized single-log rate: for `α + r < 0`,
`(n : ℝ)^α · log n · n^r → 0` (log n ≤ 1 + log(2n) and the landed
`mesh_log_power_rpow_tendsto`). -/
private theorem p7_alpha_log_rpow_tendsto (α r : ℝ) (h : α + r < 0) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ α * Real.log n * (n : ℝ) ^ r) atTop (𝓝 0) := by
  have hlogge : ∀ n : ℕ, 0 ≤ Real.log (n : ℝ) := by
    intro n
    rcases n with _ | m
    · simp
    · exact Real.log_nonneg (by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le m)))
  refine squeeze_zero' (Eventually.of_forall fun n => mul_nonneg
    (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) α) (hlogge n))
    (Real.rpow_nonneg (Nat.cast_nonneg n) r)) ?_
    (mesh_log_power_rpow_tendsto (α + r) h 1)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog2n : Real.log (2 * (n : ℝ)) = Real.log 2 + Real.log (n : ℝ) := by
    rw [Real.log_mul (by norm_num) hnR.ne']
  have h1 : Real.log (n : ℝ) ≤ 1 + Real.log (2 * (n : ℝ)) := by
    have h2 := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    rw [hlog2n]
    linarith
  have h3 : 0 ≤ (n : ℝ) ^ r := Real.rpow_nonneg hnR.le r
  calc (n : ℝ) ^ α * Real.log n * (n : ℝ) ^ r
      ≤ (n : ℝ) ^ α * (1 + Real.log (2 * (n : ℝ))) * (n : ℝ) ^ r :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hnR.le α)) h3
    _ = (1 + Real.log (2 * (n : ℝ))) * ((n : ℝ) ^ α * (n : ℝ) ^ r) := by ring
    _ = (1 + Real.log (2 * (n : ℝ))) ^ 1 * (n : ℝ) ^ (α + r) := by
        rw [Real.rpow_add hnR, pow_one]

/-- **E7 building block.** Two-log rate: for `α + r < 0`,
`(1 + log(2n)) · (n : ℝ)^α · log n · n^r → 0`. -/
private theorem p7_alpha_loglog_rpow_tendsto (α r : ℝ) (h : α + r < 0) :
    Tendsto (fun n : ℕ => (1 + Real.log (2 * (n : ℝ)))
      * ((n : ℝ) ^ α * Real.log n * (n : ℝ) ^ r)) atTop (𝓝 0) := by
  have hLpos : ∀ n : ℕ, (0:ℝ) ≤ 1 + Real.log (2 * (n:ℝ)) := by
    intro n
    rcases n with _ | m
    · simp
    · have h2 := Real.log_nonneg (show (1:ℝ) ≤ 2 * (((m:ℕ) + 1 : ℕ) : ℝ) by
        norm_cast
        omega)
      linarith
  have hlogge : ∀ n : ℕ, 0 ≤ Real.log (n : ℝ) := by
    intro n
    rcases n with _ | m
    · simp
    · exact Real.log_nonneg (by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le m)))
  have hbase := mesh_log_power_rpow_tendsto (α + r) h 2
  refine squeeze_zero' (Eventually.of_forall fun n => mul_nonneg (hLpos n)
    (mul_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) α) (hlogge n))
      (Real.rpow_nonneg (Nat.cast_nonneg n) r))) ?_ hbase
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog2n : Real.log (2 * (n : ℝ)) = Real.log 2 + Real.log (n : ℝ) := by
    rw [Real.log_mul (by norm_num) hnR.ne']
  have h1 : Real.log (n : ℝ) ≤ 1 + Real.log (2 * (n : ℝ)) := by
    have h2 := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    rw [hlog2n]
    linarith
  have h2 : (n : ℝ) ^ α * (n : ℝ) ^ r = (n : ℝ) ^ (α + r) := (Real.rpow_add hnR α r).symm
  have h3 : 0 ≤ (n : ℝ) ^ (α + r) := Real.rpow_nonneg hnR.le _
  have h4 : 0 ≤ 1 + Real.log (2 * (n : ℝ)) := hLpos n
  calc (1 + Real.log (2 * (n : ℝ))) * ((n : ℝ) ^ α * Real.log n * (n : ℝ) ^ r)
      = ((1 + Real.log (2 * (n : ℝ))) * Real.log (n : ℝ))
          * ((n : ℝ) ^ α * (n : ℝ) ^ r) := by ring
    _ ≤ ((1 + Real.log (2 * (n : ℝ))) * (1 + Real.log (2 * (n : ℝ))))
          * (n : ℝ) ^ (α + r) := by
        rw [h2]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 h4) h3
    _ = (1 + Real.log (2 * (n : ℝ))) ^ 2 * (n : ℝ) ^ (α + r) := by rw [pow_two]

/-- **E7, conditional conservative rate (file 24 E8's boxed bound as an
explicit ordinary hypothesis).**  Given the conservative mesh-polynomial
eventual bound `E|ŝ_n - s_σ| ≤ C (1+log(2n))² n^{-(1-b)}` (whose derivation
from the landed long-L1 bound `hurstHolder_q1_logScale_L1_lt_one` runs through
the explicit row-bound split and the term dominations), the rate condition
`(1-γ)ψ < 1-b` — the bandwidth window `γ > 1 - (1-b)/ψ` — yields
`S_n^ψ · E|ŝ_n - s_σ| → 0`. -/
theorem p7_unknownScale_scale_L1_rate_of_mesh_bound
    (b γ ψ C : ℝ) (hb : b < 1) (hC : 0 ≤ C) (hwin : (1 - γ) * ψ < 1 - b)
    (g : ℕ → ℝ)
    (hg : ∀ᶠ n in atTop, 0 ≤ g n)
    (hbound : ∀ᶠ n in atTop, g n ≤ C * (1 + Real.log (2 * (n : ℝ))) ^ 2
      * (n : ℝ) ^ (-(1 - b))) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ ((1 - γ) * ψ) * g n) atTop (𝓝 0) := by
  have hmesh := (mesh_log_power_rpow_tendsto ((1 - γ) * ψ - (1 - b)) (by linarith) 2).const_mul C
  have hmesh0 : Tendsto (fun n : ℕ => C * (1 + Real.log (2 * (n : ℝ))) ^ 2 *
      (n : ℝ) ^ ((1 - γ) * ψ - (1 - b))) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_assoc] using hmesh
  refine squeeze_zero'
    (hg.mono fun n hn => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) hn) ?_ hmesh0
  filter_upwards [hbound, eventually_ge_atTop 1] with n hn hn1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have h1 : (n : ℝ) ^ (-(1 - b)) * (n : ℝ) ^ ((1 - γ) * ψ)
      = (n : ℝ) ^ ((1 - γ) * ψ - (1 - b)) := by
    have h2 := Real.rpow_add hnR (-(1 - b)) ((1 - γ) * ψ)
    rw [show -(1 - b) + ((1:ℝ) - γ) * ψ = (1 - γ) * ψ - (1 - b) from by ring] at h2
    exact h2.symm
  have h3 : (C * (1 + Real.log (2 * (n : ℝ))) ^ 2 * (n : ℝ) ^ (-(1 - b))) *
      (n : ℝ) ^ ((1 - γ) * ψ)
      = C * (1 + Real.log (2 * (n : ℝ))) ^ 2 * (n : ℝ) ^ ((1 - γ) * ψ - (1 - b)) := by
    calc (C * (1 + Real.log (2 * (n : ℝ))) ^ 2 * (n : ℝ) ^ (-(1 - b))) *
        (n : ℝ) ^ ((1 - γ) * ψ)
        = C * (1 + Real.log (2 * (n : ℝ))) ^ 2 *
          ((n : ℝ) ^ (-(1 - b)) * (n : ℝ) ^ ((1 - γ) * ψ)) := by ring
      _ = C * (1 + Real.log (2 * (n : ℝ))) ^ 2 *
          (n : ℝ) ^ ((1 - γ) * ψ - (1 - b)) := by rw [h1]
  calc (n : ℝ) ^ ((1 - γ) * ψ) * g n
      = g n * (n : ℝ) ^ ((1 - γ) * ψ) := by ring
    _ ≤ (C * (1 + Real.log (2 * (n : ℝ))) ^ 2 * (n : ℝ) ^ (-(1 - b))) *
        (n : ℝ) ^ ((1 - γ) * ψ) :=
        mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg hnR.le _)
    _ = C * (1 + Real.log (2 * (n : ℝ))) ^ 2 *
        (n : ℝ) ^ ((1 - γ) * ψ - (1 - b)) := h3

/-- **E7, conservative `s = 1` window (file 24 E9 + E3).**  For the long-memory
band `3/4 ≤ h ≤ b < 1`, the bandwidth window `1 - (1-b)/ψ < γ < 1` (with
`ψ = 2 - 2h ∈ (0, 1/2]`) forces BOTH the scale-L¹ rate condition
`(1-γ)ψ < 1-b` AND the truth-centering bias condition `(1-γ)ψ < γ·s` in the
conservative form `s = 1`. -/
theorem p7_conservative_window_s_one (h b γ : ℝ)
    (hbh : h ≤ b) (hb : b < 1) (h34 : 3 / 4 ≤ h)
    (hγ : 1 - (1 - b) / (2 - 2 * h) < γ) (hγ1 : γ < 1) :
    (1 - γ) * (2 - 2 * h) < 1 - b ∧ (1 - γ) * (2 - 2 * h) < γ := by
  have hψpos : 0 < 2 - 2 * h := by linarith
  have hγhalf : 1 / 2 < γ := by
    have h1 : (1 - b) / (2 - 2 * h) ≤ 1 / 2 := by
      have hcast := (div_le_iff₀ hψpos).mpr (show (1:ℝ) - b ≤ (1:ℝ) / 2 * (2 - 2 * h) by
        nlinarith [hbh])
      linarith [hcast]
    linarith
  constructor
  · have h1 : (1 - (1 - b) / (2 - 2 * h)) * (2 - 2 * h) < γ * (2 - 2 * h) :=
      mul_lt_mul_of_pos_right hγ hψpos
    have h2 : (1 - (1 - b) / (2 - 2 * h)) * (2 - 2 * h) = (2 - 2 * h) - (1 - b) := by
      have h3 : (1 - (1 - b) / (2 - 2 * h)) * (2 - 2 * h)
          = (2 - 2 * h) - (2 - 2 * h) * ((1 - b) / (2 - 2 * h)) := by ring
      have h4 : (2 - 2 * h) * ((1 - b) / (2 - 2 * h)) = 1 - b := by
        rw [div_eq_inv_mul, ← mul_assoc, mul_inv_cancel₀ hψpos.ne', one_mul]
      rw [h3, h4]
    rw [h2] at h1
    linarith
  · have hsmall : (2 : ℝ) - 2 * h ≤ 1 / 2 := by linarith
    have h1 : (1 - γ) * (2 - 2 * h) < (1 - 1 / 2) * (2 - 2 * h) := by
      refine mul_lt_mul_of_pos_right ?_ hψpos
      linarith
    have h3 : (1 - 1 / 2) * (2 - 2 * h) ≤ 1 / 2 := by
      rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
      nlinarith [hsmall]
    linarith [h1, h3, hγhalf]

/-- **E7, window nonemptiness.** The conservative window
`1 - (1-b)/ψ < γ < 1` is nonempty for every long-memory `3/4 ≤ h ≤ b < 1`. -/
theorem p7_bandwidth_window_nonempty (h b : ℝ) (hbh : h ≤ b) (hb : b < 1)
    (h34 : 3 / 4 ≤ h) :
    ∃ γ : ℝ, 1 - (1 - b) / (2 - 2 * h) < γ ∧ γ < 1 := by
  have hψpos : 0 < 2 - 2 * h := by linarith
  have h2 : 0 < 1 - b := by linarith
  have hpos : 0 < (1 - b) / (2 * (2 - 2 * h)) := div_pos h2 (by linarith)
  have hdiv : (1 - b) / (2 * (2 - 2 * h)) < (1 - b) / (2 - 2 * h) := by
    rw [div_lt_div_iff₀ (by linarith : (0 : ℝ) < 2 * (2 - 2 * h)) hψpos]
    nlinarith
  refine ⟨1 - (1 - b) / (2 * (2 - 2 * h)), by linarith [hdiv, hpos], by linarith [hpos]⟩

end Hurst
