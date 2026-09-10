import Hurst.SecondChaosSeriesConvergence
import Hurst.HermitePair
import Mathlib.Probability.Independence.Basic

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Polynomial
open scoped Topology
namespace Hurst

/-- Distinct centered squares in an iid standard Gaussian sequence are
orthogonal in `L²`; each has squared norm `2`. -/
theorem iid_standardGaussian_centeredSquare_integral
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    [IsProbabilityMeasure P] (Z : ℕ → Omega → ℝ)
    (hZmeas : ∀ j, AEMeasurable (Z j) P) (hZi : iIndepFun Z P)
    (hZlaw : ∀ j, P.map (Z j) = gaussianReal 0 1) (i j : ℕ) :
    (∫ x, ((Z i x) ^ 2 - 1) * ((Z j x) ^ 2 - 1) ∂P) =
      if i = j then 2 else 0 := by
  have hLaw : ∀ k, HasLaw (Z k) (gaussianReal 0 1) P := fun k ↦
    ⟨hZmeas k, hZlaw k⟩
  split_ifs with hij
  · subst j
    let f : ℝ → ℝ := fun z ↦ (z ^ 2 - 1) * (z ^ 2 - 1)
    have hf : AEStronglyMeasurable f (gaussianReal 0 1) :=
      (show Continuous f by fun_prop).aestronglyMeasurable
    have hmap := (hLaw i).integral_comp hf
    change ∫ x, f (Z i x) ∂P = 2
    rw [show (∫ x, f (Z i x) ∂P) = ∫ z, f z ∂gaussianReal 0 1 by
      simpa [Function.comp_def] using hmap]
    dsimp [f]
    simpa [gaussianHermite_two] using
      (standardGaussian_hermite_orthogonality 2 2)
  · have hPair : HasLaw (fun x ↦ (Z i x, Z j x))
        ((gaussianReal 0 1).prod (gaussianReal 0 1)) P :=
      (hZi.indepFun hij).hasLaw_prod (hLaw i) (hLaw j)
    let f : ℝ × ℝ → ℝ := fun z ↦ (z.1 ^ 2 - 1) * (z.2 ^ 2 - 1)
    have hf : AEStronglyMeasurable f
        ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
      (show Continuous f by fun_prop).aestronglyMeasurable
    have hmap := hPair.integral_comp hf
    change ∫ x, f (Z i x, Z j x) ∂P = 0
    rw [show (∫ x, f (Z i x, Z j x) ∂P) =
        ∫ z, f z ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) by
      simpa [Function.comp_def] using hmap]
    dsimp [f]
    simpa [gaussianHermite_two] using
      (standardGaussian_pair_hermite 2 2 0 1 (by norm_num))

/-- Every centered square in an iid standard Gaussian sequence belongs to
`L²`.  The formulation only needs almost-everywhere measurability of the
chosen coordinate representatives. -/
theorem iid_standardGaussian_centeredSquare_memLp
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    [IsProbabilityMeasure P] (Z : ℕ → Omega → ℝ)
    (hZmeas : ∀ j, AEMeasurable (Z j) P)
    (hZlaw : ∀ j, P.map (Z j) = gaussianReal 0 1) (j : ℕ) :
    MemLp (fun x ↦ (Z j x) ^ 2 - 1) 2 P := by
  have hbase : MemLp (fun z : ℝ ↦ z ^ 2 - 1) 2 (gaussianReal 0 1) := by
    have h := standardGaussian_polynomial_memLp_two (gaussianHermite 2)
    simpa [gaussianHermite_two] using h
  apply MemLp.comp_of_map (f := Z j) (g := fun z : ℝ ↦ z ^ 2 - 1) _ (hZmeas j)
  rwa [hZlaw j]

/-- Exact `L²` isometry for every finite spectral sum of independent
centered Gaussian squares. -/
theorem iid_standardGaussian_centeredSquare_finset_L2
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    [IsProbabilityMeasure P] (Z : ℕ → Omega → ℝ)
    (hZmeas : ∀ j, AEMeasurable (Z j) P) (hZi : iIndepFun Z P)
    (hZlaw : ∀ j, P.map (Z j) = gaussianReal 0 1)
    (lambda : ℕ → ℝ) (s : Finset ℕ) :
    (∫ x, (∑ j ∈ s, lambda j * ((Z j x) ^ 2 - 1)) ^ 2 ∂P) =
      2 * ∑ j ∈ s, (lambda j) ^ 2 := by
  let H : ℕ → Omega → ℝ := fun j x ↦ (Z j x) ^ 2 - 1
  have hH2 : ∀ j, MemLp (H j) 2 P := fun j ↦ by
    simpa [H] using
      iid_standardGaussian_centeredSquare_memLp P Z hZmeas hZlaw j
  have hprod : ∀ i j, Integrable (fun x ↦
      (lambda i * H i x) * (lambda j * H j x)) P := fun i j ↦
    ((hH2 i).const_mul (lambda i)).integrable_mul ((hH2 j).const_mul (lambda j))
  have hpairInt : ∀ i j, (∫ x,
      (lambda i * H i x) * (lambda j * H j x) ∂P) =
      lambda i * lambda j * (if i = j then 2 else 0) := by
    intro i j
    rw [show (fun x ↦ (lambda i * H i x) * (lambda j * H j x)) =
        fun x ↦ (lambda i * lambda j) * (H i x * H j x) by
      funext x
      ring]
    rw [integral_const_mul]
    simp only [H, iid_standardGaussian_centeredSquare_integral P Z hZmeas hZi hZlaw]
  have hsquare : (fun x ↦ (∑ j ∈ s, lambda j * H j x) ^ 2) =
      fun x ↦ ∑ i ∈ s, ∑ j ∈ s,
        (lambda i * H i x) * (lambda j * H j x) := by
    funext x
    simp only [pow_two, Finset.sum_mul_sum]
  rw [show (∫ x, (∑ j ∈ s, lambda j * ((Z j x) ^ 2 - 1)) ^ 2 ∂P) =
      ∫ x, (∑ j ∈ s, lambda j * H j x) ^ 2 ∂P by rfl]
  rw [hsquare]
  rw [integral_finsetSum s (fun i hi ↦
    integrable_finsetSum s (fun j hj ↦ hprod i j))]
  calc
    ∑ i ∈ s, ∫ x, ∑ j ∈ s,
        (lambda i * H i x) * (lambda j * H j x) ∂P =
        ∑ i ∈ s, ∑ j ∈ s,
          lambda i * lambda j * (if i = j then 2 else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_finsetSum s (fun j hj ↦ hprod i j)]
      apply Finset.sum_congr rfl
      intro j hj
      exact hpairInt i j
    _ = ∑ i ∈ s, 2 * lambda i ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [hi]
      ring
    _ = 2 * ∑ j ∈ s, lambda j ^ 2 := by
      rw [Finset.mul_sum]

/-- For a fixed spectral cutoff, coefficientwise convergence implies
convergence in distribution of the corresponding Gaussian-chaos sums. -/
theorem secondChaosSeriesPartial_coefficients_tendstoInDistribution
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    [IsProbabilityMeasure P] (Z : ℕ → Omega → ℝ)
    (hZmeas : ∀ j, AEMeasurable (Z j) P)
    (lambdaN : ℕ → ℕ → ℝ) (lambda : ℕ → ℝ) (K : ℕ)
    (hlambda : ∀ j < K, Tendsto (fun n ↦ lambdaN n j) atTop (nhds (lambda j))) :
    TendstoInDistribution
      (fun n ↦ secondChaosSeriesPartial (lambdaN n) Z K) atTop
      (secondChaosSeriesPartial lambda Z K) (fun _ ↦ P) P := by
  apply tendstoInDistribution_of_ae_tendsto
  · intro n
    unfold secondChaosSeriesPartial
    have hm : AEMeasurable (∑ j ∈ Finset.range K,
        fun x ↦ lambdaN n j * ((Z j x) ^ 2 - 1)) P := by
      apply Finset.aemeasurable_sum
      intro j hj
      exact ((hZmeas j).pow_const 2).sub aemeasurable_const |>.const_mul _
    convert hm using 1
    funext x
    simp
  · unfold secondChaosSeriesPartial
    have hm : AEMeasurable (∑ j ∈ Finset.range K,
        fun x ↦ lambda j * ((Z j x) ^ 2 - 1)) P := by
      apply Finset.aemeasurable_sum
      intro j hj
      exact ((hZmeas j).pow_const 2).sub aemeasurable_const |>.const_mul _
    convert hm using 1
    funext x
    simp
  · filter_upwards [] with x
    apply tendsto_finsetSum
    intro j hj
    exact (hlambda j (Finset.mem_range.mp hj)).mul_const ((Z j x) ^ 2 - 1)

/-- Removing a smaller finite spectral block from a larger one leaves exactly
the squared-eigenvalue mass on the set difference. -/
theorem iid_standardGaussian_centeredSquare_finset_difference_L2
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    [IsProbabilityMeasure P] (Z : ℕ → Omega → ℝ)
    (hZmeas : ∀ j, AEMeasurable (Z j) P) (hZi : iIndepFun Z P)
    (hZlaw : ∀ j, P.map (Z j) = gaussianReal 0 1)
    (lambda : ℕ → ℝ) (s t : Finset ℕ) (hts : t ⊆ s) :
    MemLp (fun x ↦
      (∑ j ∈ s, lambda j * ((Z j x) ^ 2 - 1)) -
        ∑ j ∈ t, lambda j * ((Z j x) ^ 2 - 1)) 2 P ∧
    (∫ x, ((∑ j ∈ s, lambda j * ((Z j x) ^ 2 - 1)) -
        ∑ j ∈ t, lambda j * ((Z j x) ^ 2 - 1)) ^ 2 ∂P) =
      2 * ∑ j ∈ s \ t, lambda j ^ 2 := by
  let H : ℕ → Omega → ℝ := fun j x ↦ lambda j * ((Z j x) ^ 2 - 1)
  have hH2 : ∀ j, MemLp (H j) 2 P := fun j ↦ by
    exact (iid_standardGaussian_centeredSquare_memLp P Z hZmeas hZlaw j).const_mul _
  have hfun : (fun x ↦ (∑ j ∈ s, H j x) - ∑ j ∈ t, H j x) =
      fun x ↦ ∑ j ∈ s \ t, H j x := by
    funext x
    have hsum := Finset.sum_sdiff hts (f := fun j ↦ H j x)
    linarith
  constructor
  · rw [show (fun x ↦
        (∑ j ∈ s, lambda j * ((Z j x) ^ 2 - 1)) -
          ∑ j ∈ t, lambda j * ((Z j x) ^ 2 - 1)) =
        fun x ↦ (∑ j ∈ s, H j x) - ∑ j ∈ t, H j x by rfl]
    rw [hfun]
    exact memLp_finsetSum (s \ t) (fun j hj ↦ hH2 j)
  · rw [show (fun x ↦
        ((∑ j ∈ s, lambda j * ((Z j x) ^ 2 - 1)) -
          ∑ j ∈ t, lambda j * ((Z j x) ^ 2 - 1)) ^ 2) =
        fun x ↦ ((∑ j ∈ s, H j x) - ∑ j ∈ t, H j x) ^ 2 by rfl]
    rw [show (fun x ↦ ((∑ j ∈ s, H j x) - ∑ j ∈ t, H j x) ^ 2) =
        fun x ↦ (∑ j ∈ s \ t, H j x) ^ 2 by
      funext x
      rw [congrFun hfun x]]
    simpa [H] using
      iid_standardGaussian_centeredSquare_finset_L2
        P Z hZmeas hZi hZlaw lambda (s \ t)

end Hurst
