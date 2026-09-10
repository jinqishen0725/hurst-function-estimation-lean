import Hurst.FiniteIidGaussianVector
import Hurst.SecondChaosTriangularSpectral
import Hurst.DistributionEventualTransfer

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Hurst

/-- Replace the limiting random variable by any identically distributed
representative, possibly on a different probability space. -/
theorem TendstoInDistribution.identDistrib_limit
    {ι E Omega' Theta : Type*} {Omega : ι → Type*}
    [∀ i, MeasurableSpace (Omega i)]
    (P : ∀ i, Measure (Omega i)) [∀ i, IsProbabilityMeasure (P i)]
    [MeasurableSpace Omega'] (P' : Measure Omega') [IsProbabilityMeasure P']
    [MeasurableSpace Theta] (nu : Measure Theta) [IsProbabilityMeasure nu]
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    (X : ∀ i, Omega i → E) (l : Filter ι)
    (Z : Omega' → E) (W : Theta → E)
    (h : TendstoInDistribution X l Z P P')
    (hZW : IdentDistrib Z W P' nu) :
    TendstoInDistribution X l W P nu where
  forall_aemeasurable := h.forall_aemeasurable
  aemeasurable_limit := hZW.aemeasurable_snd
  tendsto := by
    convert h.tendsto using 1
    congr 1
    apply Subtype.ext
    exact hZW.map_eq.symm

/-- On a fixed finite standard-Gaussian space, coefficientwise convergence
of a finite centered-square sum implies convergence in distribution. -/
theorem centeredSpectralSquares_coefficients_tendstoInDistribution
    (lambdaN : ℕ → Fin K → ℝ) (lambda : Fin K → ℝ)
    (hlambda : ∀ j, Tendsto (fun n ↦ lambdaN n j) atTop (𝓝 (lambda j))) :
    TendstoInDistribution (fun n ↦ centeredSpectralSquares (lambdaN n))
      atTop (centeredSpectralSquares lambda)
      (fun _ ↦ stdGaussian (EuclideanSpace ℝ (Fin K)))
      (stdGaussian (EuclideanSpace ℝ (Fin K))) := by
  apply tendstoInDistribution_of_ae_tendsto
  · intro n
    exact (centeredSpectralSquares_memLp_two (lambdaN n)).aemeasurable
  · exact (centeredSpectralSquares_memLp_two lambda).aemeasurable
  · filter_upwards [] with x
    unfold centeredSpectralSquares
    apply tendsto_finsetSum
    intro j hj
    exact (hlambda j).mul_const (x j ^ 2 - 1)

/-- Entirely internal spectral-truncation criterion for convergence of a
triangular array of finite symmetric Gaussian quadratic forms to a stated
second-chaos series law.

The two substantive hypotheses are deterministic: convergence of every
padded eigenvalue coefficient and a uniform `ℓ²` bound on the discarded
eigenvalue tail. -/
theorem centeredMatrixQuadratic_tendsto_secondChaos_of_spectral_data
    (m : ℕ → ℕ)
    (A : ∀ n, Matrix (Fin (m n)) (Fin (m n)) ℝ)
    (hA : ∀ n, (A n).IsHermitian)
    {Theta : Type*} [MeasurableSpace Theta]
    (P' : Measure Theta) [IsProbabilityMeasure P']
    (Q : Theta → ℝ) (lambda : ℕ → ℝ)
    (hQ : IsSecondChaosSeriesLaw P' Q lambda)
    (hm : Tendsto m atTop atTop)
    (hcoeff : ∀ j : ℕ, Tendsto (fun n ↦
      if hj : j < m n then (hA n).eigenvalues ⟨j, hj⟩ else 0)
      atTop (𝓝 (lambda j)))
    (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (htail : ∀ K, ∀ᶠ n in atTop,
      2 * (∑ i : Fin (m n),
        if K ≤ i.val then (hA n).eigenvalues i ^ 2 else 0) ≤ e K) :
    TendstoInDistribution (fun n ↦ centeredMatrixQuadratic (A n))
      atTop Q
      (fun n ↦ stdGaussian (EuclideanSpace ℝ (Fin (m n)))) P' := by
  let Y := fun n ↦ centeredMatrixQuadratic (A n)
  let YK := fun K n ↦ centeredMatrixQuadraticSpectralPrefix (hA n) K
  apply tendstoInDistribution_of_secondChaos_spectral_truncations
    (fun n ↦ stdGaussian (EuclideanSpace ℝ (Fin (m n)))) P'
    Y YK Q lambda hQ (e := e)
  · intro n
    dsimp only [Y]
    unfold centeredMatrixQuadratic
    fun_prop
  · intro K Z hZmeas hZi hZlaw
    let lambdaN : ℕ → Fin K → ℝ := fun n j ↦
      if hKm : K ≤ m n then
        (hA n).eigenvalues (Fin.castLE hKm j)
      else 0
    have hlambdaN : ∀ j : Fin K,
        Tendsto (fun n ↦ lambdaN n j) atTop (𝓝 (lambda j.val)) := by
      intro j
      apply (hcoeff j.val).congr'
      filter_upwards [hm.eventually_ge_atTop K] with n hKm
      dsimp only [lambdaN]
      rw [dif_pos hKm, dif_pos (j.isLt.trans_le hKm)]
      congr
    have hcommon := centeredSpectralSquares_coefficients_tendstoInDistribution
      lambdaN (fun j : Fin K ↦ lambda j.val) hlambdaN
    let X : ∀ n, EuclideanSpace ℝ (Fin (m n)) → ℝ := fun n ↦
      if hKm : K ≤ m n then
        centeredMatrixQuadraticSpectralPrefix (hA n) K
      else fun _ ↦ 0
    have hrow : ∀ n, IdentDistrib (X n)
        (centeredSpectralSquares (lambdaN n))
        (stdGaussian (EuclideanSpace ℝ (Fin (m n))))
        (stdGaussian (EuclideanSpace ℝ (Fin K))) := by
      intro n
      by_cases hKm : K ≤ m n
      · simpa only [X, lambdaN, hKm, ↓reduceDIte] using
          centeredMatrixQuadraticSpectralPrefix_identDistrib
            (hA n) K hKm
      · have hzero : lambdaN n = 0 := by
          funext j
          simp [lambdaN, hKm]
        rw [hzero]
        have htarget : centeredSpectralSquares (0 : Fin K → ℝ) =
            fun _ ↦ 0 := by
          funext x
          simp [centeredSpectralSquares]
        rw [htarget]
        have hXzero : X n = fun _ ↦ 0 := by
          simp [X, hKm]
        rw [hXzero]
        refine ⟨measurable_const.aemeasurable,
          measurable_const.aemeasurable, ?_⟩
        simp [Measure.map_const]
    have hX := tendstoInDistribution_of_identDistrib_rows
      (fun n ↦ stdGaussian (EuclideanSpace ℝ (Fin (m n))))
      (stdGaussian (EuclideanSpace ℝ (Fin K))) X
      (fun n ↦ centeredSpectralSquares (lambdaN n))
      (centeredSpectralSquares (fun j : Fin K ↦ lambda j.val))
      (stdGaussian (EuclideanSpace ℝ (Fin K))) atTop hrow hcommon
    have htarget : IdentDistrib
        (centeredSpectralSquares (fun j : Fin K ↦ lambda j.val))
        (secondChaosSeriesPartial lambda Z K)
        (stdGaussian (EuclideanSpace ℝ (Fin K))) P' := by
      have hbase := centeredSpectralSquares_iid_identDistrib
        P' Z hZmeas hZi hZlaw (fun j : Fin K ↦ lambda j.val)
      convert hbase using 1
      funext x
      unfold secondChaosSeriesPartial
      exact (Fin.sum_univ_eq_sum_range
        (fun j ↦ lambda j * (Z j x ^ 2 - 1)) K).symm
    have hXtarget := TendstoInDistribution.identDistrib_limit
      (fun n ↦ stdGaussian (EuclideanSpace ℝ (Fin (m n))))
      (stdGaussian (EuclideanSpace ℝ (Fin K))) P'
      X atTop (centeredSpectralSquares (fun j : Fin K ↦ lambda j.val))
      (secondChaosSeriesPartial lambda Z K) hX htarget
    apply tendstoInDistribution_congr_eventually
      (fun n ↦ stdGaussian (EuclideanSpace ℝ (Fin (m n)))) P'
      X (YK K) (secondChaosSeriesPartial lambda Z K) atTop
    · intro n
      dsimp only [YK]
      exact (centeredMatrixQuadraticSpectralPrefix_measurable
        (hA n) K).aemeasurable
    · filter_upwards [hm.eventually_ge_atTop K] with n hKm
      filter_upwards [] with x
      change X n x = centeredMatrixQuadraticSpectralPrefix (hA n) K x
      simp [X, hKm]
    · exact hXtarget
  · exact he
  · intro K
    filter_upwards [htail K] with n hn
    have hL2 := centeredMatrixQuadratic_sub_spectralPrefix_L2 (hA n) K
    exact ⟨hL2.1, hL2.2.le.trans hn⟩

end Hurst
