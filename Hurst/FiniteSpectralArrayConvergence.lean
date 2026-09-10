import Hurst.FiniteGaussianSpectralConvergence
import Hurst.SpectralPermutation
import Hurst.DistributionVaryingLawTransfer

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Polynomial
open scoped Topology
namespace Hurst

/-- The initial index block of a finite centered Gaussian spectral sum. -/
def centeredSpectralPrefix {d : ℕ} (lambda : Fin d → ℝ) (K : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i : Fin d, if i.val < K then lambda i * (x i ^ 2 - 1) else 0

theorem centeredSpectralPrefix_measurable {d : ℕ}
    (lambda : Fin d → ℝ) (K : ℕ) :
    Measurable (centeredSpectralPrefix lambda K) := by
  unfold centeredSpectralPrefix
  apply Finset.measurable_sum
  intro i hi
  by_cases h : i.val < K
  · simp only [h, if_true]
    fun_prop
  · simp only [h, if_false]
    exact measurable_const

private theorem centeredSpectralPrefix_eq_prefixCoordinates {d : ℕ}
    (lambda : Fin d → ℝ) (K : ℕ) (hKd : K ≤ d)
    (x : EuclideanSpace ℝ (Fin d)) :
    centeredSpectralPrefix lambda K x =
      centeredSpectralSquares (fun j : Fin K ↦ lambda (Fin.castLE hKd j))
        (euclideanFinPrefix K d hKd x) := by
  unfold centeredSpectralPrefix centeredSpectralSquares
  simp_rw [euclideanFinPrefix_apply]
  rw [← Finset.sum_filter]
  apply Finset.sum_bij
    (fun i hi ↦ (⟨i.val, (Finset.mem_filter.mp hi).2⟩ : Fin K))
  · intro i hi
    simp
  · intro i hi j hj hij
    exact Fin.ext (congrArg (fun z : Fin K => z.val) hij)
  · intro j hj
    refine ⟨Fin.castLE hKd j, ?_, ?_⟩
    · simp
    · exact Fin.ext rfl
  · intro i hi
    rfl

theorem centeredSpectralPrefix_identDistrib {d : ℕ}
    (lambda : Fin d → ℝ) (K : ℕ) (hKd : K ≤ d) :
    IdentDistrib (centeredSpectralPrefix lambda K)
      (centeredSpectralSquares
        (fun j : Fin K ↦ lambda (Fin.castLE hKd j)))
      (stdGaussian (EuclideanSpace ℝ (Fin d)))
      (stdGaussian (EuclideanSpace ℝ (Fin K))) := by
  let T := euclideanFinPrefix K d hKd
  let F := centeredSpectralSquares
    (fun j : Fin K ↦ lambda (Fin.castLE hKd j))
  have hT := euclideanFinPrefix_measurePreserving K d hKd
  have hF : Measurable F := by
    dsimp only [F]
    unfold centeredSpectralSquares
    exact Finset.measurable_sum _ fun i _ => by fun_prop
  have hpoint : centeredSpectralPrefix lambda K = F ∘ T := by
    funext x
    exact centeredSpectralPrefix_eq_prefixCoordinates lambda K hKd x
  refine ⟨(centeredSpectralPrefix_measurable lambda K).aemeasurable,
    hF.aemeasurable, ?_⟩
  rw [hpoint, ← Measure.map_map hF hT.measurable, hT.map_eq]

theorem centeredSpectralSquares_sub_prefix_L2 {d : ℕ}
    (lambda : Fin d → ℝ) (K : ℕ) :
    MemLp (fun x ↦ centeredSpectralSquares lambda x -
      centeredSpectralPrefix lambda K x) 2
      (stdGaussian (EuclideanSpace ℝ (Fin d))) ∧
    (∫ x, (centeredSpectralSquares lambda x -
      centeredSpectralPrefix lambda K x) ^ 2
        ∂stdGaussian (EuclideanSpace ℝ (Fin d))) =
      2 * ∑ i : Fin d, if K ≤ i.val then lambda i ^ 2 else 0 := by
  let tail : Fin d → ℝ := fun i ↦ if K ≤ i.val then lambda i else 0
  have hpoint : (fun x ↦ centeredSpectralSquares lambda x -
      centeredSpectralPrefix lambda K x) = centeredSpectralSquares tail := by
    funext x
    unfold centeredSpectralSquares centeredSpectralPrefix tail
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hiK : i.val < K
    · have hKi : ¬K ≤ i.val := not_le.mpr hiK
      simp [hiK, hKi]
    · have hKi : K ≤ i.val := not_lt.mp hiK
      simp [hiK, hKi]
  have htail2 := centeredSpectralSquares_memLp_two tail
  constructor
  · rwa [hpoint]
  · rw [hpoint, centeredSpectralSquares_secondMoment]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [tail]
    split_ifs <;> simp_all

/-- Internal convergence theorem for varying finite centered spectral sums.
The coefficient order is explicit, so this theorem can be used after a
rowwise eigenvalue permutation supplied by deterministic spectral matching. -/
theorem centeredSpectralSquares_tendsto_secondChaos_of_padded_l2
    (m : ℕ → ℕ) (lambdaN : ∀ n, Fin (m n) → ℝ)
    {Theta : Type*} [MeasurableSpace Theta]
    (P' : Measure Theta) [IsProbabilityMeasure P']
    (Q : Theta → ℝ) (lambda : ℕ → ℝ)
    (hQ : IsSecondChaosSeriesLaw P' Q lambda)
    (hm : Tendsto m atTop atTop)
    (hcoeff : ∀ j : ℕ, Tendsto (fun n ↦
      if hj : j < m n then lambdaN n ⟨j, hj⟩ else 0)
      atTop (𝓝 (lambda j)))
    (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (htail : ∀ K, ∀ᶠ n in atTop,
      2 * (∑ i : Fin (m n), if K ≤ i.val then lambdaN n i ^ 2 else 0) ≤ e K) :
    TendstoInDistribution (fun n ↦ centeredSpectralSquares (lambdaN n))
      atTop Q (fun n ↦ stdGaussian (EuclideanSpace ℝ (Fin (m n)))) P' := by
  let Y := fun n ↦ centeredSpectralSquares (lambdaN n)
  let YK := fun K n ↦ centeredSpectralPrefix (lambdaN n) K
  apply tendstoInDistribution_of_secondChaos_spectral_truncations
    (fun n ↦ stdGaussian (EuclideanSpace ℝ (Fin (m n)))) P'
    Y YK Q lambda hQ (e := e)
  · intro n
    dsimp only [Y]
    exact (centeredSpectralSquares_memLp_two (lambdaN n)).aemeasurable
  · intro K Z hZmeas hZi hZlaw
    let coeffK : ℕ → Fin K → ℝ := fun n j ↦
      if hKm : K ≤ m n then lambdaN n (Fin.castLE hKm j) else 0
    have hcoeffK : ∀ j : Fin K,
        Tendsto (fun n ↦ coeffK n j) atTop (𝓝 (lambda j.val)) := by
      intro j
      apply (hcoeff j.val).congr'
      filter_upwards [hm.eventually_ge_atTop K] with n hKm
      dsimp only [coeffK]
      rw [dif_pos hKm, dif_pos (j.isLt.trans_le hKm)]
      congr
    have hcommon := centeredSpectralSquares_coefficients_tendstoInDistribution
      coeffK (fun j : Fin K ↦ lambda j.val) hcoeffK
    let X : ∀ n, EuclideanSpace ℝ (Fin (m n)) → ℝ := fun n ↦
      if hKm : K ≤ m n then centeredSpectralPrefix (lambdaN n) K
      else fun _ ↦ 0
    have hrow : ∀ n, IdentDistrib (X n)
        (centeredSpectralSquares (coeffK n))
        (stdGaussian (EuclideanSpace ℝ (Fin (m n))))
        (stdGaussian (EuclideanSpace ℝ (Fin K))) := by
      intro n
      by_cases hKm : K ≤ m n
      · simpa only [X, coeffK, hKm, ↓reduceDIte] using
          centeredSpectralPrefix_identDistrib (lambdaN n) K hKm
      · have hzero : coeffK n = 0 := by
          funext j
          simp [coeffK, hKm]
        rw [hzero]
        have htarget : centeredSpectralSquares (0 : Fin K → ℝ) =
            fun _ ↦ 0 := by
          funext x
          simp [centeredSpectralSquares]
        rw [htarget]
        have hXzero : X n = fun _ ↦ 0 := by simp [X, hKm]
        rw [hXzero]
        refine ⟨measurable_const.aemeasurable,
          measurable_const.aemeasurable, ?_⟩
        simp [Measure.map_const]
    have hX := tendstoInDistribution_of_identDistrib_rows
      (fun n ↦ stdGaussian (EuclideanSpace ℝ (Fin (m n))))
      (stdGaussian (EuclideanSpace ℝ (Fin K))) X
      (fun n ↦ centeredSpectralSquares (coeffK n))
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
      exact (centeredSpectralPrefix_measurable (lambdaN n) K).aemeasurable
    · filter_upwards [hm.eventually_ge_atTop K] with n hKm
      filter_upwards [] with x
      change X n x = centeredSpectralPrefix (lambdaN n) K x
      simp [X, hKm]
    · exact hXtarget
  · exact he
  · intro K
    filter_upwards [htail K] with n hn
    have hL2 := centeredSpectralSquares_sub_prefix_L2 (lambdaN n) K
    exact ⟨hL2.1, hL2.2.le.trans hn⟩

/-- A permutation-aware version for finite symmetric Gaussian quadratic
forms.  The row permutations are explicit mathematical data, so no ordering
property of mathlib's eigenvalue enumeration is assumed. -/
theorem centeredMatrixQuadratic_tendsto_secondChaos_of_permuted_spectral_data
    (m : ℕ → ℕ)
    (A : ∀ n, Matrix (Fin (m n)) (Fin (m n)) ℝ)
    (hA : ∀ n, (A n).IsHermitian)
    (sigma : ∀ n, Equiv.Perm (Fin (m n)))
    {Theta : Type*} [MeasurableSpace Theta]
    (P' : Measure Theta) [IsProbabilityMeasure P']
    (Q : Theta → ℝ) (lambda : ℕ → ℝ)
    (hQ : IsSecondChaosSeriesLaw P' Q lambda)
    (hm : Tendsto m atTop atTop)
    (hcoeff : ∀ j : ℕ, Tendsto (fun n ↦
      if hj : j < m n then
        (hA n).eigenvalues (sigma n ⟨j, hj⟩) else 0)
      atTop (𝓝 (lambda j)))
    (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (htail : ∀ K, ∀ᶠ n in atTop,
      2 * (∑ i : Fin (m n), if K ≤ i.val then
        (hA n).eigenvalues (sigma n i) ^ 2 else 0) ≤ e K) :
    TendstoInDistribution (fun n ↦ centeredMatrixQuadratic (A n))
      atTop Q (fun n ↦ stdGaussian (EuclideanSpace ℝ (Fin (m n)))) P' := by
  let lambdaN : ∀ n, Fin (m n) → ℝ := fun n i ↦
    (hA n).eigenvalues (sigma n i)
  have hspectral := centeredSpectralSquares_tendsto_secondChaos_of_padded_l2
    m lambdaN P' Q lambda hQ hm (by
      intro j
      simpa only [lambdaN] using hcoeff j) e he (by
      intro K
      simpa only [lambdaN] using htail K)
  apply tendstoInDistribution_of_identDistrib_rows_varying
    (fun n ↦ stdGaussian (EuclideanSpace ℝ (Fin (m n))))
    (fun n ↦ stdGaussian (EuclideanSpace ℝ (Fin (m n)))) P'
    (fun n ↦ centeredMatrixQuadratic (A n))
    (fun n ↦ centeredSpectralSquares (lambdaN n)) Q atTop
  · intro n
    exact (centeredMatrixQuadratic_identDistrib_eigenvalueSquares (hA n)).trans
      (centeredSpectralSquares_permute_identDistrib (sigma n)
        (hA n).eigenvalues)
  · exact hspectral

end Hurst
