import Hurst.StandardGaussianPrefix
import Hurst.SecondChaosSeriesL2

noncomputable section
open Set MeasureTheory ProbabilityTheory Matrix Filter Polynomial
open scoped RealInnerProductSpace Topology
namespace Hurst

variable {d : ℕ}

/-- The part of a finite symmetric Gaussian quadratic form carried by the
first `K` entries of the chosen eigenvalue enumeration. -/
def centeredMatrixQuadraticSpectralPrefix
    {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian) (K : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i : Fin d, if i.val < K then
    hA.eigenvalues i * (hermitianEigenCoordinates hA x i ^ 2 - 1) else 0

theorem centeredMatrixQuadraticSpectralPrefix_measurable
    {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian) (K : ℕ) :
    Measurable (centeredMatrixQuadraticSpectralPrefix hA K) := by
  unfold centeredMatrixQuadraticSpectralPrefix
  apply Finset.measurable_sum
  intro i hi
  by_cases h : i.val < K
  · simp only [h, if_true]
    fun_prop
  · simp only [h, if_false]
    exact measurable_const

/-- Finite centered spectral sums are in `L²` under the canonical Gaussian
law. -/
theorem centeredSpectralSquares_memLp_two
    {ι : Type*} [Fintype ι] [DecidableEq ι] (lam : ι → ℝ) :
    MemLp (centeredSpectralSquares lam) 2
      (stdGaussian (EuclideanSpace ℝ ι)) := by
  unfold centeredSpectralSquares
  apply memLp_finsetSum
  intro i hi
  have hbase : MemLp (fun z : ℝ ↦ z ^ 2 - 1) 2 (gaussianReal 0 1) := by
    simpa [gaussianHermite_two] using
      standardGaussian_polynomial_memLp_two (gaussianHermite 2)
  exact (hbase.comp_measurePreserving
    (stdGaussian_coordinate_measurePreserving i)).const_mul (lam i)

private theorem spectralPrefix_eq_prefixCoordinates
    {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian)
    (K : ℕ) (hKd : K ≤ d) (x : EuclideanSpace ℝ (Fin d)) :
    centeredMatrixQuadraticSpectralPrefix hA K x =
      centeredSpectralSquares
        (fun j : Fin K ↦ hA.eigenvalues (Fin.castLE hKd j))
        (euclideanFinPrefix K d hKd (hermitianEigenCoordinates hA x)) := by
  unfold centeredMatrixQuadraticSpectralPrefix centeredSpectralSquares
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

/-- The finite spectral prefix has the law of a `K`-term independent
Gaussian-chaos sum with the corresponding eigenvalues. -/
theorem centeredMatrixQuadraticSpectralPrefix_identDistrib
    {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian)
    (K : ℕ) (hKd : K ≤ d) :
    IdentDistrib (centeredMatrixQuadraticSpectralPrefix hA K)
      (centeredSpectralSquares
        (fun j : Fin K ↦ hA.eigenvalues (Fin.castLE hKd j)))
      (stdGaussian (EuclideanSpace ℝ (Fin d)))
      (stdGaussian (EuclideanSpace ℝ (Fin K))) := by
  let T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin K) :=
    fun x ↦ euclideanFinPrefix K d hKd (hermitianEigenCoordinates hA x)
  have hT : MeasurePreserving T
      (stdGaussian (EuclideanSpace ℝ (Fin d)))
      (stdGaussian (EuclideanSpace ℝ (Fin K))) := by
    exact (euclideanFinPrefix_measurePreserving K d hKd).comp
      (hermitianEigenCoordinates_measurePreserving hA)
  let F := centeredSpectralSquares
    (fun j : Fin K ↦ hA.eigenvalues (Fin.castLE hKd j))
  have hF : Measurable F := by
    dsimp only [F]
    unfold centeredSpectralSquares
    exact Finset.measurable_sum _ fun j _ => by fun_prop
  have hpoint : centeredMatrixQuadraticSpectralPrefix hA K =
      F ∘ T := by
    funext x
    exact spectralPrefix_eq_prefixCoordinates hA K hKd x
  refine ⟨?_, hF.aemeasurable, ?_⟩
  · rw [hpoint]
    exact hF.aemeasurable.comp_measurable hT.measurable
  · rw [hpoint, ← Measure.map_map hF hT.measurable, hT.map_eq]

/-- Exact `L²` spectral-tail identity for a finite symmetric Gaussian
quadratic form. -/
theorem centeredMatrixQuadratic_sub_spectralPrefix_L2
    {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian) (K : ℕ) :
    MemLp (fun x ↦ centeredMatrixQuadratic A x -
      centeredMatrixQuadraticSpectralPrefix hA K x) 2
      (stdGaussian (EuclideanSpace ℝ (Fin d))) ∧
    (∫ x, (centeredMatrixQuadratic A x -
      centeredMatrixQuadraticSpectralPrefix hA K x) ^ 2
        ∂stdGaussian (EuclideanSpace ℝ (Fin d))) =
      2 * ∑ i : Fin d, if K ≤ i.val then hA.eigenvalues i ^ 2 else 0 := by
  let tail : Fin d → ℝ := fun i ↦
    if K ≤ i.val then hA.eigenvalues i else 0
  let F := centeredSpectralSquares tail
  have hpoint : (fun x ↦ centeredMatrixQuadratic A x -
      centeredMatrixQuadraticSpectralPrefix hA K x) =
      F ∘ (hermitianEigenCoordinates hA) := by
    funext x
    rw [centeredMatrixQuadratic_eq_centeredSpectralSquares_eigenCoordinates hA x]
    unfold centeredMatrixQuadraticSpectralPrefix centeredSpectralSquares F tail
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hiK : i.val < K
    · have hKi : ¬K ≤ i.val := not_le.mpr hiK
      simp [hiK, hKi]
    · have hKi : K ≤ i.val := not_lt.mp hiK
      simp [hiK, hKi]
  have hT := hermitianEigenCoordinates_measurePreserving hA
  have hF2 : MemLp F 2 (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    centeredSpectralSquares_memLp_two tail
  have hFm : Measurable F := by
    dsimp only [F]
    unfold centeredSpectralSquares
    exact Finset.measurable_sum _ fun i _ => by fun_prop
  have hsource : Measurable (fun x ↦ centeredMatrixQuadratic A x -
      centeredMatrixQuadraticSpectralPrefix hA K x) := by
    rw [hpoint]
    have hcoord : Measurable (fun x : EuclideanSpace ℝ (Fin d) ↦
        hermitianEigenCoordinates hA x) :=
      (hermitianEigenCoordinates hA).continuous.measurable
    exact hFm.comp hcoord
  have hident : IdentDistrib
      (fun x ↦ centeredMatrixQuadratic A x -
        centeredMatrixQuadraticSpectralPrefix hA K x) F
      (stdGaussian (EuclideanSpace ℝ (Fin d)))
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    refine ⟨hsource.aemeasurable, hF2.aemeasurable, ?_⟩
    · rw [hpoint, ← Measure.map_map hFm hT.measurable,
        hT.map_eq]
  constructor
  · exact hident.symm.memLp_snd hF2
  · calc
      (∫ x, (centeredMatrixQuadratic A x -
          centeredMatrixQuadraticSpectralPrefix hA K x) ^ 2
            ∂stdGaussian (EuclideanSpace ℝ (Fin d))) =
          ∫ x, (F x) ^ 2 ∂stdGaussian (EuclideanSpace ℝ (Fin d)) :=
        hident.sq.integral_eq
      _ = 2 * ∑ i : Fin d, tail i ^ 2 :=
        centeredSpectralSquares_secondMoment tail
      _ = 2 * ∑ i : Fin d,
          if K ≤ i.val then hA.eigenvalues i ^ 2 else 0 := by
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        dsimp only [tail]
        split_ifs <;> simp_all

end Hurst
