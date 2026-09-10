import Hurst.FanoLowerBound
import Hurst.GaussianKLBound

/-! Reference-law Fano bounds connected to actual Gaussian covariance families.
The remaining paper-specific work is to construct the separated Hurst family and
prove its uniform spectral floor and covariance-entry error bounds. -/
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Matrix
open scoped ENNReal
namespace Hurst

theorem mutualInformation_le_reference {X : Type*} [MeasurableSpace X]
    {M : ℕ} [NeZero M] (Q : Kernel (Fin M) X) [IsMarkovKernel Q]
    (R : Measure X) [IsProbabilityMeasure R] :
    mutualInformation Q ≤ (M : ℝ≥0∞)⁻¹ * ∑ j, klDiv (Q j) R := by
  unfold mutualInformation
  rw [mixture_eq_inv_smul_sum]
  exact mul_le_mul_right (sum_klDiv_mixture_le (fun j => Q j) R) _

theorem mutualInformation_le_of_reference_bound {X : Type*} [MeasurableSpace X]
    {M : ℕ} [NeZero M] (Q : Kernel (Fin M) X) [IsMarkovKernel Q]
    (R : Measure X) [IsProbabilityMeasure R] (K : ℝ≥0∞)
    (hK : ∀ j, klDiv (Q j) R ≤ K) : mutualInformation Q ≤ K := by
  calc
    mutualInformation Q ≤ (M : ℝ≥0∞)⁻¹ * ∑ j, klDiv (Q j) R :=
      mutualInformation_le_reference Q R
    _ ≤ (M : ℝ≥0∞)⁻¹ * ∑ _j : Fin M, K :=
      mul_le_mul_right (Finset.sum_le_sum (fun j _ => hK j)) _
    _ = K := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ← mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast (NeZero.ne M))
          (ENNReal.natCast_ne_top M), one_mul]

def gaussianCovarianceFamily {M d : ℕ} (A : Fin M → Matrix (Fin d) (Fin d) ℝ) :
    Kernel (Fin M) (EuclideanSpace ℝ (Fin d)) where
  toFun j := multivariateGaussian 0 (A j)
  measurable' := measurable_of_countable _

instance gaussianCovarianceFamily_isMarkov {M d : ℕ}
    (A : Fin M → Matrix (Fin d) (Fin d) ℝ) : IsMarkovKernel (gaussianCovarianceFamily A) where
  isProbabilityMeasure j := by
    change IsProbabilityMeasure (multivariateGaussian 0 (A j))
    infer_instance

/-- An actual Gaussian testing lower bound from a spectral floor and matrix-entry errors.
No KL, mutual-information, or testing-error bound is assumed. -/
theorem gaussian_fano_frobenius {M d : ℕ} [NeZero M]
    (A : Fin M → Matrix (Fin d) (Fin d) ℝ) (hA : ∀ j, (A j).PosDef)
    (hfloor : ∀ j i, (1 / 4 : ℝ) ≤ (hA j).1.eigenvalues i)
    (R : ℝ) (hR : ∀ j, (∑ i, ∑ k, ((A j - 1) i k) ^ 2) ≤ R) (hM : 2 ≤ M) :
    1 - (ENNReal.ofReal (2 * R) + ENNReal.ofReal (Real.log 2)) /
      ENNReal.ofReal (Real.log (M : ℝ)) ≤ multiwayTestingError (gaussianCovarianceFamily A) := by
  have hI : mutualInformation (gaussianCovarianceFamily A) ≤ ENNReal.ofReal (2 * R) := by
    apply mutualInformation_le_of_reference_bound _ (multivariateGaussian 0
      (1 : Matrix (Fin d) (Fin d) ℝ))
    intro j
    exact (klDiv_multivariateGaussian_unit_frobenius_quarter (A j) (hA j) (hfloor j)).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hR j) (by norm_num)))
  calc
    _ ≤ 1 - (mutualInformation (gaussianCovarianceFamily A) + ENNReal.ofReal (Real.log 2)) /
        ENNReal.ofReal (Real.log (M : ℝ)) := by gcongr
    _ ≤ _ := fano_inequality _ hM

/-- Finite-family minimax lower bound with actual correlated Gaussian observations.
The target separation is geometric and must still be supplied by the Hurst packing. -/
theorem gaussian_minimax_frobenius {Ω : Type*} [MeasurableSpace Ω]
    [PseudoEMetricSpace Ω] [OpensMeasurableSpace Ω] {M d : ℕ} [NeZero M]
    (A : Fin M → Matrix (Fin d) (Fin d) ℝ) (hA : ∀ j, (A j).PosDef)
    (hfloor : ∀ j i, (1 / 4 : ℝ) ≤ (hA j).1.eigenvalues i)
    (R : ℝ) (hR : ∀ j, (∑ i, ∑ k, ((A j - 1) i k) ^ 2) ≤ R) (hM : 2 ≤ M)
    (Φ : ℝ≥0∞ → ℝ≥0∞) (hΦ : Monotone Φ) (g : Fin M → Ω) (δ : ℝ≥0∞)
    (hsep : IsSeparatedFamily g id δ) :
    Φ δ * (1 - (ENNReal.ofReal (2 * R) + ENNReal.ofReal (Real.log 2)) /
      ENNReal.ofReal (Real.log (M : ℝ))) ≤ minimaxRiskDist Φ g (gaussianCovarianceFamily A) := by
  calc
    _ ≤ Φ δ * multiwayTestingError (gaussianCovarianceFamily A) :=
      mul_le_mul_right (gaussian_fano_frobenius A hA hfloor R hR hM) _
    _ ≤ _ := by
      simpa only [Kernel.comap_id] using
        minimax_ge_testing_error Φ g (gaussianCovarianceFamily A) id measurable_id δ hΦ hsep

/-- The same Gaussian packing lower bound applies to a full parameter class containing
the candidates. The law-identification premise is the remaining mBm model connection. -/
theorem gaussian_minimax_subfamily_frobenius {Θ Ω : Type*}
    [MeasurableSpace Θ] [MeasurableSpace Ω] [PseudoEMetricSpace Ω] [OpensMeasurableSpace Ω]
    {M d : ℕ} [NeZero M]
    (P : Kernel Θ (EuclideanSpace ℝ (Fin d))) [IsMarkovKernel P]
    (θfam : Fin M → Θ) (hθ : Measurable θfam)
    (A : Fin M → Matrix (Fin d) (Fin d) ℝ) (hA : ∀ j, (A j).PosDef)
    (hlaw : ∀ j, P (θfam j) = multivariateGaussian 0 (A j))
    (hfloor : ∀ j i, (1 / 4 : ℝ) ≤ (hA j).1.eigenvalues i)
    (R : ℝ) (hR : ∀ j, (∑ i, ∑ k, ((A j - 1) i k) ^ 2) ≤ R) (hM : 2 ≤ M)
    (Φ : ℝ≥0∞ → ℝ≥0∞) (hΦ : Monotone Φ) (g : Θ → Ω) (δ : ℝ≥0∞)
    (hsep : IsSeparatedFamily g θfam δ) :
    Φ δ * (1 - (ENNReal.ofReal (2 * R) + ENNReal.ofReal (Real.log 2)) /
      ENNReal.ofReal (Real.log (M : ℝ))) ≤ minimaxRiskDist Φ g P := by
  have hQ : P.comap θfam hθ = gaussianCovarianceFamily A := by
    apply DFunLike.ext
    intro j
    exact hlaw j
  have hgeom := minimax_ge_testing_error Φ g P θfam hθ δ hΦ hsep
  rw [hQ] at hgeom
  exact (mul_le_mul_right (gaussian_fano_frobenius A hA hfloor R hR hM) (Φ δ)).trans hgeom

end Hurst
