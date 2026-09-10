import Hurst.LocalBias
import Hurst.PointwiseTaylor

noncomputable section
open Set Filter
open scoped Topology
namespace Hurst

theorem localPolynomialWeights_taylor_reproduce (r n q : ℕ) (δ t : ℝ) (f : ℝ → ℝ)
    (hδ : δ≠0) (hdet : IsUnit (localDesignGram r n q δ t).det) :
    smooth (localPolynomialWeights r n q δ t) (fun i => taylorJet r f t (grid n i.val))=f t := by
  simp only [scaled_taylorJet r f t _ δ hδ]
  have he := polynomial_reproduction (0 : Fin (r+1)) (localPolynomialWeights r n q δ t)
    (fun i k => ((grid n i.val-t)/δ)^k.val)
    (fun k => iteratedDeriv k.val f t*δ^k.val/(k.val.factorial:ℝ))
    (localPolynomialWeights_moments r n q δ t hdet)
  simpa using he

theorem localPolynomial_bias_leading_identity (r n q : ℕ) (δ t : ℝ) (f : ℝ → ℝ)
    (hδ : δ≠0) (hdet : IsUnit (localDesignGram r n q δ t).det) :
    (smooth (localPolynomialWeights r n q δ t) (fun i => f (grid n i.val))-f t)/δ^(r+1)-
      (iteratedDeriv (r+1) f t/((r+1).factorial:ℝ))*
        (∑ i,localPolynomialWeights r n q δ t i*((grid n i.val-t)/δ)^(r+1)) =
      smooth (localPolynomialWeights r n q δ t)
        (fun i => f (grid n i.val)-taylorJet (r+1) f t (grid n i.val))/δ^(r+1) := by
  have hrepro := localPolynomialWeights_taylor_reproduce r n q δ t f hδ hdet
  have hid (i : Fin (n-q)) :
      f (grid n i.val)=taylorJet r f t (grid n i.val)+
        (iteratedDeriv (r+1) f t/((r+1).factorial:ℝ))*δ^(r+1)*((grid n i.val-t)/δ)^(r+1)+
        (f (grid n i.val)-taylorJet (r+1) f t (grid n i.val)) := by
    rw [taylorJet_succ,div_pow]
    field_simp
    <;> ring
  have he : smooth (localPolynomialWeights r n q δ t) (fun i => f (grid n i.val)) =
      f t+(iteratedDeriv (r+1) f t/((r+1).factorial:ℝ))*δ^(r+1)*
        (∑ i,localPolynomialWeights r n q δ t i*((grid n i.val-t)/δ)^(r+1))+
      smooth (localPolynomialWeights r n q δ t)
        (fun i => f (grid n i.val)-taylorJet (r+1) f t (grid n i.val)) := by
    conv_lhs => arg 2; ext i; rw [hid i]
    rw [smooth_add,smooth_add,smooth_scale,hrepro]
    rfl
  rw [he]
  field_simp
  <;> ring

theorem localPolynomial_remainder_bound_on_support (r n q k : ℕ) (δ t η ε : ℝ) (f : ℝ → ℝ)
    (hδ : 0<δ) (hδη : δ<η) (hε : 0≤ε)
    (hrem : ∀ y : ℝ,|y-t|<η → |f y-taylorJet k f t y|≤ε*|y-t|^k) :
    |smooth (localPolynomialWeights r n q δ t) (fun i => f (grid n i.val)-taylorJet k f t (grid n i.val))| ≤
      (∑ i,|localPolynomialWeights r n q δ t i|)*(ε*δ^k) := by
  unfold smooth
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : 1≤|(grid n i.val-t)/δ|
  · simp only [localPolynomialWeights_zero r n q δ t i hi,zero_mul,abs_zero,le_refl]
  · have hz : |grid n i.val-t|<δ := by
      have hh := lt_of_not_ge hi
      rw [abs_div,abs_of_pos hδ] at hh
      exact (div_lt_one hδ).mp hh
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    exact (hrem _ (hz.trans hδη)).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg _) hz.le k) hε)

end Hurst
