import Hurst.LocalPolynomial
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! A direct finite-design replacement for the quadrature argument in 8.4.
The moment conditions follow from the actual inverse Gram matrix. Uniform
stability and Taylor residual bounds remain explicit analytic hypotheses. -/
noncomputable section
open scoped BigOperators
namespace Hurst
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

def designGram (K : ι → ℝ) (A : ι → κ → ℝ) : Matrix κ κ ℝ :=
  fun k l => ∑ i, K i*A i k*A i l

def gramWeights (z : κ) (K : ι → ℝ) (A : ι → κ → ℝ) : ι → ℝ :=
  fun i => K i*∑ l, (designGram K A)⁻¹ z l*A i l

theorem gramWeights_moments (z : κ) (K : ι → ℝ) (A : ι → κ → ℝ)
    (hdet : IsUnit (designGram K A).det) (k : κ) :
    (∑ i, gramWeights z K A i*A i k) = if k=z then 1 else 0 := by
  have he : (∑ i, gramWeights z K A i*A i k) =
      ((designGram K A)⁻¹ * designGram K A) z k := by
    simp only [gramWeights, Matrix.mul_apply, designGram]
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, Matrix.nonsing_inv_mul _ hdet]
  simp [Matrix.one_apply, eq_comm]

theorem gramWeights_reproduce (z : κ) (K : ι → ℝ) (A : ι → κ → ℝ)
    (β : κ → ℝ) (hdet : IsUnit (designGram K A).det) :
    smooth (gramWeights z K A) (fun i => ∑ k, β k*A i k) = β z :=
  polynomial_reproduction z _ A β (gramWeights_moments z K A hdet)

theorem direct_local_bias (z : κ) (K : ι → ℝ) (A : ι → κ → ℝ)
    (β : κ → ℝ) (F : ι → ℝ) (B : ℝ)
    (hdet : IsUnit (designGram K A).det)
    (hrem : ∀ i, |F i - ∑ k, β k*A i k| ≤ B) :
    |smooth (gramWeights z K A) F - β z| ≤ (∑ i, |gramWeights z K A i|)*B := by
  let r := fun i => F i - ∑ k, β k*A i k
  have he : F = fun i => (∑ k, β k*A i k)+r i := by funext i; dsimp [r]; ring
  rw [he, smooth_add, gramWeights_reproduce z K A β hdet, add_sub_cancel_left]
  exact smooth_residual_bound _ r B hrem

/-- Taylor control is only needed at observations with nonzero kernel
weight; distant observations need not satisfy a bandwidth-size remainder. -/
theorem direct_local_bias_on_support (z : κ) (K : ι → ℝ) (A : ι → κ → ℝ)
    (β : κ → ℝ) (F : ι → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hdet : IsUnit (designGram K A).det)
    (hrem : ∀ i, K i ≠ 0 → |F i - ∑ k, β k*A i k| ≤ B) :
    |smooth (gramWeights z K A) F - β z| ≤ (∑ i, |gramWeights z K A i|)*B := by
  classical
  let F' := fun i => if K i = 0 then ∑ k, β k*A i k else F i
  have he : smooth (gramWeights z K A) F = smooth (gramWeights z K A) F' := by
    unfold smooth
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : K i = 0
    · simp [gramWeights, hi]
    · simp [F', hi]
  rw [he]
  apply direct_local_bias z K A β F' B hdet
  intro i
  by_cases hi : K i = 0
  · simpa [F', hi] using hB
  · simpa [F', hi] using hrem i hi

/-- No numerical integration error enters this bound. -/
theorem direct_local_bias_stable (z : κ) (K : ι → ℝ) (A : ι → κ → ℝ)
    (β : κ → ℝ) (F : ι → ℝ) (B C : ℝ) (hB : 0 ≤ B)
    (hdet : IsUnit (designGram K A).det)
    (hrem : ∀ i, |F i - ∑ k, β k*A i k| ≤ B)
    (hstable : (∑ i, |gramWeights z K A i|) ≤ C) :
    |smooth (gramWeights z K A) F - β z| ≤ C*B :=
  (direct_local_bias z K A β F B hdet hrem).trans (mul_le_mul_of_nonneg_right hstable hB)

/-- Smooth H and the log-variance correction separately. This is the finite
sample deterministic bias step of 3.2, with no Riemann-sum remainder. -/
theorem log_bias_from_taylor (z : κ) (K : ι → ℝ) (A : ι → κ → ℝ)
    (β γ : κ → ℝ) (H ell err : ι → ℝ) (L BH BE rho C : ℝ)
    (hL : 0 ≤ L) (hBH : 0 ≤ BH) (hBE : 0 ≤ BE) (hrho : 0 ≤ rho)
    (hdet : IsUnit (designGram K A).det)
    (hH : ∀ i, |H i-∑ k, β k*A i k| ≤ BH)
    (hell : ∀ i, |ell i-∑ k, γ k*A i k| ≤ BE)
    (herr : ∀ i, |err i| ≤ rho)
    (hstable : (∑ i, |gramWeights z K A i|) ≤ C) :
    |smooth (gramWeights z K A) (fun i => -2*L*H i+ell i+err i) -
      (-2*L*β z+γ z)| ≤ C*(2*L*BH+BE+rho) := by
  let w := gramWeights z K A
  have h1 := direct_local_bias_stable z K A β H BH C hBH hdet hH hstable
  have h2 := direct_local_bias_stable z K A γ ell BE C hBE hdet hell hstable
  have h3 : |smooth w err| ≤ C*rho :=
    (smooth_residual_bound w err rho herr).trans (mul_le_mul_of_nonneg_right hstable hrho)
  rw [smooth_add, smooth_add, smooth_scale]
  have he : -2*L*smooth w H+smooth w ell+smooth w err-(-2*L*β z+γ z) =
      (-2*L)*(smooth w H-β z)+(smooth w ell-γ z)+smooth w err := by ring
  change |-2*L*smooth w H+smooth w ell+smooth w err-(-2*L*β z+γ z)| ≤ _
  rw [he]
  calc
    _ ≤ |(-2*L)*(smooth w H-β z)|+|smooth w ell-γ z|+|smooth w err| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = 2*L*|smooth w H-β z|+|smooth w ell-γ z|+|smooth w err| := by
      rw [abs_mul, show |(-2:ℝ)*L| = 2*L by rw [abs_mul, abs_of_nonneg hL]; norm_num]
    _ ≤ 2*L*(C*BH)+C*BE+C*rho := by gcongr
    _ = _ := by ring

/-- An explicit sufficient bound for stability of the signed local weights. -/
theorem gramWeights_l1_bound (z : κ) (K : ι → ℝ) (A : ι → κ → ℝ)
    (Q B M : ℝ) (hQ : 0 ≤ Q) (hB : 0 ≤ B)
    (hinv : ∀ l, |(designGram K A)⁻¹ z l| ≤ Q)
    (hA : ∀ i l, |A i l| ≤ B) (hK : (∑ i, |K i|) ≤ M) :
    (∑ i, |gramWeights z K A i|) ≤ M*((Fintype.card κ:ℝ)*Q*B) := by
  have hrow : ∀ i, |∑ l, (designGram K A)⁻¹ z l*A i l| ≤ (Fintype.card κ:ℝ)*Q*B := by
    intro i
    calc
      _ ≤ ∑ l, |(designGram K A)⁻¹ z l*A i l| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _l : κ, Q*B := by
        apply Finset.sum_le_sum
        intro l _
        rw [abs_mul]
        exact mul_le_mul (hinv l) (hA i l) (abs_nonneg _) hQ
      _ = _ := by simp [mul_assoc]
  calc
    _ ≤ ∑ i, |K i| *((Fintype.card κ:ℝ)*Q*B) := by
      apply Finset.sum_le_sum
      intro i _
      rw [gramWeights, abs_mul]
      exact mul_le_mul_of_nonneg_left (hrow i) (abs_nonneg _)
    _ = (∑ i, |K i|)*((Fintype.card κ:ℝ)*Q*B) := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hK (by positivity)

end Hurst
