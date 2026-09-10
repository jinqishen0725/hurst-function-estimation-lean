import Hurst.LocalDesign
import Hurst.LatticeCount

noncomputable section
open Set
open scoped BigOperators
namespace Hurst

def localPolynomialWeights (r n q : ℕ) (b t : ℝ) : Fin (n - q) → ℝ :=
  gramWeights (0 : Fin (r + 1))
    (fun i => ((n : ℝ) * b)⁻¹ * localKernel ((grid n i.val - t) / b))
    (fun i k => ((grid n i.val - t) / b) ^ k.val)

theorem localPolynomialWeights_formula (r n q : ℕ) (b t : ℝ) (i : Fin (n - q)) :
    localPolynomialWeights r n q b t i =
      ((n : ℝ) * b)⁻¹ * localKernel ((grid n i.val - t) / b) *
        ∑ k : Fin (r + 1), (localDesignGram r n q b t)⁻¹ 0 k * ((grid n i.val - t) / b) ^ k.val := rfl

theorem localPolynomialWeights_zero (r n q : ℕ) (b t : ℝ) (i : Fin (n - q))
    (hi : 1 ≤ |(grid n i.val - t) / b|) : localPolynomialWeights r n q b t i = 0 := by
  rw [localPolynomialWeights_formula, localKernel_zero _ hi, mul_zero, zero_mul]

theorem localPolynomialWeights_moments (r n q : ℕ) (b t : ℝ)
    (hdet : IsUnit (localDesignGram r n q b t).det) (k : Fin (r + 1)) :
    (∑ i, localPolynomialWeights r n q b t i * ((grid n i.val - t) / b) ^ k.val) =
      if k = 0 then 1 else 0 := gramWeights_moments _ _ _ hdet k

theorem localPolynomialWeights_bound_from_inverse (r n q : ℕ) (b t C B : ℝ) (hn : 0 < n) (hb : 0 < b)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hkernel : ∀ x, localKernel x ≤ B)
    (hinv : ∀ i j, |(localDesignGram r n q b t)⁻¹ i j| ≤ C) :
    ∀ i, |localPolynomialWeights r n q b t i| ≤ B * (r + 1) * C / ((n : ℝ) * b) := by
  intro i
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  by_cases hz : 1 ≤ |(grid n i.val - t) / b|
  · rw [localPolynomialWeights_zero r n q b t i hz, abs_zero]
    positivity
  have hz1 : |(grid n i.val - t) / b| ≤ 1 := (lt_of_not_ge hz).le
  have hsum : |∑ k : Fin (r + 1), (localDesignGram r n q b t)⁻¹ 0 k * ((grid n i.val - t) / b) ^ k.val| ≤
      (r + 1) * C := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _k : Fin (r + 1), C := by
        apply Finset.sum_le_sum
        intro k hk
        rw [abs_mul, abs_pow]
        have hp : |(grid n i.val - t) / b| ^ k.val ≤ 1 := pow_le_one₀ (abs_nonneg _) hz1
        exact (mul_le_mul (hinv 0 k) hp (by positivity) hC).trans_eq (mul_one C)
      _ = (r + 1) * C := by simp
  rw [localPolynomialWeights_formula, abs_mul, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ ((n : ℝ) * b)⁻¹), abs_of_nonneg (localKernel_nonneg _)]
  calc
    _ ≤ (((n : ℝ) * b)⁻¹ * B) * ((r + 1) * C) := by gcongr; exact hkernel _
    _ = _ := by ring

/-- Actual local polynomial weights are uniformly stable on the whole closed interval. -/
theorem localPolynomialWeights_uniform_stability (r q : ℕ) :
    ∃ N₀ > 0, ∃ C > 0, ∀ n : ℕ, 0 < n → q ≤ n → ∀ b t : ℝ,
      0 < b → b ≤ 1 / 2 → t ∈ Icc (0 : ℝ) 1 → N₀ ≤ (n : ℝ) * b →
      IsUnit (localDesignGram r n q b t).det ∧
      (∀ i, |localPolynomialWeights r n q b t i| ≤ C / ((n : ℝ) * b)) ∧
      (∑ i, |localPolynomialWeights r n q b t i|) ≤ C ∧
      ∀ k : Fin (r + 1),
        (∑ i, localPolynomialWeights r n q b t i * ((grid n i.val - t) / b) ^ k.val) =
          if k = 0 then 1 else 0 := by
  classical
  obtain ⟨N₀, hN₀, D, hD, hinv⟩ := localDesignGram_uniform_inverse r q
  obtain ⟨B, hB, hkernel0⟩ := kernelMomentFunction_bounded 0
  have hkernel : ∀ x, localKernel x ≤ B := by
    intro x
    simpa only [kernelMomentFunction, pow_zero, mul_one, abs_of_nonneg (localKernel_nonneg x)] using hkernel0 x
  let A := B * (r + 1) * D
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨max N₀ 1, lt_of_lt_of_le hN₀ (le_max_left _ _), 1 + 3 * A, by positivity, ?_⟩
  intro n hn hq b t hb hbhalf ht hN
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hNb : (1 : ℝ) ≤ n * b := (le_max_right _ _).trans hN
  obtain ⟨hdet, hi⟩ := hinv n hn hq b t hb hbhalf ht ((le_max_left _ _).trans hN)
  have hbound := localPolynomialWeights_bound_from_inverse r n q b t D B hn hb hD hB hkernel hi
  refine ⟨hdet, ?_, ?_, localPolynomialWeights_moments r n q b t hdet⟩
  · intro i
    exact (hbound i).trans (div_le_div_of_nonneg_right (by dsimp [A]; nlinarith) (by positivity))
  · let S : Finset (Fin (n - q)) := Finset.univ.filter (fun i => |(grid n i.val - t) / b| < 1)
    have hScard : (S.card : ℝ) ≤ 3 * ((n : ℝ) * b) := by
      have h := midpoint_active_card_bound n (n - q) hn b t hb S (fun i hiS => (Finset.mem_filter.mp hiS).2)
      linarith
    have he : (∑ i, |localPolynomialWeights r n q b t i|) = ∑ i ∈ S, |localPolynomialWeights r n q b t i| := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i hi his
      have hz : 1 ≤ |(grid n i.val - t) / b| := by
        have hnots : ¬ |(grid n i.val - t) / b| < 1 := by simpa [S] using his
        exact le_of_not_gt hnots
      simp only [localPolynomialWeights_zero r n q b t i hz, abs_zero]
    rw [he]
    calc
      _ ≤ ∑ _i ∈ S, A / ((n : ℝ) * b) := Finset.sum_le_sum (fun i hiS => hbound i)
      _ = (S.card : ℝ) * (A / ((n : ℝ) * b)) := by simp
      _ ≤ (3 * ((n : ℝ) * b)) * (A / ((n : ℝ) * b)) := mul_le_mul_of_nonneg_right hScard (by positivity)
      _ = 3 * A := by field_simp
      _ ≤ 1 + 3 * A := by linarith

end Hurst
