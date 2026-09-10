import Hurst.LocalWeights

noncomputable section
open Set
namespace Hurst

theorem weight_square_sum_le {ι : Type*} [Fintype ι] (w : ι → ℝ) (A B : ℝ)
    (hA : 0≤A) (hmax : ∀ i,|w i|≤A) (hl1 : ∑ i,|w i|≤B) : (∑ i,w i^2)≤A*B := by
  calc
    _ ≤ ∑ i,A*|w i| := by
      apply Finset.sum_le_sum
      intro i _
      calc
        w i^2 = |w i| * |w i| := by rw [← pow_two,sq_abs]
        _ ≤ A*|w i| := mul_le_mul_of_nonneg_right (hmax i) (abs_nonneg _)
    _ = A*∑ i,|w i| := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hl1 hA

theorem localPolynomialWeights_energy (r q : ℕ) :
    ∃ N₀>0, ∃ D>0, ∀ n : ℕ, 0<n → q≤n → ∀ δ t : ℝ,
      0<δ → δ≤1/2 → t∈Icc (0:ℝ) 1 → N₀≤(n:ℝ)*δ →
      (n:ℝ)*δ*(∑ i,localPolynomialWeights r n q δ t i^2)≤D := by
  obtain ⟨N₀,hN₀,C,hC,hw⟩ := localPolynomialWeights_uniform_stability r q
  refine ⟨N₀,hN₀,C^2,by positivity,?_⟩
  intro n hn hqn δ t hδ hδ2 ht hN
  obtain ⟨hdet,hmax,hl1,hmom⟩ := hw n hn hqn δ t hδ hδ2 ht hN
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hnd : 0<(n:ℝ)*δ := mul_pos hnR hδ
  have he := mul_le_mul_of_nonneg_left
    (weight_square_sum_le _ (C/((n:ℝ)*δ)) C (by positivity) hmax hl1) hnd.le
  have hid : (n:ℝ)*δ*(C/((n:ℝ)*δ)*C)=C^2 := by field_simp
  exact he.trans_eq hid

end Hurst
