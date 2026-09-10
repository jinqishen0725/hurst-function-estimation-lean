import Hurst.SecondIncrement
import Hurst.HolderSecond

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace ENNReal
namespace Hurst

/-- Uniform second-difference freezing error on the original Holder class, including p=2. -/
theorem hurstHolder_second_increment_remainder (p a b M : ℝ)
    (hp : 2 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M) :
    ∃ C ≥ 0, ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) →
      ∀ t l : ℝ, 0 < l → t ∈ Ioo (0 : ℝ) 1 → t + 2 * l ∈ Ioo (0 : ℝ) 1 →
      ∀ h0 h1 h2 : Ioo (0 : ℝ) 1, (h0 : ℝ) = f t → (h1 : ℝ) = f (t + l) → (h2 : ℝ) = f (t + 2 * l) →
      ‖l ^ (-(h0 : ℝ)) • (varyingSecondIncrement h0 h1 h2 t l - frozenSecondIncrement h0 t l)‖ ≤
        C * l * (1 + |Real.log l|) := by
  obtain ⟨B, hB, hLip⟩ := hurstHolder_uniform_lower_derivative_lipschitz p (by linarith)
  obtain ⟨D, hD, hSecond⟩ := hurstHolder_second_difference_bound p hp
  obtain ⟨C, hC, hc⟩ := varyingSecondIncrement_uniform_remainder a b (B * (1 + M)) (D * (1 + M))
    ha hb hab (by positivity) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro f hf hF t l hl ht ht2 h0 h1 h2 he0 he1 he2
  have ht1 : t + l ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht2.2]⟩
  have hp0 : 0 < Nat.floor p := by
    have he := hurstHolder_floor_pos p (by linarith)
    omega
  have hd1 := hLip M hM f hf 0 hp0 t ht (t + l) ht1
  have hd2 := hLip M hM f hf 0 hp0 t ht (t + 2 * l) ht2
  simp only [iteratedDeriv_zero, add_sub_cancel_left, abs_of_pos hl] at hd1
  simp only [iteratedDeriv_zero, add_sub_cancel_left, abs_of_pos (by positivity : 0 < 2 * l)] at hd2
  have hdd := hSecond M hM f hf t l hl.le ht ht2
  apply hc h0 h1 h2 (he0 ▸ hF ht) (he1 ▸ hF ht1) (he2 ▸ hF ht2) t l hl (by linarith [ht.1, ht2.2])
    (by rw [abs_of_pos ht1.1]; exact ht1.2.le) (by rw [abs_of_pos ht2.1]; exact ht2.2.le)
  · simpa only [he0, he1] using hd1
  · simpa only [he0, he2, mul_assoc, mul_left_comm, mul_comm] using hd2
  · simpa only [he0, he1, he2] using hdd

end Hurst
