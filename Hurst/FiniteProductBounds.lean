import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

noncomputable section
open Set
namespace Hurst

theorem abs_finite_product_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hf : ∀ i ∈ s, |f i| ≤ B) : |∏ i ∈ s, f i| ≤ B ^ s.card := by
  rw [Finset.abs_prod]
  have h := Finset.prod_le_prod (fun i hi => abs_nonneg (f i)) hf
  simpa only [Finset.prod_const] using h

/-- Uniform product difference bound, used for the finite Faà di Bruno formula. -/
theorem finite_product_difference_bound {ι : Type*} (s : Finset ι) (f g : ι → ℝ) (B D ε : ℝ)
    (hB : 1 ≤ B) (hD : 0 ≤ D) (hε : 0 ≤ ε)
    (hf : ∀ i ∈ s, |f i| ≤ B) (hg : ∀ i ∈ s, |g i| ≤ B)
    (hd : ∀ i ∈ s, |f i - g i| ≤ D * ε) :
    |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| ≤ (s.card : ℝ) * D * B ^ s.card * ε := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hB0 : 0 ≤ B := by linarith
    have htail := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (fun i hi => hg i (Finset.mem_insert_of_mem hi)) (fun i hi => hd i (Finset.mem_insert_of_mem hi))
    have hprod := abs_finite_product_le s g B hB0 (fun i hi => hg i (Finset.mem_insert_of_mem hi))
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha, Nat.cast_add, Nat.cast_one, pow_succ]
    have he : f a * (∏ i ∈ s, f i) - g a * (∏ i ∈ s, g i) =
        f a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i) + (f a - g a) * ∏ i ∈ s, g i := by ring
    rw [he]
    have h1 := mul_le_mul (hf a (Finset.mem_insert_self a s)) htail (abs_nonneg _) hB0
    have h2 := mul_le_mul (hd a (Finset.mem_insert_self a s)) hprod (abs_nonneg _) (mul_nonneg hD hε)
    have h3 := mul_le_mul_of_nonneg_left hB (show 0 ≤ D * B ^ s.card * ε by positivity)
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul]
    nlinarith

end Hurst
