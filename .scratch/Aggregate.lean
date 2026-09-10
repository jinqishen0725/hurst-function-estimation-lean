import Hurst.ShiftedWeightEnergy

noncomputable section
open Filter
open scoped Topology
namespace Hurst

theorem finZeroExtendedShift_boundary_card {m : ℕ} (k : ℕ) :
    (Finset.univ.filter (fun i : Fin m => ¬ i.val + k < m)).card ≤ k := by
  classical
  by_cases hk : k = 0
  · subst k
    simp
  let f : Fin m → Fin k := fun i =>
    if h : ¬ i.val + k < m then
      ⟨i.val + k - m, by omega⟩
    else ⟨0, Nat.pos_of_ne_zero hk⟩
  have hc : (Finset.univ.filter (fun i : Fin m => ¬ i.val + k < m)).card ≤
      (Finset.univ : Finset (Fin k)).card := by
    apply Finset.card_le_card_of_injOn f
    · intro i hi
      exact Finset.mem_univ _
    · intro i hi j hj hij
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
      apply Fin.ext
      dsimp [f] at hij
      rw [dif_pos hi, dif_pos hj] at hij
      simp only [Fin.mk.injEq] at hij
      omega
  simpa using hc

theorem finZeroExtendedShift_sq_sum_bound
    {m : ℕ} (k : ℕ) (w : Fin m → ℝ) (active : Fin m → Prop)
    [DecidablePred active] (a b M : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hM : 0 ≤ M)
    (hvalid : ∀ (i : Fin m) (hi : i.val + k < m),
      |w ⟨i.val + k, hi⟩ - w i| ≤ a)
    (hzero : ∀ (i : Fin m) (hi : i.val + k < m),
      ¬ active i → ¬ active ⟨i.val + k, hi⟩ →
        w ⟨i.val + k, hi⟩ - w i = 0)
    (hweight : ∀ i, |w i| ≤ b)
    (hactive : ((Finset.univ.filter active).card : ℝ) ≤ M) :
    (∑ i, (finZeroExtendedShift k w i - w i) ^ 2) ≤
      2 * M * a ^ 2 + (k : ℝ) * b ^ 2 := by
  classical
  let V := Finset.univ.filter (fun i : Fin m => i.val + k < m)
  let B := Finset.univ.filter (fun i : Fin m => ¬ i.val + k < m)
  let A := Finset.univ.filter active
  let T := Finset.univ.filter (fun i : Fin m =>
    ∃ h : i.val + k < m, active ⟨i.val + k, h⟩)
  let S := V.filter (fun i : Fin m => active i ∨
    ∃ h : i.val + k < m, active ⟨i.val + k, h⟩)
  have hsplit :
      (∑ i, (finZeroExtendedShift k w i - w i) ^ 2) =
        (∑ i ∈ V, (finZeroExtendedShift k w i - w i) ^ 2) +
        ∑ i ∈ B, (finZeroExtendedShift k w i - w i) ^ 2 := by
    simpa only [V, B] using
      (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun i : Fin m => i.val + k < m)
        (fun i => (finZeroExtendedShift k w i - w i) ^ 2)).symm
  have hVeq :
      (∑ i ∈ V, (finZeroExtendedShift k w i - w i) ^ 2) =
        ∑ i ∈ S, (finZeroExtendedShift k w i - w i) ^ 2 := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hiV hiS
    simp only [S, Finset.mem_filter] at hiS
    have hv : i.val + k < m := by
      simpa only [V, Finset.mem_filter, Finset.mem_univ, true_and] using hiV
    have hna : ¬ active i := fun h => hiS ⟨hiV, Or.inl h⟩
    have hnas : ¬ active ⟨i.val + k, hv⟩ := fun h => hiS ⟨hiV, Or.inr ⟨hv, h⟩⟩
    rw [finZeroExtendedShift, dif_pos hv, hzero i hv hna hnas]
    norm_num
  have hTcard : T.card ≤ A.card := by
    let f : Fin m → Fin m := fun i =>
      if h : i.val + k < m then ⟨i.val + k, h⟩ else i
    apply Finset.card_le_card_of_injOn f
    · intro i hi
      simp only [Finset.mem_coe, T, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      obtain ⟨h, ha'⟩ := hi
      change f i ∈ A
      simp only [f, dif_pos h, A, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ha'
    · intro i hi j hj hij
      simp only [Finset.mem_coe, T, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
      obtain ⟨hi', _⟩ := hi
      obtain ⟨hj', _⟩ := hj
      apply Fin.ext
      dsimp [f] at hij
      rw [dif_pos hi', dif_pos hj'] at hij
      simp only [Fin.mk.injEq] at hij
      omega
  have hScard : S.card ≤ A.card + T.card := by
    calc
      S.card ≤ (A ∪ T).card := by
        apply Finset.card_le_card
        intro i hi
        simp only [S, Finset.mem_filter] at hi
        rcases hi.2 with hai | hti
        · exact Finset.mem_union_left T (by
            simpa only [A, Finset.mem_filter, Finset.mem_univ, true_and] using hai)
        · exact Finset.mem_union_right A (by
            simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and] using hti)
      _ ≤ A.card + T.card := Finset.card_union_le _ _
  have hScardR : (S.card : ℝ) ≤ 2 * M := by
    have hs : S.card ≤ 2 * A.card := by omega
    have hsR : (S.card : ℝ) ≤ 2 * (A.card : ℝ) := by exact_mod_cast hs
    have hAR : (A.card : ℝ) ≤ M := by simpa only [A] using hactive
    linarith
  have hV :
      (∑ i ∈ V, (finZeroExtendedShift k w i - w i) ^ 2) ≤
        2 * M * a ^ 2 := by
    rw [hVeq]
    calc
      _ ≤ S.card • a ^ 2 := Finset.sum_le_card_nsmul S _ _ (by
        intro i hi
        simp only [S, Finset.mem_filter, V, Finset.mem_univ, true_and] at hi
        have hv := hi.1
        rw [finZeroExtendedShift, dif_pos hv, sq_le_sq]
        simpa only [abs_of_nonneg ha] using hvalid i hv)
      _ = (S.card : ℝ) * a ^ 2 := by simp
      _ ≤ (2 * M) * a ^ 2 := mul_le_mul_of_nonneg_right hScardR (sq_nonneg _)
      _ = 2 * M * a ^ 2 := by ring
  have hBcard : (B.card : ℝ) ≤ k := by
    exact_mod_cast (show B.card ≤ k from by
      simpa only [B] using finZeroExtendedShift_boundary_card (m := m) k)
  have hB :
      (∑ i ∈ B, (finZeroExtendedShift k w i - w i) ^ 2) ≤
        (k : ℝ) * b ^ 2 := by
    calc
      _ ≤ B.card • b ^ 2 := Finset.sum_le_card_nsmul B _ _ (by
        intro i hi
        have hnv : ¬ i.val + k < m := by
          simpa only [B, Finset.mem_filter, Finset.mem_univ, true_and] using hi
        rw [finZeroExtendedShift, dif_neg hnv, zero_sub, neg_sq, sq_le_sq]
        simpa only [abs_of_nonneg hb] using hweight i)
      _ = (B.card : ℝ) * b ^ 2 := by simp
      _ ≤ (k : ℝ) * b ^ 2 := mul_le_mul_of_nonneg_right hBcard (sq_nonneg _)
  rw [hsplit]
  exact add_le_add hV hB

end Hurst
