import Hurst.MergedWeights

noncomputable section
open Set
namespace Hurst

/-- Spatially merged local-polynomial weights with a bounded deterministic
coefficient attached to every pilot centre. -/
def coefficientAveragedLocalWeights (r n q m : ℕ) (δ : ℝ)
    (c : Fin m → ℝ) (i : Fin (n-q)) : ℝ :=
  (∑ j : Fin m, c j * localPolynomialWeights r n q δ (grid m j.val) i)/(m:ℝ)

theorem coefficientAveragedLocalWeights_uniform_bounds (r q : ℕ) :
    ∃ N₀ > 0, ∃ D > 0, ∀ n m : ℕ, 0 < n → q ≤ n → 0 < m → ∀ δ : ℝ,
      0 < δ → δ ≤ 1/2 → N₀ ≤ (n:ℝ)*δ → 1 ≤ (m:ℝ)*δ →
      ∀ c : Fin m → ℝ, ∀ K : ℝ, 0 ≤ K → (∀ j, |c j| ≤ K) →
      (∑ i, |coefficientAveragedLocalWeights r n q m δ c i|) ≤ K*D ∧
      ∀ i, |coefficientAveragedLocalWeights r n q m δ c i| ≤ 3*(K*D)/(n:ℝ) := by
  classical
  obtain ⟨N₀,hN₀,D,hD,hw⟩ := localPolynomialWeights_uniform_stability r q
  refine ⟨N₀,hN₀,D,hD,?_⟩
  intro n m hn hq hm δ hδ hδhalf hnd hmd c K hK hc
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hmR : (0:ℝ)<m := by exact_mod_cast hm
  have ht : ∀ j : Fin m, grid m j.val ∈ Icc (0:ℝ) 1 := fun j =>
    ⟨(grid_mem m j.val hm j.isLt).1.le,(grid_mem m j.val hm j.isLt).2.le⟩
  have hl1 : ∀ j : Fin m, ∑ i, |localPolynomialWeights r n q δ (grid m j.val) i| ≤ D :=
    fun j => (hw n hn hq δ _ hδ hδhalf (ht j) hnd).2.2.1
  have hmax : ∀ j : Fin m, ∀ i, |localPolynomialWeights r n q δ (grid m j.val) i| ≤ D/((n:ℝ)*δ) :=
    fun j => (hw n hn hq δ _ hδ hδhalf (ht j) hnd).2.1
  constructor
  · unfold coefficientAveragedLocalWeights
    simp only [abs_div,abs_of_pos hmR,← Finset.sum_div]
    apply (div_le_iff₀ hmR).mpr
    calc
      _ ≤ ∑ i,∑ j : Fin m,|c j*localPolynomialWeights r n q δ (grid m j.val) i| :=
        Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ = ∑ j : Fin m,∑ i,|c j| * |localPolynomialWeights r n q δ (grid m j.val) i| := by
        simp_rw [abs_mul]
        exact Finset.sum_comm
      _ ≤ ∑ j : Fin m,∑ i,K * |localPolynomialWeights r n q δ (grid m j.val) i| := by
        exact Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun i _ =>
          mul_le_mul_of_nonneg_right (hc j) (abs_nonneg _)))
      _ = ∑ j : Fin m,K*(∑ i,|localPolynomialWeights r n q δ (grid m j.val) i|) := by
        simp only [Finset.mul_sum]
      _ ≤ ∑ _j : Fin m,K*D := Finset.sum_le_sum (fun j _ =>
        mul_le_mul_of_nonneg_left (hl1 j) hK)
      _ = K*D*(m:ℝ) := by simp [mul_comm]
  · intro i
    let S := Finset.univ.filter (fun j : Fin m => localPolynomialWeights r n q δ (grid m j.val) i ≠ 0)
    have hactive : ∀ j∈S,|(grid m j.val-grid n i.val)/δ|<1 := by
      intro j hj
      have hne := (Finset.mem_filter.mp hj).2
      have hh : |(grid n i.val-grid m j.val)/δ|<1 := by
        by_contra h
        exact hne (localPolynomialWeights_zero r n q δ _ i (le_of_not_gt h))
      simpa only [abs_div,abs_sub_comm] using hh
    have hcard := midpoint_active_card_bound m m hm δ (grid n i.val) hδ S hactive
    have hcard3 : (S.card:ℝ)≤3*((m:ℝ)*δ) := by linarith
    have hsum : ∑ j : Fin m,|c j*localPolynomialWeights r n q δ (grid m j.val) i| =
        ∑ j∈S,|c j*localPolynomialWeights r n q δ (grid m j.val) i| := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro j hj hnot
      have hz : localPolynomialWeights r n q δ (grid m j.val) i=0 := by
        by_contra hz
        exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz⟩)
      simp [hz]
    have he : |∑ j : Fin m,c j*localPolynomialWeights r n q δ (grid m j.val) i| ≤
        3*((m:ℝ)*δ)*(K*D/((n:ℝ)*δ)) := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      rw [hsum]
      calc
        _ ≤ ∑ j∈S,K*(D/((n:ℝ)*δ)) := Finset.sum_le_sum (fun j _ => by
          rw [abs_mul]
          exact mul_le_mul (hc j) (hmax j i) (abs_nonneg _) hK)
        _ = (S.card:ℝ)*(K*(D/((n:ℝ)*δ))) := by simp
        _ ≤ 3*((m:ℝ)*δ)*(K*(D/((n:ℝ)*δ))) :=
          mul_le_mul_of_nonneg_right hcard3 (by positivity)
        _ = _ := by ring
    unfold coefficientAveragedLocalWeights
    rw [abs_div,abs_of_pos hmR]
    calc
      _ ≤ (3*((m:ℝ)*δ)*(K*D/((n:ℝ)*δ)))/(m:ℝ) := (div_le_div_iff_of_pos_right hmR).mpr he
      _ = 3*(K*D)/(n:ℝ) := by field_simp

end Hurst
