import Hurst.MomentExpansion

noncomputable section
open Set
namespace Hurst

def colorClassSum {ι : Type*} [Fintype ι] {d : ℕ}
    (color : ι → Fin d) (Y : ι → ℝ) (c : Fin d) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => color i = c), Y i

theorem sum_eq_sum_colorClassSum {ι : Type*} [Fintype ι] {d : ℕ}
    (color : ι → Fin d) (Y : ι → ℝ) :
    (∑ i, Y i) = ∑ c, colorClassSum color Y c := by
  classical
  symm
  simpa [colorClassSum] using
    (Finset.sum_fiberwise_eq_sum_filter (Finset.univ : Finset ι)
      (Finset.univ : Finset (Fin d)) color Y)

/-- Deterministic grouping inequality used after splitting weakly correlated
indices into residue classes. No independence between classes is used. -/
theorem abs_sum_pow_le_colorClassSum {ι : Type*} [Fintype ι] {d : ℕ}
    (color : ι → Fin d) (Y : ι → ℝ) (m : ℕ) :
    |∑ i, Y i| ^ (m + 1) ≤
      (d : ℝ) ^ m * ∑ c, |colorClassSum color Y c| ^ (m + 1) := by
  classical
  rw [sum_eq_sum_colorClassSum color Y]
  calc
    |∑ c, colorClassSum color Y c| ^ (m + 1) ≤
        (∑ c, |colorClassSum color Y c|) ^ (m + 1) := by
      exact pow_le_pow_left₀ (abs_nonneg _) (Finset.abs_sum_le_sum_abs _ _) _
    _ ≤ (d : ℝ) ^ m * ∑ c, |colorClassSum color Y c| ^ (m + 1) := by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        (pow_sum_le_card_mul_sum_pow
          (s := (Finset.univ : Finset (Fin d)))
          (f := fun c => |colorClassSum color Y c|)
          (fun _ _ => abs_nonneg _) m)

def residueColor (d : ℕ) (hd : 0 < d) {n : ℕ} (i : Fin n) : Fin d :=
  ⟨i.val % d, Nat.mod_lt _ hd⟩

theorem residueColor_equal_separation (d : ℕ) (hd : 0 < d) {n : ℕ}
    {i j : Fin n} (hij : i ≠ j)
    (hc : residueColor d hd i = residueColor d hd j) :
    d ≤ (i.val - j.val) + (j.val - i.val) := by
  have hm : i.val % d = j.val % d := congrArg Fin.val hc
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  by_cases hle : i.val ≤ j.val
  · have hlt : i.val < j.val := lt_of_le_of_ne hle hne
    have hdvd : d ∣ j.val - i.val := (Nat.modEq_iff_dvd' hle).mp hm
    have hbound : d ≤ j.val - i.val := Nat.le_of_dvd (Nat.sub_pos_of_lt hlt) hdvd
    omega
  · have hji : j.val ≤ i.val := Nat.le_of_lt (lt_of_not_ge hle)
    have hlt : j.val < i.val := lt_of_le_of_ne hji hne.symm
    have hdvd : d ∣ i.val - j.val := (Nat.modEq_iff_dvd' hji).mp hm.symm
    have hbound : d ≤ i.val - j.val := Nat.le_of_dvd (Nat.sub_pos_of_lt hlt) hdvd
    omega

end Hurst
