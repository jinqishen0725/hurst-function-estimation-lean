import Mathlib.InformationTheory.Hamming
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic

noncomputable section
open Set
namespace Hurst

/-- A finite maximal separated set covers the space by balls of the same radius. -/
theorem finite_greedy_packing {X : Type*} [Fintype X] [DecidableEq X]
    (d : X → X → ℕ) (hd : ∀ x y, d x y = d y x) (hself : ∀ x, d x x = 0) (r : ℕ) :
    ∃ S : Finset X, (∀ x ∈ S, ∀ y ∈ S, x ≠ y → r < d x y) ∧
      ∀ x, ∃ y ∈ S, d x y ≤ r := by
  classical
  let P := fun S : Finset X => ∀ x ∈ S, ∀ y ∈ S, x ≠ y → r < d x y
  obtain ⟨S, _, hmax⟩ := Finite.exists_le_maximal (p := P) (a := (∅ : Finset X)) (by simp [P])
  refine ⟨S, hmax.1, ?_⟩
  intro x
  by_contra hx
  push Not at hx
  have hnew : P (insert x S) := by
    intro u hu v hv huv
    rcases Finset.mem_insert.mp hu with hux | huS
    · rcases Finset.mem_insert.mp hv with hvx | hvS
      · exact (huv (hux.trans hvx.symm)).elim
      · rw [hux]
        exact hx v hvS
    · rcases Finset.mem_insert.mp hv with hvx | hvS
      · rw [hvx, hd]
        exact hx u huS
      · exact hmax.1 u huS v hvS huv
  have hsub := hmax.2 hnew (Finset.subset_insert x S)
  have hxs : x ∈ S := hsub (Finset.mem_insert_self x S)
  have hh := hx x hxs
  rw [hself x] at hh
  omega

theorem finite_cover_card_bound {X : Type*} [Fintype X] [DecidableEq X]
    (d : X → X → ℕ) (r : ℕ) (S : Finset X) (V : ℝ)
    (hcover : ∀ x, ∃ y ∈ S, d x y ≤ r)
    (hball : ∀ y, ((Finset.univ.filter (fun x => d x y ≤ r)).card : ℝ) ≤ V) :
    (Fintype.card X : ℝ) ≤ S.card * V := by
  classical
  have hsub : (Finset.univ : Finset X) ⊆ S.biUnion (fun y => Finset.univ.filter (fun x => d x y ≤ r)) := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hcover x
    exact Finset.mem_biUnion.mpr ⟨y, hy, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy⟩⟩
  have hc := (Finset.card_le_card hsub).trans (Finset.card_biUnion_le)
  calc
    _ ≤ ((∑ y ∈ S, (Finset.univ.filter (fun x => d x y ≤ r)).card : ℕ) : ℝ) := by exact_mod_cast hc
    _ = ∑ y ∈ S, ((Finset.univ.filter (fun x => d x y ≤ r)).card : ℝ) := by rw [Nat.cast_sum]
    _ ≤ ∑ _y ∈ S, V := Finset.sum_le_sum (fun y _ => hball y)
    _ = _ := by simp

/-- The Hamming generating function is a finite product identity, with no binomial counting premise. -/
theorem hamming_generating_function (m : ℕ) (x : Fin m → Bool) (t : ℝ) :
    (∑ y : Fin m → Bool, t ^ hammingDist x y) = (1 + t) ^ m := by
  classical
  have he (y : Fin m → Bool) : t ^ hammingDist x y = ∏ i, if x i ≠ y i then t else 1 := by
    simp only [hammingDist, Finset.prod_ite, Finset.prod_const, one_pow, mul_one]
  simp_rw [he]
  rw [← Fintype.prod_sum (fun i : Fin m => fun b : Bool => if x i ≠ b then t else 1)]
  have hb : ∀ i : Fin m, (∑ b : Bool, if x i ≠ b then t else 1) = 1 + t := by
    intro i
    cases x i <;> simp [add_comm]
  simp only [hb, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem hamming_ball_generating_bound (m r : ℕ) (x : Fin m → Bool) (t : ℝ)
    (ht : 0 < t) (ht1 : t ≤ 1) :
    ((Finset.univ.filter (fun y => hammingDist x y ≤ r)).card : ℝ) * t ^ r ≤ (1 + t) ^ m := by
  classical
  let S := Finset.univ.filter (fun y => hammingDist x y ≤ r)
  calc
    _ = ∑ _y ∈ S, t ^ r := by simp [S]
    _ ≤ ∑ y ∈ S, t ^ hammingDist x y := by
      apply Finset.sum_le_sum
      intro y hy
      exact pow_le_pow_of_le_one ht.le ht1 (Finset.mem_filter.mp hy).2
    _ ≤ ∑ y : Fin m → Bool, t ^ hammingDist x y :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun y _ _ => pow_nonneg ht.le _)
    _ = _ := hamming_generating_function m x t

/-- The entropy exponent in the one-eighth Hamming ball. -/
theorem eighth_entropy_identity :
    Real.log (1 + (1 / 7 : ℝ)) - (1 / 8 : ℝ) * Real.log (1 / 7 : ℝ) = Real.binEntropy (1 / 8) := by
  have h1 : Real.log (1 / 7 : ℝ) = -Real.log 7 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
    ring
  have h2 : Real.log (8 / 7 : ℝ) = Real.log 8 - Real.log 7 := Real.log_div (by norm_num) (by norm_num)
  norm_num only [Real.binEntropy]
  rw [h1, h2]
  ring

theorem hamming_ball_entropy_bound (m : ℕ) (x : Fin m → Bool) :
    ((Finset.univ.filter (fun y => hammingDist x y ≤ Nat.floor ((m : ℝ) / 8))).card : ℝ) ≤
      Real.exp ((m : ℝ) * Real.binEntropy (1 / 8)) := by
  have hr : ((Nat.floor ((m : ℝ) / 8) : ℕ) : ℝ) ≤ (m : ℝ) / 8 := Nat.floor_le (by positivity)
  have hp : (1 / 7 : ℝ) ^ ((m : ℝ) / 8) ≤ (1 / 7 : ℝ) ^ Nat.floor ((m : ℝ) / 8) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hr
  have hc : 0 ≤ ((Finset.univ.filter (fun y => hammingDist x y ≤ Nat.floor ((m : ℝ) / 8))).card : ℝ) := Nat.cast_nonneg _
  have hm := (mul_le_mul_of_nonneg_left hp hc).trans
    (hamming_ball_generating_bound m _ x (1 / 7) (by norm_num) (by norm_num))
  have hpos : 0 < (1 / 7 : ℝ) ^ ((m : ℝ) / 8) := Real.rpow_pos_of_pos (by norm_num) _
  have he : (1 + (1 / 7 : ℝ)) ^ m / (1 / 7 : ℝ) ^ ((m : ℝ) / 8) =
      Real.exp ((m : ℝ) * Real.binEntropy (1 / 8)) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos (by norm_num),
      ← Real.exp_sub]
    congr 1
    rw [← eighth_entropy_identity]
    ring
  rw [← he]
  exact (le_div_iff₀ hpos).mpr hm

/-- Exponentially many binary codewords with strict one-eighth Hamming separation. -/
theorem binary_code_packing :
    ∃ c > 0, ∀ m : ℕ, 0 < m → ∃ S : Finset (Fin m → Bool), S.Nonempty ∧
      c * (m : ℝ) ≤ Real.log (S.card : ℝ) ∧
      ∀ x ∈ S, ∀ y ∈ S, x ≠ y → (m : ℝ) / 8 < (hammingDist x y : ℝ) := by
  let c := Real.log 2 - Real.binEntropy (1 / 8)
  have hc : 0 < c := sub_pos.mpr (Real.binEntropy_lt_log_two.mpr (by norm_num))
  refine ⟨c, hc, ?_⟩
  intro m hm
  obtain ⟨S, hsep, hcover⟩ := finite_greedy_packing (X := Fin m → Bool) hammingDist hammingDist_comm hammingDist_self
    (Nat.floor ((m : ℝ) / 8))
  have hnonempty : S.Nonempty := by
    obtain ⟨y, hy, _⟩ := hcover (fun _ => false)
    exact ⟨y, hy⟩
  have hcard := finite_cover_card_bound hammingDist (Nat.floor ((m : ℝ) / 8)) S
    (Real.exp ((m : ℝ) * Real.binEntropy (1 / 8))) hcover
    (fun y => by simpa only [hammingDist_comm] using hamming_ball_entropy_bound m y)
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] at hcard
  have hSpos : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hnonempty
  have hlog := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) m) hcard
  rw [Real.log_mul hSpos.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_pow] at hlog
  refine ⟨S, hnonempty, ?_, ?_⟩
  · dsimp only [c]
    nlinarith
  · intro x hx y hy hxy
    have hd : (Nat.floor ((m : ℝ) / 8) : ℝ) + 1 ≤ (hammingDist x y : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (hsep x hx y hy hxy)
    exact (Nat.lt_floor_add_one ((m : ℝ) / 8)).trans_le hd

end Hurst
