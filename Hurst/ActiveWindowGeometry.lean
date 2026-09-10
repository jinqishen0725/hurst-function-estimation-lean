import Hurst.ActiveSetReindex
import Hurst.WeightProfileLimit
import Mathlib.Order.Interval.Finset.Nat

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace Hurst

theorem localWeightActiveSet_card_lower (n q : ℕ) (hn : 0 < n)
    (δ t : ℝ) (hδ : 0 < δ)
    (hleft : 0 ≤ (n : ℝ) * (t - δ) - 1 / 2)
    (hright : (n : ℝ) * (t + δ) - 1 / 2 ≤ n - q)
    (hwide : 1 ≤ 2 * ((n : ℝ) * δ)) :
    2 * ((n : ℝ) * δ) - 1 ≤
      ((localWeightActiveSet n q δ t).card : ℝ) := by
  classical
  let loR := (n : ℝ) * (t - δ) - 1 / 2
  let hiR := (n : ℝ) * (t + δ) - 1 / 2
  let lo := Nat.floor loR + 1
  let hi := Nat.ceil hiR
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlohiR : loR + 1 ≤ hiR := by dsimp only [loR, hiR]; nlinarith
  have hlohi : lo ≤ hi := by
    exact_mod_cast (show (lo : ℝ) ≤ hi from by
      have hflo : ((Nat.floor loR : ℕ) : ℝ) ≤ loR :=
        Nat.floor_le (by simpa only [loR] using hleft)
      have hceil : hiR ≤ ((Nat.ceil hiR : ℕ) : ℝ) := Nat.le_ceil hiR
      dsimp only [lo, hi]
      rw [Nat.cast_add, Nat.cast_one]
      linarith)
  have hqn : q ≤ n := by
    exact_mod_cast (show (q : ℝ) ≤ n by
      nlinarith [hleft, hwide])
  have hhi : hi ≤ n - q := by
    apply (Nat.ceil_le).2
    rw [Nat.cast_sub hqn]
    exact hright
  let U := Finset.Ico lo hi
  let emb : {i // i ∈ U} ↪ Fin (n - q) :=
    ⟨fun i => ⟨i.val, lt_of_lt_of_le (Finset.mem_Ico.mp i.property).2 hhi⟩,
      fun i j h => Subtype.ext (by simpa using congrArg Fin.val h)⟩
  let T : Finset (Fin (n - q)) := Finset.univ.map emb
  have hsub : T ⊆ localWeightActiveSet n q δ t := by
    intro i hiT
    rw [Finset.mem_map] at hiT
    obtain ⟨j, _, rfl⟩ := hiT
    have hjI := Finset.mem_Ico.mp j.property
    have hjlo : loR < (j.val : ℝ) := by
      have hf := Nat.lt_floor_add_one loR
      have : Nat.floor loR + 1 ≤ j := hjI.1
      exact hf.trans_le (by exact_mod_cast this)
    have hjhi : (j.val : ℝ) < hiR := (Nat.lt_ceil).mp hjI.2
    have hglo : t - δ < grid n (emb j).val := by
      change t - δ < grid n j.val
      unfold grid
      apply (lt_div_iff₀ hnR).2
      dsimp only [loR] at hjlo
      linarith
    have hghi : grid n (emb j).val < t + δ := by
      change grid n j.val < t + δ
      unfold grid
      apply (div_lt_iff₀ hnR).2
      dsimp only [hiR] at hjhi
      linarith
    rw [localWeightActiveSet, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [abs_lt]
    constructor
    · apply (lt_div_iff₀ hδ).2
      linarith
    · apply (div_lt_iff₀ hδ).2
      linarith
  have hcardT : T.card = hi - lo := by
    dsimp only [T]
    rw [Finset.card_map, Finset.card_univ, Fintype.card_coe, Nat.card_Ico]
  have hcard := Finset.card_le_card hsub
  rw [hcardT] at hcard
  have hcast : ((hi - lo : ℕ) : ℝ) = (hi : ℝ) - lo := by
    rw [Nat.cast_sub hlohi]
  have hloUpper : (lo : ℝ) ≤ loR + 1 := by
    have hflo : ((Nat.floor loR : ℕ) : ℝ) ≤ loR :=
      Nat.floor_le (by simpa only [loR] using hleft)
    dsimp only [lo]
    rw [Nat.cast_add, Nat.cast_one]
    linarith
  have hhiLower : hiR ≤ (hi : ℝ) := by
    exact Nat.le_ceil hiR
  have hlen : 2 * ((n : ℝ) * δ) - 1 ≤ (hi : ℝ) - lo := by
    dsimp only [loR, hiR] at hloUpper hhiLower
    nlinarith
  exact hlen.trans (by rw [← hcast]; exact_mod_cast hcard)

/-- An interior shrinking window contains asymptotically `2 n δ` midpoint-grid
indices, even after deleting the final fixed `q` grid positions. -/
theorem localWeightActiveSet_card_ratio_tendsto_two
    (q : ℕ) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop) :
    (∀ᶠ n in atTop, 0 < (localWeightActiveSet n q (δ n) t).card) ∧
    Tendsto (fun n : ℕ =>
      ((localWeightActiveSet n q (δ n) t).card : ℝ) / ((n : ℝ) * δ n))
      atTop (𝓝 2) := by
  have ht0 : 0 < t := ht.1
  have ht1 : 0 < 1 - t := by linarith [ht.2]
  have heδL : ∀ᶠ n in atTop, δ n < t / 2 :=
    hδ0.eventually (Iio_mem_nhds (by linarith))
  have heδR : ∀ᶠ n in atTop, δ n < (1 - t) / 2 :=
    hδ0.eventually (Iio_mem_nhds (by linarith))
  have henL : ∀ᶠ n : ℕ in atTop, 1 / t ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (1 / t)
  have henR : ∀ᶠ n : ℕ in atTop, 2 * (q : ℝ) / (1 - t) ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (2 * (q : ℝ) / (1 - t))
  have heN1 : ∀ᶠ n : ℕ in atTop, 1 ≤ (n : ℝ) * δ n := hN.eventually_ge_atTop 1
  have hgeom : ∀ᶠ n in atTop,
      0 < n ∧ 0 < δ n ∧ 1 ≤ (n : ℝ) * δ n ∧
      2 * ((n : ℝ) * δ n) - 1 ≤
        ((localWeightActiveSet n q (δ n) t).card : ℝ) ∧
      ((localWeightActiveSet n q (δ n) t).card : ℝ) ≤
        2 * ((n : ℝ) * δ n) + 1 := by
    filter_upwards [hδpos, heδL, heδR, henL, henR, heN1,
      eventually_ge_atTop 1] with n hnδ hnδL hnδR hnL hnR hnN hn1
    have hn0 : 0 < n := by omega
    have hnR0 : (0 : ℝ) < n := by exact_mod_cast hn0
    have hleft : 0 ≤ (n : ℝ) * (t - δ n) - 1 / 2 := by
      have hnt : 1 ≤ (n : ℝ) * t := by
        have := (div_le_iff₀ ht0).mp hnL
        nlinarith
      nlinarith
    have hright : (n : ℝ) * (t + δ n) - 1 / 2 ≤ n - q := by
      have hnqt : (q : ℝ) ≤ (n : ℝ) * ((1 - t) / 2) := by
        have := (div_le_iff₀ ht1).mp hnR
        nlinarith
      nlinarith
    have hlower := localWeightActiveSet_card_lower n q hn0 (δ n) t hnδ
      hleft hright (by nlinarith)
    have hupper := midpoint_active_card_bound n (n - q) hn0 (δ n) t hnδ
      (localWeightActiveSet n q (δ n) t)
      (fun i hi => (Finset.mem_filter.mp hi).2)
    exact ⟨hn0, hnδ, hnN, hlower, hupper⟩
  constructor
  · filter_upwards [hgeom] with n hn
    exact_mod_cast (show (0 : ℝ) <
      ((localWeightActiveSet n q (δ n) t).card : ℝ) by linarith [hn.2.2.1, hn.2.2.2.1])
  · have hinv : Tendsto (fun n : ℕ => ((n : ℝ) * δ n)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hN
    have hlowT : Tendsto (fun n : ℕ => 2 - ((n : ℝ) * δ n)⁻¹)
        atTop (𝓝 (2 - 0)) := tendsto_const_nhds.sub hinv
    have huppT : Tendsto (fun n : ℕ => 2 + ((n : ℝ) * δ n)⁻¹)
        atTop (𝓝 (2 + 0)) := tendsto_const_nhds.add hinv
    have hlowT' : Tendsto (fun n : ℕ => 2 - ((n : ℝ) * δ n)⁻¹)
        atTop (𝓝 2) := by simpa using hlowT
    have huppT' : Tendsto (fun n : ℕ => 2 + ((n : ℝ) * δ n)⁻¹)
        atTop (𝓝 2) := by simpa using huppT
    have hlow : ∀ᶠ n : ℕ in atTop,
        2 - ((n : ℝ) * δ n)⁻¹ ≤
          ((localWeightActiveSet n q (δ n) t).card : ℝ) / ((n : ℝ) * δ n) := by
      filter_upwards [hgeom] with n hn
      have hpos : 0 < (n : ℝ) * δ n := mul_pos (by exact_mod_cast hn.1) hn.2.1
      apply (le_div_iff₀ hpos).2
      calc
        (2 - ((n : ℝ) * δ n)⁻¹) * ((n : ℝ) * δ n) =
            2 * ((n : ℝ) * δ n) - 1 := by
              rw [sub_mul, inv_mul_cancel₀ hpos.ne']
        _ ≤ ((localWeightActiveSet n q (δ n) t).card : ℝ) := hn.2.2.2.1
    have hupp : ∀ᶠ n : ℕ in atTop,
        ((localWeightActiveSet n q (δ n) t).card : ℝ) / ((n : ℝ) * δ n) ≤
          2 + ((n : ℝ) * δ n)⁻¹ := by
      filter_upwards [hgeom] with n hn
      have hpos : 0 < (n : ℝ) * δ n := mul_pos (by exact_mod_cast hn.1) hn.2.1
      apply (div_le_iff₀ hpos).2
      calc
        ((localWeightActiveSet n q (δ n) t).card : ℝ) ≤
            2 * ((n : ℝ) * δ n) + 1 := hn.2.2.2.2
        _ = (2 + ((n : ℝ) * δ n)⁻¹) * ((n : ℝ) * δ n) := by
          rw [add_mul, inv_mul_cancel₀ hpos.ne']
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowT' huppT' hlow hupp

end Hurst
