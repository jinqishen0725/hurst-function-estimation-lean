import Hurst.OptimalActiveRowDensity
import Hurst.OptimalMeanLeading
import Mathlib.Data.Nat.Find

noncomputable section
open Set Filter
open scoped Topology
namespace Hurst

theorem exists_rowSize_gt (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (r : ℕ) : ∃ n, r < m n := by
  have hev : ∀ᶠ n in atTop, r + 1 ≤ m n := hm.eventually_ge_atTop (r + 1)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  exact ⟨N, Nat.lt_of_succ_le (hN N le_rfl)⟩

/-- The first source row whose size is strictly larger than the requested
exact row size. -/
def firstRowAbove (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) (r : ℕ) : ℕ :=
  Nat.find (exists_rowSize_gt m hm r)

theorem firstRowAbove_spec (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (r : ℕ) : r < m (firstRowAbove m hm r) := by
  exact Nat.find_spec (exists_rowSize_gt m hm r)

theorem firstRowAbove_min (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (r n : ℕ) (hn : n < firstRowAbove m hm r) : m n ≤ r := by
  exact Nat.le_of_not_gt (Nat.find_min (exists_rowSize_gt m hm r) hn)

/-- Select the predecessor of the first row that exceeds the desired exact
row size.  This is the source row used for dense padding. -/
def denseRowSelector (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) (r : ℕ) : ℕ :=
  firstRowAbove m hm r - 1

theorem denseRowSelector_tendsto_atTop (m : ℕ → ℕ)
    (hm : Tendsto m atTop atTop) :
    Tendsto (denseRowSelector m hm) atTop atTop := by
  rw [tendsto_atTop]
  intro K
  let R := ∑ i ∈ Finset.range (K + 1), m i
  filter_upwards [eventually_ge_atTop R] with r hr
  have hbelow : ∀ i ≤ K, m i ≤ r := by
    intro i hi
    have himem : i ∈ Finset.range (K + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hi)
    have hisum : m i ≤ R := by
      dsimp only [R]
      exact Finset.single_le_sum (fun j _ => Nat.zero_le (m j)) himem
    exact hisum.trans hr
  have hKcross : K < firstRowAbove m hm r := by
    unfold firstRowAbove
    rw [Nat.lt_find_iff]
    intro i hi
    exact Nat.not_lt_of_ge (hbelow i hi)
  dsimp only [denseRowSelector]
  omega

theorem denseRowSelector_eventually_le (m : ℕ → ℕ)
    (hm : Tendsto m atTop atTop) :
    ∀ᶠ r in atTop, m (denseRowSelector m hm r) ≤ r := by
  filter_upwards [eventually_ge_atTop (m 0)] with r hr
  have hcross0 : 0 < firstRowAbove m hm r := by
    unfold firstRowAbove
    rw [Nat.find_pos]
    exact Nat.not_lt_of_ge hr
  apply firstRowAbove_min m hm r
  dsimp only [denseRowSelector]
  omega

theorem firstRowAbove_eq_selector_succ_eventually (m : ℕ → ℕ)
    (hm : Tendsto m atTop atTop) :
    ∀ᶠ r in atTop,
      firstRowAbove m hm r = denseRowSelector m hm r + 1 := by
  filter_upwards [eventually_ge_atTop (m 0)] with r hr
  have hcross0 : 0 < firstRowAbove m hm r := by
    unfold firstRowAbove
    rw [Nat.find_pos]
    exact Nat.not_lt_of_ge hr
  dsimp only [denseRowSelector]
  omega

/-- If successive source-row sizes have ratio tending to one, predecessor
selection embeds them below every exact row with an asymptotically negligible
number of padding coordinates. -/
theorem denseRowSelector_size_ratio_tendsto_one (m : ℕ → ℕ)
    (hm : Tendsto m atTop atTop)
    (hratio : Tendsto (fun n : ℕ => ((m (n + 1) : ℕ) : ℝ) / (m n : ℝ))
      atTop (𝓝 1)) :
    Tendsto (fun r : ℕ => (m (denseRowSelector m hm r) : ℝ) / (r : ℝ))
      atTop (𝓝 1) := by
  let s := denseRowSelector m hm
  have hs : Tendsto s atTop atTop := denseRowSelector_tendsto_atTop m hm
  have hQ : Tendsto (fun r : ℕ => (m (s r + 1) : ℝ) / (m (s r) : ℝ))
      atTop (𝓝 1) := hratio.comp hs
  have hLower : Tendsto (fun r : ℕ => (m (s r) : ℝ) / (m (s r + 1) : ℝ))
      atTop (𝓝 1) := by
    have hinv := hQ.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    norm_num at hinv
    refine hinv.congr' ?_
    have hmSelTop : Tendsto (fun r => m (s r)) atTop atTop := hm.comp hs
    have hmSelPos : ∀ᶠ r in atTop, 0 < m (s r) :=
      hmSelTop.eventually_gt_atTop 0
    have hmNextPos : ∀ᶠ r in atTop, 0 < m (s r + 1) := by
      have hsNext : Tendsto (fun r => s r + 1) atTop atTop :=
        by
          rw [tendsto_atTop]
          intro K
          filter_upwards [(tendsto_atTop.1 hs K)] with r hr
          omega
      exact (hm.comp hsNext).eventually_gt_atTop 0
    filter_upwards [hmSelPos, hmNextPos] with r hms hmn
    field_simp [hms.ne', hmn.ne']
  have hupper : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hLower hupper
  · have hle := denseRowSelector_eventually_le m hm
    have hcrossEq := firstRowAbove_eq_selector_succ_eventually m hm
    have hrpos : ∀ᶠ r : ℕ in atTop, 0 < r := eventually_gt_atTop 0
    have hmSelTop : Tendsto (fun r => m (s r)) atTop atTop := hm.comp hs
    have hmSelPos : ∀ᶠ r in atTop, 0 < m (s r) :=
      hmSelTop.eventually_gt_atTop 0
    filter_upwards [hle, hcrossEq, hrpos, hmSelPos] with r hleR hEq hr hms
    have hcross : r < m (s r + 1) := by
      rw [← hEq]
      exact firstRowAbove_spec m hm r
    exact div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ m (s r))
      (by exact_mod_cast hr) (by exact_mod_cast hcross.le)
  · filter_upwards [denseRowSelector_eventually_le m hm,
      (eventually_gt_atTop 0 : ∀ᶠ r : ℕ in atTop, 0 < r)] with r hleR hr
    exact (div_le_one (by exact_mod_cast hr : (0 : ℝ) < r)).2
      (by exact_mod_cast hleR)

/-- Dense exact-row embedding specialized to the active window at the paper's
optimal bandwidth. -/
theorem optimalActive_denseRowSelector_size_ratio_tendsto_one
    (q r : ℕ) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    let δ := optimalLocalBandwidth ((r : ℝ) + 1)
    let m := fun n => (localWeightActiveSet n q (δ n) t).card
    Tendsto (fun N : ℕ =>
      (m (denseRowSelector m
        (localWeightActiveSet_card_tendsto_atTop q t ht δ
          (optimalLocalBandwidth_bias_conditions r 0 (by norm_num)).1
          (optimalLocalBandwidth_bias_conditions r 0 (by norm_num)).2.1
          (optimalLocalBandwidth_bias_conditions r 0 (by norm_num)).2.2.1) N) : ℝ) /
        (N : ℝ)) atTop (𝓝 1) := by
  dsimp only
  obtain ⟨hδpos, hδ0, hS, _hBias, _hLong⟩ :=
    optimalLocalBandwidth_bias_conditions r 0 (by norm_num)
  let δ := optimalLocalBandwidth ((r : ℝ) + 1)
  let m := fun n => (localWeightActiveSet n q (δ n) t).card
  have hm : Tendsto m atTop atTop := by
    simpa only [m, δ] using
      localWeightActiveSet_card_tendsto_atTop q t ht
        (optimalLocalBandwidth ((r : ℝ) + 1)) hδpos hδ0 hS
  have hsucc : Tendsto (fun n : ℕ => ((m (n + 1) : ℕ) : ℝ) / (m n : ℝ))
      atTop (𝓝 1) := by
    apply localWeightActiveSet_card_succ_ratio_tendsto_one
      q t ht (optimalLocalBandwidth ((r : ℝ) + 1)) hδpos hδ0 hS
    exact optimalLocalEffectiveSize_succ_ratio_tendsto_one ((r : ℝ) + 1)
  exact denseRowSelector_size_ratio_tendsto_one m hm hsucc

theorem exists_optimalActive_denseRowSelector
    (q r : ℕ) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    let δ := optimalLocalBandwidth ((r : ℝ) + 1)
    let m := fun n => (localWeightActiveSet n q (δ n) t).card
    ∃ hm : Tendsto m atTop atTop,
      Tendsto (denseRowSelector m hm) atTop atTop ∧
      (∀ᶠ N in atTop, m (denseRowSelector m hm N) ≤ N) ∧
      Tendsto (fun N : ℕ =>
        (m (denseRowSelector m hm N) : ℝ) / (N : ℝ)) atTop (𝓝 1) := by
  dsimp only
  obtain ⟨hδpos, hδ0, hS, _hBias, _hLong⟩ :=
    optimalLocalBandwidth_bias_conditions r 0 (by norm_num)
  let δ := optimalLocalBandwidth ((r : ℝ) + 1)
  let m := fun n => (localWeightActiveSet n q (δ n) t).card
  have hm : Tendsto m atTop atTop := by
    simpa only [m, δ] using
      localWeightActiveSet_card_tendsto_atTop q t ht
        (optimalLocalBandwidth ((r : ℝ) + 1)) hδpos hδ0 hS
  have hsucc : Tendsto (fun n : ℕ => ((m (n + 1) : ℕ) : ℝ) / (m n : ℝ))
      atTop (𝓝 1) := by
    apply localWeightActiveSet_card_succ_ratio_tendsto_one
      q t ht (optimalLocalBandwidth ((r : ℝ) + 1)) hδpos hδ0 hS
    exact optimalLocalEffectiveSize_succ_ratio_tendsto_one ((r : ℝ) + 1)
  exact ⟨hm, denseRowSelector_tendsto_atTop m hm,
    denseRowSelector_eventually_le m hm,
    denseRowSelector_size_ratio_tendsto_one m hm hsucc⟩

end Hurst
