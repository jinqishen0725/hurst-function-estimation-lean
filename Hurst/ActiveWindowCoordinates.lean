import Hurst.ActiveWindowGeometry

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace Hurst

/-- Membership in the active window is order-convex on the midpoint grid. -/
theorem localWeightActiveSet_mem_between
    (n q : ℕ) (hn : 0 < n) (δ t : ℝ) (hδ : 0 < δ)
    {i k j : Fin (n - q)}
    (hi : i ∈ localWeightActiveSet n q δ t)
    (hk : k ∈ localWeightActiveSet n q δ t)
    (hij : i ≤ j) (hjk : j ≤ k) :
    j ∈ localWeightActiveSet n q δ t := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hi' := (Finset.mem_filter.mp hi).2
  have hk' := (Finset.mem_filter.mp hk).2
  rw [localWeightActiveSet, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [abs_lt] at hi' hk' ⊢
  have hgij : grid n i.val ≤ grid n j.val := by
    unfold grid
    gcongr
    exact_mod_cast hij
  have hgjk : grid n j.val ≤ grid n k.val := by
    unfold grid
    gcongr
    exact_mod_cast hjk
  constructor
  · exact hi'.1.trans_le ((div_le_div_iff_of_pos_right hδ).2 (sub_le_sub_right hgij t))
  · exact ((div_le_div_iff_of_pos_right hδ).2 (sub_le_sub_right hgjk t)).trans_lt hk'.2

/-- Consecutive active ranks correspond to consecutive original grid indices. -/
theorem localWeightActiveIndex_adjacent
    (n q : ℕ) (hn : 0 < n) (δ t : ℝ) (hδ : 0 < δ)
    (j : ℕ) (hj : j + 1 < (localWeightActiveSet n q δ t).card) :
    (localWeightActiveIndex n q δ t
        ⟨j + 1, hj⟩).val =
      (localWeightActiveIndex n q δ t
        ⟨j, by omega⟩).val + 1 := by
  let a : Fin (localWeightActiveSet n q δ t).card :=
    ⟨j, by omega⟩
  let b : Fin (localWeightActiveSet n q δ t).card := ⟨j + 1, hj⟩
  have hab : a < b := by simp [a, b]
  have hlt := localWeightActiveIndex_strictMono n q δ t hab
  change localWeightActiveIndex n q δ t a < localWeightActiveIndex n q δ t b at hlt
  apply Nat.le_antisymm
  · by_contra hnot
    have hgap : (localWeightActiveIndex n q δ t a).val + 1 <
        (localWeightActiveIndex n q δ t b).val := Nat.lt_of_not_ge hnot
    let m : Fin (n - q) :=
      ⟨(localWeightActiveIndex n q δ t a).val + 1,
        lt_of_lt_of_le hgap (localWeightActiveIndex n q δ t b).isLt.le⟩
    have hma : localWeightActiveIndex n q δ t a ≤ m := by
      apply Fin.le_iff_val_le_val.mpr
      simp [m]
    have hmb : m ≤ localWeightActiveIndex n q δ t b := by
      apply Fin.le_iff_val_le_val.mpr
      exact hgap.le
    have hm : m ∈ localWeightActiveSet n q δ t :=
      localWeightActiveSet_mem_between n q hn δ t hδ
        (localWeightActiveIndex_mem n q δ t a)
        (localWeightActiveIndex_mem n q δ t b) hma hmb
    let c : Fin (localWeightActiveSet n q δ t).card :=
      (localWeightActiveEquiv n q δ t).symm ⟨m, hm⟩
    have hcval : localWeightActiveIndex n q δ t c = m := by
      change ((localWeightActiveEquiv n q δ t c).val : Fin (n - q)) = m
      simpa [c]
    have hac : a < c := by
      apply lt_of_not_ge
      intro hca
      have himg := (localWeightActiveIndex_strictMono n q δ t).monotone hca
      rw [hcval] at himg
      change m.val ≤ (localWeightActiveIndex n q δ t a).val at himg
      simp [m] at himg
    have hcb : c < b := by
      apply lt_of_not_ge
      intro hbc
      have himg := (localWeightActiveIndex_strictMono n q δ t).monotone hbc
      rw [hcval] at himg
      change (localWeightActiveIndex n q δ t b).val ≤ m.val at himg
      exact (not_le_of_gt hgap) (by simpa [m] using himg)
    change j < c.val at hac
    change c.val < j + 1 at hcb
    omega
  · exact hlt

/-- Every active rank is its rank offset from the first active grid index. -/
theorem localWeightActiveIndex_eq_first_add_rank
    (n q : ℕ) (hn : 0 < n) (δ t : ℝ) (hδ : 0 < δ)
    (hcard : 0 < (localWeightActiveSet n q δ t).card)
    (j : Fin (localWeightActiveSet n q δ t).card) :
    (localWeightActiveIndex n q δ t j).val =
      (localWeightActiveIndex n q δ t ⟨0, hcard⟩).val + j.val := by
  let c := (localWeightActiveSet n q δ t).card
  have hmain : ∀ k : ℕ, (hk : k < c) →
      (localWeightActiveIndex n q δ t ⟨k, hk⟩).val =
        (localWeightActiveIndex n q δ t ⟨0, hcard⟩).val + k := by
    intro k
    induction k with
    | zero =>
        intro hk
        simp
    | succ k ih =>
        intro hk
        have hk0 : k < c := lt_trans (Nat.lt_succ_self k) hk
        rw [localWeightActiveIndex_adjacent n q hn δ t hδ k (by simpa using hk)]
        rw [ih hk0]
        omega
  exact hmain j.val j.isLt

/-- The first active midpoint lies within one grid mesh of the left edge of
the physical window. -/
theorem localWeightActiveIndex_first_coordinate_bounds
    (n q : ℕ) (hn : 0 < n) (δ t : ℝ) (hδ : 0 < δ)
    (hcard : 0 < (localWeightActiveSet n q δ t).card)
    (hleft : 0 ≤ (n : ℝ) * (t - δ) - 1 / 2) :
    -1 < (grid n (localWeightActiveIndex n q δ t ⟨0, hcard⟩).val - t) / δ ∧
      (grid n (localWeightActiveIndex n q δ t ⟨0, hcard⟩).val - t) / δ ≤
        -1 + 1 / ((n : ℝ) * δ) := by
  let a : Fin (localWeightActiveSet n q δ t).card := ⟨0, hcard⟩
  let ia := localWeightActiveIndex n q δ t a
  have hia := (Finset.mem_filter.mp (localWeightActiveIndex_mem n q δ t a)).2
  have hbounds : -1 < (grid n ia.val - t) / δ ∧
      (grid n ia.val - t) / δ < 1 := by simpa [abs_lt] using hia
  refine ⟨by simpa [a, ia] using hbounds.1, ?_⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hia0 : 0 < ia.val := by
    by_contra hzero
    have hval : ia.val = 0 := Nat.eq_zero_of_not_pos hzero
    have hgridle : grid n ia.val ≤ t - δ := by
      unfold grid
      rw [hval]
      apply (div_le_iff₀ hnR).2
      nlinarith
    have : (grid n ia.val - t) / δ ≤ -1 := by
      apply (div_le_iff₀ hδ).2
      linarith
    linarith
  let p : Fin (n - q) := ⟨ia.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) ia.isLt⟩
  have hpval : p.val + 1 = ia.val := by simp [p, Nat.sub_add_cancel hia0]
  have hp_lt : p < ia := by exact_mod_cast (show p.val < ia.val by omega)
  have hpnot : p ∉ localWeightActiveSet n q δ t := by
    intro hp
    let c : Fin (localWeightActiveSet n q δ t).card :=
      (localWeightActiveEquiv n q δ t).symm ⟨p, hp⟩
    have hcval : localWeightActiveIndex n q δ t c = p := by
      change ((localWeightActiveEquiv n q δ t c).val : Fin (n - q)) = p
      simp [c]
    have hca : c < a := by
      apply lt_of_not_ge
      intro hac
      have himg := (localWeightActiveIndex_strictMono n q δ t).monotone hac
      rw [hcval] at himg
      exact (not_le_of_gt hp_lt) (by simpa [ia] using himg)
    change c.val < 0 at hca
    omega
  have hpabs : ¬ |(grid n p.val - t) / δ| < 1 := by
    simpa only [localWeightActiveSet, Finset.mem_filter, Finset.mem_univ, true_and] using hpnot
  have hpupper : (grid n p.val - t) / δ < 1 := by
    have hgrid : grid n p.val < grid n ia.val := by
      unfold grid
      apply (div_lt_div_iff_of_pos_right hnR).2
      have hpcast : (p.val : ℝ) < ia.val := by exact_mod_cast hp_lt
      linarith
    exact ((div_lt_div_iff_of_pos_right hδ).2 (sub_lt_sub_right hgrid t)).trans_le hbounds.2.le
  have hplower : (grid n p.val - t) / δ ≤ -1 := by
    by_contra hnot
    exact hpabs ((abs_lt).2 ⟨lt_of_not_ge hnot, hpupper⟩)
  have hmesh :
      (grid n ia.val - t) / δ =
        (grid n p.val - t) / δ + 1 / ((n : ℝ) * δ) := by
    unfold grid
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
    have hδ0 : δ ≠ 0 := ne_of_gt hδ
    rw [show (ia.val : ℝ) = (p.val : ℝ) + 1 by exact_mod_cast hpval.symm]
    field_simp
    ring
  rw [hmesh]
  linarith

/-- A deterministic, uniform rank-coordinate error bound.  The three terms
are respectively the left-edge mesh error, the active-cardinality ratio
error, and the use of `j+1` in the profile convention. -/
theorem localWeightActiveIndex_rank_coordinate_error
    (n q : ℕ) (hn : 0 < n) (δ t : ℝ) (hδ : 0 < δ)
    (hcard : 0 < (localWeightActiveSet n q δ t).card)
    (hleft : 0 ≤ (n : ℝ) * (t - δ) - 1 / 2)
    (j : Fin (localWeightActiveSet n q δ t).card) :
    |(grid n (localWeightActiveIndex n q δ t j).val - t) / δ -
        (2 * (((j.val + 1 : ℕ) : ℝ) /
          ((localWeightActiveSet n q δ t).card : ℝ)) - 1)| ≤
      1 / ((n : ℝ) * δ) +
        |((localWeightActiveSet n q δ t).card : ℝ) / ((n : ℝ) * δ) - 2| +
        2 / ((localWeightActiveSet n q δ t).card : ℝ) := by
  let c : ℝ := ((localWeightActiveSet n q δ t).card : ℝ)
  let scale : ℝ := (n : ℝ) * δ
  let x0 : ℝ :=
    (grid n (localWeightActiveIndex n q δ t ⟨0, hcard⟩).val - t) / δ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hscale : 0 < scale := mul_pos hnR hδ
  have hc : 0 < c := by dsimp only [c]; exact_mod_cast hcard
  have hfirst := localWeightActiveIndex_first_coordinate_bounds n q hn δ t hδ hcard hleft
  have hx0nonneg : 0 ≤ x0 + 1 := by dsimp only [x0]; linarith [hfirst.1]
  have hx0upper : x0 + 1 ≤ 1 / scale := by
    dsimp only [x0, scale]
    linarith [hfirst.2]
  have hphys :
      (grid n (localWeightActiveIndex n q δ t j).val - t) / δ =
        x0 + (j.val : ℝ) / scale := by
    rw [localWeightActiveIndex_eq_first_add_rank n q hn δ t hδ hcard j]
    dsimp only [x0, scale]
    unfold grid
    have hn0 : (n : ℝ) ≠ 0 := hnR.ne'
    have hδ0 : δ ≠ 0 := hδ.ne'
    rw [Nat.cast_add]
    field_simp
    ring
  have hjnonneg : 0 ≤ (j.val : ℝ) / c := div_nonneg (by positivity) hc.le
  have hjle : (j.val : ℝ) / c ≤ 1 := by
    apply (div_le_one hc).2
    dsimp only [c]
    exact_mod_cast j.isLt.le
  have halg :
      (j.val : ℝ) / scale - 2 * (((j.val + 1 : ℕ) : ℝ) / c) =
        ((j.val : ℝ) / c) * (c / scale - 2) - 2 / c := by
    rw [Nat.cast_add, Nat.cast_one]
    field_simp [hscale.ne', hc.ne']
    ring
  rw [hphys]
  have hrearrange :
      x0 + (j.val : ℝ) / scale -
          (2 * (((j.val + 1 : ℕ) : ℝ) / c) - 1) =
        (x0 + 1) +
          ((j.val : ℝ) / scale - 2 * (((j.val + 1 : ℕ) : ℝ) / c)) := by ring
  rw [show ((localWeightActiveSet n q δ t).card : ℝ) = c by rfl,
    show (n : ℝ) * δ = scale by rfl, hrearrange, halg]
  calc
    |(x0 + 1) + ((j.val : ℝ) / c * (c / scale - 2) - 2 / c)| ≤
        |x0 + 1| + |(j.val : ℝ) / c * (c / scale - 2) - 2 / c| := abs_add_le _ _
    _ ≤ |x0 + 1| +
        (|(j.val : ℝ) / c * (c / scale - 2)| + |2 / c|) := by gcongr; exact abs_sub _ _
    _ = |x0 + 1| + ((j.val : ℝ) / c * |c / scale - 2| + 2 / c) := by
      rw [abs_mul, abs_of_nonneg hjnonneg, abs_of_nonneg (div_nonneg (by norm_num) hc.le)]
    _ ≤ 1 / scale + (|c / scale - 2| + 2 / c) := by
      gcongr
      · exact (abs_of_nonneg hx0nonneg).trans_le hx0upper
      · calc
          (j.val : ℝ) / c * |c / scale - 2| ≤ 1 * |c / scale - 2| :=
            mul_le_mul_of_nonneg_right hjle (abs_nonneg _)
          _ = |c / scale - 2| := one_mul _
    _ = 1 / scale + |c / scale - 2| + 2 / c := by ring

/-- Uniformly over active ranks, physical midpoint coordinates and the
`(j+1)/card` profile coordinates have the same limit. -/
theorem localWeightActiveIndex_rank_coordinate_uniform_tendsto
    (q : ℕ) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      ∀ j : Fin (localWeightActiveSet n q (δ n) t).card,
        |(grid n (localWeightActiveIndex n q (δ n) t j).val - t) / δ n -
            (2 * (((j.val + 1 : ℕ) : ℝ) /
              ((localWeightActiveSet n q (δ n) t).card : ℝ)) - 1)| ≤ ε := by
  have hratioData := localWeightActiveSet_card_ratio_tendsto_two q t ht δ hδpos hδ0 hN
  have hcardpos := hratioData.1
  have hratio := hratioData.2
  let cardR : ℕ → ℝ := fun n => ((localWeightActiveSet n q (δ n) t).card : ℝ)
  let scale : ℕ → ℝ := fun n => (n : ℝ) * δ n
  have hratio1 : ∀ᶠ n : ℕ in atTop, 1 < cardR n / scale n :=
    hratio.eventually (Ioi_mem_nhds (by norm_num))
  have hn1 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  have hcardTop : Tendsto cardR atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [hratio1, hδpos, hn1, hN.eventually_ge_atTop (max b 0)] with
      n hrat hnδ hn hscaleB
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hspos : 0 < scale n := by exact mul_pos hnR hnδ
    have hbscale : b ≤ scale n := le_trans (le_max_left _ _) hscaleB
    have hcardeq : cardR n = (cardR n / scale n) * scale n := by
      field_simp [hspos.ne']
    rw [hcardeq]
    nlinarith
  have hinvScale : Tendsto (fun n : ℕ => (scale n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hN
  have hinvCard : Tendsto (fun n : ℕ => (cardR n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hcardTop
  have hratioErr : Tendsto (fun n : ℕ => |cardR n / scale n - 2|)
      atTop (𝓝 0) := by
    convert (hratio.sub tendsto_const_nhds).abs using 1 <;> norm_num
  have herr : Tendsto (fun n : ℕ =>
      (scale n)⁻¹ + |cardR n / scale n - 2| + 2 * (cardR n)⁻¹)
      atTop (𝓝 0) := by
    convert (hinvScale.add hratioErr).add (tendsto_const_nhds.mul hinvCard) using 1 <;>
      norm_num [div_eq_mul_inv]
  have ht0 : 0 < t := ht.1
  have heδL : ∀ᶠ n in atTop, δ n < t / 2 :=
    hδ0.eventually (Iio_mem_nhds (by linarith))
  have henL : ∀ᶠ n : ℕ in atTop, 1 / t ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (1 / t)
  intro ε hε
  have hevent : ∀ᶠ n : ℕ in atTop,
      (scale n)⁻¹ + |cardR n / scale n - 2| + 2 * (cardR n)⁻¹ < ε :=
    herr.eventually (Iio_mem_nhds hε)
  filter_upwards [hcardpos, hδpos, hn1, heδL, henL, hevent] with
    n hncard hnδ hn hnδL hnL hnerr
  have hn0 : 0 < n := by omega
  have hleft : 0 ≤ (n : ℝ) * (t - δ n) - 1 / 2 := by
    have hnt : 1 ≤ (n : ℝ) * t := by
      have := (div_le_iff₀ ht0).mp hnL
      nlinarith
    nlinarith
  intro j
  have hbound := localWeightActiveIndex_rank_coordinate_error
    n q hn0 (δ n) t hnδ hncard hleft j
  exact hbound.trans (by
    dsimp only [scale, cardR] at hnerr
    simpa only [one_div, div_eq_mul_inv, one_mul] using hnerr.le)

end Hurst
