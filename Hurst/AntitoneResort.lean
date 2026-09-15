import Hurst.CapstoneV3
import Hurst.FrozenSpectralCount
import Hurst.GeneralKHasSum

/-!
# The antitone re-sort of a nonneg square-summable sequence (the `hAnti` finisher)

The capstone `Hurst.CapstoneV3` carries the honest boundary hypothesis
`hAnti : Antitone val` for the P2-constructed eigenvalue enumeration `val`
(the hypothesis of `actualQ1LongStatistic_tendsto_secondChaos_v3`).  This file
lands the classical decreasing re-sort that discharges such hypotheses:

* `Hurst.antitoneResort` — the quantile / generalized-inverse construction
  `antitoneResort val n := sInf {s | lvlCount val s ≤ n}`, where `lvlCount val s`
  is the number of entries of `val` strictly above `s` (an `ℕ∞` level count).
* `Hurst.antitoneResort_antitone` — the re-sort is antitone BY CONSTRUCTION
  (the level sets are nested in `n`).
* `Hurst.antitoneResort_nonneg` — nonnegativity is inherited from `val ≥ 0`
  (any level below `0` already counts all indices).
* `Hurst.antitoneResort_le_of_lvlCount_le` and
  `Hurst.antitoneResort_gt_of_lt_lvlCount` — the level-counting characterizations
  (`lvlCount val d ≤ m → antitoneResort val m ≤ d`; at `d > 0`, the strict
  converse form `m < lvlCount val d → d < antitoneResort val m` holds).
* `Hurst.lvlCount_antitoneResort_eq` — the multiset identity (level-count form):
  for every `d > 0`, `#{m | antitoneResort val m > d} = #{m | val m > d}`.
* `Hurst.antitoneResort_exists` — the packaged existence statement: a nonneg
  square-summable sequence has a nonneg antitone re-sort with matching level
  counts above every positive threshold.

The hypotheses used throughout are ONLY: `val : ℕ → ℝ`, `∀ m, 0 ≤ val m`,
`Summable (fun m => val m * val m)`.  For the P2 enumeration these hold under
operator positivity (`Hurst.GeneralKHasSum`: `HS.summable_pow_of_posTOp` at
`k = 2` plus entrywise nonnegativity), so discharging the capstone's `hAnti`
on the resorted sequence is immediate.  The transfer of the `Summable` /
`HasSum` identities to the resorted sequence is the documented next step: the
level-count identity above every positive threshold landed here is exactly the
input of the layer-cake identity `MeasureTheory.lintegral_eq_lintegral_meas_lt`
composed with the counting-measure bridge `MeasureTheory.lintegral_count`
(both verified present in the pinned mathlib), which turns matching level
counts into matching `∑' ENNReal.ofReal (· ^ k)` and hence matching
`HasSum (· ^ k)` targets.
-/

open MeasureTheory Set

noncomputable section

namespace Hurst

/-- The level count: the number of indices whose value strictly exceeds `s`,
as an element of `ℕ∞` (`⊤` when infinitely many entries exceed `s`). -/
def lvlCount (val : ℕ → ℝ) (s : ℝ) : ℕ∞ :=
  Set.encard {m : ℕ | val m > s}

/-- The decreasing re-sort (quantile / generalized inverse): `antitoneResort val n`
is the `n`-th largest level of `val`. -/
def antitoneResort (val : ℕ → ℝ) (n : ℕ) : ℝ :=
  sInf {s : ℝ | lvlCount val s ≤ (n : ℕ∞)}

private theorem encard_Iio_nat (c : ℕ) : (Set.Iio c : Set ℕ).encard = (c : ℕ∞) := by
  rw [← Finset.coe_range, Set.Finite.encard_eq_coe_toFinset_card (Finset.finite_toSet _)]
  simp

section Resort

variable {val : ℕ → ℝ}

/-- A square-summable sequence is bounded. -/
theorem bounded_of_squareSummable (hnn : ∀ m, 0 ≤ val m)
    (hsum : Summable (fun m => val m * val m)) : ∃ M : ℝ, ∀ m, val m ≤ M := by
  refine ⟨(∑' m, val m * val m).sqrt, fun m => ?_⟩
  have hterm : val m * val m ≤ ∑' i, val i * val i := by
    have h := Summable.sum_le_tsum (s := {m})
      (fun i _ => mul_nonneg (hnn i) (hnn i)) hsum
    rwa [Finset.sum_singleton] at h
  refine le_of_not_gt fun hlt => ?_
  have h1 : Real.sqrt (∑' i, val i * val i) * Real.sqrt (∑' i, val i * val i)
      < val m * val m := by
    nlinarith [Real.sqrt_nonneg (∑' i, val i * val i), hlt]
  rw [Real.mul_self_sqrt (tsum_nonneg fun i => mul_nonneg (hnn i) (hnn i))] at h1
  linarith

/-- A square-summable nonneg sequence has a zero level count above its bound. -/
theorem lvlCount_zero_of_squareSummable (hnn : ∀ m, 0 ≤ val m)
    (hsum : Summable (fun m => val m * val m)) : ∃ s : ℝ, lvlCount val s = 0 := by
  obtain ⟨M, hM⟩ := bounded_of_squareSummable hnn hsum
  refine ⟨M + 1, ?_⟩
  have hempty : {m : ℕ | val m > M + 1} = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun m hm => ?_
    have hm' : val m > M + 1 := hm
    exact absurd hm' (by linarith [hM m])
  rw [lvlCount, hempty]
  exact Set.encard_empty

/-- The level set defining the re-sort is nonempty (square-summable case). -/
theorem levelSet_nonempty (hnn : ∀ m, 0 ≤ val m)
    (hsum : Summable (fun m => val m * val m)) (n : ℕ) :
    {s : ℝ | lvlCount val s ≤ (n : ℕ∞)}.Nonempty := by
  obtain ⟨s, hs⟩ := lvlCount_zero_of_squareSummable hnn hsum
  exact ⟨s, Set.mem_setOf.mpr (by rw [hs]; exact zero_le)⟩

/-- Every level admitted by the re-sort level set is nonneg (for `val ≥ 0`). -/
theorem levelSet_zero_lowerBound (hnn : ∀ m, 0 ≤ val m) (n : ℕ) :
    (0 : ℝ) ∈ lowerBounds {s : ℝ | lvlCount val s ≤ (n : ℕ∞)} := by
  intro s hs
  by_contra h
  have hs_neg : s < 0 := not_le.mp h
  have hsub : (Set.univ : Set ℕ) ⊆ {m : ℕ | val m > s} := fun m _ =>
    Set.mem_setOf.mpr (lt_of_lt_of_le hs_neg (hnn m))
  have huniv : (⊤ : ℕ∞) ≤ lvlCount val s := by
    have h1 : (Set.univ : Set ℕ).encard = (⊤ : ℕ∞) :=
      Set.encard_eq_top_iff.mpr Set.infinite_univ
    calc (⊤ : ℕ∞) = (Set.univ : Set ℕ).encard := h1.symm
      _ ≤ Set.encard {m : ℕ | val m > s} := Set.encard_mono hsub
      _ = lvlCount val s := rfl
  exact absurd (le_trans huniv hs) (not_le.mpr (ENat.coe_lt_top n))

theorem levelSet_bddBelow (hnn : ∀ m, 0 ≤ val m) (n : ℕ) :
    BddBelow {s : ℝ | lvlCount val s ≤ (n : ℕ∞)} :=
  ⟨0, levelSet_zero_lowerBound hnn n⟩

/-- **Core characterization**: if the `d`-level has at most `m` entries above it,
the re-sort is at most `d`. -/
theorem antitoneResort_le_of_lvlCount_le (hnn : ∀ m, 0 ≤ val m)
    (_hsum : Summable (fun m => val m * val m)) (m : ℕ) (d : ℝ)
    (h : lvlCount val d ≤ (m : ℕ∞)) : antitoneResort val m ≤ d :=
  csInf_le (levelSet_bddBelow hnn m) h

/-- **The re-sort is antitone** (by construction: the level sets are nested). -/
theorem antitoneResort_antitone (hnn : ∀ m, 0 ≤ val m)
    (hsum : Summable (fun m => val m * val m)) : Antitone (antitoneResort val) := by
  intro n n' hnn'
  refine csInf_le_csInf (levelSet_bddBelow hnn n') (levelSet_nonempty hnn hsum n) ?_
  intro s hs
  exact le_trans hs (ENat.coe_le_coe.mpr hnn')

/-- **The re-sort is nonneg** (for `val ≥ 0`). -/
theorem antitoneResort_nonneg (hnn : ∀ m, 0 ≤ val m)
    (hsum : Summable (fun m => val m * val m)) (n : ℕ) : 0 ≤ antitoneResort val n :=
  le_csInf (levelSet_nonempty hnn hsum n) (levelSet_zero_lowerBound hnn n)

/-- **Level-count finiteness above a positive threshold** (Markov-type consequence
of square-summability). -/
theorem lvlCount_lt_top_of_pos (hnn : ∀ m, 0 ≤ val m)
    (hsum : Summable (fun m => val m * val m)) (d : ℝ) (hd : 0 < d) : lvlCount val d < ⊤ := by
  refine Set.encard_lt_top_iff.mpr ?_
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hsum.tendsto_atTop_zero (d * d) (by positivity)
  refine Set.Finite.subset (Set.finite_Iio N) ?_
  intro m hm
  by_contra hge
  have h1 : val m * val m < d * d := by
    have h2 := hN m (not_lt.mp hge)
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (hnn m) (hnn m))] at h2
  have h3 : d * d ≤ val m * val m := by
    have hmd : d ≤ val m := le_of_lt hm
    nlinarith [hnn m, hmd]
  exact absurd h3 (not_le.mpr h1)

/-- **The strict level-counting characterization**: below the level count, the
re-sort strictly exceeds the threshold. -/
theorem antitoneResort_gt_of_lt_lvlCount (hnn : ∀ m, 0 ≤ val m)
    (hsum : Summable (fun m => val m * val m)) (m : ℕ) (d : ℝ) (hd : 0 < d)
    (hm : (m : ℕ∞) < lvlCount val d) : d < antitoneResort val m := by
  have hAfin : {m : ℕ | val m > d}.Finite :=
    Set.encard_lt_top_iff.mp (lvlCount_lt_top_of_pos hnn hsum d hd)
  by_cases hA : {m : ℕ | val m > d}.Nonempty
  · -- the min-gap argument over the finite level set
    set B : Finset ℕ := hAfin.toFinset with hBdef
    have hBne : B.Nonempty := (Set.Finite.toFinset_nonempty hAfin).mpr hA
    set ε : ℝ := (B.image (fun i => val i - d)).min' (Finset.image_nonempty.mpr hBne) with hεdef
    have hεpos : 0 < ε := by
      have hmem : ε ∈ B.image (fun i => val i - d) := Finset.min'_mem _ _
      obtain ⟨i, hiB, hie⟩ := Finset.mem_image.mp hmem
      have hid : d < val i := by
        have hi : i ∈ {m : ℕ | val m > d} := (Set.Finite.mem_toFinset hAfin).mp hiB
        exact hi
      have hεi : ε = val i - d := hie.symm
      linarith
    have hεle : ∀ i ∈ B, ε ≤ val i - d := fun i hi =>
      Finset.min'_le (B.image (fun i => val i - d)) (val i - d) (Finset.mem_image_of_mem _ hi)
    have hlb : (d + ε) ∈ lowerBounds {s : ℝ | lvlCount val s ≤ (m : ℕ∞)} := by
      intro s hs
      by_contra hlt
      have hsub : {m : ℕ | val m > d} ⊆ {i : ℕ | val i > s} := by
        intro i hi
        have hiB : i ∈ B := (Set.Finite.mem_toFinset hAfin).mpr hi
        have hvd : d < val i := hi
        have hide : d + ε ≤ val i := by
          have himg := hεle i hiB
          linarith
        have hvs : s < val i := by linarith
        exact Set.mem_setOf.mpr hvs
      have h1 : lvlCount val d ≤ lvlCount val s := Set.encard_mono hsub
      exact absurd (le_trans h1 hs) (not_le.mpr hm)
    show d < sInf {s : ℝ | lvlCount val s ≤ (m : ℕ∞)}
    linarith [le_csInf (levelSet_nonempty hnn hsum m) hlb, hεpos]
  · exfalso
    have hz : lvlCount val d = 0 := by
      have : {m : ℕ | val m > d} = ∅ :=
        Set.eq_empty_iff_forall_notMem.mpr fun m hm => hA ⟨m, hm⟩
      rw [lvlCount, this, Set.encard_empty]
    rw [hz] at hm
    exact absurd hm (by exact_mod_cast Nat.not_lt_zero m)

/-- **The multiset identity (level-count form)**: above every positive threshold,
the re-sort has exactly as many entries as the original sequence. -/
theorem lvlCount_antitoneResort_eq (hnn : ∀ m, 0 ≤ val m)
    (hsum : Summable (fun m => val m * val m)) (d : ℝ) (hd : 0 < d) :
    lvlCount (antitoneResort val) d = lvlCount val d := by
  have hfin : lvlCount val d < ⊤ := lvlCount_lt_top_of_pos hnn hsum d hd
  obtain ⟨c, hc⟩ : ∃ c : ℕ, (c : ℕ∞) = lvlCount val d :=
    ⟨(lvlCount val d).toNat, ENat.coe_toNat hfin.ne⟩
  have hset : {m : ℕ | antitoneResort val m > d} = Set.Iio c := by
    refine Set.ext fun m => ?_
    constructor
    · intro hmr
      refine Set.mem_Iio.mpr ?_
      by_contra hge
      have hle : lvlCount val d ≤ (m : ℕ∞) := by
        rw [← hc]
        exact_mod_cast not_lt.mp hge
      have hmr' : d < antitoneResort val m := hmr
      exact absurd hmr' (not_lt.mpr (antitoneResort_le_of_lvlCount_le hnn hsum m d hle))
    · intro hmc
      refine antitoneResort_gt_of_lt_lvlCount hnn hsum m d hd ?_
      rw [← hc]
      exact ENat.coe_lt_coe.mpr (Set.mem_Iio.mp hmc)
  rw [lvlCount, hset, ← hc, encard_Iio_nat]

/-- **The packaged existence theorem (the `hAnti` finisher)**: a nonneg
square-summable sequence admits a nonneg antitone re-sort whose level counts
above every positive threshold match the original sequence exactly. -/
theorem antitoneResort_exists (hnn : ∀ m, 0 ≤ val m)
    (hsum : Summable (fun m => val m * val m)) :
    ∃ val' : ℕ → ℝ, Antitone val' ∧ (∀ n, 0 ≤ val' n) ∧
      (∀ d : ℝ, 0 < d → lvlCount val' d = lvlCount val d) :=
  ⟨antitoneResort val, antitoneResort_antitone hnn hsum, antitoneResort_nonneg hnn hsum,
    fun d hd => lvlCount_antitoneResort_eq hnn hsum d hd⟩

end Resort

end Hurst
