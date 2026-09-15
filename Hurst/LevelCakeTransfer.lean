import Hurst.AntitoneResort
import Hurst.GeneralKHasSum
import Hurst.P6LawIdentification

/-!
# The level-cake transfer: the HasSum of a resorted sequence via matching level counts

This file closes the documented next step of `Hurst.AntitoneResort` (see its gap note):
the level-count identity `∀ d > 0, #{m | val' m > d} = #{m | val m > d}` (the output of
`Hurst.lvlCount_antitoneResort_eq`) is promoted, by the discrete layer-cake route, to the
`HasSum` / `Summable` / tsum identity of the `k`-th powers for every `k ≥ 1`:

* `Hurst.real_pow_level_mem` / `Hurst.level_pow_set_eq` — the `√`-substitution bridge:
  for `u ≥ 0`, `t > 0`, `k ≥ 1`, `t ^ (k⁻¹) < u ↔ t < u ^ k`, so the level sets of the
  `k`-th powers are the level sets of the original sequence at the threshold `t ^ (k⁻¹)`.
* `Hurst.tsum_ofReal_eq_lintegral_tail` — the counting-measure bridge + layer cake:
  for a nonneg sequence `g`, `∑' n, ENNReal.ofReal (g n) = ∫⁻ t in Ioi 0, count {n | t < g n}`
  (mathlib: `MeasureTheory.lintegral_count`, `MeasureTheory.lintegral_eq_lintegral_meas_lt`,
  `MeasureTheory.Measure.count_apply = Set.encard`).
* `Hurst.tsum_ofReal_pow_eq_of_level_eq` — matching level counts above every positive
  threshold give matching `∑' ENNReal.ofReal (· ^ k)` (the integrands agree POINTWISE on
  `Ioi 0`, so no a.e. argument is needed).
* `Hurst.hasSum_pow_of_antitoneResort` — the mission statement: under the level-count
  identity and `Summable (val ^ k)`, the resorted sequence satisfies
  `HasSum (fun n => val' n ^ k) (∑' n, val n ^ k)` (and hence its own `Summable`/tsum
  identity, `Hurst.summable_pow_of_antitoneResort` / `Hurst.tsum_pow_of_antitoneResort`).
* `Hurst.hasSum_pow_of_resort_lvlCount` — the `hAnti` consumption: instantiating the
  transfer at `val' = Hurst.antitoneResort val` via `Hurst.lvlCount_antitoneResort_eq`,
  i.e. the antitone re-sort of a nonneg sequence inherits the `HasSum` obligations.

The `k ≥ 1` bound is honest: for `k ≥ 2` the hypothesis `Summable (val ^ k)` is supplied by
the interpolation layer `HS.summable_pow_of_posTOp` (`Hurst.GeneralKHasSum`); at `k = 1`
square-summability alone does not imply summability of `val`.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace Hurst

/-! ### The pow/rpow threshold bridge (√-substitution) -/

/-- For `u ≥ 0`, `t > 0`, `k ≥ 1`: `t ^ (k⁻¹) < u ↔ t < u ^ k`. -/
private theorem real_pow_level_mem {k : ℕ} (hk : 1 ≤ k) {t : ℝ} (ht : 0 < t) {u : ℝ}
    (hu : 0 ≤ u) : t ^ ((k : ℝ)⁻¹) < u ↔ t < u ^ k := by
  have hkpos : (0:ℝ) < (k : ℝ) := by exact_mod_cast lt_of_lt_of_le zero_lt_one hk
  have hk0 : (k : ℝ) ≠ 0 := ne_of_gt hkpos
  have hkmul : (k : ℝ)⁻¹ * (k : ℝ) = 1 := by field_simp
  have hsnn : 0 ≤ t ^ ((k : ℝ)⁻¹) := Real.rpow_nonneg (le_of_lt ht) _
  rw [← Real.rpow_natCast u k]
  constructor
  · intro h
    have h2 := (Real.rpow_lt_rpow_iff hsnn hu hkpos).mpr h
    rwa [← Real.rpow_mul hsnn, hkmul, Real.rpow_one] at h2
  · intro h
    have h2 := (Real.rpow_lt_rpow_iff hsnn hu hkpos).mp h
    rwa [← Real.rpow_mul hsnn, hkmul, Real.rpow_one] at h2

/-- The level sets of the `k`-th powers are the level sets of the original sequence at
the `√`-substituted threshold. -/
private theorem level_pow_set_eq (val : ℕ → ℝ) (hnn : ∀ n, 0 ≤ val n) (k : ℕ) (hk : 1 ≤ k)
    (t : ℝ) (ht : 0 < t) : {n : ℕ | t < val n ^ k} = {n : ℕ | t ^ ((k : ℝ)⁻¹) < val n} := by
  ext n
  simp only [Set.mem_setOf_eq]
  exact (real_pow_level_mem hk ht (hnn n)).symm

/-! ### The counting-measure bridge + layer cake for a nonneg sequence -/

/-- **The counting-measure bridge + layer cake**: for a nonneg sequence `g : ℕ → ℝ`,
`∑' n, ENNReal.ofReal (g n) = ∫⁻ t in Ioi 0, count {n | t < g n}` — `lintegral_count`
(the counting-measure bridge) composed with `lintegral_eq_lintegral_meas_lt` (the layer
cake); the counting measure of a set is its `encard` (`Measure.count_apply`). -/
private theorem tsum_ofReal_eq_lintegral_tail (g : ℕ → ℝ) (hnn : ∀ n, 0 ≤ g n) :
    (∑' n, ENNReal.ofReal (g n))
      = ∫⁻ t in Ioi (0:ℝ), MeasureTheory.Measure.count {n : ℕ | t < g n} := by
  rw [← MeasureTheory.lintegral_count (fun n => ENNReal.ofReal (g n)),
    MeasureTheory.lintegral_eq_lintegral_meas_lt MeasureTheory.Measure.count
      (Filter.Eventually.of_forall fun _ => zero_le)
      ((measurable_of_countable (fun n => g n)).aemeasurable)]

/-- The counting measure on ℕ of any set is its `encard`. -/
private theorem count_eq_encard (S : Set ℕ) : MeasureTheory.Measure.count S = S.encard :=
  MeasureTheory.Measure.count_apply (S.to_countable.measurableSet)

/-! ### Matching level counts give matching ENNReal power tsums -/

/-- **The level-cake identification (the ENNReal layer)**: if `val` and `val'` are nonneg
and their level counts above every positive threshold agree, then the `k`-th-power tsums
agree in `ℝ≥0∞` for every `k ≥ 1`. -/
private theorem tsum_ofReal_pow_eq_of_level_eq {val val' : ℕ → ℝ}
    (hnn : ∀ n, 0 ≤ val n ∧ 0 ≤ val' n)
    (hLevel : ∀ d : ℝ, 0 < d → Set.encard {m : ℕ | val' m > d} = Set.encard {m | val m > d})
    (k : ℕ) (hk : 1 ≤ k) :
    (∑' n, ENNReal.ofReal (val' n ^ k)) = (∑' n, ENNReal.ofReal (val n ^ k)) := by
  rw [tsum_ofReal_eq_lintegral_tail (fun n => val' n ^ k)
      (fun n => pow_nonneg ((hnn n).2) k),
    tsum_ofReal_eq_lintegral_tail (fun n => val n ^ k)
      (fun n => pow_nonneg ((hnn n).1) k)]
  refine MeasureTheory.setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 < t := ht
  have hs0 : 0 < t ^ ((k : ℝ)⁻¹) := Real.rpow_pos_of_pos ht _
  have hsnn : 0 ≤ t ^ ((k : ℝ)⁻¹) := le_of_lt hs0
  have hrew1 : MeasureTheory.Measure.count {n : ℕ | t < val' n ^ k}
      = MeasureTheory.Measure.count {n : ℕ | val' n > t ^ ((k : ℝ)⁻¹)} := by
    rw [level_pow_set_eq val' (fun n => (hnn n).2) k hk t ht0]
  have hrew2 : MeasureTheory.Measure.count {n : ℕ | val n > t ^ ((k : ℝ)⁻¹)}
      = MeasureTheory.Measure.count {n : ℕ | t < val n ^ k} := by
    rw [level_pow_set_eq val (fun n => (hnn n).1) k hk t ht0]
  calc MeasureTheory.Measure.count {n : ℕ | t < val' n ^ k}
      _ = MeasureTheory.Measure.count {n : ℕ | val' n > t ^ ((k : ℝ)⁻¹)} := hrew1
      _ = Set.encard {m : ℕ | val' m > t ^ ((k : ℝ)⁻¹)} := count_eq_encard _
      _ = Set.encard {m : ℕ | val m > t ^ ((k : ℝ)⁻¹)} := hLevel _ hs0
      _ = MeasureTheory.Measure.count {n : ℕ | val n > t ^ ((k : ℝ)⁻¹)} :=
        (count_eq_encard _).symm
      _ = MeasureTheory.Measure.count {n : ℕ | t < val n ^ k} := hrew2

/-! ### The HasSum transfer to the resorted sequence -/

/-- **The mission theorem (the level-cake HasSum transfer)**: if `val, val' : ℕ → ℝ` are
nonneg with matching level counts above every positive threshold
(`hLevel`, the output shape of `Hurst.lvlCount_antitoneResort_eq`), and the `k`-th power
series of `val` converges (`Summable`, `k ≥ 1`), then the resorted sequence `val'` has the
same `k`-th power series value:
`HasSum (fun n => val' n ^ k) (∑' n, val n ^ k)`.
In particular `∑' n, val' n ^ k = ∑' n, val n ^ k`
(`Hurst.tsum_pow_of_antitoneResort`) and `val' ^ k` is summable
(`Hurst.summable_pow_of_antitoneResort`). -/
theorem hasSum_pow_of_antitoneResort {val val' : ℕ → ℝ}
    (hnn : ∀ n, 0 ≤ val n ∧ 0 ≤ val' n)
    (hLevel : ∀ d : ℝ, 0 < d → Set.encard {m : ℕ | val' m > d} = Set.encard {m | val m > d})
    (k : ℕ) (hk : 1 ≤ k) (hsum : Summable (fun n => val n ^ k)) :
    HasSum (fun n => val' n ^ k) (∑' n, val n ^ k) := by
  have hE := tsum_ofReal_pow_eq_of_level_eq hnn hLevel k hk
  have hfin : (∑' n, ENNReal.ofReal (val' n ^ k)) ≠ ∞ := by
    rw [hE]
    exact ENNReal.ofReal_ne_top
  have hH := ENNReal.hasSum_toReal hfin
  have hterm : ∀ n, (ENNReal.ofReal (val' n ^ k)).toReal = val' n ^ k :=
    fun n => ENNReal.toReal_ofReal ((hnn n).2)
  have htarget : (∑' n, (ENNReal.ofReal (val' n ^ k)).toReal) = (∑' n, val n ^ k) := by
    calc (∑' n, (ENNReal.ofReal (val' n ^ k)).toReal)
        = ((∑' n, ENNReal.ofReal (val' n ^ k))).toReal :=
          (ENNReal.tsum_toReal_eq (fun n => ENNReal.ofReal_ne_top)).symm
      _ = (ENNReal.ofReal (∑' n, val n ^ k)).toReal := by rw [hE]
      _ = (∑' n, val n ^ k) :=
          ENNReal.toReal_ofReal (tsum_nonneg fun n => pow_nonneg (hnn n).1 k)
  rw [htarget] at hH
  exact hH.congr hterm

/-- The resorted sequence's `k`-th power series is summable. -/
theorem summable_pow_of_antitoneResort {val val' : ℕ → ℝ}
    (hnn : ∀ n, 0 ≤ val n ∧ 0 ≤ val' n)
    (hLevel : ∀ d : ℝ, 0 < d → Set.encard {m : ℕ | val' m > d} = Set.encard {m | val m > d})
    (k : ℕ) (hk : 1 ≤ k) (hsum : Summable (fun n => val n ^ k)) :
    Summable (fun n => val' n ^ k) :=
  (hasSum_pow_of_antitoneResort hnn hLevel k hk hsum).summable

/-- The tsum identity: the level-cake transfer upgrades to the equality of the
`k`-th-power tsums. -/
theorem tsum_pow_of_antitoneResort {val val' : ℕ → ℝ}
    (hnn : ∀ n, 0 ≤ val n ∧ 0 ≤ val' n)
    (hLevel : ∀ d : ℝ, 0 < d → Set.encard {m : ℕ | val' m > d} = Set.encard {m | val m > d})
    (k : ℕ) (hk : 1 ≤ k) (hsum : Summable (fun n => val n ^ k)) :
    (∑' n, val' n ^ k) = (∑' n, val n ^ k) :=
  (hasSum_pow_of_antitoneResort hnn hLevel k hk hsum).tsum_eq

/-! ### The `hAnti` consumption: the antitone re-sort inherits the HasSum obligations -/

/-- **The `hAnti` finisher**: the antitone re-sort of a nonneg square-summable sequence
inherits the `k`-th power `HasSum` for every `k ≥ 1` with `Summable (val ^ k)` — the
transfer instantiated at `val' = Hurst.antitoneResort val` through
`Hurst.lvlCount_antitoneResort_eq`. -/
theorem hasSum_pow_of_resort_lvlCount (val : ℕ → ℝ) (hnn : ∀ n, 0 ≤ val n)
    (hsq : Summable (fun n => val n * val n)) (k : ℕ) (hk : 1 ≤ k)
    (hsum : Summable (fun n => val n ^ k)) :
    HasSum (fun n => antitoneResort val n ^ k) (∑' n, val n ^ k) :=
  hasSum_pow_of_antitoneResort
    (val := val) (val' := antitoneResort val)
    (fun n => ⟨hnn n, antitoneResort_nonneg hnn hsq n⟩)
    (fun d hd => lvlCount_antitoneResort_eq hnn hsq d hd)
    k hk hsum

end Hurst

end
