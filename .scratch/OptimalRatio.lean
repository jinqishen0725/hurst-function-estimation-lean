import Hurst.OptimalBandwidth
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

noncomputable section
open Set Filter
open scoped Topology
namespace Hurst

theorem nat_succ_cast_div_self_tendsto_one :
    Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
  have h : Tendsto (fun n : ℕ => (1 : ℝ) + 1 / n) atTop (𝓝 (1 + 0)) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  have heq : (fun n : ℕ => (1 : ℝ) + 1 / n) =ᶠ[atTop]
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / (n : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    field_simp
    simp [Nat.cast_add, Nat.cast_one, add_comm]
  simpa using h.congr' heq

theorem nat_succ_log_div_log_tendsto_one :
    Tendsto (fun n : ℕ => Real.log (n + 1) / Real.log n) atTop (𝓝 1) := by
  have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have harg : Tendsto (fun n : ℕ => (1 : ℝ) + 1 / n) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hinv
  have hsmall : Tendsto (fun n : ℕ => Real.log ((1 : ℝ) + 1 / n)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (Real.continuousAt_log one_ne_zero).tendsto.comp harg
  have hlogtop : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hfrac : Tendsto (fun n : ℕ => Real.log ((1 : ℝ) + 1 / n) / Real.log n)
      atTop (𝓝 0) := hsmall.div_atTop hlogtop
  have h : Tendsto (fun n : ℕ => (1 : ℝ) +
      Real.log ((1 : ℝ) + 1 / n) / Real.log n) atTop (𝓝 (1 + 0)) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add hfrac
  have heq : (fun n : ℕ => (1 : ℝ) +
      Real.log ((1 : ℝ) + 1 / n) / Real.log n) =ᶠ[atTop]
      (fun n : ℕ => Real.log (n + 1) / Real.log n) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hnR : (0 : ℝ) < n := by positivity
    have hratio : (0 : ℝ) < 1 + 1 / n := by positivity
    have hmul : (n + 1 : ℝ) = (n : ℝ) * (1 + 1 / n) := by
      field_simp
    rw [hmul, Real.log_mul hnR.ne' hratio.ne']
    have hlogne : Real.log (n : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hn)).ne'
    field_simp
  simpa using h.congr' heq

/-- The effective optimal-bandwidth sample size changes by a relative `o(1)`
from one grid size to the next. -/
theorem optimalLocalEffectiveSize_succ_ratio_tendsto_one
    (p : ℝ) (hp : 1 ≤ p) :
    Tendsto (fun n : ℕ =>
      (((n + 1 : ℕ) : ℝ) * optimalLocalBandwidth p (n + 1)) /
        ((n : ℝ) * optimalLocalBandwidth p n)) atTop (𝓝 1) := by
  let α : ℝ := -1 / (2 * p + 1)
  have hnat := nat_succ_cast_div_self_tendsto_one
  have hlog := nat_succ_log_div_log_tendsto_one
  have hbase : Tendsto (fun n : ℕ =>
      ((((n + 1 : ℕ) : ℝ) * Real.log (n + 1) ^ 2) /
        ((n : ℝ) * Real.log n ^ 2))) atTop (𝓝 1) := by
    convert hnat.mul (hlog.pow 2) using 1
    · funext n
      ring
    · norm_num
  have hpow : Tendsto (fun n : ℕ =>
      (((((n + 1 : ℕ) : ℝ) * Real.log (n + 1) ^ 2) /
        ((n : ℝ) * Real.log n ^ 2)) ^ α)) atTop (𝓝 1) := by
    simpa using hbase.rpow_const (p := α) (Or.inl one_ne_zero)
  have hprod : Tendsto (fun n : ℕ =>
      (((n + 1 : ℕ) : ℝ) / (n : ℝ)) *
        (((((n + 1 : ℕ) : ℝ) * Real.log (n + 1) ^ 2) /
          ((n : ℝ) * Real.log n ^ 2)) ^ α)) atTop (𝓝 1) := by
    simpa using hnat.mul hpow
  apply hprod.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn0 : (0 : ℝ) < n := by positivity
  have hnp0 : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hln : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hlnp : 0 < Real.log ((n + 1 : ℕ) : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n + 1 by omega))
  unfold optimalLocalBandwidth
  dsimp only [α]
  rw [Real.div_rpow (by positivity) (by positivity)]
  simp only [Nat.cast_add, Nat.cast_one, add_comm]
  field_simp [hn0.ne', hnp0.ne', hln.ne', hlnp.ne']

end Hurst
