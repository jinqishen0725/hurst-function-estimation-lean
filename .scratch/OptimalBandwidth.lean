import Hurst.GridErrorLimit

noncomputable section
open Set Filter
open scoped Topology
namespace Hurst

def optimalLocalBandwidth (p : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) * Real.log n ^ 2) ^ (-1 / (2 * p + 1))

theorem optimalLocalBandwidth_pos (p : ℝ) (n : ℕ) (hn : 1 < n) : 0 < optimalLocalBandwidth p n := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hlog := Real.log_pos hnR
  exact Real.rpow_pos_of_pos (by positivity) _

theorem optimalLocalBandwidth_bias_balance (p : ℝ) (n : ℕ) :
    (optimalLocalBandwidth p n) ^ (2 * p) = (lowerBoundRate p n) ^ 2 := by
  unfold optimalLocalBandwidth lowerBoundRate
  rw [← Real.rpow_mul (by positivity), ← Real.rpow_natCast (((n : ℝ) * Real.log n ^ 2) ^ (-p / (2 * p + 1))) 2, ← Real.rpow_mul (by positivity)]
  congr 1
  ring

theorem optimalLocalBandwidth_variance_balance (p : ℝ) (hp : 1 ≤ p) (n : ℕ) (hn : 1 < n) :
    1 / ((n : ℝ) * optimalLocalBandwidth p n * Real.log n ^ 2) = (lowerBoundRate p n) ^ 2 := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hlog := Real.log_pos hnR
  have hx : 0 < (n : ℝ) * Real.log n ^ 2 := by positivity
  have hd : 2 * p + 1 ≠ 0 := by linarith
  unfold optimalLocalBandwidth lowerBoundRate
  rw [← Real.rpow_natCast (((n : ℝ) * Real.log n ^ 2) ^ (-p / (2 * p + 1))) 2, ← Real.rpow_mul hx.le]
  calc
    _ = (((n : ℝ) * Real.log n ^ 2) ^ (1 : ℝ) * ((n : ℝ) * Real.log n ^ 2) ^ (-1 / (2 * p + 1)))⁻¹ := by rw [Real.rpow_one]; ring
    _ = ((n : ℝ) * Real.log n ^ 2) ^ (-(1 + -1 / (2 * p + 1))) := by rw [← Real.rpow_add hx, Real.rpow_neg hx.le]
    _ = _ := by congr 1; field_simp; ring

theorem optimalLocalBandwidth_upper (p : ℝ) (hp : 1 ≤ p) (n : ℕ) (hn : 0 < n) (hlog : 1 ≤ Real.log n) :
    optimalLocalBandwidth p n ≤ (n : ℝ) ^ (-1 / (2 * p + 1)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold optimalLocalBandwidth
  apply Real.rpow_le_rpow_of_nonpos hnR
  · nlinarith [sq_nonneg (Real.log (n : ℝ) - 1)]
  · have hd : 0 < 2 * p + 1 := by linarith
    exact div_nonpos_of_nonpos_of_nonneg (by norm_num) hd.le

/-- The bandwidth tends to zero while retaining an unbounded number of local grid points. -/
theorem optimalLocalBandwidth_eventual_design (p N₀ : ℝ) (hp : 1 ≤ p) :
    ∀ᶠ n : ℕ in atTop,
      1 < n ∧ 0 < optimalLocalBandwidth p n ∧ optimalLocalBandwidth p n ≤ 1 / 2 ∧
      N₀ ≤ (n : ℝ) * optimalLocalBandwidth p n ∧
      (1 / (n : ℝ)) ≤ (lowerBoundRate p n) ^ 2 ∧ 1 ≤ Real.log n := by
  have hd : 0 < 2 * p + 1 := by linarith
  have hα : 0 < 1 / (2 * p + 1) := by positivity
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (-1 / (2 * p + 1))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_div] using! (tendsto_rpow_neg_atTop hα).comp tendsto_natCast_atTop_atTop
  have hsmall := hpow.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hlog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  have hlogsmall := (nat_log_power_div_rpow_tendsto (1 / 2) (by norm_num) 2).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  have hlogα := (nat_log_power_div_rpow_tendsto (1 / (2 * p + 1)) hα 2).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  have hgrowth : ∀ᶠ n : ℕ in atTop, N₀ ≤ (n : ℝ) ^ (1 / 2 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop N₀
  filter_upwards [eventually_ge_atTop 2, hsmall, hlog, hlogsmall, hlogα, hgrowth] with n hn hs hL hLs hLa hgrow
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnR : (0 : ℝ) < n := by positivity
  have hℓ : 0 < Real.log (n : ℝ) := by linarith
  have hx : 0 < (n : ℝ) * Real.log n ^ 2 := by positivity
  have hbpos := optimalLocalBandwidth_pos p n (by omega)
  have hup := optimalLocalBandwidth_upper p hp n (by omega) hL
  have hLogsq : Real.log (n : ℝ) ^ 2 ≤ (n : ℝ) ^ (1 / 2 : ℝ) :=
    (div_le_one (Real.rpow_pos_of_pos hnR _)).mp hLs.le
  have hblow : (n : ℝ) ^ (-1 / 2 : ℝ) ≤ optimalLocalBandwidth p n := by
    have hmul : (n : ℝ) * Real.log n ^ 2 ≤ (n : ℝ) ^ (3 / 2 : ℝ) := by
      calc
        _ ≤ (n : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) := mul_le_mul_of_nonneg_left hLogsq hnR.le
        _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hnR]; norm_num
    have he := Real.rpow_le_rpow_of_nonpos hx hmul (show -1 / (2 * p + 1) ≤ 0 from div_nonpos_of_nonpos_of_nonneg (by norm_num) hd.le)
    rw [← Real.rpow_mul hnR.le] at he
    apply le_trans _ he
    apply Real.rpow_le_rpow_of_exponent_le hn1
    rw [show (3 / 2 : ℝ) * (-1 / (2 * p + 1)) = (-3 / 2) / (2 * p + 1) by ring]
    apply (le_div_iff₀ hd).mpr
    nlinarith
  have hgrow' : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (n : ℝ) * optimalLocalBandwidth p n := by
    have he := mul_le_mul_of_nonneg_left hblow hnR.le
    have hid : (n : ℝ) * (n : ℝ) ^ (-1 / 2 : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) := by
      calc
        _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-1 / 2 : ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hnR]; norm_num
    rwa [hid] at he
  have hblog : optimalLocalBandwidth p n * Real.log n ^ 2 ≤ 1 := by
    have he := mul_le_mul_of_nonneg_right hup (sq_nonneg (Real.log (n : ℝ)))
    have hid : (n : ℝ) ^ (-1 / (2 * p + 1)) * Real.log n ^ 2 = Real.log n ^ 2 / (n : ℝ) ^ (1 / (2 * p + 1)) := by
      rw [neg_div, Real.rpow_neg hnR.le]
      ring
    rw [hid] at he
    exact he.trans hLa.le
  refine ⟨by omega, hbpos, hup.trans hs.le, hgrow.trans hgrow', ?_, hL⟩
  rw [← optimalLocalBandwidth_variance_balance p hp n (by omega)]
  have hden : (n : ℝ) * optimalLocalBandwidth p n * Real.log n ^ 2 ≤ n := by
    have he := mul_le_mul_of_nonneg_left hblog hnR.le
    nlinarith
  exact one_div_le_one_div_of_le (by positivity) hden

end Hurst
