import Hurst.CapstoneV3Closed
import Hurst.GeneralKHasSumFinal
import Hurst.EquivalentKernel

/-! Independent applicability audit of the session-3 spectral endpoint.
This leaves the implementation unchanged and checks the exact `hconst` premise.
-/

namespace Hurst

theorem session3_fullChain_all_rows_impossible (t gamma : ℝ) :
    ¬ (∀ n : ℕ,
      0 < (localWeightActiveSet n 1 ((n : ℝ) ^ (-gamma)) t).card) := by
  intro hm
  have hzero := hm 0
  simp [localWeightActiveSet] at hzero

theorem session3_indicator_const_forces_zero (omega : ℝ → ℝ)
    (hconst : ∀ x y : ℝ, (HS.I : Set ℝ).indicator omega x =
      (HS.I : Set ℝ).indicator omega y) :
    ∀ x ∈ HS.I, omega x = 0 := by
  intro x hx
  have h := hconst x 2
  rw [Set.indicator_of_mem hx, Set.indicator_of_notMem
    (show (2 : ℝ) ∉ HS.I by norm_num [HS.I])] at h
  exact h

theorem session3_equivalentKernel_hconst_impossible (r : ℕ) :
    ¬ (∀ x y : ℝ, (HS.I : Set ℝ).indicator (equivalentKernel r) x =
      (HS.I : Set ℝ).indicator (equivalentKernel r) y) := by
  intro hconst
  have hz := session3_indicator_const_forces_zero (equivalentKernel r) hconst
  have hi : (∫ x in (-1 : ℝ)..1, equivalentKernel r x) = 0 := by
    calc
      (∫ x in (-1 : ℝ)..1, equivalentKernel r x) =
          ∫ x in (-1 : ℝ)..1, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact hz x (by simpa [HS.I, Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hx)
      _ = 0 := by simp
  have hone := equivalentKernel_integral r
  linarith

end Hurst

#print axioms Hurst.session3_indicator_const_forces_zero
#print axioms Hurst.session3_equivalentKernel_hconst_impossible
#print axioms Hurst.session3_fullChain_all_rows_impossible
#print axioms HS.rieszSpectrumVal_hGen
#print axioms HS.hBridge
#print axioms HS.hPair_riesz
#print axioms Hurst.actualQ1LongStatistic_tendsto_secondChaos_v3_closed_antitone
