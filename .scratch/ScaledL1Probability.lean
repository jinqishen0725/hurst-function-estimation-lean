import Hurst.InverseL1Limit

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Hurst

theorem scaled_L1_probability_tendsto {Ω : ℕ → Type*} [∀ n,MeasurableSpace (Ω n)]
    (P : ∀ n,Measure (Ω n)) (R : ∀ n,Ω n → ℝ) (ρ : ℕ → ℝ)
    (hR : ∀ᶠ n in atTop,Integrable (R n) (P n))
    (hρ : ∀ᶠ n in atTop,0<ρ n)
    (hlim : Tendsto (fun n => (∫ ω,|R n ω| ∂P n)/ρ n) atTop (𝓝 0))
    (ε : ℝ) (hε : 0<ε) :
    Tendsto (fun n => (P n).real {ω | ε≤|R n ω|/ρ n}) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun n => measureReal_nonneg)) ?_
    (by simpa only [zero_div] using hlim.div_const ε)
  filter_upwards [hR,hρ] with n hn hρn
  have he : {ω | ε≤|R n ω|/ρ n}={ω | ε*ρ n≤|R n ω|} := by
    ext ω
    exact le_div_iff₀ hρn
  rw [he]
  have hm := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall (fun ω => abs_nonneg (R n ω))) hn.abs (ε*ρ n)
  have hb : (P n).real {ω | ε*ρ n≤|R n ω|}≤(∫ ω,|R n ω| ∂P n)/(ε*ρ n) := by
    apply (le_div_iff₀ (mul_pos hε hρn)).mpr
    nlinarith [hm]
  exact hb.trans_eq (by ring)

end Hurst
