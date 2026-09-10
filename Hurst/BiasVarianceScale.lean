import Hurst.MeanLimitTransfer
import Hurst.Moments
import Hurst.OptimalMeanLeading

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Hurst

theorem mse_scale_bound_of_mean_variance {Ω : ℕ → Type*} [∀ n,MeasurableSpace (Ω n)]
    (P : ∀ n,Measure (Ω n)) [∀ n,IsProbabilityMeasure (P n)] (X : ∀ n,Ω n → ℝ)
    (hX : ∀ᶠ n in atTop,MemLp (X n) 2 (P n)) (μ L ρ : ℕ → ℝ) (β V : ℝ) (hV : 0≤V)
    (hpos : ∀ᶠ n in atTop,0<L n*ρ n)
    (hmean : Tendsto (fun n => ((∫ ω,X n ω ∂P n)-μ n)/(L n*ρ n)) atTop (𝓝 β))
    (hvar : ∀ᶠ n in atTop,Var[X n;P n]≤V*(L n)^2*(ρ n)^2) :
    ∃ A≥0,∀ᶠ n in atTop,(∫ ω,(X n ω-μ n)^2 ∂P n)≤A^2*(L n)^2*(ρ n)^2 := by
  let D := |β|+1
  let A := Real.sqrt (V+D^2)
  have hA : A^2=V+D^2 := Real.sq_sqrt (by positivity)
  refine ⟨A,Real.sqrt_nonneg _,?_⟩
  have hb : ∀ᶠ n in atTop,|((∫ ω,X n ω ∂P n)-μ n)/(L n*ρ n)|≤D :=
    hmean.abs.eventually_le_const (by dsimp [D]; linarith)
  filter_upwards [hX,hpos,hvar,hb] with n hn hp hv hb
  rw [mse_decomposition (X n) (μ n) hn,hA]
  rw [abs_div,abs_of_pos hp] at hb
  have hh := (div_le_iff₀ hp).mp hb
  have hsq := pow_le_pow_left₀ (abs_nonneg _) hh 2
  rw [sq_abs] at hsq
  nlinarith

theorem optimalLocalBandwidth_raw_variance_balance (r n : ℕ) (hn : 1<n) :
    1/((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n) =
      (Real.log n)^2*((optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1))^2 := by
  have hp : (1:ℝ)≤(r:ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) r]
  have hnR : (1:ℝ)<n := by exact_mod_cast hn
  have hlog := Real.log_pos hnR
  have hδ := optimalLocalBandwidth_pos ((r:ℝ)+1) n hn
  have he := optimalLocalBandwidth_variance_balance ((r:ℝ)+1) hp n hn
  rw [← optimalLocalBandwidth_bias_balance] at he
  have hpow : (optimalLocalBandwidth ((r:ℝ)+1) n)^(2*((r:ℝ)+1)) =
      ((optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1))^2 := by
    rw [← pow_mul,← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  rw [hpow] at he
  calc
    _ = (Real.log n)^2*(1/((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n*(Real.log n)^2)) := by field_simp
    _ = _ := by rw [he]

end Hurst
