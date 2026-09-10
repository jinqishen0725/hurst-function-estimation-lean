import Hurst.HolderTaylor

noncomputable section
open Set Filter Asymptotics
open scoped Topology
namespace Hurst

theorem taylorWithinEval_eq_taylorJet (f : ℝ → ℝ) (r : ℕ) (U : Set ℝ) (t y : ℝ)
    (hU : U∈𝓝 t) : taylorWithinEval f r U t y=taylorJet r f t y := by
  rw [taylor_within_apply,taylorJet,Fin.sum_univ_eq_sum_range
    (fun k : ℕ => iteratedDeriv k f t*(y-t)^k/(k.factorial:ℝ))]
  apply Finset.sum_congr rfl
  intro k _
  rw [iteratedDerivWithin_eq_of_mem_nhds f k U t hU,smul_eq_mul]
  ring

theorem taylorJet_isLittleO (f : ℝ → ℝ) (r : ℕ) (U : Set ℝ) (hU : Convex ℝ U)
    (hf : ContDiffOn ℝ r f U) (t : ℝ) (ht : U∈𝓝 t) :
    (fun y => f y-taylorJet r f t y) =o[𝓝 t] (fun y => (y-t)^r) := by
  have he := taylor_isLittleO hU (mem_of_mem_nhds ht) hf
  simpa only [nhdsWithin_eq_nhds.mpr ht,taylorWithinEval_eq_taylorJet f r U t _ ht] using he

theorem taylorJet_local_remainder (f : ℝ → ℝ) (r : ℕ) (U : Set ℝ) (hU : Convex ℝ U)
    (hf : ContDiffOn ℝ r f U) (t : ℝ) (ht : U∈𝓝 t) (ε : ℝ) (hε : 0<ε) :
    ∃ η>0,∀ y : ℝ,|y-t|<η → |f y-taylorJet r f t y|≤ε*|y-t|^r := by
  have he := (taylorJet_isLittleO f r U hU hf t ht).bound hε
  obtain ⟨η,hη,hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨η,hη,?_⟩
  intro y hy
  simpa only [Real.norm_eq_abs,abs_pow] using hball (by simpa only [Real.dist_eq] using hy)

end Hurst
