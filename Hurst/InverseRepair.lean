import Hurst.Scaling
import Hurst.Moments
import Mathlib.Topology.Order.IntermediateValue

/-! A complete clipped-calibration theorem, independent of the mBm model.
It supplies the nonlinear finite-sample step needed by Theorems 3.4 and 4.3.
The stochastic error of the input estimator remains a separate obligation. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Topology
namespace Hurst

/-- A decreasing function with a quantitative lower bound on its slope. -/
def StrongDecrease (f : ℝ → ℝ) (a b m : ℝ) : Prop :=
  ∀ x ∈ Icc a b, ∀ z ∈ Icc a b, x ≤ z → m*(z-x) ≤ f x-f z

/-- Exact inversion inside the range, endpoint clipping outside it. -/
def ClippedInverseAt (f : ℝ → ℝ) (a b y x : ℝ) : Prop :=
  x ∈ Icc a b ∧ (f x = y ∨ (x=a ∧ f a ≤ y) ∨ (x=b ∧ y ≤ f b))

theorem clippedInverse_exists (f : ℝ → ℝ) (a b y : ℝ) (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) : ∃ x, ClippedInverseAt f a b y x := by
  by_cases ha : f a ≤ y
  · exact ⟨a, ⟨⟨le_rfl, hab⟩, Or.inr (Or.inl ⟨rfl, ha⟩)⟩⟩
  · by_cases hb : y ≤ f b
    · exact ⟨b, ⟨⟨hab, le_rfl⟩, Or.inr (Or.inr ⟨rfl, hb⟩)⟩⟩
    · obtain ⟨x, hx, he⟩ := intermediate_value_Icc' hab hf
        (show y ∈ Icc (f b) (f a) from ⟨le_of_not_ge hb, le_of_not_ge ha⟩)
      exact ⟨x, hx, Or.inl he⟩

def boundedInverse (f : ℝ → ℝ) (a b y : ℝ) : ℝ := by
  classical
  exact if h : ∃ x, ClippedInverseAt f a b y x then Classical.choose h else a

theorem boundedInverse_spec (f : ℝ → ℝ) (a b y : ℝ) (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) :
    ClippedInverseAt f a b y (boundedInverse f a b y) := by
  have he := clippedInverse_exists f a b y hab hf
  classical
  simp only [boundedInverse, dif_pos he]
  exact Classical.choose_spec he

theorem clippedInverse_gap (f : ℝ → ℝ) (a b m y w x z : ℝ)
    (hf : StrongDecrease f a b m)
    (hx : ClippedInverseAt f a b y x) (hz : ClippedInverseAt f a b w z)
    (hxz : x < z) : m*(z-x) ≤ y-w := by
  have hfx : f x ≤ y := by
    rcases hx.2 with h | h | h
    · exact h.le
    · simpa [h.1] using h.2
    · have hb := hz.1.2; rw [h.1] at hxz; linarith
  have hfz : w ≤ f z := by
    rcases hz.2 with h | h | h
    · exact h.ge
    · have ha := hx.1.1; rw [h.1] at hxz; linarith
    · simpa [h.1] using h.2
  have hd := hf x hx.1 z hz.1 hxz.le
  linarith

theorem clippedInverse_contraction (f : ℝ → ℝ) (a b m y w x z : ℝ)
    (hm : 0 < m) (hf : StrongDecrease f a b m)
    (hx : ClippedInverseAt f a b y x) (hz : ClippedInverseAt f a b w z) :
    |x-z| ≤ |y-w|/m := by
  apply (le_div_iff₀ hm).mpr
  rcases lt_trichotomy x z with h | h | h
  · have hg := clippedInverse_gap f a b m y w x z hf hx hz h
    rw [abs_of_nonpos (by linarith : x-z ≤ 0)]
    have ha := le_abs_self (y-w)
    nlinarith
  · simp [h]
  · have hg := clippedInverse_gap f a b m w y z x hf hz hx h
    rw [abs_of_nonneg (by linarith : 0 ≤ x-z)]
    have ha := neg_le_abs (y-w)
    nlinarith

theorem boundedInverse_error (f : ℝ → ℝ) (a b m y H : ℝ)
    (hm : 0 < m) (hab : a ≤ b) (hc : ContinuousOn f (Icc a b))
    (hf : StrongDecrease f a b m) (hH : H ∈ Icc a b) :
    |boundedInverse f a b y-H| ≤ |y-f H|/m :=
  clippedInverse_contraction f a b m y (f H) _ H hm hf
    (boundedInverse_spec f a b y hab hc) ⟨hH, Or.inl rfl⟩

theorem boundedInverse_lipschitz (f : ℝ → ℝ) (a b m : ℝ)
    (hm : 0 < m) (hab : a ≤ b) (hc : ContinuousOn f (Icc a b))
    (hf : StrongDecrease f a b m) :
    LipschitzWith ⟨m⁻¹, (inv_pos.mpr hm).le⟩ (boundedInverse f a b) := by
  apply LipschitzWith.of_dist_le_mul
  intro y w
  change |boundedInverse f a b y-boundedInverse f a b w| ≤ m⁻¹*|y-w|
  simpa [div_eq_mul_inv, mul_comm] using
    clippedInverse_contraction f a b m y w _ _ hm hf
      (boundedInverse_spec f a b y hab hc) (boundedInverse_spec f a b w hab hc)

/-- Finite-sample MSE transfer, including measurability and integrability of the
constructed nonlinear estimator. The only statistical premise is an L2 input. -/
theorem boundedInverse_mse {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (f : ℝ → ℝ) (a b m H : ℝ)
    (hm : 0 < m) (hab : a ≤ b) (hc : ContinuousOn f (Icc a b))
    (hf : StrongDecrease f a b m) (hH : H ∈ Icc a b) (hX : MemLp X 2 μ) :
    (∫ ω, (boundedInverse f a b (X ω)-H)^2 ∂μ) ≤
      (variance X μ + ((∫ ω, X ω ∂μ)-f H)^2)/m^2 := by
  have hmeas : AEStronglyMeasurable (fun ω => (boundedInverse f a b (X ω)-H)^2) μ := by
    exact (((boundedInverse_lipschitz f a b m hm hab hc hf).continuous.comp_aestronglyMeasurable
      hX.aestronglyMeasurable).sub aestronglyMeasurable_const).pow 2
  have hg : Integrable (fun ω => (X ω-f H)^2/m^2) μ :=
    ((hX.sub (memLp_const (f H))).integrable_sq).div_const _
  have hbound : ∀ ω, (boundedInverse f a b (X ω)-H)^2 ≤ (X ω-f H)^2/m^2 := by
    intro ω
    have he := boundedInverse_error f a b m (X ω) H hm hab hc hf hH
    have hs := mul_self_le_mul_self (abs_nonneg _) he
    simpa [← sq, div_pow, sq_abs] using hs
  have hInt : Integrable (fun ω => (boundedInverse f a b (X ω)-H)^2) μ :=
    hg.mono' hmeas (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hbound ω)
  calc
    _ ≤ ∫ ω, (X ω-f H)^2/m^2 ∂μ := integral_mono hInt hg hbound
    _ = _ := by rw [integral_div, mse_decomposition X (f H) hX]

/-- Endpoint-extended calibrations; these correctly use the limits at H=0. -/
def calibrationOne (L c H : ℝ) : ℝ := c-2*L*H
def calibrationTwo (L c H : ℝ) : ℝ := c-2*L*H+Real.log (4-(2:ℝ)^(2*H))

theorem calibrationOne_agrees (L c H : ℝ) (hH : 0 < H) :
    calibrationOne L c H = G 1 L c H := (G_one L c H hH.ne').symm

theorem calibrationTwo_agrees (L c H : ℝ) (hH : 0 < H) :
    calibrationTwo L c H = G 2 L c H := by
  rw [G, g_two_unit H hH.ne']
  unfold calibrationTwo; ring

theorem calibrationOne_continuous (L c : ℝ) : Continuous (calibrationOne L c) := by
  unfold calibrationOne; fun_prop

theorem calibrationOne_strongDecrease (L c a b : ℝ) :
    StrongDecrease (calibrationOne L c) a b (2*L) := by
  intro x hx z hz hxz
  unfold calibrationOne; linarith

theorem calibrationTwo_positive_inside (H : ℝ) (hH : H < 1) :
    0 < 4-(2:ℝ)^(2*H) := by
  have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<2)
    (show 2*H < (2:ℝ) by linarith)
  norm_num at h
  linarith

theorem calibrationTwo_continuousOn (L c u : ℝ) (hu : u < 1) :
    ContinuousOn (calibrationTwo L c) (Icc 0 u) := by
  apply ContinuousOn.add
  · fun_prop
  · apply ContinuousOn.log
    · exact (show Continuous (fun H : ℝ => (4:ℝ)-(2:ℝ)^(2*H)) by
        have ht : (2:ℝ) ≠ 0 := by norm_num
        fun_prop).continuousOn
    · intro H hH
      exact (calibrationTwo_positive_inside H (hH.2.trans_lt hu)).ne'

theorem calibrationTwo_strongDecrease (L c u : ℝ) (hu : u < 1) :
    StrongDecrease (calibrationTwo L c) 0 u (2*L) := by
  intro x hx z hz hxz
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
    (show 2*x ≤ 2*z by linarith)
  have hl := Real.log_le_log (calibrationTwo_positive_inside z (hz.2.trans_lt hu))
    (show 4-(2:ℝ)^(2*z) ≤ 4-(2:ℝ)^(2*x) by linarith)
  unfold calibrationTwo
  linarith

/-- Explicit q=1 repaired-estimator MSE bound in the paper's G notation. -/
theorem repaired_q1_mse {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (L c H : ℝ)
    (hL : 0 < L) (hH : H ∈ Ioo 0 1) (hX : MemLp X 2 μ) :
    (∫ ω, (boundedInverse (calibrationOne L c) 0 1 (X ω)-H)^2 ∂μ) ≤
      (variance X μ + ((∫ ω, X ω ∂μ)-G 1 L c H)^2)/(4*L^2) := by
  have h := boundedInverse_mse μ X (calibrationOne L c) 0 1 (2*L) H
    (by positivity) (by norm_num) (calibrationOne_continuous L c).continuousOn
    (calibrationOne_strongDecrease L c 0 1) ⟨hH.1.le,hH.2.le⟩ hX
  simpa [calibrationOne_agrees L c H hH.1, mul_pow, show (2:ℝ)^2=4 by norm_num] using h

/-- Explicit q=2 repaired-estimator MSE bound; u can approach 1 with n. -/
theorem repaired_q2_mse {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (L c H u : ℝ)
    (hL : 0 < L) (hH : 0 < H) (hHu : H ≤ u) (hu : u < 1)
    (hX : MemLp X 2 μ) :
    (∫ ω, (boundedInverse (calibrationTwo L c) 0 u (X ω)-H)^2 ∂μ) ≤
      (variance X μ + ((∫ ω, X ω ∂μ)-G 2 L c H)^2)/(4*L^2) := by
  have h := boundedInverse_mse μ X (calibrationTwo L c) 0 u (2*L) H
    (by positivity) (hH.le.trans hHu) (calibrationTwo_continuousOn L c u hu)
    (calibrationTwo_strongDecrease L c u hu) ⟨hH.le,hHu⟩ hX
  simpa [calibrationTwo_agrees L c H hH, mul_pow, show (2:ℝ)^2=4 by norm_num] using h

/-- Moment bound for dependent input and nuisance estimators. No independence. -/
theorem dependent_difference_mse {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X S : Ω → ℝ) (t s : ℝ)
    (hX : MemLp X 2 μ) (hS : MemLp S 2 μ) :
    (∫ ω, ((X ω-S ω)-(t-s))^2 ∂μ) ≤
      2*((variance X μ+((∫ ω, X ω ∂μ)-t)^2)+
         (variance S μ+((∫ ω, S ω ∂μ)-s)^2)) := by
  have hInt := ((hX.sub hS).sub (memLp_const (t-s))).integrable_sq
  have hXt : Integrable (fun ω => (X ω-t)^2) μ := (hX.sub (memLp_const t)).integrable_sq
  have hSs : Integrable (fun ω => (S ω-s)^2) μ := (hS.sub (memLp_const s)).integrable_sq
  have hpoint : ∀ ω, ((X ω-S ω)-(t-s))^2 ≤ 2*(X ω-t)^2+2*(S ω-s)^2 := by
    intro ω; nlinarith [sq_nonneg ((X ω-t)+(S ω-s))]
  calc
    _ ≤ ∫ ω, 2*(X ω-t)^2+2*(S ω-s)^2 ∂μ :=
      integral_mono hInt ((hXt.const_mul 2).add (hSs.const_mul 2)) hpoint
    _ = _ := by
      rw [integral_add (hXt.const_mul 2) (hSs.const_mul 2), integral_const_mul,
        integral_const_mul, mse_decomposition X t hX, mse_decomposition S s hS]
      ring

/-- Repaired finite-sample backfitting theorem. The input estimator targets
f(H)+s and the nuisance estimator targets s. -/
theorem boundedInverse_backfitting_mse {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X S : Ω → ℝ)
    (f : ℝ → ℝ) (a b m H s : ℝ) (hm : 0 < m) (hab : a ≤ b)
    (hc : ContinuousOn f (Icc a b)) (hf : StrongDecrease f a b m)
    (hH : H ∈ Icc a b) (hX : MemLp X 2 μ) (hS : MemLp S 2 μ) :
    (∫ ω, (boundedInverse f a b (X ω-S ω)-H)^2 ∂μ) ≤
      2*((variance X μ+((∫ ω, X ω ∂μ)-(f H+s))^2)+
         (variance S μ+((∫ ω, S ω ∂μ)-s)^2))/m^2 := by
  have hinv := boundedInverse_mse μ (fun ω => X ω-S ω) f a b m H
    hm hab hc hf hH (hX.sub hS)
  rw [← mse_decomposition (fun ω => X ω-S ω) (f H) (hX.sub hS)] at hinv
  have hdiff := dependent_difference_mse μ X S (f H+s) s hX hS
  simp only [add_sub_cancel_right] at hdiff
  exact hinv.trans (div_le_div_of_nonneg_right hdiff (sq_nonneg _))

/-- An upper cutoff not depending on the unknown H. -/
def upperCutoff (n : ℕ) : ℝ := 1-((n:ℝ)+2)⁻¹

theorem upperCutoff_bounds (n : ℕ) : 0 < upperCutoff n ∧ upperCutoff n < 1 := by
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
  have hp : 0 < ((n:ℝ)+2)⁻¹ := inv_pos.mpr (by linarith)
  have hl : ((n:ℝ)+2)⁻¹ < 1 := (inv_lt_one₀ (by linarith)).mpr (by linarith)
  unfold upperCutoff; constructor <;> linarith

theorem upperCutoff_tendsto : Filter.Tendsto upperCutoff Filter.atTop (𝓝 1) := by
  have ht : Filter.Tendsto (fun n : ℕ => (n:ℝ)+2) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hi := tendsto_inv_atTop_zero.comp ht
  change Filter.Tendsto (fun n : ℕ => 1-((n:ℝ)+2)⁻¹) _ _
  simpa using (tendsto_const_nhds (x := (1:ℝ))).sub hi

theorem upperCutoff_eventually_contains (H : ℝ) (hH : H < 1) :
    ∀ᶠ n in Filter.atTop, H ≤ upperCutoff n :=
  (upperCutoff_tendsto.eventually_const_lt hH).mono fun _ hn => hn.le

end Hurst
