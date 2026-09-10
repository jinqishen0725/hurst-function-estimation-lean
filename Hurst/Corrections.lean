import Hurst.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Counterexamples and corrected deterministic steps. These results are NOT
proofs of the paper's full statistical theorems. See summary.md. -/
noncomputable section
open Filter
open scoped Topology
namespace Hurst

/-- Exact range of the q=1 transform: Section 2's lower endpoint is finite. -/
theorem G_one_range (L c : ℝ) (hL : 0 < L) :
    (G 1 L c) '' Set.Ioo 0 1 = Set.Ioo (c-2*L) c := by
  ext y
  constructor
  · rintro ⟨H, ⟨h0, h1⟩, rfl⟩
    rw [G_one L c H (ne_of_gt h0)]
    constructor <;> nlinarith
  · rintro ⟨hlo, hhi⟩
    refine ⟨(c-y)/(2*L), ⟨div_pos (by linarith) (by positivity), ?_⟩, ?_⟩
    · apply (div_lt_one (by positivity : 0 < 2*L)).mpr; linarith
    · rw [G_one L c _ (ne_of_gt (div_pos (by linarith) (by positivity)))]
      field_simp; ring

/-- Concrete input omitted by the inverse extension in (2.8). -/
theorem G_one_no_preimage (L c : ℝ) (hL : 0 < L) :
    ¬ ∃ H ∈ Set.Ioo (0:ℝ) 1, G 1 L c H = c-2*L-1 := by
  rintro ⟨H, hH, he⟩
  have hr : c-2*L-1 ∈ (G 1 L c) '' Set.Ioo 0 1 := ⟨H,hH,he⟩
  rw [G_one_range L c hL] at hr
  linarith [hr.1]

def clip (a b x : ℝ) : ℝ := max a (min b x)
def inverseOne (L c y : ℝ) : ℝ := clip 0 1 ((c-y)/(2*L))

theorem clip_mem (a b x : ℝ) (hab : a ≤ b) : clip a b x ∈ Set.Icc a b := by
  exact ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩

theorem clip_identity (a b x : ℝ) (hx : x ∈ Set.Icc a b) : clip a b x = x := by
  simp [clip, min_eq_right hx.2, max_eq_right hx.1]

theorem clip_error (a b x H : ℝ) (hH : H ∈ Set.Icc a b) :
    |clip a b x - H| ≤ |x-H| := by
  by_cases hx : x < a
  · have he : clip a b x = a := by simp [clip, min_eq_right (hx.le.trans hH.1 |>.trans hH.2), max_eq_left hx.le]
    rw [he, abs_of_nonpos (by linarith [hH.1]), abs_of_nonpos (by linarith [hH.1])]
    linarith
  · by_cases hxb : b < x
    · have he : clip a b x = b := by simp [clip, min_eq_left hxb.le, max_eq_right (hH.1.trans hH.2)]
      rw [he, abs_of_nonneg (by linarith [hH.2]), abs_of_nonneg (by linarith [hH.2])]; linarith
    · rw [clip_identity a b x ⟨le_of_not_gt hx, le_of_not_gt hxb⟩]

theorem inverseOne_recovers (L c H : ℝ) (hL : 0 < L) (hH : H ∈ Set.Ioo 0 1) :
    inverseOne L c (G 1 L c H) = H := by
  rw [inverseOne, G_one L c H (ne_of_gt hH.1)]
  have he : (c-(c-2*L*H))/(2*L) = H := by field_simp; ring
  rw [he]; exact clip_identity _ _ _ ⟨hH.1.le,hH.2.le⟩

/-- The exact negative sign, before taking any distributional limit (3.4/S.4.34). -/
theorem inverse_affine_sign (L c x y : ℝ) (hL : L ≠ 0) :
    2*L * ((c-x)/(2*L) - (c-y)/(2*L)) = -(x-y) := by
  field_simp; ring

/-- Slutsky step for arbitrary real sequences with vanishing linearization remainder. -/
theorem negative_limit {x y e : ℕ → ℝ} {z : ℝ}
    (hx : Tendsto x atTop (𝓝 z)) (he : Tendsto e atTop (𝓝 0))
    (hy : ∀ n, y n = -x n + e n) : Tendsto y atTop (𝓝 (-z)) := by
  simpa only [← hy, add_zero] using hx.neg.add he

/-- Corollary 3.5's coefficient after multiplying the bias by its normalization. -/
theorem corollary_bias_G (A L B R : ℝ) (hbalance : A*L*B = 1) :
    A * (-2*L*B*R) = -2*R := by
  calc
    A * (-2*L*B*R) = -2 * R * (A*L*B) := by ring
    _ = -2*R := by rw [hbalance]; ring

theorem corollary_bias_H (R : ℝ) : -(-2*R) = 2*R := by ring

theorem corollary_printed_mean_wrong (R : ℝ) (hR : R ≠ 0) :
    -2*R ≠ R ∧ 2*R ≠ R := by constructor <;> intro h <;> apply hR <;> linarith

/-- q=1 leading covariance coefficient obtained from -1/2 times a mixed derivative. -/
def leadingOne (H : ℝ) := H*(2*H-1)
def printedLeadingOne (H : ℝ) := (2*H)*(2*H-1)

theorem leading_half_factor (H : ℝ) : leadingOne H = printedLeadingOne H / 2 := by
  unfold leadingOne printedLeadingOne; ring

theorem leading_critical_value : leadingOne (3/4) = 3/8 ∧ printedLeadingOne (3/4) = 3/4 := by
  norm_num [leadingOne, printedLeadingOne]

/-- The polynomial printed on p.855 has the wrong sign at the RIGHT endpoint. -/
def printedBump (x : ℝ) :=
  if x ∈ Set.Ioo (-(1/2:ℝ)) (1/2) then
    Real.exp (-1/(x+1/2) - 1/(x-1/2)) else 0

/-- A smooth replacement with precisely the required support. -/
def correctedBump (x : ℝ) := expNegInvGlue (1/4 - x^2)

theorem correctedBump_smooth : ContDiff ℝ (⊤ : ℕ∞) correctedBump := by
  exact expNegInvGlue.contDiff.comp (contDiff_const.sub (contDiff_id.pow 2))

theorem correctedBump_nonneg (x : ℝ) : 0 ≤ correctedBump x := expNegInvGlue.nonneg _

theorem correctedBump_positive (x : ℝ) (hx : x ∈ Set.Ioo (-(1/2:ℝ)) (1/2)) :
    0 < correctedBump x := by
  apply expNegInvGlue.pos_of_pos
  nlinarith [sq_nonneg (x+1/2), mul_pos (show 0 < x+1/2 by linarith [hx.1])
    (show 0 < 1/2-x by linarith [hx.2])]

theorem correctedBump_zero (x : ℝ) (hx : x ≤ -(1/2:ℝ) ∨ 1/2 ≤ x) :
    correctedBump x = 0 := by
  apply expNegInvGlue.zero_of_nonpos
  rcases hx with hx | hx <;> nlinarith [sq_nonneg (x+1/2), sq_nonneg (x-1/2)]

theorem printedBump_growth (k : ℝ) (hk : 4 ≤ k) :
    Real.exp (k-2) ≤ printedBump (1/2-1/k) := by
  have hk0 : 0 < k := by linarith
  have hki : 0 < 1/k := one_div_pos.mpr hk0
  have hki1 : 1/k < 1 := (div_lt_one hk0).mpr (by linarith)
  have hx : (1/2-1/k:ℝ) ∈ Set.Ioo (-(1/2:ℝ)) (1/2) := ⟨by linarith, by linarith⟩
  rw [printedBump, if_pos hx]
  apply Real.exp_le_exp.mpr
  have hk1 : k-1 ≠ 0 := by linarith
  have he : -1/(1/2-1/k+1/2) - 1/(1/2-1/k-1/2) = k-k/(k-1) := by
    have ha : (1/2-1/k+1/2:ℝ) = (k-1)/k := by field_simp; ring
    have hb : (1/2-1/k-1/2:ℝ) = -1/k := by ring
    rw [ha, hb]
    field_simp
    ring
  rw [he]
  have hd : k/(k-1) ≤ 2 := (div_le_iff₀ (by linarith : 0 < k-1)).mpr (by linarith)
  linarith

/-- Therefore the printed bump is not even bounded. -/
theorem printedBump_unbounded : ∀ M : ℝ, ∃ x ∈ Set.Ioo (-(1/2:ℝ)) (1/2), M < printedBump x := by
  intro M
  let k : ℝ := max 4 (M+3)
  have hk : 4 ≤ k := le_max_left _ _
  have hkM : M+3 ≤ k := le_max_right _ _
  have hk0 : 0 < k := by linarith
  have hki : 0 < 1/k := one_div_pos.mpr hk0
  have hki1 : 1/k < 1 := (div_lt_one hk0).mpr (by linarith)
  refine ⟨1/2-1/k, ⟨by linarith, by linarith⟩, ?_⟩
  have he := Real.add_one_le_exp (k-2)
  have hg := printedBump_growth k hk
  linarith

/-- Packing separation must be twice the testing radius, with DISTINCT indices. -/
theorem packing_radius (distance separation : ℝ) (h : separation ≤ distance) :
    2*(separation/2) ≤ distance := by linarith

theorem impossible_self_separation (δ : ℝ) (hδ : 0 < δ) : ¬ 0 ≥ 2*δ := by linarith

/-- Covariance integral in S.1 needs 1/(2D²), because at s=t=1 the integral is 2D². -/
theorem spectral_normalization (D : ℝ) (hD : D ≠ 0) :
    (2*D^2)/(2*D^2) = 1 ∧ (2*D^2)/(D^2) = 2 := by
  constructor <;> field_simp

/-- S.3.17 must use the variance. This is the exact pointwise log identity. -/
theorem log_square_scale (s z : ℝ) (hs : s ≠ 0) (hz : z ≠ 0) :
    Real.log ((s*z)^2) = Real.log (s^2) + Real.log (z^2) := by
  rw [mul_pow, Real.log_mul (pow_ne_zero _ hs) (pow_ne_zero _ hz)]

/-- S.6.1 at u=0, q=1, H=1/2: raw Brownian increment variance is 1/n,
whereas the printed target is g=1. The error does not even tend to zero. -/
theorem raw_variance_error_limit :
    Tendsto (fun n : ℕ => |(n:ℝ)⁻¹-1|) atTop (𝓝 1) := by
  have hi : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  simpa using (hi.sub (tendsto_const_nhds (x := (1:ℝ)))).abs

theorem raw_variance_error_not_bigO {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0)) :
    ¬ Asymptotics.IsBigO atTop (fun n : ℕ => |(n:ℝ)⁻¹-1|) r := by
  intro h
  have he := tendsto_nhds_unique raw_variance_error_limit (h.trans_tendsto hr)
  norm_num at he

theorem normalized_variance (n : ℝ) (hn : n ≠ 0) : n * n⁻¹ = 1 := mul_inv_cancel₀ hn

end Hurst
