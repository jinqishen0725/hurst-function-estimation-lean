import Hurst.ActualFirstLongCorrelationPerturbation
import Hurst.FirstLongUniformQuotient
import Hurst.CovarianceParameter
import Hurst.ActiveSetReindex
import Hurst.FirstLongDiagonalBand

noncomputable section
open Set Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

/-- Exact factorization of the frozen cross-parameter first-increment tail.
The three factors are respectively the smooth covariance coefficient, the
power mismatch, and the centered second-difference quotient. -/
theorem firstIncrementCrossLagCorrelation_scaled_factorization
    (h k x psi : ℝ) (hx : 1 < x) :
    x ^ psi * firstIncrementCrossLagCorrelation h k x =
      harmonizableCovCoeff h k * x ^ (h + k + psi - 2) *
        centeredCrossRpowQuotient (h + k) x⁻¹ := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hxm : 0 < x - 1 := sub_pos.mpr hx
  have hxp : 0 < x + 1 := by linarith
  have eplus : (x + 1) ^ (h + k) =
      x ^ (h + k) * (1 + x⁻¹) ^ (h + k) := by
    rw [← Real.mul_rpow hx0.le (by positivity : 0 ≤ 1 + x⁻¹)]
    congr 1
    field_simp
  have eminus : (x - 1) ^ (h + k) =
      x ^ (h + k) * (1 - x⁻¹) ^ (h + k) := by
    rw [← Real.mul_rpow hx0.le (by
      rw [sub_nonneg]
      exact (inv_le_one₀ hx0).mpr hx.le)]
    congr 1
    field_simp
  have hpowers : x ^ psi * x ^ (h + k) =
      x ^ (h + k + psi - 2) * x ^ (2 : ℝ) := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
    congr 1
    ring
  unfold firstIncrementCrossLagCorrelation centeredCrossRpowQuotient
  rw [abs_of_pos hxp, abs_of_pos hxm, abs_of_pos hx0, eplus, eminus]
  rw [← show harmonizableD ((h + k) / 2) ^ 2 /
      (2 * harmonizableD h * harmonizableD k) =
        harmonizableCovCoeff h k by rfl]
  rw [show x ^ (h + k) * (1 + x⁻¹) ^ (h + k) +
        x ^ (h + k) * (1 - x⁻¹) ^ (h + k) - 2 * x ^ (h + k) =
      x ^ (h + k) *
        ((1 + x⁻¹) ^ (h + k) + (1 - x⁻¹) ^ (h + k) - 2) by ring]
  rw [show x ^ psi *
      ((harmonizableD ((h + k) / 2) ^ 2 /
          (2 * harmonizableD h * harmonizableD k)) *
        (x ^ (h + k) *
          ((1 + x⁻¹) ^ (h + k) + (1 - x⁻¹) ^ (h + k) - 2))) =
      (harmonizableD ((h + k) / 2) ^ 2 /
          (2 * harmonizableD h * harmonizableD k)) *
        (x ^ psi * x ^ (h + k)) *
        ((1 + x⁻¹) ^ (h + k) + (1 - x⁻¹) ^ (h + k) - 2) by ring,
    hpowers, Real.rpow_two]
  field_simp [hx0.ne']
  <;> ring

/-- The smooth cross-covariance prefactor is Lipschitz near its diagonal
value `1/2`, uniformly on any compact Hurst interval. -/
theorem harmonizableCovCoeff_sub_half_le
    (a b : ℝ) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) :
    ∃ C ≥ 0, ∀ h k h0 : ℝ,
      h ∈ Icc a b → k ∈ Icc a b → h0 ∈ Icc a b →
      |harmonizableCovCoeff h k - 1 / 2| ≤
        C * (|h - h0| + |k - h0|) := by
  obtain ⟨C, hC, hbound⟩ :=
    harmonizableCovCoeff_uniform_derivative_control a b ha hb hab
  refine ⟨C, hC, ?_⟩
  intro h k h0 hh hk hh0
  have hkh :
      |harmonizableCovCoeff h k - harmonizableCovCoeff h h| ≤
        C * |k - h| := by
    have hm := (convex_Icc a b).norm_image_sub_le_of_norm_deriv_le
      (fun z hz => (harmonizableCovCoeff_hasDerivAt h z
        ⟨ha.trans_le hh.1, hh.2.trans_lt hb⟩
        ⟨ha.trans_le hz.1, hz.2.trans_lt hb⟩).differentiableAt)
      (fun z hz => by
        rw [Real.norm_eq_abs]
        rw [(harmonizableCovCoeff_hasDerivAt h z
          ⟨ha.trans_le hh.1, hh.2.trans_lt hb⟩
          ⟨ha.trans_le hz.1, hz.2.trans_lt hb⟩).deriv]
        exact (hbound h z hh hz).2)
      hk hh
    simpa only [Real.norm_eq_abs, abs_sub_comm] using hm
  have hdiag : harmonizableCovCoeff h h = 1 / 2 := by
    unfold harmonizableCovCoeff
    have hD : harmonizableD h ≠ 0 :=
      (harmonizableD_pos h (ha.trans_le hh.1) (hh.2.trans_lt hb)).ne'
    rw [show (h + h) / 2 = h by ring]
    field_simp [hD]
  rw [hdiag] at hkh
  have hdist : |k - h| ≤ |h - h0| + |k - h0| := by
    have ht := abs_add_le (k - h0) (h0 - h)
    rw [show k - h0 + (h0 - h) = k - h by ring] at ht
    calc
      _ ≤ |k - h0| + |h0 - h| := ht
      _ = _ := by rw [abs_sub_comm h0 h, add_comm]
  exact hkh.trans (mul_le_mul_of_nonneg_left hdist hC)

/-- Quantitative frozen tail estimate, uniform in two parameters in a compact
Hurst interval.  The displayed four terms correspond to coefficient drift,
power drift, the `O(1/x)` second-difference remainder, and drift of the tail
constant. -/
theorem firstIncrementCrossLagCorrelation_scaled_error_le
    (a b : ℝ) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) :
    ∃ C ≥ 0, ∀ h k h0 x psi M : ℝ,
      h ∈ Icc a b → k ∈ Icc a b → h0 ∈ Icc a b →
      2 ≤ x → 0 ≤ M → psi = 2 - 2 * h0 →
      |(h + k - 2 * h0) * Real.log x| ≤ M →
      |x ^ psi * firstIncrementCrossLagCorrelation h k x -
          h0 * (2 * h0 - 1)| ≤
        C * (|h - h0| + |k - h0|) *
            |x ^ (h + k - 2 * h0)| *
            |centeredCrossRpowQuotient (h + k) x⁻¹| +
          (1 / 2 : ℝ) *
            (Real.exp M *
              (|h + k - 2 * h0| * |Real.log x|)) *
            |centeredCrossRpowQuotient (h + k) x⁻¹| +
          16 * x⁻¹ +
          (3 / 2 : ℝ) * (|h - h0| + |k - h0|) := by
  obtain ⟨C, hC, hcoef⟩ :=
    harmonizableCovCoeff_sub_half_le a b ha hb hab
  refine ⟨C, hC, ?_⟩
  intro h k h0 x psi M hh hk hh0 hx hM hpsi hlog
  let d := |h - h0| + |k - h0|
  let beta := h + k - 2 * h0
  let Q := centeredCrossRpowQuotient (h + k) x⁻¹
  let T := (h + k) * (h + k - 1)
  let T0 := (2 * h0) * (2 * h0 - 1)
  have hx0 : 0 < x := by linarith
  have hfactor := firstIncrementCrossLagCorrelation_scaled_factorization
    h k x psi (by linarith)
  have hexp : h + k + psi - 2 = beta := by dsimp only [beta]; rw [hpsi]; ring
  rw [hexp] at hfactor
  have hcoef' : |harmonizableCovCoeff h k - 1 / 2| ≤ C * d :=
    hcoef h k h0 hh hk hh0
  have hbeta : |beta| ≤ d := by
    dsimp only [beta, d]
    calc
      |h + k - 2 * h0| = |(h - h0) + (k - h0)| := by congr 1 <;> ring
      _ ≤ _ := abs_add_le _ _
  have hpow : |x ^ beta - 1| ≤
      Real.exp M * (|beta| * |Real.log x|) :=
    rpow_sub_one_bound x beta M hx0 hM (by simpa only [beta] using hlog)
  have hα0 : 0 ≤ h + k := by linarith [hh.1, hk.1]
  have hα2 : h + k ≤ 2 := by linarith [hh.2, hk.2]
  have hinvpos : 0 < x⁻¹ := inv_pos.mpr hx0
  have hinvhalf : x⁻¹ ≤ 1 / 2 := by
    simpa only [one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hx)
  have hQ : |Q - T| ≤ 32 * x⁻¹ := by
    simpa only [Q, T] using centeredCrossRpowQuotient_uniform_error
      (h + k) x⁻¹ hα0 hα2 hinvpos hinvhalf
  have hαdist : |h + k - 2 * h0| ≤ d := by simpa only [beta] using hbeta
  have hαfactor : |h + k + 2 * h0 - 1| ≤ 3 := by
    rw [abs_le]
    constructor <;> linarith [hh.1, hh.2, hk.1, hk.2, hh0.1, hh0.2]
  have hT : |T - T0| ≤ 3 * d := by
    have hid : T - T0 =
        (h + k - 2 * h0) * (h + k + 2 * h0 - 1) := by
      dsimp only [T, T0]
      ring
    rw [hid, abs_mul]
    calc
      |h + k - 2 * h0| * |h + k + 2 * h0 - 1| ≤
          d * |h + k + 2 * h0 - 1| :=
        mul_le_mul_of_nonneg_right hαdist (abs_nonneg _)
      _ ≤ d * 3 := mul_le_mul_of_nonneg_left hαfactor (by dsimp [d]; positivity)
      _ = 3 * d := by ring
  have htarget : h0 * (2 * h0 - 1) = (1 / 2 : ℝ) * T0 := by
    dsimp only [T0]
    ring
  rw [hfactor, htarget]
  have halgebra :
      harmonizableCovCoeff h k * x ^ beta * Q - (1 / 2 : ℝ) * T0 =
        (harmonizableCovCoeff h k - 1 / 2) * x ^ beta * Q +
          (1 / 2 : ℝ) * (x ^ beta - 1) * Q +
          (1 / 2 : ℝ) * (Q - T) +
          (1 / 2 : ℝ) * (T - T0) := by ring
  rw [halgebra]
  have habs :
      |(harmonizableCovCoeff h k - 1 / 2) * x ^ beta * Q +
          (1 / 2 : ℝ) * (x ^ beta - 1) * Q +
          (1 / 2 : ℝ) * (Q - T) +
          (1 / 2 : ℝ) * (T - T0)| ≤
        |(harmonizableCovCoeff h k - 1 / 2) * x ^ beta * Q| +
          |(1 / 2 : ℝ) * (x ^ beta - 1) * Q| +
          |(1 / 2 : ℝ) * (Q - T)| +
          |(1 / 2 : ℝ) * (T - T0)| := by
    rw [show
      (harmonizableCovCoeff h k - 1 / 2) * x ^ beta * Q +
          (1 / 2 : ℝ) * (x ^ beta - 1) * Q +
          (1 / 2 : ℝ) * (Q - T) + (1 / 2 : ℝ) * (T - T0) =
        ((harmonizableCovCoeff h k - 1 / 2) * x ^ beta * Q +
          (1 / 2 : ℝ) * (x ^ beta - 1) * Q) +
        ((1 / 2 : ℝ) * (Q - T) + (1 / 2 : ℝ) * (T - T0)) by ring]
    calc
      _ ≤ |(harmonizableCovCoeff h k - 1 / 2) * x ^ beta * Q +
            (1 / 2 : ℝ) * (x ^ beta - 1) * Q| +
          |(1 / 2 : ℝ) * (Q - T) + (1 / 2 : ℝ) * (T - T0)| :=
        abs_add_le _ _
      _ ≤ (|(harmonizableCovCoeff h k - 1 / 2) * x ^ beta * Q| +
            |(1 / 2 : ℝ) * (x ^ beta - 1) * Q|) +
          (|(1 / 2 : ℝ) * (Q - T)| + |(1 / 2 : ℝ) * (T - T0)|) :=
        add_le_add (abs_add_le _ _) (abs_add_le _ _)
      _ = _ := by ring
  calc
    _ ≤ |(harmonizableCovCoeff h k - 1 / 2) * x ^ beta * Q| +
          |(1 / 2 : ℝ) * (x ^ beta - 1) * Q| +
          |(1 / 2 : ℝ) * (Q - T)| +
          |(1 / 2 : ℝ) * (T - T0)| := by
      exact habs
    _ ≤ (C * d) * |x ^ beta| * |Q| +
          (1 / 2 : ℝ) *
            (Real.exp M * (|beta| * |Real.log x|)) * |Q| +
          (1 / 2 : ℝ) * (32 * x⁻¹) +
          (1 / 2 : ℝ) * (3 * d) := by
      have hA :
          |(harmonizableCovCoeff h k - 1 / 2) * x ^ beta * Q| ≤
            (C * d) * |x ^ beta| * |Q| := by
        simp only [abs_mul]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoef' (abs_nonneg _)) (abs_nonneg _)
      have hB : |(1 / 2 : ℝ) * (x ^ beta - 1) * Q| ≤
          (1 / 2 : ℝ) *
            (Real.exp M * (|beta| * |Real.log x|)) * |Q| := by
        simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow (by norm_num)) (abs_nonneg _)
      have hCterm : |(1 / 2 : ℝ) * (Q - T)| ≤
          (1 / 2 : ℝ) * (32 * x⁻¹) := by
        simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        exact mul_le_mul_of_nonneg_left hQ (by norm_num)
      have hD : |(1 / 2 : ℝ) * (T - T0)| ≤
          (1 / 2 : ℝ) * (3 * d) := by
        simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        exact mul_le_mul_of_nonneg_left hT (by norm_num)
      simpa only [d, beta, Q, T, T0] using
        add_le_add (add_le_add (add_le_add hA hB) hCterm) hD
    _ = C * d * |x ^ beta| * |Q| +
          (1 / 2 : ℝ) *
            (Real.exp M * (|beta| * |Real.log x|)) * |Q| +
          16 * x⁻¹ + (3 / 2 : ℝ) * d := by ring

/-- A convenient version of the preceding estimate in which the power and
quotient factors have already been bounded by elementary constants. -/
theorem firstIncrementCrossLagCorrelation_scaled_error_le_explicit
    (a b : ℝ) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) :
    ∃ C ≥ 0, ∀ h k h0 x psi M : ℝ,
      h ∈ Icc a b → k ∈ Icc a b → h0 ∈ Icc a b →
      2 ≤ x → 0 ≤ M → psi = 2 - 2 * h0 →
      |(h + k - 2 * h0) * Real.log x| ≤ M →
      |x ^ psi * firstIncrementCrossLagCorrelation h k x -
          h0 * (2 * h0 - 1)| ≤
        18 * C * (|h - h0| + |k - h0|) *
            (1 + Real.exp M *
              (|h + k - 2 * h0| * |Real.log x|)) +
          9 * Real.exp M *
              (|h + k - 2 * h0| * |Real.log x|) +
          16 * x⁻¹ +
          (3 / 2 : ℝ) * (|h - h0| + |k - h0|) := by
  obtain ⟨C, hC, hraw⟩ :=
    firstIncrementCrossLagCorrelation_scaled_error_le a b ha hb hab
  refine ⟨C, hC, ?_⟩
  intro h k h0 x psi M hh hk hh0 hx hM hpsi hlog
  have hbase := hraw h k h0 x psi M hh hk hh0 hx hM hpsi hlog
  let beta := h + k - 2 * h0
  let Q := centeredCrossRpowQuotient (h + k) x⁻¹
  have hx0 : 0 < x := by linarith
  have hpow := rpow_sub_one_bound x beta M hx0 hM (by simpa only [beta] using hlog)
  have hpowabs : |x ^ beta| ≤
      1 + Real.exp M * (|beta| * |Real.log x|) := by
    calc
      |x ^ beta| = |(x ^ beta - 1) + 1| := by ring_nf
      _ ≤ |x ^ beta - 1| + |(1 : ℝ)| := abs_add_le _ _
      _ ≤ Real.exp M * (|beta| * |Real.log x|) + 1 :=
        add_le_add hpow (by norm_num)
      _ = _ := by ring
  have hα0 : 0 ≤ h + k := by linarith [hh.1, hk.1]
  have hα2 : h + k ≤ 2 := by linarith [hh.2, hk.2]
  have hpoly : |(h + k) * (h + k - 1)| ≤ 2 := by
    rw [abs_mul]
    have h1 : |h + k| ≤ 2 := by rw [abs_of_nonneg hα0]; exact hα2
    have h2 : |h + k - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    nlinarith [abs_nonneg (h + k), abs_nonneg (h + k - 1)]
  have hQerr := centeredCrossRpowQuotient_uniform_error
      (h + k) x⁻¹ hα0 hα2 (inv_pos.mpr hx0)
      (by simpa only [one_div] using
        (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hx))
  have hQabs : |Q| ≤ 18 := by
    have hinv : x⁻¹ ≤ 1 / 2 :=
      (by simpa only [one_div] using
        (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hx))
    calc
      |Q| = |(Q - (h + k) * (h + k - 1)) +
          (h + k) * (h + k - 1)| := by ring_nf
      _ ≤ |Q - (h + k) * (h + k - 1)| +
          |(h + k) * (h + k - 1)| := abs_add_le _ _
      _ ≤ 32 * x⁻¹ + 2 := add_le_add (by simpa only [Q] using hQerr) hpoly
      _ ≤ 18 := by linarith
  have hd0 : 0 ≤ |h - h0| + |k - h0| := by positivity
  have hE0 : 0 ≤ Real.exp M *
      (|h + k - 2 * h0| * |Real.log x|) := by positivity
  apply hbase.trans
  change
    C * (|h - h0| + |k - h0|) *
          |x ^ (h + k - 2 * h0)| *
          |centeredCrossRpowQuotient (h + k) x⁻¹| +
        (1 / 2 : ℝ) *
            (Real.exp M *
              (|h + k - 2 * h0| * |Real.log x|)) *
          |centeredCrossRpowQuotient (h + k) x⁻¹| +
        16 * x⁻¹ +
        (3 / 2 : ℝ) * (|h - h0| + |k - h0|) ≤ _
  have hfirst :
      C * (|h - h0| + |k - h0|) * |x ^ beta| ≤
        C * (|h - h0| + |k - h0|) *
          (1 + Real.exp M * (|beta| * |Real.log x|)) :=
    mul_le_mul_of_nonneg_left hpowabs (mul_nonneg hC hd0)
  have hfirst' :
      C * (|h - h0| + |k - h0|) * |x ^ beta| * |Q| ≤
        (C * (|h - h0| + |k - h0|) *
          (1 + Real.exp M * (|beta| * |Real.log x|))) * 18 :=
    mul_le_mul hfirst hQabs (abs_nonneg _)
      (mul_nonneg (mul_nonneg hC hd0) (by positivity))
  have hsecond :
      (1 / 2 : ℝ) *
          (Real.exp M * (|beta| * |Real.log x|)) * |Q| ≤
        ((1 / 2 : ℝ) *
          (Real.exp M * (|beta| * |Real.log x|))) * 18 :=
    mul_le_mul_of_nonneg_left hQabs
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (by positivity))
  calc
    _ ≤ (C * (|h - h0| + |k - h0|) *
            (1 + Real.exp M *
              (|h + k - 2 * h0| * |Real.log x|))) * 18 +
          ((1 / 2 : ℝ) *
            (Real.exp M *
              (|h + k - 2 * h0| * |Real.log x|))) * 18 +
          16 * x⁻¹ +
          (3 / 2 : ℝ) * (|h - h0| + |k - h0|) := by
      simpa only [beta, Q] using
        add_le_add (add_le_add (add_le_add hfirst' hsecond) le_rfl) le_rfl
    _ = _ := by ring

theorem firstIncrementCrossLagCorrelation_swap (h k x : ℝ) :
    firstIncrementCrossLagCorrelation h k x =
      firstIncrementCrossLagCorrelation k h x := by
  unfold firstIncrementCrossLagCorrelation
  rw [show (h + k) / 2 = (k + h) / 2 by ring,
    show h + k = k + h by ring]
  congr 1
  · ring

/-- On the midpoint grid, the frozen normalized inner product depends exactly
on the integer distance between the two q=1 left endpoints. -/
theorem normalizedFrozenIncrement_grid_inner_eq_cross_dist
    (n : ℕ) (hn : 0 < n) (H : Fin n → Ioo (0 : ℝ) 1)
    (i j : Fin (n - 1)) :
    ⟪normalizedFrozenIncrement (H (strideFirstLeft n 1 i))
        (grid n i.val) (1 / (n : ℝ)),
      normalizedFrozenIncrement (H (strideFirstLeft n 1 j))
        (grid n j.val) (1 / (n : ℝ))⟫ =
      firstIncrementCrossLagCorrelation
        (H (strideFirstLeft n 1 i))
        (H (strideFirstLeft n 1 j)) (Nat.dist i.val j.val) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rcases le_total i.val j.val with hij | hji
  · have hgrid : grid n j.val = grid n i.val +
        (j.val - i.val : ℕ) * (1 / (n : ℝ)) := by
      unfold grid
      rw [Nat.cast_sub hij]
      field_simp
      ring
    rw [Nat.dist_eq_sub_of_le hij]
    rw [hgrid]
    exact normalizedFrozenIncrement_cross_parameter_lag
      (H (strideFirstLeft n 1 i)) (H (strideFirstLeft n 1 j))
      (grid n i.val) (1 / (n : ℝ)) ((j.val - i.val : ℕ) : ℝ)
      (by positivity)
  · have hgrid : grid n i.val = grid n j.val +
        (i.val - j.val : ℕ) * (1 / (n : ℝ)) := by
      unfold grid
      rw [Nat.cast_sub hji]
      field_simp
      ring
    rw [Nat.dist_eq_sub_of_le_right hji, real_inner_comm,
      firstIncrementCrossLagCorrelation_swap]
    rw [hgrid]
    exact normalizedFrozenIncrement_cross_parameter_lag
      (H (strideFirstLeft n 1 j)) (H (strideFirstLeft n 1 i))
      (grid n j.val) (1 / (n : ℝ)) ((i.val - j.val : ℕ) : ℝ)
      (by positivity)

/-- Uniform local Hurst drift on the actual active q=1 window. -/
theorem hurstHolder_q1_active_hurst_drift
    (p M : ℝ) (hp : 1 ≤ p) (hM : 0 ≤ M) :
    ∃ L > 0, ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      ∀ n : ℕ, 0 < n → ∀ δ t : ℝ, 0 < δ → t ∈ Ioo (0 : ℝ) 1 →
      ∀ i : Fin (localWeightActiveSet n 1 δ t).card,
      |(midpointSampleHurst f hf.1 n
          (strideFirstLeft n 1 (localWeightActiveIndex n 1 δ t i)) : ℝ) -
          f t| ≤ L * (1 + M) * δ := by
  obtain ⟨L, hL, hLip⟩ := hurstHolder_uniform_lower_derivative_lipschitz p hp
  refine ⟨L, hL, ?_⟩
  intro f hf n hn δ t hδ ht i
  let ii := localWeightActiveIndex n 1 δ t i
  have hgrid := grid_mem n ii.val hn (strideFirstLeft n 1 ii).isLt
  have hactive :=
    (Finset.mem_filter.mp (localWeightActiveIndex_mem n 1 δ t i)).2
  have hdist : |grid n ii.val - t| < δ := by
    calc
      _ = δ * |(grid n ii.val - t) / δ| := by
        rw [abs_div, abs_of_pos hδ]
        field_simp
      _ < δ * 1 := mul_lt_mul_of_pos_left hactive hδ
      _ = δ := mul_one δ
  have h := hLip M hM f hf 0
    (by have := hurstHolder_floor_pos p hp; omega)
    t ht (grid n ii.val) hgrid
  simp only [iteratedDeriv_zero] at h
  change |f (grid n ii.val) - f t| ≤ L * (1 + M) * δ
  exact h.trans (mul_le_mul_of_nonneg_left hdist.le (by positivity))

/-- Fully model-specific uniform tail estimate for two active q=1 rows.  It
combines local Hurst drift, the frozen cross-tail expansion, and the actual
mBm covariance-normalization perturbation. -/
theorem hurstHolder_q1_active_scaled_actual_tail_error
    (p a b M : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∃ Ccov ≥ 0, ∃ Ctail ≥ 0, ∃ L > 0,
      ∀ n : ℕ, 0 < n → ∀ δ : ℝ, 0 < δ →
      ∀ i j : Fin (localWeightActiveSet n 1 δ t).card,
      gridCovarianceError b Ccov n ≤ 1 / 2 →
      2 ≤ (Nat.dist
        (localWeightActiveIndex n 1 δ t i).val
        (localWeightActiveIndex n 1 δ t j).val : ℝ) →
      let x := (Nat.dist
        (localWeightActiveIndex n 1 δ t i).val
        (localWeightActiveIndex n 1 δ t j).val : ℝ)
      let D := 2 * L * (1 + M) * δ
      let E := D * |Real.log x|
      |x ^ (2 - 2 * f t) *
          vectorCorrelation
            (gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
              (localWeightActiveIndex n 1 δ t i))
            (gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
              (localWeightActiveIndex n 1 δ t j)) -
          f t * (2 * f t - 1)| ≤
        18 * Ctail * D * (1 + Real.exp E * E) +
          9 * Real.exp E * E + 16 * x⁻¹ +
          (3 / 2 : ℝ) * D +
          4 * x ^ (2 - 2 * f t) * gridCovarianceError b Ccov n := by
  obtain ⟨Ccov, hCcov, hpert⟩ :=
    hurstHolder_stride_first_correlation_perturbation
      p a b M hp ha hb hab hM f hf hF 1 (by norm_num)
  obtain ⟨Ctail, hCtail, htail⟩ :=
    firstIncrementCrossLagCorrelation_scaled_error_le_explicit a b ha hb hab
  obtain ⟨L, hL, hdrift⟩ := hurstHolder_q1_active_hurst_drift p M hp hM
  refine ⟨Ccov, hCcov, Ctail, hCtail, L, hL, ?_⟩
  intro n hn δ hδ i j hsmall hlag
  let ii := localWeightActiveIndex n 1 δ t i
  let jj := localWeightActiveIndex n 1 δ t j
  let H := midpointSampleHurst f hf.1 n
  let hi : ℝ := H (strideFirstLeft n 1 ii)
  let hj : ℝ := H (strideFirstLeft n 1 jj)
  let h0 := f t
  let x : ℝ := Nat.dist ii.val jj.val
  let D := 2 * L * (1 + M) * δ
  let E := D * |Real.log x|
  have hx : 2 ≤ x := by simpa only [x, ii, jj] using hlag
  have hx0 : 0 < x := by linarith
  have hhi : hi ∈ Icc a b := by
    exact hF (grid_mem n ii.val hn (strideFirstLeft n 1 ii).isLt)
  have hhj : hj ∈ Icc a b := by
    exact hF (grid_mem n jj.val hn (strideFirstLeft n 1 jj).isLt)
  have hh0 : h0 ∈ Icc a b := hF ht
  have hdi : |hi - h0| ≤ L * (1 + M) * δ := by
    simpa only [hi, h0, H, ii] using hdrift f hf n hn δ t hδ ht i
  have hdj : |hj - h0| ≤ L * (1 + M) * δ := by
    simpa only [hj, h0, H, jj] using hdrift f hf n hn δ t hδ ht j
  have hD0 : 0 ≤ D := by dsimp only [D]; positivity
  have hd : |hi - h0| + |hj - h0| ≤ D := by
    dsimp only [D]
    linarith
  have hbeta : |hi + hj - 2 * h0| ≤ D := by
    calc
      _ = |(hi - h0) + (hj - h0)| := by congr 1 <;> ring
      _ ≤ |hi - h0| + |hj - h0| := abs_add_le _ _
      _ ≤ D := hd
  have hbetaLog :
      |hi + hj - 2 * h0| * |Real.log x| ≤ E := by
    dsimp only [E]
    exact mul_le_mul_of_nonneg_right hbeta (abs_nonneg _)
  have hlog : |(hi + hj - 2 * h0) * Real.log x| ≤ E := by
    rw [abs_mul]
    exact hbetaLog
  have hE0 : 0 ≤ E := mul_nonneg hD0 (abs_nonneg _)
  have hfrozenTail := htail hi hj h0 x (2 - 2 * h0) E
    hhi hhj hh0 hx hE0 rfl hlog
  have hfrozenTail' :
      |x ^ (2 - 2 * h0) * firstIncrementCrossLagCorrelation hi hj x -
          h0 * (2 * h0 - 1)| ≤
        18 * Ctail * D * (1 + Real.exp E * E) +
          9 * Real.exp E * E + 16 * x⁻¹ + (3 / 2 : ℝ) * D := by
    apply hfrozenTail.trans
    have hCE : 0 ≤ Real.exp E := (Real.exp_pos E).le
    have hCEprod :
        Real.exp E * (|hi + hj - 2 * h0| * |Real.log x|) ≤
          Real.exp E * E := mul_le_mul_of_nonneg_left hbetaLog hCE
    have hparen :
        1 + Real.exp E * (|hi + hj - 2 * h0| * |Real.log x|) ≤
          1 + Real.exp E * E := add_le_add le_rfl hCEprod
    have hfirst :
        18 * Ctail * (|hi - h0| + |hj - h0|) *
            (1 + Real.exp E *
              (|hi + hj - 2 * h0| * |Real.log x|)) ≤
          18 * Ctail * D * (1 + Real.exp E * E) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hd (mul_nonneg (by norm_num) hCtail))
        hparen (by positivity)
        (mul_nonneg (mul_nonneg (by norm_num) hCtail) hD0)
    have hsecond :
        9 * Real.exp E *
            (|hi + hj - 2 * h0| * |Real.log x|) ≤
          9 * Real.exp E * E :=
      mul_le_mul_of_nonneg_left hbetaLog (by positivity)
    have hfourth :
        (3 / 2 : ℝ) * (|hi - h0| + |hj - h0|) ≤
          (3 / 2 : ℝ) * D := mul_le_mul_of_nonneg_left hd (by norm_num)
    exact add_le_add (add_le_add (add_le_add hfirst hsecond) le_rfl) hfourth
  have hpert0 := hpert n hn hsmall ii jj
  have hfrozen :
      ⟪normalizedFrozenIncrement (H (strideFirstLeft n 1 ii))
          (grid n ii.val) (1 / (n : ℝ)),
        normalizedFrozenIncrement (H (strideFirstLeft n 1 jj))
          (grid n jj.val) (1 / (n : ℝ))⟫ =
        firstIncrementCrossLagCorrelation hi hj x := by
    simpa only [hi, hj, x] using
      normalizedFrozenIncrement_grid_inner_eq_cross_dist n hn H ii jj
  have hpert' :
      |vectorCorrelation (gridStrideFirstActual n 1 H ii)
          (gridStrideFirstActual n 1 H jj) -
        firstIncrementCrossLagCorrelation hi hj x| ≤
          4 * gridCovarianceError b Ccov n := by
    rw [← hfrozen]
    simpa [H] using hpert0
  have hscaledPert :
      |x ^ (2 - 2 * h0) *
          vectorCorrelation (gridStrideFirstActual n 1 H ii)
            (gridStrideFirstActual n 1 H jj) -
        x ^ (2 - 2 * h0) *
          firstIncrementCrossLagCorrelation hi hj x| ≤
        4 * x ^ (2 - 2 * h0) * gridCovarianceError b Ccov n := by
    rw [← mul_sub, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg hx0.le (2 - 2 * h0))]
    have hm := mul_le_mul_of_nonneg_left hpert'
      (Real.rpow_nonneg hx0.le (2 - 2 * h0))
    nlinarith
  have htotal := abs_sub_le
    (x ^ (2 - 2 * h0) *
      vectorCorrelation (gridStrideFirstActual n 1 H ii)
        (gridStrideFirstActual n 1 H jj))
    (x ^ (2 - 2 * h0) * firstIncrementCrossLagCorrelation hi hj x)
    (h0 * (2 * h0 - 1))
  change |x ^ (2 - 2 * h0) *
          vectorCorrelation (gridStrideFirstActual n 1 H ii)
            (gridStrideFirstActual n 1 H jj) - h0 * (2 * h0 - 1)| ≤ _
  exact htotal.trans
    (add_le_add hscaledPert hfrozenTail' |>.trans_eq (by ring))

/-- Algebraic bridge from a tail estimate at integer lag `x` to a relative
error between the actual `S`-scaled mesh entry and its Riesz reference entry. -/
theorem scaled_tail_error_to_relative_riesz
    (S x psi c r F : ℝ) (hS : 0 < S) (hx : 0 < x) (hc : 0 < c)
    (hF : 0 ≤ F) (htail : |x ^ psi * r - c| ≤ F) :
    |S ^ psi * r - c * (S / x) ^ psi| ≤
      (F / c) * |c * (S / x) ^ psi| := by
  have hxpow : 0 < x ^ psi := Real.rpow_pos_of_pos hx _
  have hratio : 0 < (S / x) ^ psi :=
    Real.rpow_pos_of_pos (div_pos hS hx) _
  have hfactor :
      S ^ psi * r - c * (S / x) ^ psi =
        (S / x) ^ psi * (x ^ psi * r - c) := by
    rw [Real.div_rpow hS.le hx.le]
    field_simp [hxpow.ne']
    <;> ring
  rw [hfactor, abs_mul, abs_of_pos hratio]
  have hm := mul_le_mul_of_nonneg_left htail hratio.le
  calc
    (S / x) ^ psi * |x ^ psi * r - c| ≤ (S / x) ^ psi * F := hm
    _ = (F / c) * |c * (S / x) ^ psi| := by
      rw [abs_mul, abs_of_pos hc, abs_of_pos hratio]
      field_simp [hc.ne']

/-- Active q=1 indices are separated by fewer than twice the effective local
sample size.  This converts the actual perturbation error into a uniform
relative off-band error. -/
theorem localWeightActiveIndex_dist_lt_two_effective
    (n : ℕ) (δ t : ℝ) (hδ : 0 < δ)
    (i j : Fin (localWeightActiveSet n 1 δ t).card) :
    (Nat.dist
        (localWeightActiveIndex n 1 δ t i).val
        (localWeightActiveIndex n 1 δ t j).val : ℝ) <
      2 * ((n : ℝ) * δ) := by
  let ii := localWeightActiveIndex n 1 δ t i
  let jj := localWeightActiveIndex n 1 δ t j
  have hi := (Finset.mem_filter.mp (localWeightActiveIndex_mem n 1 δ t i)).2
  have hj := (Finset.mem_filter.mp (localWeightActiveIndex_mem n 1 δ t j)).2
  have hi' : |grid n ii.val - t| < δ := by
    calc
      _ = δ * |(grid n ii.val - t) / δ| := by
        rw [abs_div, abs_of_pos hδ]
        field_simp
      _ < δ * 1 := mul_lt_mul_of_pos_left hi hδ
      _ = δ := mul_one δ
  have hj' : |grid n jj.val - t| < δ := by
    calc
      _ = δ * |(grid n jj.val - t) / δ| := by
        rw [abs_div, abs_of_pos hδ]
        field_simp
      _ < δ * 1 := mul_lt_mul_of_pos_left hj hδ
      _ = δ := mul_one δ
  have hn : 0 < n := by
    by_contra hn0
    have : n = 0 := Nat.eq_zero_of_not_pos hn0
    subst n
    exact Fin.elim0 ii
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hgrid :
      |grid n ii.val - grid n jj.val| =
        (Nat.dist ii.val jj.val : ℝ) / n := by
    unfold grid
    rcases le_total ii.val jj.val with hij | hji
    · have hijR : (ii.val : ℝ) ≤ jj.val := by exact_mod_cast hij
      rw [show ((ii.val : ℝ) + 1 / 2) / n -
          ((jj.val : ℝ) + 1 / 2) / n =
          ((ii.val : ℝ) - jj.val) / n by ring,
        abs_div, abs_of_pos hnR,
        abs_of_nonpos (sub_nonpos.mpr hijR),
        Nat.dist_eq_sub_of_le hij, Nat.cast_sub hij]
      ring
    · have hjiR : (jj.val : ℝ) ≤ ii.val := by exact_mod_cast hji
      rw [show ((ii.val : ℝ) + 1 / 2) / n -
          ((jj.val : ℝ) + 1 / 2) / n =
          ((ii.val : ℝ) - jj.val) / n by ring,
        abs_div, abs_of_pos hnR,
        abs_of_nonneg (sub_nonneg.mpr hjiR),
        Nat.dist_eq_sub_of_le_right hji, Nat.cast_sub hji]
  have htri : |grid n ii.val - grid n jj.val| < 2 * δ := by
    calc
      _ = |(grid n ii.val - t) - (grid n jj.val - t)| := by ring_nf
      _ ≤ |grid n ii.val - t| + |grid n jj.val - t| := abs_sub _ _
      _ < δ + δ := add_lt_add hi' hj'
      _ = 2 * δ := by ring
  rw [hgrid] at htri
  have hscaled := (div_lt_iff₀ hnR).mp htri
  dsimp only [ii, jj] at hscaled ⊢
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hscaled

end Hurst
