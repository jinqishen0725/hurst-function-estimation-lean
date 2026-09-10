import Hurst.Corrections
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section
open scoped BigOperators
namespace Hurst

/-- Bias and stochastic error after inverse transformation, (3.4). -/
def T1 (n b p psi : ℝ) : ℝ :=
  Real.log n * (b^p + (n*b)^(-min 2 p)) + Real.log n / n + n^(-psi)
def T2 (n b d psi : ℝ) : ℝ :=
  if d < 2*psi then (n*b)^(-d)
  else if d = 2*psi then (n*b)^(-d)*Real.log (n*b)
  else (n*b)^(-2*psi)
def psi (q H : ℝ) := 2*q-2*H

theorem short_memory_q1_d1 (H : ℝ) : 1 < 2*psi 1 H ↔ H < 3/4 := by
  unfold psi; constructor <;> intro h <;> linarith

theorem short_memory_q1_d2 (H : ℝ) : 2 < 2*psi 1 H ↔ H < 1/2 := by
  unfold psi; constructor <;> intro h <;> linarith

theorem short_memory_q1_d3 (H : ℝ) : 3 < 2*psi 1 H ↔ H < 1/4 := by
  unfold psi; constructor <;> intro h <;> linarith

theorem short_memory_q2 (H d : ℝ) (hH : H < 1) (hd : d ≤ 3) : d < 2*psi 2 H := by
  unfold psi; linarith

/-- Exact balance defining the optimal bandwidth; no asymptotic stochastic premise. -/
theorem bandwidth_balance (n b L p d : ℝ) (hn : 0 < n) (hb : 0 < b)
    (he : b^(2*p+d) = (n^d * L^2)⁻¹) :
    b^(2*p) = (n*b)^(-d) / L^2 := by
  have hnd : n^d ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hn d)
  have hbd : b^d ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hb d)
  rw [Real.rpow_add hb] at he
  rw [Real.mul_rpow hn.le hb.le, Real.rpow_neg hn.le, Real.rpow_neg hb.le]
  have he' := congrArg (fun x : ℝ => x / b^d) he
  simpa [mul_inv, div_eq_mul_inv, hbd, mul_assoc, mul_comm, mul_left_comm] using he'

/-- Exponent governing the quadrature remainder in (3.5). -/
theorem quadrature_exponent (p d r : ℝ) (h : 2*p+d ≠ 0) :
    -r + d*(p+r)/(2*p+d) = p*(d-2*r)/(2*p+d) := by
  apply (eq_div_iff h).2
  rw [add_mul, div_mul_cancel₀ _ h]
  ring

theorem d3_p_three_halves_boundary :
    -(3/2:ℝ) + 3*((3/2)+(3/2))/(2*(3/2)+3) = 0 ∧
    (2:ℝ)*((3/2)+(3/2))/(2*(3/2)+3) = 1 := by norm_num

/-- MSE transfer used in 3.4 and 4.3, with explicit numerical hypotheses. -/
theorem inverse_mse_bound (x e L : ℝ) (hL : 0 < L)
    (he : |x| ≤ |e|/(2*L)) : x^2 ≤ e^2/(4*L^2) := by
  have h : x^2 ≤ (|e|/(2*L))^2 := by
    have hh := mul_self_le_mul_self (abs_nonneg x) he
    simpa [← sq, sq_abs] using hh
  calc
    x^2 ≤ (|e|/(2*L))^2 := h
    _ = e^2/(4*L^2) := by rw [div_pow, mul_pow, sq_abs]; norm_num

theorem error_sum_square (x y : ℝ) : (x+y)^2 ≤ 2*x^2+2*y^2 := by
  nlinarith [sq_nonneg (x-y)]

theorem bias_variance_bound (m v B V : ℝ) (_hB : 0 ≤ B)
    (hm : |m| ≤ B) (hv : v ≤ V) : v+m^2 ≤ V+B^2 := by
  have hh : m^2 ≤ B^2 := by
    have hh := mul_self_le_mul_self (abs_nonneg m) hm
    simpa [← sq, sq_abs] using hh
  linarith

/-- The exact local remainder estimate that turns a Gaussian KL expression
into a Frobenius bound in Proposition 8.1. -/
theorem log_quadratic_remainder (x : ℝ) (hx : |x| ≤ 1/2) :
    |Real.log (1+x)-x| ≤ 2*x^2 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -x) (by simpa using lt_of_le_of_lt hx (by norm_num : (1/2:ℝ)<1)) 1
  norm_num [Finset.sum_range_succ, sub_neg_eq_add] at h
  have hd : 0 < 1-|x| := by linarith
  have hh : |x|^2/(1-|x|) ≤ 2*x^2 := by
    apply (div_le_iff₀ hd).mpr
    rw [sq_abs]
    nlinarith [sq_nonneg x, mul_nonneg (sq_nonneg x) (show 0 ≤ 1-2*|x| by linarith)]
  calc
    |Real.log (1+x)-x| = |-x+Real.log (1+x)| := by congr 1; ring
    _ ≤ |x|^2/(1-|x|) := by simpa only [sq_abs] using h
    _ ≤ 2*x^2 := hh

def spectralKL {ι : Type*} (s : Finset ι) (ev : ι → ℝ) : ℝ :=
  (1/2) * ∑ i ∈ s, (ev i - Real.log (1+ev i))

theorem spectralKL_bound {ι : Type*} (s : Finset ι) (ev : ι → ℝ)
    (hev : ∀ i ∈ s, |ev i| ≤ 1/2) :
    0 ≤ spectralKL s ev ∧ spectralKL s ev ≤ ∑ i ∈ s, (ev i)^2 := by
  have hterm : ∀ i ∈ s, 0 ≤ ev i-Real.log (1+ev i) := by
    intro i hi
    have hx := (abs_le.mp (hev i hi)).1
    have hlog := Real.log_le_sub_one_of_pos (show 0 < 1+ev i by linarith)
    linarith
  constructor
  · exact mul_nonneg (by norm_num) (Finset.sum_nonneg hterm)
  · have hsum : (∑ i ∈ s, (ev i-Real.log (1+ev i))) ≤ ∑ i ∈ s, 2*(ev i)^2 := by
      apply Finset.sum_le_sum
      intro i hi
      have h := log_quadratic_remainder (ev i) (hev i hi)
      have he : |Real.log (1+ev i)-ev i| = ev i-Real.log (1+ev i) := by
        rw [abs_of_nonpos (by linarith [hterm i hi])]; ring
      rwa [he] at h
    rw [← Finset.mul_sum] at hsum
    unfold spectralKL
    linarith

theorem symmetric_trace_square {ι : Type*} [Fintype ι] (D : ι → ι → ℝ)
    (hs : ∀ i j, D i j = D j i) :
    (∑ i, ∑ j, D i j * D j i) = ∑ i, ∑ j, (D i j)^2 := by
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← hs i j]; ring

end Hurst
