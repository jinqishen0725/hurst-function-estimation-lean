import Hurst.TracePowerTransfer
import Hurst.ActualFirstLongWeightedKernel
import Hurst.ActualWeightedOperatorNorm
import Hurst.LocalWeights
import Hurst.FeatureQuadraticSpectral
import Hurst.ActiveSetReindex

/-!
# Actual-mesh trace transfer (P2c prerequisite scoping lemmas)

This file pins down the deterministic Frobenius-form inputs needed to transfer
trace-power sums from the actual long-memory second-chaos matrices to their
mesh-Riesz comparison matrices.

## Scoping summary (exact definitions)

* The second-chaos spectral matrix whose eigenvalue power sums must converge is
  `weightedFeatureQuadraticMatrix v a w` = `CFC.sqrt R * diagonal w * CFC.sqrt R`
  with `R = Matrix.gram ℝ (fun k => standardizedFeatureVector v (a k))`
  (Hurst/FeatureQuadraticSpectral.lean).  Its ENTRIES are NOT `w i * w j * corr`;
  they are `(sqrt R * diagonal w * sqrt R) i j`.  However its power traces agree
  with those of the row-weighted correlation matrix `diagonal w * R`
  (`trace_pow_weightedFeatureQuadraticMatrix_eq` below, via cyclic trace).
* The mesh-Riesz comparison object in
  `hurstHolder_q1_actual_weighted_kernel_hilbertSchmidt_to_riesz` is the kernel
  array `u i * (S^psi * q1ActualLongActiveKernel ...) - equivalentKernel r (...) *
  q1RieszActiveKernel ...` measured by `realScaleMeshEnergy S K = S⁻¹² ∑ K i j²`,
  i.e. `‖K / S‖_F²`.  Mesh normalization is division by `S = n * δ`.
* The weight bound available is `localPolynomialWeights_uniform_stability`
  (from `localDesignGram_uniform_inverse`): for `0 < b ≤ 1/2`, `t ∈ Icc 0 1`,
  `N₀ ≤ n * b`, every weight satisfies `|w| ≤ C / (n * b)` and
  `∑ |w| ≤ C`, uniformly in `n, b, t`.
-/

set_option maxHeartbeats 1000000

noncomputable section
open Set Filter Matrix
open scoped Topology Matrix.Norms.Frobenius MatrixOrder
namespace Hurst

/-! ## Cyclic trace of powers -/

private theorem pow_succ'_split {κ : Type*} [Fintype κ] [DecidableEq κ]
    (X Y : Matrix κ κ ℝ) :
    ∀ j : ℕ, (X * Y) ^ (j + 1) = X * (Y * X) ^ j * Y
  | 0 => by simp
  | j + 1 => by
      calc (X * Y) ^ (j + 2) = (X * Y) ^ (j + 1) * (X * Y) :=
            pow_succ (X * Y) (j + 1)
        _ = X * (Y * X) ^ j * Y * (X * Y) := by rw [pow_succ'_split X Y j]
        _ = X * (Y * X) ^ (j + 1) * Y := by simp only [mul_assoc, pow_succ]

/-- The traces of powers of `X * Y` and `Y * X` agree for every exponent
(including `0`, where both traces are the dimension). -/
theorem trace_pow_mul_swap {κ : Type*} [Fintype κ] [DecidableEq κ]
    (X Y : Matrix κ κ ℝ) :
    ∀ k : ℕ, Matrix.trace ((X * Y) ^ k) = Matrix.trace ((Y * X) ^ k) := by
  intro k
  induction k with
  | zero => simp
  | succ k =>
      rw [pow_succ'_split X Y k, Matrix.trace_mul_cycle, ← pow_succ']

/-- Conjugating a symmetric positive matrix `R` by `CFC.sqrt R` does not change
power traces compared to the row-weighted matrix `D * R`. -/
theorem trace_pow_sqrtDiagMul_sqrt_eq {κ : Type*} [Fintype κ] [DecidableEq κ]
    (R D : Matrix κ κ ℝ) (hR : R.PosSemidef) (k : ℕ) :
    Matrix.trace ((CFC.sqrt R * D * CFC.sqrt R) ^ k)
      = Matrix.trace ((D * R) ^ k) := by
  have hsquare : CFC.sqrt R * CFC.sqrt R = R :=
    CFC.sqrt_mul_sqrt_self R (ha := hR.nonneg)
  cases k with
  | zero => simp
  | succ k =>
      rw [mul_assoc (CFC.sqrt R) D (CFC.sqrt R),
        trace_pow_mul_swap (X := CFC.sqrt R) (Y := D * CFC.sqrt R) (k + 1),
        mul_assoc D (CFC.sqrt R) (CFC.sqrt R), hsquare]

/-! ## The actual mesh-normalized correlation matrix

The entries of the mesh-normalized actual kernel of the weighted second-chaos
chain are `w'_i * corr i j` (row weights times the long-memory correlations):
exactly `diagonalCorrelationMatrix`.  This is the row-weight form; the
pair-weight form `w i * w j * corr i j` does NOT occur in the actual chain. -/

/-- Diagonal row weights times a correlation array. -/
def diagonalCorrelationMatrix {κ : Type*} [Fintype κ] [DecidableEq κ]
    (c : κ → ℝ) (corr : κ → κ → ℝ) : Matrix κ κ ℝ :=
  Matrix.diagonal c * Matrix.of corr

theorem diagonalCorrelationMatrix_apply {κ : Type*} [Fintype κ] [DecidableEq κ]
    (c : κ → ℝ) (corr : κ → κ → ℝ) (i j : κ) :
    diagonalCorrelationMatrix c corr i j = c i * corr i j := by
  rw [diagonalCorrelationMatrix]
  simp

/-- Frobenius norm of the mesh-normalized actual correlation matrix under a
uniform correlation bound. -/
theorem frobenius_norm_diagonalCorrelationMatrix_le {κ : Type*} [Fintype κ]
    [DecidableEq κ] (c : κ → ℝ) (corr : κ → κ → ℝ) (hcorr : ∀ i j, |corr i j| ≤ 1) :
    ‖diagonalCorrelationMatrix c corr‖
      ≤ Real.sqrt ((Fintype.card κ : ℝ) * ∑ i, c i ^ 2) := by
  have hnorm : ‖diagonalCorrelationMatrix c corr‖
      = Real.sqrt (∑ i, ∑ j, |diagonalCorrelationMatrix c corr i j| ^ 2) := by
    rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
    congr 1
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by simp [Real.norm_eq_abs]
  have hsq : (∑ i, ∑ j, |diagonalCorrelationMatrix c corr i j| ^ 2)
      ≤ (Fintype.card κ : ℝ) * ∑ i, c i ^ 2 := by
    have hrow : ∀ i : κ,
        (∑ j, |diagonalCorrelationMatrix c corr i j| ^ 2) ≤ (Fintype.card κ : ℝ) * c i ^ 2 := by
      intro i
      calc (∑ j, |diagonalCorrelationMatrix c corr i j| ^ 2)
          = ∑ j, (|c i| * |corr i j|) ^ 2 := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [diagonalCorrelationMatrix_apply, abs_mul]
        _ ≤ ∑ _j : κ, c i ^ 2 := by
            apply Finset.sum_le_sum
            intro j _
            rw [mul_pow, sq_abs]
            exact (mul_le_mul le_rfl
              (pow_le_one₀ (abs_nonneg (corr i j)) (hcorr i j)) (sq_nonneg _)
              (sq_nonneg _)).trans_eq (mul_one _)
        _ = (Fintype.card κ : ℝ) * c i ^ 2 := by simp
    calc (∑ i, ∑ j, |diagonalCorrelationMatrix c corr i j| ^ 2)
        ≤ ∑ i, ((Fintype.card κ : ℝ) * c i ^ 2) := by
          exact Finset.sum_le_sum fun i _ => hrow i
      _ = (Fintype.card κ : ℝ) * ∑ i, c i ^ 2 := by
          rw [Finset.mul_sum]
  rw [hnorm]
  exact Real.sqrt_le_sqrt hsq

/-! ## Generic pair-weight Frobenius bound -/

/-- If every entry is bounded by the product of two weights, the Frobenius norm
is bounded by the weight energy `∑ w i ^ 2`. -/
theorem frobenius_norm_le_sum_sq_of_entry_le {κ : Type*} [Fintype κ]
    (M : Matrix κ κ ℝ) (w : κ → ℝ) (h : ∀ i j, |M i j| ≤ |w i * w j|) :
    ‖M‖ ≤ ∑ i, w i ^ 2 := by
  have hnorm : ‖M‖ = Real.sqrt (∑ i, ∑ j, |M i j| ^ 2) := by
    rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
    congr 1
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by simp [Real.norm_eq_abs]
  have hsq : (∑ i, ∑ j, |M i j| ^ 2) ≤ (∑ i, w i ^ 2) ^ 2 := by
    calc (∑ i, ∑ j, |M i j| ^ 2)
        ≤ ∑ i, ∑ j, (|w i| * |w j|) ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          have hj := h i j
          rw [abs_mul] at hj
          exact pow_le_pow_left₀ (abs_nonneg _) hj 2
      _ = ∑ i, ∑ j, |w i| ^ 2 * |w j| ^ 2 := by simp_rw [mul_pow]
      _ = ∑ i, (|w i| ^ 2 * ∑ j, |w j| ^ 2) := by simp_rw [← Finset.mul_sum]
      _ = (∑ i, |w i| ^ 2) * (∑ j, |w j| ^ 2) := by simp_rw [Finset.sum_mul]
      _ = (∑ i, w i ^ 2) ^ 2 := by
          have h1 : ∑ i, |w i| ^ 2 = ∑ i, w i ^ 2 := by
            exact Finset.sum_congr rfl fun i _ => by rw [sq_abs]
          rw [h1, pow_two]
  rw [hnorm]
  exact (Real.sqrt_le_sqrt hsq).trans
    (by rw [Real.sqrt_sq_eq_abs, abs_eq_self.2 (Finset.sum_nonneg fun i _ => sq_nonneg _)])

/-! ## Fintype trace-power transfer (varying index types) -/

/-- `abs_trace_le_sqrt_card_mul_frobenius` for an arbitrary finite index type. -/
theorem abs_trace_le_sqrt_card_frobenius {κ : Type*} [Fintype κ]
    (Z : Matrix κ κ ℝ) :
    |Matrix.trace Z| ≤ Real.sqrt (Fintype.card κ) * ‖Z‖ := by
  have hnorm : ‖Z‖ = Real.sqrt (∑ i, ∑ j, |Z i j| ^ 2) := by
    rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
    congr 1
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by simp [Real.norm_eq_abs]
  have h3 : Real.sqrt (∑ i, |Z i i| ^ 2)
      ≤ Real.sqrt (∑ i, ∑ j, |Z i j| ^ 2) :=
    Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ =>
      Finset.single_le_sum (f := fun j => |Z i j| ^ 2) (fun j _ => by positivity)
        (Finset.mem_univ i))
  calc |Matrix.trace Z| = |∑ i, Z i i| := by simp [Matrix.trace, Matrix.diag]
    _ ≤ ∑ i, |Z i i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (1 * |Z i i|) := by simp
    _ ≤ Real.sqrt (∑ _i : κ, (1 : ℝ) ^ 2) * Real.sqrt (∑ i, |Z i i| ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _ => 1) (fun i => |Z i i|)
    _ ≤ Real.sqrt (Fintype.card κ) * Real.sqrt (∑ i, ∑ j, |Z i j| ^ 2) :=
        mul_le_mul (show Real.sqrt (∑ _i : κ, (1 : ℝ) ^ 2) ≤ Real.sqrt (Fintype.card κ) from
          by simp) h3 (by simp) (Real.sqrt_nonneg _)
    _ = Real.sqrt (Fintype.card κ) * ‖Z‖ := by rw [hnorm]

/-- `abs_trace_pow_sub_le` for an arbitrary finite index type: the
Frobenius-norm perturbation bound for traces of matrix powers. -/
theorem abs_trace_pow_sub_le_of_fintype {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A B : Matrix κ κ ℝ) (k : ℕ) :
    |Matrix.trace (A ^ k) - Matrix.trace (B ^ k)|
      ≤ Real.sqrt (Fintype.card κ)
        * (k * (max ‖A‖ ‖B‖) ^ (k - 1) * ‖A - B‖) := by
  have hL : ∀ (s : ℕ) (Y : Matrix κ κ ℝ),
      ‖A ^ s * Y‖ ≤ ‖A‖ ^ s * ‖Y‖ := by
    intro s
    induction s with
    | zero => intro Y; simp
    | succ s ih =>
      intro Y
      calc ‖A ^ (s + 1) * Y‖ = ‖A ^ s * (A * Y)‖ := by rw [pow_succ, mul_assoc]
        _ ≤ ‖A‖ ^ s * ‖A * Y‖ := ih (A * Y)
        _ ≤ ‖A‖ ^ s * (‖A‖ * ‖Y‖) :=
            mul_le_mul_of_nonneg_left (Matrix.frobenius_norm_mul A Y)
              (pow_nonneg (norm_nonneg A) s)
        _ = ‖A‖ ^ (s + 1) * ‖Y‖ := by rw [pow_succ]; ring
  have hR : ∀ (Y : Matrix κ κ ℝ) (s : ℕ),
      ‖Y * B ^ s‖ ≤ ‖Y‖ * ‖B‖ ^ s := by
    intro Y s
    induction s with
    | zero => simp
    | succ s ih =>
      calc ‖Y * B ^ (s + 1)‖ = ‖Y * B ^ s * B‖ := by rw [pow_succ, ← mul_assoc]
        _ ≤ ‖Y * B ^ s‖ * ‖B‖ := Matrix.frobenius_norm_mul _ _
        _ ≤ (‖Y‖ * ‖B‖ ^ s) * ‖B‖ :=
            mul_le_mul_of_nonneg_right ih (norm_nonneg B)
        _ = ‖Y‖ * ‖B‖ ^ (s + 1) := by rw [pow_succ]; ring
  have hterm : ∀ t ∈ Finset.range k,
      ‖A ^ (k - 1 - t) * (A - B) * B ^ t‖ ≤ (max ‖A‖ ‖B‖) ^ (k - 1) * ‖A - B‖ := by
    intro t ht
    have hnp : 0 ≤ ‖A‖ ^ (k - 1 - t) := pow_nonneg (norm_nonneg A) (k - 1 - t)
    have e1 : ‖A ^ (k - 1 - t) * (A - B) * B ^ t‖
        ≤ ‖A‖ ^ (k - 1 - t) * (‖A - B‖ * ‖B‖ ^ t) := by
      rw [mul_assoc]
      exact le_trans (hL (k - 1 - t) ((A - B) * B ^ t))
        (mul_le_mul_of_nonneg_left (hR (A - B) t) hnp)
    have e2 : ‖A‖ ^ (k - 1 - t) * (‖A - B‖ * ‖B‖ ^ t)
        ≤ (max ‖A‖ ‖B‖) ^ (k - 1) * ‖A - B‖ := by
      have h3 : ‖A‖ ^ (k - 1 - t) * (‖A - B‖ * ‖B‖ ^ t)
          = (‖A‖ ^ (k - 1 - t) * ‖B‖ ^ t) * ‖A - B‖ := by
        rw [mul_comm ‖A - B‖ (‖B‖ ^ t), mul_assoc]
      rw [h3]
      exact mul_le_mul_of_nonneg_right
        (pow_mul_pow_le_max_pow ‖A‖ ‖B‖ (norm_nonneg A) (norm_nonneg B) k t
          (Finset.mem_range.mp ht)) (norm_nonneg (A - B))
    exact e1.trans e2
  calc |Matrix.trace (A ^ k) - Matrix.trace (B ^ k)|
      = |Matrix.trace (A ^ k - B ^ k)| := by rw [Matrix.trace_sub]
    _ = |∑ t ∈ Finset.range k,
          Matrix.trace (A ^ (k - 1 - t) * (A - B) * B ^ t)| := by
        rw [matrix_pow_sub_pow_telescope, Matrix.trace_sum]
    _ ≤ ∑ t ∈ Finset.range k,
          |Matrix.trace (A ^ (k - 1 - t) * (A - B) * B ^ t)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ Finset.range k,
          (Real.sqrt (Fintype.card κ) * ‖A ^ (k - 1 - t) * (A - B) * B ^ t‖) :=
        Finset.sum_le_sum fun t _ => abs_trace_le_sqrt_card_frobenius _
    _ = Real.sqrt (Fintype.card κ) * ∑ t ∈ Finset.range k,
          ‖A ^ (k - 1 - t) * (A - B) * B ^ t‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ Real.sqrt (Fintype.card κ)
          * (k * (max ‖A‖ ‖B‖) ^ (k - 1) * ‖A - B‖) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
        calc ∑ t ∈ Finset.range k, ‖A ^ (k - 1 - t) * (A - B) * B ^ t‖
            ≤ ∑ t ∈ Finset.range k, ((max ‖A‖ ‖B‖) ^ (k - 1) * ‖A - B‖) :=
              Finset.sum_le_sum hterm
          _ = k * (max ‖A‖ ‖B‖) ^ (k - 1) * ‖A - B‖ := by
              rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range, mul_assoc]

/-! ## Mesh-normalized trace-power convergence (deliverable 3)

If two eventually-Frobenius-bounded matrix arrays differ by at most
`sqrt(2 / card) * δ n` in Frobenius norm with `δ n → 0`, then every fixed power
trace difference tends to zero.  The dimension factor `sqrt (card)` cancels
against `sqrt (2 / card)`, leaving `sqrt 2 * δ n`. -/
theorem mesh_frobenius_trace_pow_tendsto
    (κ : ℕ → Type*) [∀ n, Fintype (κ n)] [∀ n, DecidableEq (κ n)]
    (A G : ∀ n, Matrix (κ n) (κ n) ℝ) (δ : ℕ → ℝ)
    (C : ℝ)
    (hC : ∀ᶠ n in atTop, max ‖A n‖ ‖G n‖ ≤ C)
    (hΔ : ∀ᶠ n in atTop,
      ‖A n - G n‖ ≤ Real.sqrt (2 / (Fintype.card (κ n) : ℝ)) * δ n)
    (hδpos : ∀ᶠ n in atTop, 0 ≤ δ n)
    (hδ : Tendsto δ atTop (𝓝 0)) (k : ℕ) :
    Tendsto (fun n => |Matrix.trace ((A n) ^ k) - Matrix.trace ((G n) ^ k)|)
      atTop (𝓝 0) := by
  have hcard : ∀ n : ℕ,
      (Fintype.card (κ n) : ℝ) * (2 / (Fintype.card (κ n) : ℝ)) ≤ 2 := by
    intro n
    rcases Nat.eq_zero_or_pos (Fintype.card (κ n)) with h0 | h0
    · simp [show Fintype.card (κ n) = 0 from h0]
    · have hne : (Fintype.card (κ n) : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt h0
      exact (mul_div_cancel₀ 2 hne).le
  have hkey : ∀ n : ℕ, Real.sqrt (Fintype.card (κ n)) * Real.sqrt (2 / (Fintype.card (κ n) : ℝ))
      ≤ Real.sqrt 2 := by
    intro n
    have hnonneg : 0 ≤ (Fintype.card (κ n) : ℝ) * (2 / (Fintype.card (κ n) : ℝ)) := by
      positivity
    have h1 : Real.sqrt (Fintype.card (κ n)) * Real.sqrt (2 / (Fintype.card (κ n) : ℝ))
        = Real.sqrt ((Fintype.card (κ n) : ℝ) * (2 / (Fintype.card (κ n) : ℝ))) :=
      (Real.sqrt_mul (by positivity : 0 ≤ (Fintype.card (κ n) : ℝ))
        (2 / (Fintype.card (κ n) : ℝ))).symm
    rw [h1]
    exact Real.sqrt_le_sqrt (hcard n)
  have hupperTendsto : Tendsto (fun n : ℕ => ((k * C ^ (k - 1)) * Real.sqrt 2) * δ n)
      atTop (𝓝 0) := by
    simpa using hδ.const_mul ((k * C ^ (k - 1)) * Real.sqrt 2)
  refine squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_ hupperTendsto
  filter_upwards [hC, hΔ, hδpos] with n hCn hΔn hδn
  have hC0 : 0 ≤ C :=
    le_trans (le_trans (norm_nonneg (A n)) (le_max_left ‖A n‖ ‖G n‖)) hCn
  have hCk : 0 ≤ k * C ^ (k - 1) := mul_nonneg (Nat.cast_nonneg k) (pow_nonneg hC0 _)
  have hmax : (max ‖A n‖ ‖G n‖) ^ (k - 1) ≤ C ^ (k - 1) :=
    pow_le_pow_left₀ (le_trans (norm_nonneg (A n)) (le_max_left ‖A n‖ ‖G n‖)) hCn _
  have hupper : 0 ≤ k * C ^ (k - 1) * (Real.sqrt (2 / (Fintype.card (κ n) : ℝ)) * δ n) :=
    mul_nonneg hCk (mul_nonneg (Real.sqrt_nonneg _) hδn)
  calc |Matrix.trace ((A n) ^ k) - Matrix.trace ((G n) ^ k)|
      ≤ Real.sqrt (Fintype.card (κ n))
        * (k * (max ‖A n‖ ‖G n‖) ^ (k - 1) * ‖A n - G n‖) :=
        abs_trace_pow_sub_le_of_fintype (A n) (G n) k
    _ ≤ Real.sqrt (Fintype.card (κ n))
        * (k * C ^ (k - 1) * (Real.sqrt (2 / (Fintype.card (κ n) : ℝ)) * δ n)) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
        calc k * (max ‖A n‖ ‖G n‖) ^ (k - 1) * ‖A n - G n‖
            ≤ k * C ^ (k - 1) * ‖A n - G n‖ :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hmax (Nat.cast_nonneg k))
                (norm_nonneg (A n - G n))
          _ ≤ k * C ^ (k - 1) * (Real.sqrt (2 / (Fintype.card (κ n) : ℝ)) * δ n) :=
              mul_le_mul_of_nonneg_left hΔn hCk
    _ = (k * C ^ (k - 1)) * ((Real.sqrt (Fintype.card (κ n))
          * Real.sqrt (2 / (Fintype.card (κ n) : ℝ))) * δ n) := by ring
    _ ≤ (k * C ^ (k - 1)) * (Real.sqrt 2 * δ n) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hkey n) hδn) hCk
    _ = ((k * C ^ (k - 1)) * Real.sqrt 2) * δ n := by ring

/-! ## Actual chain weight bounds (deliverable 1)

Uniform ℓ∞ bounds for the local-polynomial weights from the uniform
inverse-Gram bound `localDesignGram_uniform_inverse` (via
`localPolynomialWeights_uniform_stability`). -/

/-- Eventual ℓ∞ weight bound along the mesh scale `n * δ`: every local
polynomial weight is `O(1 / (n δ))` once `δ ≤ 1/2` and `n δ → ∞`. -/
theorem localWeights_linf_eventually_of_meshScale (r : ℕ) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) (δ : ℕ → ℝ)
    (hδpos : ∀ᶠ n in atTop, 0 < δ n) (hδle : ∀ᶠ n in atTop, δ n ≤ 1 / 2)
    (hS : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop) :
    ∃ C > 0, ∀ᶠ n in atTop, ∀ i : Fin (n - 1),
      |localPolynomialWeights r n 1 (δ n) t i| ≤ C / ((n : ℝ) * δ n) := by
  obtain ⟨N₀, hN₀, Cw, hCw, hstab⟩ := localPolynomialWeights_uniform_stability r 1
  refine ⟨Cw, hCw, ?_⟩
  filter_upwards [hδpos, hδle, hS.eventually_ge_atTop N₀,
    eventually_ge_atTop 1] with n hpos hle hN hn1
  have hn : 0 < n := by omega
  have hres := hstab n hn hn1 (δ n) t hpos hle ht hN
  exact hres.2.1

/-- The actual second-chaos chain weights `u n j = S n * w n (active j)` are
eventually uniformly bounded, where `w n = localPolynomialWeights r n 1 (δ n) t`
and the active reindexing is `localWeightActiveIndex n 1 (δ n) t j`. -/
theorem actualLongChainWeight_bound (r : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (δ : ℕ → ℝ)
    (hδpos : ∀ᶠ n in atTop, 0 < δ n) (hδle : ∀ᶠ n in atTop, δ n ≤ 1 / 2)
    (hS : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop) :
    ∃ C > 0, ∀ᶠ n in atTop,
      ∀ j : Fin (localWeightActiveSet n 1 (δ n) t).card,
        |(n : ℝ) * δ n * localPolynomialWeights r n 1 (δ n) t
            (localWeightActiveIndex n 1 (δ n) t j)| ≤ C := by
  obtain ⟨Cw, hCw, hbound⟩ := localWeights_linf_eventually_of_meshScale r t ht δ
    hδpos hδle hS
  refine ⟨Cw, hCw, ?_⟩
  filter_upwards [hbound, hδpos, eventually_ge_atTop 1] with n hb hpos hn1
  intro j
  have hn0 : 0 < n := by omega
  have hSn : 0 < (n : ℝ) * δ n := by
    have h1 : 0 < (n : ℝ) := by exact_mod_cast hn0
    positivity
  have h := hb (localWeightActiveIndex n 1 (δ n) t j)
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) * δ n)]
  calc (n : ℝ) * δ n * |localPolynomialWeights r n 1 (δ n) t
        (localWeightActiveIndex n 1 (δ n) t j)|
      ≤ (n : ℝ) * δ n * (Cw / ((n : ℝ) * δ n)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = Cw := mul_div_cancel₀ Cw (ne_of_gt hSn)

/-! ## Power traces of the actual spectral matrix (deliverable 2)

The exact second-chaos spectral matrix is `weightedFeatureQuadraticMatrix v a w`
(its law realizes the quadratic statistic under `stdGaussian`, see
`FeatureQuadraticSpectral`).  Its power traces equal those of the
mesh-normalized actual correlation matrix `diagonalCorrelationMatrix w corr`
with `corr i j = featureCorrelation v (a i) (a j)`, so Frobenius control of the
latter transfers to the former.  Note the entries of the spectral matrix itself
are NOT `w i * w j * corr i j` (they involve `CFC.sqrt` of the Gram matrix);
the honest row-weight form is the one below. -/

theorem trace_pow_weightedFeatureQuadraticMatrix_eq
    {ι κ E : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (a : κ → EuclideanSpace ℝ ι) (w : κ → ℝ) (k : ℕ) :
    Matrix.trace ((weightedFeatureQuadraticMatrix v a w) ^ k)
      = Matrix.trace ((diagonalCorrelationMatrix w
          (fun i j => featureCorrelation v (a i) (a j))) ^ k) := by
  have hgram : Matrix.gram ℝ (fun k ↦ standardizedFeatureVector v (a k))
      = Matrix.of (fun i j => featureCorrelation v (a i) (a j)) := by
    ext i j
    simp [Matrix.gram, standardizedFeatureVector_inner]
  have hA : weightedFeatureQuadraticMatrix v a w
      = CFC.sqrt (Matrix.gram ℝ (fun k ↦ standardizedFeatureVector v (a k)))
          * Matrix.diagonal w
        * CFC.sqrt (Matrix.gram ℝ (fun k ↦ standardizedFeatureVector v (a k))) :=
    rfl
  have hpsd : (Matrix.gram ℝ (fun k ↦ standardizedFeatureVector v (a k))).PosSemidef :=
    Matrix.posSemidef_gram ℝ (fun k ↦ standardizedFeatureVector v (a k))
  rw [hA, trace_pow_sqrtDiagMul_sqrt_eq _ (Matrix.diagonal w) hpsd k, hgram,
    diagonalCorrelationMatrix]

/-- Entrywise bound of the actual mesh-normalized correlation matrix:
every entry is at most the row weight in absolute value. -/
theorem diagonalCorrelationMatrix_abs_le_of_corr {κ : Type*} [Fintype κ] [DecidableEq κ]
    (c : κ → ℝ) (corr : κ → κ → ℝ) (hcorr : ∀ i j, |corr i j| ≤ 1) (i j : κ) :
    |diagonalCorrelationMatrix c corr i j| ≤ |c i| := by
  rw [diagonalCorrelationMatrix_apply, abs_mul]
  calc |c i| * |corr i j| ≤ |c i| * 1 :=
          mul_le_mul_of_nonneg_left (hcorr i j) (abs_nonneg (c i))
    _ = |c i| := by rw [mul_one]

end Hurst
