import Hurst.FrozenQuadratureFinal
import Hurst.BandRemovalSharp
import Hurst.MatrixWordExpansion
import Hurst.BandPowerSum
import Hurst.FrozenQuadratureRun
import Hurst.MatrixFrobeniusTrace

/-!
# The far-band word assembly: the trace-difference engine and its inputs

This file lands the word-level assembly feeding the `hFarWord` hypothesis of
`Hurst.frozenQuad_hFquad_of_farWord` (the last assembly of the corrected
route).  The full analytic instantiation (producing the entry envelope for the
ACTUAL frozen-vs-Riesz difference from the row-profile bridge (A) and the
far-band per-entry envelope (B2)) remains open — see the honest gap note at
the bottom — but the entire WORD/TRACE engine between the entry envelope and
`hFarWord` is proved here, together with the stratified Frobenius bound that
converts the `16 * d^{-(1+psi)}` RELATIVE far-band decay + near-band
boundedness into Frobenius vanishing.

## What is landed here

1. **The telescope** `matrix_pow_sub_sum_range`:
   `F ^ k - T ^ k = ∑ s ∈ range k, F ^ s * (F - T) * T ^ (k - 1 - s)`.
2. **The sharp trace-difference bound** `abs_trace_pow_sub_le_frob`: with
   `‖F‖, ‖T‖ ≤ M`,
   `|tr(F ^ k) - tr(T ^ k)| ≤ k * M ^ (k - 1) * ‖F - T‖`
   — only the Frobenius norm of the DIFFERENCE carries the smallness; the
   scales of `F` and `T` enter through the bounded `M` alone (no `sqrt m`,
   no entry-count loss).
3. **The vanishing of the difference scale from the far-band relative decay**
   `frobenius_le_of_entry_envelope`: if every entry of `Δ` is bounded by `b`
   on the near band (`Nat.dist ≤ 1`) and by the RELATIVE power law
   `a * d^{-(1+psi)}` on the far band (`d ≥ 2`), then
   `‖Δ‖² ≤ m * (4 * b² + 6 * a²)` — using the row distance stratification
   `sum_row_dist_le` (each integer distance occurs at most twice per row) and
   the convergence of `∑ d^{-(2+2ψ)}` for `ψ > 0`.  Feeding
   `b = S^{ψ-1} * B_near`, `a = S^{ψ-1} * A` this is `O(S^{2ψ-1}) → 0`
   (since `2 * ψ < 1`).
4. **The `hFarWord` glue** `farWord_of_frobeniusSmall`: eventual uniform
   Frobenius bounds `‖F_n‖, ‖T_n‖ ≤ B` on the frozen and Riesz quadrature
   matrices PLUS `‖F_n - T_n‖_F → 0` imply the exact `hFarWord` shape
   `∀ eps > 0, ∀ᶠ n in atTop, |tr(F_n ^ k) - tr(T_n ^ k)| < eps`; and
   `frozenQuad_hFquad_of_frobeniusSmall` composes it with
   `Hurst.frozenQuad_hFquad_of_farWord` into the full frozen quadrature.

## Honest gap note (the remaining analytic step)

What remains open is the production of the two Frobenius inputs for the actual
matrices: (a) the eventual uniform Frobenius bounds `‖F_n‖, ‖T_n‖ ≤ B` (the
Riesz side reduces to the `2ψ < 1` band power sums of `Hurst.BandPowerSum`
against the `S^{ψ-1}`-normalization; the frozen side additionally needs the
uniform `S^{ψ-1}`-scaled entry bound on the far band), and (b) the entry
envelope of `Δ_n = F_n - T_n` in the EXACT two-constant form of
`frobenius_le_of_entry_envelope` — the far-band `16 * d^{-(1+ψ)}` relative
decay of (B2) matches, but (B2)'s `eps * B + B_omega * eps` profile/class
error terms are NOT `d^{-(1+ψ)}`-decaying, so closing them requires either
the word-level relative machinery or a rate-refined concentration analysis.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Set Filter Matrix
open scoped Matrix.Norms.Frobenius Topology

namespace Hurst

/-! ### Frobenius power and product bounds -/

/-- Frobenius submultiplicativity against a fixed power on the right. -/
private theorem frobenius_mul_pow_le {m : ℕ} (A T : Matrix (Fin m) (Fin m) ℝ) :
    ∀ u : ℕ, ‖A * T ^ u‖ ≤ ‖A‖ * ‖T‖ ^ u := by
  intro u
  induction u with
  | zero => simp
  | succ u ih =>
      calc ‖A * T ^ (u + 1)‖
          = ‖(A * T ^ u) * T‖ := by
              rw [pow_succ, ← Matrix.mul_assoc]
        _ ≤ ‖A * T ^ u‖ * ‖T‖ := Matrix.frobenius_norm_mul _ _
        _ ≤ (‖A‖ * ‖T‖ ^ u) * ‖T‖ := mul_le_mul_of_nonneg_right ih (norm_nonneg _)
        _ = ‖A‖ * ‖T‖ ^ (u + 1) := by rw [pow_succ]; ring

/-- Frobenius norm of a NONTRIVIAL matrix power is at most the power of the
norm (at `s = 0` the statement would be false: `‖1‖ = √m ≥ 1`). -/
private theorem frobenius_pow_le {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) :
    ∀ t : ℕ, ‖A ^ (t + 1)‖ ≤ ‖A‖ ^ (t + 1) := by
  intro t
  induction t with
  | zero => rw [pow_one, pow_one]
  | succ t ih =>
      calc ‖A ^ (t + 2)‖ = ‖A ^ (t + 1) * A‖ := by rw [pow_succ]
        _ ≤ ‖A ^ (t + 1)‖ * ‖A‖ := Matrix.frobenius_norm_mul _ _
        _ ≤ ‖A‖ ^ (t + 1) * ‖A‖ := mul_le_mul_of_nonneg_right ih (norm_nonneg _)
        _ = ‖A‖ ^ (t + 2) := by rw [pow_succ ‖A‖ (t + 1)]

/-- Wrap of `frobenius_pow_le` for an arbitrary exponent `s ≥ 1`. -/
private theorem frobenius_pow_le_one {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ)
    (s : ℕ) (hs : 1 ≤ s) : ‖A ^ s‖ ≤ ‖A‖ ^ s := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  exact frobenius_pow_le A t

/-! ### The telescope identity -/

/-- **The telescope.**  `F ^ k - T ^ k` is the sum over the `k` positions of
the insertion of the difference `F - T`, with an `F`-prefix and a `T`-suffix:
`F ^ k - T ^ k = ∑ s ∈ range k, F ^ s * (F - T) * T ^ (k - 1 - s)`. -/
theorem matrix_pow_sub_sum_range {m : ℕ} (F T : Matrix (Fin m) (Fin m) ℝ) :
    ∀ k : ℕ, F ^ k - T ^ k
      = ∑ s ∈ Finset.range k, F ^ s * (F - T) * T ^ (k - 1 - s) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, pow_succ, pow_succ]
      have h0 : (k + 1) - 1 - k = 0 := by omega
      rw [h0, pow_zero, mul_one]
      have hre : (∑ s ∈ Finset.range k, F ^ s * (F - T) * T ^ ((k + 1) - 1 - s))
          = (∑ s ∈ Finset.range k, F ^ s * (F - T) * T ^ (k - 1 - s)) * T := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun s hs => ?_
        have hlt : s < k := Finset.mem_range.mp hs
        have hsub : (k + 1) - 1 - s = (k - 1 - s) + 1 := by omega
        rw [hsub, pow_succ, ← Matrix.mul_assoc]
      rw [hre, ← ih, Matrix.sub_mul, Matrix.mul_sub]
      abel

/-! ### The sharp trace-difference bound -/

/-- **The sharp trace-difference bound.**  For `‖F‖, ‖T‖ ≤ M` and any `k`,
`|tr(F ^ k) - tr(T ^ k)| ≤ k * M ^ (k - 1) * ‖F - T‖`: the telescope of
`matrix_pow_sub_sum_range`, `|tr(X * Y)| ≤ ‖X‖_F ‖Y‖_F`
(`abs_matrix_trace_mul_le_frobenius`), Frobenius submultiplicativity, and the
geometric-sum identity. -/
theorem abs_trace_pow_sub_le_frob {m : ℕ} (F T : Matrix (Fin m) (Fin m) ℝ) (k : ℕ)
    (hk : 2 ≤ k) (M : ℝ) (hMF : ‖F‖ ≤ M) (hMT : ‖T‖ ≤ M) :
    |Matrix.trace (F ^ k) - Matrix.trace (T ^ k)|
      ≤ (k : ℝ) * M ^ (k - 1) * ‖F - T‖ := by
  classical
  have hMge : 0 ≤ M := le_trans (norm_nonneg _) hMF
  have htele : Matrix.trace (F ^ k) - Matrix.trace (T ^ k)
      = Matrix.trace (∑ s ∈ Finset.range k, F ^ s * (F - T) * T ^ (k - 1 - s)) := by
    rw [← Matrix.trace_sub, matrix_pow_sub_sum_range]
  -- per-term bound
  have hterm : ∀ s ∈ Finset.range k,
      |Matrix.trace (F ^ s * (F - T) * T ^ (k - 1 - s))|
        ≤ ‖F - T‖ * M ^ (k - 1) := by
    intro s hs
    have hlt : s < k := Finset.mem_range.mp hs
    by_cases hs0 : s = 0
    · subst hs0
      have hze : F ^ 0 * (F - T) = (F - T) := by simp
      rw [hze, Nat.sub_zero]
      have hA := abs_matrix_trace_mul_le_frobenius (F - T) (T ^ (k - 1))
      calc |Matrix.trace ((F - T) * T ^ (k - 1))|
          ≤ ‖F - T‖ * ‖T ^ (k - 1)‖ := hA
        _ ≤ ‖F - T‖ * M ^ (k - 1) :=
            mul_le_mul_of_nonneg_left
              (le_trans (frobenius_pow_le_one T (k - 1) (by omega))
                (pow_le_pow_left₀ (norm_nonneg T) hMT _)) (norm_nonneg _)
    · have hs1 : 1 ≤ s := by omega
      obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
      by_cases hu0 : k - 1 - (t + 1) = 0
      · -- the T-power is trivial: pair `F ^ s` with `(F - T)` directly
        have hpow : F ^ (t + 1) * (F - T) * T ^ (k - 1 - (t + 1))
            = F ^ (t + 1) * (F - T) := by
          rw [hu0, pow_zero, mul_one]
        rw [hpow]
        have hA := abs_matrix_trace_mul_le_frobenius (F ^ (t + 1)) (F - T)
        have heq : k - 1 = t + 1 := by omega
        calc |Matrix.trace (F ^ (t + 1) * (F - T))|
            ≤ ‖F ^ (t + 1)‖ * ‖F - T‖ := hA
          _ ≤ ‖F‖ ^ (t + 1) * ‖F - T‖ :=
              mul_le_mul_of_nonneg_right (frobenius_pow_le F t) (norm_nonneg _)
          _ ≤ M ^ (t + 1) * ‖F - T‖ :=
              mul_le_mul_of_nonneg_right
                (pow_le_pow_left₀ (norm_nonneg F) hMF _) (norm_nonneg _)
          _ = ‖F - T‖ * M ^ (k - 1) := by rw [heq]; ring
      · -- the general case: `F ^ s * (F - T)` paired against `T ^ u`, `u ≥ 1`
        obtain ⟨v, hv⟩ : ∃ v, k - 1 - (t + 1) = v + 1 :=
          ⟨k - 1 - (t + 1) - 1, by omega⟩
        have hpow : F ^ (t + 1) * (F - T) * T ^ (k - 1 - (t + 1))
            = (F ^ (t + 1) * (F - T)) * T ^ (v + 1) := by rw [hv]
        rw [hpow]
        have hA := abs_matrix_trace_mul_le_frobenius (F ^ (t + 1) * (F - T))
          (T ^ (v + 1))
        have hu : (k - 1 - (t + 1)) + (t + 1) = k - 1 := by omega
        have hB : ‖F ^ (t + 1) * (F - T)‖ ≤ M ^ (t + 1) * ‖F - T‖ := by
          calc ‖F ^ (t + 1) * (F - T)‖ ≤ ‖F ^ (t + 1)‖ * ‖F - T‖ :=
              Matrix.frobenius_norm_mul _ _
            _ ≤ ‖F‖ ^ (t + 1) * ‖F - T‖ :=
                mul_le_mul_of_nonneg_right (frobenius_pow_le F t) (norm_nonneg _)
            _ ≤ M ^ (t + 1) * ‖F - T‖ :=
                mul_le_mul_of_nonneg_right
                  (pow_le_pow_left₀ (norm_nonneg F) hMF _) (norm_nonneg _)
        have hC : ‖T ^ (v + 1)‖ ≤ M ^ (v + 1) :=
          le_trans (frobenius_pow_le T v) (pow_le_pow_left₀ (norm_nonneg T) hMT _)
        calc |Matrix.trace ((F ^ (t + 1) * (F - T)) * T ^ (v + 1))|
            ≤ ‖F ^ (t + 1) * (F - T)‖ * ‖T ^ (v + 1)‖ := hA
          _ ≤ (M ^ (t + 1) * ‖F - T‖) * ‖T ^ (v + 1)‖ :=
              mul_le_mul_of_nonneg_right hB (norm_nonneg _)
          _ ≤ (M ^ (t + 1) * ‖F - T‖) * M ^ (v + 1) :=
              mul_le_mul_of_nonneg_left hC
                (mul_nonneg (pow_nonneg hMge _) (norm_nonneg _))
          _ = ‖F - T‖ * M ^ (k - 1) := by
              have hsplit : (M : ℝ) ^ (k - 1) = (M : ℝ) ^ ((k - 1 - (t + 1)) + (t + 1)) := by
                rw [hu]
              rw [hsplit, pow_add, hv]
              ring
  rw [htele]
  have htrsum : Matrix.trace
      (∑ s ∈ Finset.range k, F ^ s * (F - T) * T ^ (k - 1 - s))
      = ∑ s ∈ Finset.range k, Matrix.trace (F ^ s * (F - T) * T ^ (k - 1 - s)) :=
    Matrix.trace_sum _ _
  rw [htrsum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
  exact le_of_eq (by ring)

/-! ### The stratified entry-envelope Frobenius bound -/

/-- The `d ≤ 1` indicator sum over `range m` is at most `2`. -/
private theorem sum_near_ind_le_two (m : ℕ) :
    (∑ d ∈ Finset.range m, (if d ≤ 1 then (1 : ℝ) else 0)) ≤ 2 := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range m)
    (fun d : ℕ => d ≤ 1) (fun d : ℕ => (if d ≤ 1 then (1 : ℝ) else 0))
  have hcard : ((Finset.range m).filter fun d : ℕ => d ≤ 1).card
      ≤ (Finset.range 2).card := by
    refine Finset.card_le_card fun d hd => ?_
    have hd1 : d ≤ 1 := (Finset.mem_filter.mp hd).2
    exact Finset.mem_range.mpr (by omega)
  have h1 : (∑ d ∈ (Finset.range m).filter fun d : ℕ => d ≤ 1,
      (if d ≤ 1 then (1 : ℝ) else 0)) ≤ (2 : ℝ) := by
    have hterm : ∀ d ∈ (Finset.range m).filter fun d : ℕ => d ≤ 1,
        (if d ≤ 1 then (1 : ℝ) else 0) = (1 : ℝ) := fun d hd =>
      if_pos (Finset.mem_filter.mp hd).2
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast hcard
  have h2 : (∑ d ∈ (Finset.range m).filter fun d : ℕ => ¬(d ≤ 1),
      (if d ≤ 1 then (1 : ℝ) else 0)) ≤ 0 := by
    refine Finset.sum_nonpos fun d hd => ?_
    exact (if_neg (Finset.mem_filter.mp hd).2).le
  have h0le : (0 : ℝ) ≤ 2 := by norm_num
  linarith

/-- The `1/d²` series over `range m` is at most `3` (concrete bound on the
convergent Basel-type partial sums via `sum_Ioc_inv_sq_le_sub`). -/
private theorem sum_range_inv_sq_le_three (m : ℕ) :
    (∑ d ∈ Finset.range m, (((d : ℝ) ^ 2)⁻¹)) ≤ 3 := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range m)
    (fun d : ℕ => 2 ≤ d) (fun d : ℕ => (((d : ℝ) ^ 2)⁻¹))
  have hsub2 : ((Finset.range m).filter fun d : ℕ => 2 ≤ d) ⊆ Finset.Ioc 1 m := by
    intro d hd
    have hd := Finset.mem_filter.mp hd
    have hlt : d < m := Finset.mem_range.mp hd.1
    exact Finset.mem_Ioc.mpr ⟨by omega, Nat.le_of_lt hlt⟩
  have hfar : (∑ d ∈ (Finset.range m).filter fun d : ℕ => 2 ≤ d, (((d : ℝ) ^ 2)⁻¹))
      ≤ (1 : ℝ) := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub2
      (fun d _ _ => inv_nonneg.2 (sq_nonneg (d : ℝ)))) ?_
    have hsub := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := 1) (n := m) (by norm_num) hm
    have hinv : (1 : ℝ)⁻¹ - (m : ℝ)⁻¹ ≤ (1 : ℝ) := by
      rw [inv_one]
      linarith [inv_nonneg.2 (by norm_num : (0 : ℝ) ≤ (m : ℝ))]
    linarith
  have hnear : (∑ d ∈ (Finset.range m).filter fun d : ℕ => ¬(2 ≤ d),
      (((d : ℝ) ^ 2)⁻¹)) ≤ (2 : ℝ) := by
    have hone : ∀ d ∈ (Finset.range m).filter fun d : ℕ => ¬(2 ≤ d),
        (((d : ℝ) ^ 2)⁻¹) ≤ (1 : ℝ) := by
      intro d hd
      have hd2 : d ≤ 1 := by
        have h := Finset.mem_filter.mp hd
        omega
      rcases Nat.eq_zero_or_pos d with h0 | h0
      · subst h0
        simp
      · have h1 : d = 1 := by omega
        subst h1
        norm_num
    have hcard : ((Finset.range m).filter fun d : ℕ => ¬(2 ≤ d)).card ≤ 2 := by
      have h1 : ((Finset.range m).filter fun d : ℕ => ¬(2 ≤ d)).card
          ≤ (Finset.range 2).card := by
        refine Finset.card_le_card fun d hd => ?_
        have hd2 : d ≤ 1 := by
          have h := Finset.mem_filter.mp hd
          omega
        exact Finset.mem_range.mpr (by omega)
      exact_mod_cast h1
    have hsum : (∑ d ∈ (Finset.range m).filter fun d : ℕ => ¬(2 ≤ d),
        (((d : ℝ) ^ 2)⁻¹))
        ≤ ((Finset.range m).filter fun d : ℕ => ¬(2 ≤ d)).card • (1 : ℝ) :=
      Finset.sum_le_card_nsmul _ _ (1 : ℝ) hone
    rw [nsmul_eq_mul, mul_one] at hsum
    exact le_trans hsum (by exact_mod_cast hcard)
  linarith

/-- The far-band power series `∑ d^{-(2+2ψ)}` over `range m` is at most `3`
(convergent since `2 + 2ψ ≥ 2 > 1`). -/
private theorem sum_range_far_rpow_le_three (m : ℕ) (psi : ℝ) (hpsi : 0 < psi) :
    (∑ d ∈ Finset.range m, ((d : ℝ) ^ (-(2 + 2 * psi)))) ≤ 3 := by
  refine le_trans (Finset.sum_le_sum fun d hd => ?_) (sum_range_inv_sq_le_three m)
  by_cases h0 : d = 0
  · subst h0
    rw [Nat.cast_zero, Real.zero_rpow
      (x := (-(2 + 2 * psi : ℝ))) (by linarith)]
    norm_num
  · have hdpos : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
      have : 1 ≤ d := Nat.pos_of_ne_zero h0
      exact_mod_cast this
    have hexp : -(2 + 2 * psi) ≤ -(2 : ℝ) := by linarith
    calc ((d : ℝ) ^ (-(2 + 2 * psi))) ≤ ((d : ℝ) ^ (-(2 : ℝ))) :=
        Real.rpow_le_rpow_of_exponent_le hd1 hexp
      _ = (((d : ℝ) ^ 2)⁻¹) := by
          rw [Real.rpow_neg hdpos]
          have h2 : ((d : ℝ) ^ (2 : ℝ)) = ((d : ℝ) ^ 2) := Real.rpow_natCast _ _
          rw [h2]

/-- **The stratified entry-envelope Frobenius bound.**  If every entry of `Δ`
is bounded by `b` on the near band (`Nat.dist i j ≤ 1`) and by the RELATIVE
power law `a * d^{-(1+ψ)}` on the far band (`d ≥ 2`), then
`‖Δ‖² ≤ m * (4 * b² + 6 * a²)`.  Per row, the near band contributes at most
`4 * b²` (each of the two distances `d ≤ 1` occurs at most twice per row), and
the far band contributes `2 * a² * ∑ d^{-(2+2ψ)} ≤ 6 * a²` — the
`d^{-(1+ψ)}`-decay beat that makes the far band summable.  With the
`S^{ψ-1}`-normalization `b = S^{ψ-1} * B_near`, `a = S^{ψ-1} * A` this is
`O(S^{2ψ-1}) → 0` for `2ψ < 1`. -/
theorem frobenius_le_of_entry_envelope {m : ℕ} (Δ : Matrix (Fin m) (Fin m) ℝ)
    (psi a b : ℝ) (hpsi : 0 < psi) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hnear : ∀ i j : Fin m, Nat.dist i.val j.val ≤ 1 → |Δ i j| ≤ b)
    (hfar : ∀ i j : Fin m, 2 ≤ Nat.dist i.val j.val →
      |Δ i j| ≤ a * ((Nat.dist i.val j.val : ℝ) ^ (-(1 + psi)))) :
    ‖Δ‖ ^ 2 ≤ (m : ℝ) * (4 * b ^ 2 + 6 * a ^ 2) := by
  classical
  -- per-entry bound stratified by the distance
  have hentry : ∀ (i j : Fin m),
      |Δ i j| ^ 2
        ≤ b ^ 2 * (if Nat.dist i.val j.val ≤ 1 then (1 : ℝ) else 0)
          + a ^ 2 * ((Nat.dist i.val j.val : ℝ) ^ (-(2 + 2 * psi))) := by
    intro i j
    by_cases hd : Nat.dist i.val j.val ≤ 1
    · have hab : |Δ i j| ≤ b := hnear i j hd
      have hsq : |Δ i j| ^ 2 ≤ b ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hab 2
      have hpos : (0 : ℝ) ≤ (Nat.dist i.val j.val : ℝ) ^ (-(2 + 2 * psi)) :=
        Real.rpow_nonneg (Nat.cast_nonneg _) _
      rw [if_pos hd, mul_one]
      exact le_trans hsq (le_add_of_nonneg_right
        (mul_nonneg (pow_nonneg ha 2) hpos))
    · have hd2 : 2 ≤ Nat.dist i.val j.val := by omega
      have hab : |Δ i j| ≤ a * ((Nat.dist i.val j.val : ℝ) ^ (-(1 + psi))) :=
        hfar i j hd2
      have hsq : |Δ i j| ^ 2
          ≤ (a * ((Nat.dist i.val j.val : ℝ) ^ (-(1 + psi)))) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hab 2
      have hdpos : (0 : ℝ) < (Nat.dist i.val j.val : ℝ) := by
        have : 0 < Nat.dist i.val j.val := by omega
        exact_mod_cast this
      have hsplit : ((Nat.dist i.val j.val : ℝ) ^ (-(1 + psi)))
          * ((Nat.dist i.val j.val : ℝ) ^ (-(1 + psi)))
          = (Nat.dist i.val j.val : ℝ) ^ (-(2 + 2 * psi)) := by
        have hs1 := Real.rpow_add hdpos (-(1 + psi : ℝ)) (-(1 + psi : ℝ))
        rw [show ((-(1 + psi : ℝ)) + (-(1 + psi : ℝ))) = (-(2 + 2 * psi : ℝ)) from
          by ring] at hs1
        exact hs1.symm
      have hkey : a ^ 2 * ((Nat.dist i.val j.val : ℝ) ^ (-(2 + 2 * psi)))
          = (a * ((Nat.dist i.val j.val : ℝ) ^ (-(1 + psi)))) ^ 2 := by
        rw [mul_pow, pow_two ((Nat.dist i.val j.val : ℝ) ^ (-(1 + psi))), hsplit]
      rw [if_neg hd, mul_zero, zero_add]
      exact le_trans hsq (le_of_eq hkey.symm)
  -- Frobenius norm squared as the entrywise square sum
  have hnormsq : ‖Δ‖ ^ 2 = ∑ i : Fin m, ∑ j : Fin m, |Δ i j| ^ 2 := by
    have h1 : ‖Δ‖
        = (∑ i : Fin m, ∑ j : Fin m, |Δ i j| ^ 2) ^ ((1 : ℝ) / 2) := by
      rw [Matrix.frobenius_norm_def]
      refine congrArg (fun x : ℝ => x ^ ((1 : ℝ) / 2)) ?_
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
        rw [Real.norm_eq_abs, Real.rpow_two]
    rw [h1, ← Real.sqrt_eq_rpow, pow_two]
    exact Real.mul_self_sqrt (by positivity)
  -- the per-row bound via the distance stratification
  have hrow : ∀ i : Fin m,
      (∑ j : Fin m, |Δ i j| ^ 2) ≤ 4 * b ^ 2 + 6 * a ^ 2 := by
    intro i
    have hstep : (∑ j : Fin m, |Δ i j| ^ 2)
        ≤ b ^ 2 * (∑ j : Fin m, (if Nat.dist i.val j.val ≤ 1 then (1 : ℝ) else 0))
          + a ^ 2 * (∑ j : Fin m,
              ((Nat.dist i.val j.val : ℝ) ^ (-(2 + 2 * psi)))) := by
      calc (∑ j : Fin m, |Δ i j| ^ 2)
          ≤ ∑ j : Fin m, (b ^ 2 * (if Nat.dist i.val j.val ≤ 1 then (1 : ℝ) else 0)
              + a ^ 2 * ((Nat.dist i.val j.val : ℝ) ^ (-(2 + 2 * psi)))) :=
            Finset.sum_le_sum fun j _ => hentry i j
        _ = b ^ 2 * (∑ j : Fin m, (if Nat.dist i.val j.val ≤ 1 then (1 : ℝ) else 0))
            + a ^ 2 * (∑ j : Fin m,
                ((Nat.dist i.val j.val : ℝ) ^ (-(2 + 2 * psi)))) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hnearcnt : (∑ j : Fin m, (if Nat.dist i.val j.val ≤ 1 then (1 : ℝ) else 0))
        ≤ 2 * (∑ d ∈ Finset.range m, (if d ≤ 1 then (1 : ℝ) else 0)) :=
      sum_row_dist_le (fun d => if d ≤ 1 then (1 : ℝ) else 0) (fun d => by
        by_cases h : d ≤ 1
        · simp [h]
        · simp [h]) i
    have hfarsum : (∑ j : Fin m,
        ((Nat.dist i.val j.val : ℝ) ^ (-(2 + 2 * psi))))
        ≤ 2 * (∑ d ∈ Finset.range m, ((d : ℝ) ^ (-(2 + 2 * psi)))) :=
      sum_row_dist_le (fun d => (d : ℝ) ^ (-(2 + 2 * psi)))
        (fun d => Real.rpow_nonneg (Nat.cast_nonneg d) _) i
    have h1 : (∑ j : Fin m, (if Nat.dist i.val j.val ≤ 1 then (1 : ℝ) else 0)) ≤ 4 := by
      refine le_trans hnearcnt ?_
      calc ((2 : ℝ) * (∑ d ∈ Finset.range m, (if d ≤ 1 then (1 : ℝ) else 0)))
          ≤ (2 : ℝ) * 2 :=
            mul_le_mul_of_nonneg_left (sum_near_ind_le_two m) (by norm_num)
        _ = 4 := by norm_num
    have h2 : (∑ j : Fin m, ((Nat.dist i.val j.val : ℝ) ^ (-(2 + 2 * psi)))) ≤ 6 := by
      refine le_trans hfarsum ?_
      calc ((2 : ℝ) * (∑ d ∈ Finset.range m, ((d : ℝ) ^ (-(2 + 2 * psi)))))
          ≤ (2 : ℝ) * 3 :=
            mul_le_mul_of_nonneg_left (sum_range_far_rpow_le_three m psi hpsi)
              (by norm_num)
        _ = 6 := by norm_num
    have hb2 : (0 : ℝ) ≤ b ^ 2 := pow_nonneg hb 2
    have ha2 : (0 : ℝ) ≤ a ^ 2 := pow_nonneg ha 2
    have hb4 : b ^ 2 * (∑ j : Fin m,
        (if Nat.dist i.val j.val ≤ 1 then (1 : ℝ) else 0)) ≤ b ^ 2 * 4 :=
      mul_le_mul_of_nonneg_left h1 hb2
    have ha6 : a ^ 2 * (∑ j : Fin m,
        ((Nat.dist i.val j.val : ℝ) ^ (-(2 + 2 * psi)))) ≤ a ^ 2 * 6 :=
      mul_le_mul_of_nonneg_left h2 ha2
    calc (∑ j : Fin m, |Δ i j| ^ 2)
        ≤ b ^ 2 * (∑ j : Fin m, (if Nat.dist i.val j.val ≤ 1 then (1 : ℝ) else 0))
          + a ^ 2 * (∑ j : Fin m,
              ((Nat.dist i.val j.val : ℝ) ^ (-(2 + 2 * psi)))) := hstep
      _ ≤ b ^ 2 * 4 + a ^ 2 * 6 := by linarith
      _ = 4 * b ^ 2 + 6 * a ^ 2 := by ring
  calc ‖Δ‖ ^ 2 = ∑ i : Fin m, ∑ j : Fin m, |Δ i j| ^ 2 := hnormsq
    _ ≤ ∑ i : Fin m, (4 * b ^ 2 + 6 * a ^ 2) :=
        Finset.sum_le_sum fun i _ => hrow i
    _ = (m : ℝ) * (4 * b ^ 2 + 6 * a ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]

/-! ### The `hFarWord` glue -/

/-- **The `hFarWord` glue.**  Eventual uniform Frobenius bounds `‖F_n‖, ‖T_n‖
≤ B` on the normalized frozen and Riesz quadrature matrices, plus Frobenius
convergence `‖F_n - T_n‖_F → 0`, give the exact `hFarWord` shape consumed by
`Hurst.frozenQuad_hFquad_of_farWord`:
`∀ eps > 0, ∀ᶠ n in atTop,
  |tr(F_n ^ k) - tr(T_n ^ k)| < eps`. -/
theorem farWord_of_frobeniusSmall
    (p M : ℝ) (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M) (r : ℕ) (δ : ℕ → ℝ)
    (t : ℝ) (k : ℕ) (hk : 2 ≤ k) (B : ℝ)
    (hFb : ∀ᶠ n in atTop,
      ‖actualQ1NormalizedFrozenMatrix f hf r n (δ n) t‖ ≤ B)
    (hTb : ∀ᶠ n in atTop, ‖actualQ1RieszMatrix f r n (δ n) t‖ ≤ B)
    (hΔ : Tendsto (fun n : ℕ =>
        ‖actualQ1NormalizedFrozenMatrix f hf r n (δ n) t
            - actualQ1RieszMatrix f r n (δ n) t‖) atTop (𝓝 0)) :
    ∀ eps > 0, ∀ᶠ n in atTop,
      |Matrix.trace ((actualQ1NormalizedFrozenMatrix f hf r n (δ n) t) ^ k)
        - Matrix.trace ((actualQ1RieszMatrix f r n (δ n) t) ^ k)| < eps := by
  intro eps heps
  have hscale : Tendsto (fun n : ℕ =>
      (k : ℝ) * B ^ (k - 1) *
        ‖actualQ1NormalizedFrozenMatrix f hf r n (δ n) t
            - actualQ1RieszMatrix f r n (δ n) t‖) atTop (𝓝 0) := by
    have h2 := Filter.Tendsto.const_mul ((k : ℝ) * B ^ (k - 1)) hΔ
    simpa using h2
  filter_upwards [hFb, hTb, hscale.eventually_lt_const heps]
    with n hF hT hsmall
  have hkey := abs_trace_pow_sub_le_frob
    (actualQ1NormalizedFrozenMatrix f hf r n (δ n) t)
    (actualQ1RieszMatrix f r n (δ n) t) k hk B hF hT
  exact lt_of_le_of_lt hkey hsmall

/-- **The frozen quadrature from Frobenius inputs.**  Composing
`farWord_of_frobeniusSmall` with `Hurst.frozenQuad_hFquad_of_farWord`: the
eventual uniform Frobenius bounds and the Frobenius convergence of the
normalized frozen-vs-Riesz difference give the full frozen-side quadrature
`tr(F_n ^ k) → weightedRieszCycleIntegral k ψ c (equivalentKernel r)` — the
`hFquad` input of `Hurst.frozenHsmallMirror`. -/
theorem frozenQuad_hFquad_of_frobeniusSmall
    (p a b M : ℝ) (r : ℕ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (hM : 0 ≤ M) (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (k : ℕ) (hk : 2 ≤ k)
    (B : ℝ)
    (hFb : ∀ᶠ n in atTop,
      ‖actualQ1NormalizedFrozenMatrix f hf r n (δ n) t‖ ≤ B)
    (hTb : ∀ᶠ n in atTop, ‖actualQ1RieszMatrix f r n (δ n) t‖ ≤ B)
    (hΔ : Tendsto (fun n : ℕ =>
        ‖actualQ1NormalizedFrozenMatrix f hf r n (δ n) t
            - actualQ1RieszMatrix f r n (δ n) t‖) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => Matrix.trace
        ((actualQ1NormalizedFrozenMatrix f hf r n (δ n) t) ^ k)) atTop
      (𝓝 (weightedRieszCycleIntegral k (2 - 2 * f t)
        (f t * (2 * f t - 1)) (equivalentKernel r))) :=
  frozenQuad_hFquad_of_farWord p a b M r hp ha hb hab hM f hf hF t ht hlong δ
    hδpos hδ0 hN k hk
    (farWord_of_frobeniusSmall p M f hf r δ t k hk B hFb hTb hΔ)

end Hurst
