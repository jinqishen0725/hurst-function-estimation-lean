import Hurst.MeshFactorizationBand

/-!
# Discrete pair-decay lemma

For `0 < psi < 1/2` and `a b : Fin m`, the paired decay sum
`∑ j, (dist a j + 1) ^ (-psi) * (dist b j + 1) ^ (-psi)`
is bounded uniformly in `a b : Fin m` by `2 * (m^(1-2psi)/(1-2psi) + 1)`, and hence by
`2^(1+psi) * (1 + 2 * (m^(1-2psi)/(1-2psi) + 1))` (the shape requested for the
Predicate-2 band-pairing sum: split constants universal, growth `m^{1-2psi}`).

Route: Cauchy-Schwarz for finset sums (`Finset.sum_mul_sq_le_sq_mul_sq`) reduces the
pair sum to a single-row bound `∑ j, (dist a j + 1)^(-2psi) ≤ 2 * (...)`, proved by
fiberwise reindexing over the distance `d = Nat.dist a j` (each fiber has at most two
points, via `nat_dist_cases`) plus the power-sum bound `Hurst.sum_range_rpow_neg_le`.
-/

namespace Hurst

/-! ### Distance fibers -/

/-- Distance case split: `Nat.dist x y = d` forces `y = x + d` or `y + d = x`. -/
theorem nat_dist_cases {x y d : ℕ} (h : Nat.dist x y = d) : y = x + d ∨ y + d = x := by
  have h2 : x - y + (y - x) = d := h
  omega

/-- In `Fin m`, a distance is always less than `m`. -/
theorem nat_dist_lt_of_fin {m : ℕ} (a j : Fin m) : Nat.dist a.val j.val < m := by
  rcases nat_dist_cases (rfl : Nat.dist a.val j.val = Nat.dist a.val j.val) with h | h
  · have hj := j.isLt
    have ha := a.isLt
    omega
  · have hj := j.isLt
    have ha := a.isLt
    omega

/-- The fiber `{j : Fin m | Nat.dist a.val j.val = d}` has at most two elements
(the two directions from `a`). -/
theorem card_dist_fiber_le_two {m : ℕ} (a : Fin m) (d : ℕ) :
    (Finset.univ.filter fun j : Fin m => Nat.dist a.val j.val = d).card ≤ 2 := by
  have hin : ∀ j ∈ Finset.univ.filter (fun j : Fin m => Nat.dist a.val j.val = d),
      j.val = a.val + d ∨ j.val + d = a.val := by
    intro j hj
    rw [Finset.mem_filter] at hj
    exact nat_dist_cases hj.2
  have himg : (Finset.univ.filter (fun j : Fin m => Nat.dist a.val j.val = d)).image
      (fun j : Fin m => j.val) ⊆ insert (a.val + d) {a.val - d} := by
    intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    rcases hin j hj with h | h
    · rw [h]
      exact Finset.mem_insert_self _ _
    · have h' : ↑j = ↑a - d := by omega
      rw [h']
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have h2 : (insert (a.val + d) {a.val - d} : Finset ℕ).card ≤ 2 := by
    refine (Finset.card_insert_le _ _).trans ?_
    simp
  calc (Finset.univ.filter (fun j : Fin m => Nat.dist a.val j.val = d)).card
      = ((Finset.univ.filter (fun j : Fin m => Nat.dist a.val j.val = d)).image
          (fun j : Fin m => j.val)).card :=
        (Finset.card_image_of_injective _
          (fun j j' h => Fin.val_injective h)).symm
    _ ≤ (insert (a.val + d) {a.val - d} : Finset ℕ).card := Finset.card_le_card himg
    _ ≤ 2 := h2

/-- The inner fiber sum: all points at distance `d` contribute the same weight,
and there are at most two of them. -/
theorem fiber_dist_sum_le {m : ℕ} (a : Fin m) (d : ℕ) (psi : ℝ) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin m => Nat.dist a.val j.val = d),
        (((Nat.dist a.val j.val + 1 : ℕ) : ℝ)) ^ (-(2 * psi))
      ≤ 2 * (((d + 1 : ℕ) : ℝ)) ^ (-(2 * psi)) := by
  have hval : ∀ j ∈ Finset.univ.filter (fun j : Fin m => Nat.dist a.val j.val = d),
      (((Nat.dist a.val j.val + 1 : ℕ) : ℝ)) ^ (-(2 * psi))
        = (((d + 1 : ℕ) : ℝ)) ^ (-(2 * psi)) := by
    intro j hj
    rw [Finset.mem_filter] at hj
    rw [hj.2]
  have h1 : ∑ j ∈ Finset.univ.filter (fun j : Fin m => Nat.dist a.val j.val = d),
      (((Nat.dist a.val j.val + 1 : ℕ) : ℝ)) ^ (-(2 * psi))
      = ∑ j ∈ Finset.univ.filter (fun j : Fin m => Nat.dist a.val j.val = d),
          (((d + 1 : ℕ) : ℝ)) ^ (-(2 * psi)) := Finset.sum_congr rfl hval
  rw [h1, Finset.sum_const (((d + 1 : ℕ) : ℝ) ^ (-(2 * psi))), nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right
    (Nat.cast_le.2 (card_dist_fiber_le_two a d))
    (Real.rpow_nonneg (by positivity) _)

/-! ### Row bound -/

/-- **Row bound**: for `0 < psi < 1/2` and `a : Fin m`,
`∑ j, (dist a j + 1)^(-2psi) ≤ 2 * (m^(1-2psi)/(1-2psi) + 1)`,
uniformly in `a`. -/
theorem row_rpow_neg_two_sum_le (m : ℕ) (a : Fin m) {psi : ℝ} (hpsi1 : 0 < psi)
    (hpsi2 : 2 * psi < 1) :
    ∑ j : Fin m, (((Nat.dist a.val j.val + 1 : ℕ) : ℝ)) ^ (-(2 * psi))
      ≤ 2 * (((m : ℝ) ^ (1 - 2 * psi)) / (1 - 2 * psi) + 1) := by
  have hcrit : (0 : ℝ) < 1 - 2 * psi := by linarith
  have hdist : ∀ j : Fin m, Nat.dist a.val j.val < m := fun j => nat_dist_lt_of_fin a j
  calc ∑ j : Fin m, (((Nat.dist a.val j.val + 1 : ℕ) : ℝ)) ^ (-(2 * psi))
      = ∑ d ∈ Finset.range m,
          ∑ j ∈ Finset.univ.filter (fun j : Fin m => Nat.dist a.val j.val = d),
            (((Nat.dist a.val j.val + 1 : ℕ) : ℝ)) ^ (-(2 * psi)) :=
        (Finset.sum_fiberwise_of_maps_to (fun j _ => Finset.mem_range.2 (hdist j)) _).symm
    _ ≤ ∑ d ∈ Finset.range m, 2 * (((d + 1 : ℕ) : ℝ)) ^ (-(2 * psi)) :=
        Finset.sum_le_sum fun d _ => fiber_dist_sum_le a d psi
    _ = 2 * ∑ d ∈ Finset.range m, (((d + 1 : ℕ) : ℝ)) ^ (-(2 * psi)) := by
        rw [Finset.mul_sum]
    _ ≤ 2 * (((m : ℝ) ^ (1 - 2 * psi)) / (1 - 2 * psi) + 1) :=
        mul_le_mul_of_nonneg_left (sum_range_rpow_neg_le (by linarith) hpsi2 m) (by norm_num)

/-! ### Pair decay -/

/-- **Discrete pair-decay lemma**: for `0 < psi` with `2 * psi < 1`, `a b : Fin m`,
the paired sum `∑ j, (dist a j + 1)^(-psi) * (dist b j + 1)^(-psi)` is bounded
uniformly in `a b` by `2^(1+psi) * (1 + 2 * (m^(1-2psi)/(1-2psi) + 1))`.
Growth in `m` is `m^(1-2psi)`; the split constants are universal. -/
theorem pair_decay_sum (m : ℕ) (psi : ℝ) (a b : Fin m) (hpsi1 : 0 < psi)
    (hpsi2 : 2 * psi < 1) :
    (∑ j : Fin m, ((Nat.dist a.val j.val + 1 : ℝ)) ^ (-psi) *
                  ((Nat.dist b.val j.val + 1 : ℝ)) ^ (-psi))
      ≤ 2 ^ (1 + psi) * (1 + 2 * ((m : ℝ) ^ (1 - 2 * psi) / (1 - 2 * psi) + 1)) := by
  have hrowA := row_rpow_neg_two_sum_le m a hpsi1 hpsi2
  have hrowB := row_rpow_neg_two_sum_le m b hpsi1 hpsi2
  push_cast at hrowA hrowB
  set X : ℝ := (m : ℝ) ^ (1 - 2 * psi) / (1 - 2 * psi) + 1 with hX
  have hXpos : (0 : ℝ) ≤ X := by
    rw [hX]
    have h1 : (0 : ℝ) ≤ (m : ℝ) ^ (1 - 2 * psi) := Real.rpow_nonneg (by positivity) _
    have h2 : (0 : ℝ) ≤ 1 - 2 * psi := by linarith
    linarith [div_nonneg h1 h2]
  -- Cauchy-Schwarz
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) (s := Finset.univ (α := Fin m))
    (fun j : Fin m => ((Nat.dist a.val j.val + 1 : ℝ)) ^ (-psi))
    (fun j : Fin m => ((Nat.dist b.val j.val + 1 : ℝ)) ^ (-psi))
  -- square of a power is a power with doubled exponent
  have hu2 : ∀ j : Fin m, (((Nat.dist a.val j.val + 1 : ℝ)) ^ (-psi)) ^ 2
      = ((Nat.dist a.val j.val + 1 : ℝ)) ^ (-(2 * psi)) := by
    intro j
    have hx : (0 : ℝ) ≤ (Nat.dist a.val j.val + 1 : ℝ) := by positivity
    have hnpow : (((Nat.dist a.val j.val + 1 : ℝ)) ^ (-psi)) ^ 2
        = (((Nat.dist a.val j.val + 1 : ℝ)) ^ (-psi)) ^ ((2 : ℝ)) :=
      (Real.rpow_natCast (((Nat.dist a.val j.val + 1 : ℝ)) ^ (-psi)) 2).symm
    rw [hnpow, (Real.rpow_mul hx (-psi) 2).symm]
    congr 1
    ring
  have hv2 : ∀ j : Fin m, (((Nat.dist b.val j.val + 1 : ℝ)) ^ (-psi)) ^ 2
      = ((Nat.dist b.val j.val + 1 : ℝ)) ^ (-(2 * psi)) := by
    intro j
    have hx : (0 : ℝ) ≤ (Nat.dist b.val j.val + 1 : ℝ) := by positivity
    have hnpow : (((Nat.dist b.val j.val + 1 : ℝ)) ^ (-psi)) ^ 2
        = (((Nat.dist b.val j.val + 1 : ℝ)) ^ (-psi)) ^ ((2 : ℝ)) :=
      (Real.rpow_natCast (((Nat.dist b.val j.val + 1 : ℝ)) ^ (-psi)) 2).symm
    rw [hnpow, (Real.rpow_mul hx (-psi) 2).symm]
    congr 1
    ring
  have hA : ∑ j : Fin m, (((Nat.dist a.val j.val + 1 : ℝ)) ^ (-psi)) ^ 2
      = ∑ j : Fin m, ((Nat.dist a.val j.val + 1 : ℝ)) ^ (-(2 * psi)) :=
    Finset.sum_congr rfl fun j _ => hu2 j
  have hB : ∑ j : Fin m, (((Nat.dist b.val j.val + 1 : ℝ)) ^ (-psi)) ^ 2
      = ∑ j : Fin m, ((Nat.dist b.val j.val + 1 : ℝ)) ^ (-(2 * psi)) :=
    Finset.sum_congr rfl fun j _ => hv2 j
  rw [hA, hB] at hcs
  have hsumB : (0 : ℝ) ≤ ∑ j : Fin m, ((Nat.dist b.val j.val + 1 : ℝ)) ^ (-(2 * psi)) :=
    Finset.sum_nonneg fun j _ => Real.rpow_nonneg (by positivity) _
  have hprod : (∑ j : Fin m, ((Nat.dist a.val j.val + 1 : ℝ)) ^ (-(2 * psi))) *
      (∑ j : Fin m, ((Nat.dist b.val j.val + 1 : ℝ)) ^ (-(2 * psi))) ≤ (2 * X) * (2 * X) := by
    calc (∑ j : Fin m, ((Nat.dist a.val j.val + 1 : ℝ)) ^ (-(2 * psi))) *
        (∑ j : Fin m, ((Nat.dist b.val j.val + 1 : ℝ)) ^ (-(2 * psi)))
        ≤ (2 * X) * (∑ j : Fin m, ((Nat.dist b.val j.val + 1 : ℝ)) ^ (-(2 * psi))) :=
          mul_le_mul_of_nonneg_right hrowA hsumB
      _ ≤ (2 * X) * (2 * X) := mul_le_mul_of_nonneg_left hrowB (by linarith [hXpos])
  have hsquare : (∑ j : Fin m, ((Nat.dist a.val j.val + 1 : ℝ)) ^ (-psi) *
      ((Nat.dist b.val j.val + 1 : ℝ)) ^ (-psi)) ^ 2 ≤ (2 * X) ^ 2 := by
    calc (∑ j : Fin m, ((Nat.dist a.val j.val + 1 : ℝ)) ^ (-psi) *
            ((Nat.dist b.val j.val + 1 : ℝ)) ^ (-psi)) ^ 2
        ≤ (∑ j : Fin m, ((Nat.dist a.val j.val + 1 : ℝ)) ^ (-(2 * psi))) *
            (∑ j : Fin m, ((Nat.dist b.val j.val + 1 : ℝ)) ^ (-(2 * psi))) := hcs
      _ ≤ (2 * X) * (2 * X) := hprod
      _ = (2 * X) ^ 2 := by ring
  have hnonneg : 0 ≤ ∑ j : Fin m, ((Nat.dist a.val j.val + 1 : ℝ)) ^ (-psi) *
      ((Nat.dist b.val j.val + 1 : ℝ)) ^ (-psi) := by
    refine Finset.sum_nonneg fun j _ => mul_nonneg ?_ ?_ <;>
      exact Real.rpow_nonneg (by positivity) _
  -- take square roots
  have hbound : ∀ s : ℝ, s ^ 2 ≤ (2 * X) ^ 2 → 0 ≤ s → s ≤ 2 * X := by
    intro s h h0
    refine le_of_not_gt fun hlt => ?_
    nlinarith [h0, hXpos, hlt, h]
  have hmain : ∑ j : Fin m, ((Nat.dist a.val j.val + 1 : ℝ)) ^ (-psi) *
      ((Nat.dist b.val j.val + 1 : ℝ)) ^ (-psi) ≤ 2 * X := hbound _ hsquare hnonneg
  -- dress to the requested shape
  have hpsi3 : (1 : ℝ) ≤ 1 + psi := by linarith
  have hpow : (2 : ℝ) ≤ 2 ^ (1 + psi) := by
    have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ (2 : ℝ) by norm_num) hpsi3
    rwa [Real.rpow_one] at h
  calc ∑ j : Fin m, ((Nat.dist a.val j.val + 1 : ℝ)) ^ (-psi) *
          ((Nat.dist b.val j.val + 1 : ℝ)) ^ (-psi)
      ≤ 2 * X := hmain
    _ ≤ 2 ^ (1 + psi) * (1 + 2 * X) := by
        have h1 : (0 : ℝ) ≤ 2 * X := by linarith
        have h2 : 2 * X ≤ 2 ^ (1 + psi) * (2 * X) := by
          nlinarith [hpow, h1]
        have h3 : 2 ^ (1 + psi) * (2 * X) ≤ 2 ^ (1 + psi) * (1 + 2 * X) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg (by norm_num) _)
        linarith

end Hurst
