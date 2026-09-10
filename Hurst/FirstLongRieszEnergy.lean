import Hurst.ActualFirstLongHilbertSchmidt
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
open Set Filter
open scoped Topology
namespace Hurst

private theorem rpow_neg_antitoneOn (β m : ℝ) (hβ : 0 ≤ β) :
    AntitoneOn (fun x : ℝ => x ^ (-β)) (Icc 1 m) := by
  intro x hx y hy hxy
  dsimp only
  have hx0 : 0 < x := zero_lt_one.trans_le hx.1
  have hy0 : 0 < y := zero_lt_one.trans_le hy.1
  rw [Real.rpow_neg hx0.le β, Real.rpow_neg hy0.le β]
  apply (inv_le_inv₀ (Real.rpow_pos_of_pos hy0 β)
    (Real.rpow_pos_of_pos hx0 β)).2
  exact Real.rpow_le_rpow hx0.le hxy hβ

/-- A finite nonsummable power tail has the precise polynomial order needed
for the long-memory Riesz kernel energy. -/
theorem sum_range_one_add_rpow_neg_le (m : ℕ) (β : ℝ)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    (∑ k ∈ Finset.range m, (((k + 1 : ℕ) : ℝ) ^ (-β))) ≤
      1 + ((m + 1 : ℕ) : ℝ) ^ (1 - β) / (1 - β) := by
  have hden : 0 < 1 - β := by linarith
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-β))
      (Icc 1 (1 + (m : ℝ))) := rpow_neg_antitoneOn β _ hβ0
  have hint := hanti.sum_le_integral
  have hint' :
      (∑ k ∈ Finset.range m, (((k + 2 : ℕ) : ℝ) ^ (-β))) ≤
        ∫ x : ℝ in 1..1 + (m : ℝ), x ^ (-β) := by
    convert hint using 1
    · apply Finset.sum_congr rfl
      intro k hk
      congr 1
      push_cast
      ring
  have hsum :
      (∑ k ∈ Finset.range m, (((k + 1 : ℕ) : ℝ) ^ (-β))) ≤
        1 + ∑ k ∈ Finset.range m, (((k + 2 : ℕ) : ℝ) ^ (-β)) := by
    cases m with
    | zero => simp
    | succ m =>
      rw [Finset.sum_range_succ', Finset.sum_range_succ]
      norm_num [Real.one_rpow]
      have heq :
          (∑ x ∈ Finset.range m, ((x : ℝ) + 1 + 1) ^ (-β)) =
            ∑ x ∈ Finset.range m, ((x : ℝ) + 2) ^ (-β) := by
        apply Finset.sum_congr rfl
        intro x hx
        congr 1
        ring
      rw [heq]
      have hnonneg : 0 ≤ ((m : ℝ) + 2) ^ (-β) :=
        Real.rpow_nonneg (by positivity) _
      linarith
  calc
    _ ≤ 1 + ∑ k ∈ Finset.range m, (((k + 2 : ℕ) : ℝ) ^ (-β)) := hsum
    _ ≤ 1 + (∫ x : ℝ in 1..1 + (m : ℝ), x ^ (-β)) := by linarith
    _ = 1 + (((m + 1 : ℕ) : ℝ) ^ (1 - β) - 1) / (1 - β) := by
      rw [integral_rpow (Or.inl (by linarith : -1 < -β))]
      congr 2 <;> norm_num
      · congr 1 <;> push_cast <;> ring
      · ring
    _ ≤ 1 + ((m + 1 : ℕ) : ℝ) ^ (1 - β) / (1 - β) := by
      have hnonneg : 0 ≤ (1 : ℝ) / (1 - β) := by positivity
      rw [sub_div]
      linarith

private def rankRieszTerm {m : ℕ} (β : ℝ) (i j : Fin m) : ℝ :=
  if Nat.dist i.val j.val = 0 then 0
  else (Nat.dist i.val j.val : ℝ) ^ (-β)

/-- Every row of the discrete one-dimensional Riesz kernel is bounded by two
copies of the corresponding one-sided power sum. -/
theorem sum_fin_rankRieszTerm_le (m : ℕ) (β : ℝ) (i : Fin m) :
    (∑ j : Fin m, rankRieszTerm β i j) ≤
      2 * ∑ k ∈ Finset.range m, (((k + 1 : ℕ) : ℝ) ^ (-β)) := by
  classical
  let left : Finset (Fin m) := Finset.univ.filter (fun j => j < i)
  let right : Finset (Fin m) := Finset.univ.filter (fun j => i < j)
  let φL : Fin m → Fin m := fun j =>
    ⟨i.val - j.val - 1, by have := i.isLt; omega⟩
  let φR : Fin m → Fin m := fun j =>
    ⟨j.val - i.val - 1, by have := j.isLt; omega⟩
  let g : Fin m → ℝ := fun k => ((k.val + 1 : ℕ) : ℝ) ^ (-β)
  have hsplit : (∑ j : Fin m, rankRieszTerm β i j) =
      ∑ j ∈ left, rankRieszTerm β i j +
        ∑ j ∈ right, rankRieszTerm β i j := by
    have hfirst := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun j : Fin m => j < i) (rankRieszTerm β i)
    have hright :
        (∑ j ∈ right, rankRieszTerm β i j) =
          ∑ j ∈ Finset.univ.filter (fun j : Fin m => ¬ j < i),
            rankRieszTerm β i j := by
      apply Finset.sum_subset
      · intro j hj
        rw [Finset.mem_filter] at hj ⊢
        exact ⟨Finset.mem_univ _, not_lt_of_ge hj.2.le⟩
      · intro j hj hnot
        rw [Finset.mem_filter] at hj
        have hni : ¬ i < j := by
          intro hij
          apply hnot
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hij⟩
        have hji : ¬ j < i := hj.2
        have heq : j = i := le_antisymm (le_of_not_gt hni) (le_of_not_gt hji)
        subst j
        simp [rankRieszTerm]
    rw [← hright] at hfirst
    exact hfirst.symm
  have hleftInj : Set.InjOn φL left := by
    intro j hj k hk heq
    change j ∈ left at hj
    change k ∈ left at hk
    simp only [left, Finset.mem_filter, Finset.mem_univ, true_and] at hj hk
    apply Fin.ext
    have hev := congrArg Fin.val heq
    dsimp only [φL] at hev
    omega
  have hrightInj : Set.InjOn φR right := by
    intro j hj k hk heq
    change j ∈ right at hj
    change k ∈ right at hk
    simp only [right, Finset.mem_filter, Finset.mem_univ, true_and] at hj hk
    apply Fin.ext
    have hev := congrArg Fin.val heq
    dsimp only [φR] at hev
    omega
  have hleftTerm : ∀ j ∈ left, rankRieszTerm β i j = g (φL j) := by
    intro j hj
    rw [Finset.mem_filter] at hj
    have hji : j.val < i.val := by exact_mod_cast hj.2
    have hdist : Nat.dist i.val j.val = i.val - j.val :=
      Nat.dist_eq_sub_of_le_right hji.le
    have hpos : i.val - j.val ≠ 0 := by omega
    simp only [rankRieszTerm, hdist, hpos, if_false, g, φL]
    congr 1
    have heqnat : i.val - j.val - 1 + 1 = i.val - j.val := by omega
    exact_mod_cast heqnat.symm
  have hrightTerm : ∀ j ∈ right, rankRieszTerm β i j = g (φR j) := by
    intro j hj
    rw [Finset.mem_filter] at hj
    have hij : i.val < j.val := by exact_mod_cast hj.2
    have hdist : Nat.dist i.val j.val = j.val - i.val :=
      Nat.dist_eq_sub_of_le hij.le
    have hpos : j.val - i.val ≠ 0 := by omega
    simp only [rankRieszTerm, hdist, hpos, if_false, g, φR]
    congr 1
    have heqnat : j.val - i.val - 1 + 1 = j.val - i.val := by omega
    exact_mod_cast heqnat.symm
  have hleftEq : (∑ j ∈ left, rankRieszTerm β i j) =
      ∑ k ∈ left.image φL, g k := by
    rw [Finset.sum_image hleftInj]
    exact Finset.sum_congr rfl hleftTerm
  have hrightEq : (∑ j ∈ right, rankRieszTerm β i j) =
      ∑ k ∈ right.image φR, g k := by
    rw [Finset.sum_image hrightInj]
    exact Finset.sum_congr rfl hrightTerm
  have hleftLe : (∑ k ∈ left.image φL, g k) ≤ ∑ k : Fin m, g k := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro k hk hkn
    exact Real.rpow_nonneg (by positivity) _
  have hrightLe : (∑ k ∈ right.image φR, g k) ≤ ∑ k : Fin m, g k := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro k hk hkn
    exact Real.rpow_nonneg (by positivity) _
  have hfin : (∑ k : Fin m, g k) =
      ∑ k ∈ Finset.range m, (((k + 1 : ℕ) : ℝ) ^ (-β)) := by
    simpa only [g] using Fin.sum_univ_eq_sum_range
      (fun k : ℕ => (((k + 1 : ℕ) : ℝ) ^ (-β))) m
  rw [hsplit, hleftEq, hrightEq]
  rw [hfin] at hleftLe hrightLe
  linarith

def rankRieszUnitKernel {m : ℕ} (ψ : ℝ) (i j : Fin m) : ℝ :=
  if Nat.dist i.val j.val = 0 then 0
  else (Nat.dist i.val j.val : ℝ) ^ (-ψ)

def rankRieszKernel {m : ℕ} (S ψ c : ℝ) (i j : Fin m) : ℝ :=
  c * S ^ ψ * rankRieszUnitKernel ψ i j

theorem rankRieszUnitKernel_abs_le_one {m : ℕ} (ψ : ℝ) (hψ0 : 0 ≤ ψ)
    (i j : Fin m) : |rankRieszUnitKernel ψ i j| ≤ 1 := by
  unfold rankRieszUnitKernel
  split_ifs with hzero
  · simp
  · have hkNat : 1 ≤ Nat.dist i.val j.val := Nat.one_le_iff_ne_zero.mpr hzero
    have hk : (1 : ℝ) ≤ Nat.dist i.val j.val := by exact_mod_cast hkNat
    rw [abs_of_nonneg (Real.rpow_nonneg (by positivity) _),
      Real.rpow_neg (by positivity) ψ]
    exact (inv_le_one₀ (Real.rpow_pos_of_pos (by positivity) ψ)).mpr
      (Real.one_le_rpow hk hψ0)

private theorem realScaleMeshBandEnergy_const_mul {m R : ℕ}
    (S c : ℝ) (A : Fin m → Fin m → ℝ) :
    realScaleMeshBandEnergy S R (fun i j => c * A i j) =
      c ^ 2 * realScaleMeshBandEnergy S R A := by
  unfold realScaleMeshBandEnergy
  simp_rw [mul_pow, Finset.mul_sum]
  ring

private theorem realScaleMeshEnergy_const_mul {m : ℕ}
    (S c : ℝ) (A : Fin m → Fin m → ℝ) :
    realScaleMeshEnergy S (fun i j => c * A i j) =
      c ^ 2 * realScaleMeshEnergy S A := by
  unfold realScaleMeshEnergy
  simp_rw [mul_pow, Finset.mul_sum]
  ring

theorem rankRieszKernel_band_energy_le {m R : ℕ}
    (S ψ c : ℝ) (hS : 0 < S) (hψ0 : 0 ≤ ψ) :
    realScaleMeshBandEnergy S R
        (rankRieszKernel S ψ c : Fin m → Fin m → ℝ) ≤
      c ^ 2 * (S ^ (2 * ψ - 2) * (m : ℝ) * (2 * (R : ℝ) + 1)) := by
  rw [show rankRieszKernel S ψ c = fun i j =>
      c * (S ^ ψ * rankRieszUnitKernel ψ i j) by
    funext i j
    unfold rankRieszKernel
    ring]
  rw [realScaleMeshBandEnergy_const_mul]
  exact mul_le_mul_of_nonneg_left
    (realScaleMeshBandEnergy_scaled_le S ψ hS
      (rankRieszUnitKernel ψ) (rankRieszUnitKernel_abs_le_one ψ hψ0))
    (sq_nonneg c)

private theorem rankRieszUnitKernel_sq_eq_term {m : ℕ}
    (ψ : ℝ) (i j : Fin m) :
    rankRieszUnitKernel ψ i j ^ 2 = rankRieszTerm (2 * ψ) i j := by
  unfold rankRieszUnitKernel rankRieszTerm
  split_ifs with hzero
  · simp
  · have hk0 : (0 : ℝ) ≤ Nat.dist i.val j.val := by positivity
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hk0]
    congr 1
    ring

theorem rankRieszKernel_energy_le_power_sum {m : ℕ}
    (S ψ c : ℝ) (hS : 0 < S) :
    realScaleMeshEnergy S
        (rankRieszKernel S ψ c : Fin m → Fin m → ℝ) ≤
      c ^ 2 * S ^ (2 * ψ - 2) * (m : ℝ) *
        (2 * ∑ k ∈ Finset.range m,
          (((k + 1 : ℕ) : ℝ) ^ (-(2 * ψ)))) := by
  have hrows : ∀ i : Fin m,
      (∑ j : Fin m, rankRieszUnitKernel ψ i j ^ 2) ≤
        2 * ∑ k ∈ Finset.range m,
          (((k + 1 : ℕ) : ℝ) ^ (-(2 * ψ))) := by
    intro i
    simpa only [rankRieszUnitKernel_sq_eq_term] using
      sum_fin_rankRieszTerm_le m (2 * ψ) i
  have hdouble :
      (∑ i : Fin m, ∑ j : Fin m, rankRieszUnitKernel ψ i j ^ 2) ≤
        (m : ℝ) * (2 * ∑ k ∈ Finset.range m,
          (((k + 1 : ℕ) : ℝ) ^ (-(2 * ψ)))) := by
    calc
      _ ≤ ∑ _i : Fin m, (2 * ∑ k ∈ Finset.range m,
          (((k + 1 : ℕ) : ℝ) ^ (-(2 * ψ)))) :=
        Finset.sum_le_sum fun i _ => hrows i
      _ = _ := by simp
  have hscalar : S⁻¹ ^ 2 * (S ^ ψ) ^ 2 = S ^ (2 * ψ - 2) := by
    rw [show S⁻¹ = S ^ (-1 : ℝ) by rw [Real.rpow_neg_one],
      ← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul hS.le, ← Real.rpow_mul hS.le,
      ← Real.rpow_add hS]
    congr 1
    norm_num
    ring
  rw [show rankRieszKernel S ψ c = fun i j =>
      c * (S ^ ψ * rankRieszUnitKernel ψ i j) by
    funext i j
    unfold rankRieszKernel
    ring]
  rw [realScaleMeshEnergy_const_mul]
  unfold realScaleMeshEnergy
  simp_rw [mul_pow]
  have hscaled := mul_le_mul_of_nonneg_left hdouble
    (mul_nonneg (sq_nonneg S⁻¹) (sq_nonneg (S ^ ψ)))
  calc
    c ^ 2 * (S⁻¹ ^ 2 * ∑ i : Fin m, ∑ j : Fin m,
        (S ^ ψ) ^ 2 * rankRieszUnitKernel ψ i j ^ 2) =
      c ^ 2 * ((S⁻¹ ^ 2 * (S ^ ψ) ^ 2) *
        (∑ i : Fin m, ∑ j : Fin m, rankRieszUnitKernel ψ i j ^ 2)) := by
          simp only [Finset.mul_sum]
          ring
    _ ≤ c ^ 2 * ((S⁻¹ ^ 2 * (S ^ ψ) ^ 2) *
        ((m : ℝ) * (2 * ∑ k ∈ Finset.range m,
          (((k + 1 : ℕ) : ℝ) ^ (-(2 * ψ)))))) :=
      mul_le_mul_of_nonneg_left hscaled (sq_nonneg c)
    _ = _ := by
      rw [hscalar]
      ring

/-- Uniform energy bound when the matrix side length is at most three times
the real mesh scale. -/
theorem rankRieszKernel_energy_le_const {m : ℕ}
    (S ψ c : ℝ) (hS : 1 ≤ S) (hm : (m : ℝ) ≤ 3 * S)
    (hψ0 : 0 ≤ ψ) (hψhalf : ψ < 1 / 2) :
    realScaleMeshEnergy S
        (rankRieszKernel S ψ c : Fin m → Fin m → ℝ) ≤
      2 * c ^ 2 * (3 + 3 * 4 ^ (1 - 2 * ψ) / (1 - 2 * ψ)) := by
  let α := 1 - 2 * ψ
  have hS0 : 0 < S := zero_lt_one.trans_le hS
  have hα0 : 0 < α := by dsimp only [α]; linarith
  have hβ := sum_range_one_add_rpow_neg_le m (2 * ψ)
    (by positivity) (by linarith)
  have hraw := rankRieszKernel_energy_le_power_sum (m := m) S ψ c hS0
  have hbase0 : 0 ≤ c ^ 2 * S ^ (2 * ψ - 2) * (m : ℝ) * 2 := by positivity
  have hsum :
      c ^ 2 * S ^ (2 * ψ - 2) * (m : ℝ) *
          (2 * ∑ k ∈ Finset.range m,
            (((k + 1 : ℕ) : ℝ) ^ (-(2 * ψ)))) ≤
        c ^ 2 * S ^ (2 * ψ - 2) * (m : ℝ) *
          (2 * (1 + ((m + 1 : ℕ) : ℝ) ^ α / α)) := by
    have hh := mul_le_mul_of_nonneg_left hβ hbase0
    simpa only [α, mul_assoc] using hh
  have hA : S ^ (2 * ψ - 2) * (m : ℝ) ≤ 3 * S ^ (-α) := by
    calc
      _ ≤ S ^ (2 * ψ - 2) * (3 * S) :=
        mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg hS0.le _)
      _ = 3 * S ^ (-α) := by
        have hpow : S ^ (2 * ψ - 2) * S = S ^ (2 * ψ - 1) := by
          calc
            _ = S ^ (2 * ψ - 2) * S ^ (1 : ℝ) := by simp
            _ = S ^ ((2 * ψ - 2) + 1) := by rw [Real.rpow_add hS0]
            _ = _ := by congr 1 <;> ring
        rw [show -α = 2 * ψ - 1 by dsimp only [α]; ring, ← hpow]
        ring
  have hAle : S ^ (2 * ψ - 2) * (m : ℝ) ≤ 3 := by
    apply hA.trans
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (Real.rpow_le_one_of_one_le_of_nonpos hS (neg_nonpos.mpr hα0.le))
      (by norm_num : (0 : ℝ) ≤ 3)
  have hm1 : (((m + 1 : ℕ) : ℝ)) ≤ 4 * S := by
    push_cast
    linarith
  have hm1pow : (((m + 1 : ℕ) : ℝ) ^ α) ≤ (4 * S) ^ α :=
    Real.rpow_le_rpow (by positivity) hm1 hα0.le
  have hApow :
      (S ^ (2 * ψ - 2) * (m : ℝ)) * (((m + 1 : ℕ) : ℝ) ^ α) ≤
        3 * 4 ^ α := by
    calc
      _ ≤ (3 * S ^ (-α)) * (4 * S) ^ α :=
        mul_le_mul hA hm1pow (Real.rpow_nonneg (by positivity) _)
          (mul_nonneg (by norm_num) (Real.rpow_nonneg hS0.le _))
      _ = 3 * 4 ^ α := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hS0.le,
          Real.rpow_neg hS0.le]
        have hcancel : (S ^ α)⁻¹ * S ^ α = 1 :=
          inv_mul_cancel₀ (Real.rpow_pos_of_pos hS0 α).ne'
        rw [show (3 * (S ^ α)⁻¹) * (4 ^ α * S ^ α) =
          3 * 4 ^ α * ((S ^ α)⁻¹ * S ^ α) by ring, hcancel, mul_one]
  calc
    _ ≤ c ^ 2 * S ^ (2 * ψ - 2) * (m : ℝ) *
          (2 * ∑ k ∈ Finset.range m,
            (((k + 1 : ℕ) : ℝ) ^ (-(2 * ψ)))) := hraw
    _ ≤ c ^ 2 * S ^ (2 * ψ - 2) * (m : ℝ) *
          (2 * (1 + ((m + 1 : ℕ) : ℝ) ^ α / α)) := hsum
    _ ≤ 2 * c ^ 2 * (3 + 3 * 4 ^ α / α) := by
      have hdiv :
          (S ^ (2 * ψ - 2) * (m : ℝ)) *
              (((m + 1 : ℕ) : ℝ) ^ α / α) ≤
            (3 * 4 ^ α) / α := by
        calc
          _ = ((S ^ (2 * ψ - 2) * (m : ℝ)) *
              ((m + 1 : ℕ) : ℝ) ^ α) / α := by ring
          _ ≤ (3 * 4 ^ α) / α :=
            (div_le_div_iff_of_pos_right hα0).2 hApow
      nlinarith [sq_nonneg c]
    _ = _ := by dsimp only [α]

/-- On a consecutive active window, the physical-index Riesz reference is
exactly the rank-coordinate Riesz kernel. -/
theorem q1RieszActiveKernel_eq_rankRieszKernel
    (n : ℕ) (hn : 0 < n) (δ t S ψ c : ℝ) (hδ : 0 < δ)
    (hS : 0 < S) (hcard : 0 < (localWeightActiveSet n 1 δ t).card) :
    q1RieszActiveKernel n δ t S ψ c =
      (rankRieszKernel S ψ c :
        Fin (localWeightActiveSet n 1 δ t).card →
          Fin (localWeightActiveSet n 1 δ t).card → ℝ) := by
  funext i j
  have hdist := localWeightActiveIndex_physical_dist_eq_rank_dist
    n 1 hn δ t hδ hcard i j
  unfold q1RieszActiveKernel rankRieszKernel rankRieszUnitKernel
  rw [hdist]
  split_ifs with hzero
  · ring
  · have hk0 : (0 : ℝ) ≤ Nat.dist i.val j.val := by positivity
    rw [Real.div_rpow hS.le hk0, Real.rpow_neg hk0]
    rw [div_eq_mul_inv]
    ring

end Hurst
