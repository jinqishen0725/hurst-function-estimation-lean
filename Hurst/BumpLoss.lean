import Hurst.BumpPacking
import Hurst.Harmonizable
import Mathlib.InformationTheory.Hamming

noncomputable section
open Set MeasureTheory
namespace Hurst

theorem correctedBump_nonzero_iff (x : ℝ) : correctedBump x ≠ 0 ↔ x ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
  constructor
  · intro hx
    constructor
    · by_contra h
      exact hx (correctedBump_zero x (Or.inl (le_of_not_gt h)))
    · by_contra h
      exact hx (correctedBump_zero x (Or.inr (le_of_not_gt h)))
  · exact fun hx => (correctedBump_positive x hx).ne'

theorem sum_abs_rpow_of_unique_active {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℝ) (s : ℝ) (hs : 0 < s) (hunique : ∀ i j, f i ≠ 0 → f j ≠ 0 → i = j) :
    |∑ i, f i| ^ s = ∑ i, |f i| ^ s := by
  by_cases hf : ∀ i, f i = 0
  · simp only [hf, Finset.sum_const_zero, abs_zero, Real.zero_rpow hs.ne']
  · obtain ⟨i, hi⟩ := not_forall.mp hf
    have hz : ∀ j, j ≠ i → f j = 0 := by
      intro j hji
      by_contra hj
      exact hji (hunique j i hj hi)
    rw [Finset.sum_eq_single i, Finset.sum_eq_single i]
    · intro j hj hji
      rw [hz j hji, abs_zero, Real.zero_rpow hs.ne']
    · simp
    · intro j hj hji
      exact hz j hji
    · simp

theorem binaryBumpSum_abs_rpow (m : ℕ) (θ : Fin m → ℝ) (x s : ℝ) (hs : 0 < s) :
    |binaryBumpSum m θ x| ^ s =
      ∑ i, |θ i| ^ s * |correctedBump ((m : ℝ) * x - i.val - 1 / 2)| ^ s := by
  have hu : ∀ i j : Fin m,
      θ i * correctedBump ((m : ℝ) * x - i.val - 1 / 2) ≠ 0 →
      θ j * correctedBump ((m : ℝ) * x - j.val - 1 / 2) ≠ 0 → i = j := by
    intro i j hi hj
    have hi' := (correctedBump_nonzero_iff _).mp (right_ne_zero_of_mul hi)
    have hj' := (correctedBump_nonzero_iff _).mp (right_ne_zero_of_mul hj)
    apply Fin.ext
    rcases lt_trichotomy i.val j.val with hij | hij | hij
    · have he : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast Nat.succ_le_of_lt hij
      linarith [hi'.2, hj'.1]
    · exact hij
    · have he : (j.val : ℝ) + 1 ≤ i.val := by exact_mod_cast Nat.succ_le_of_lt hij
      linarith [hi'.1, hj'.2]
  rw [binaryBumpSum, sum_abs_rpow_of_unique_active _ s hs hu]
  apply Finset.sum_congr rfl
  intro i _
  rw [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]

theorem correctedBump_power_integrable (s : ℝ) (hs : 0 < s) :
    Integrable (fun x => |correctedBump x| ^ s) (volume : Measure ℝ) := by
  have hcompact : HasCompactSupport correctedBump :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) correctedBump_tsupport_subset
  have hc : Continuous (fun x => |correctedBump x| ^ s) :=
    correctedBump_smooth.continuous.abs.rpow_const (fun _ => Or.inr hs.le)
  exact hc.integrable_of_hasCompactSupport (hcompact.comp_left (g := fun y : ℝ => |y| ^ s) (by simp [Real.zero_rpow hs.ne']))

theorem correctedBump_power_integral_pos (s : ℝ) (hs : 0 < s) :
    0 < ∫ x : ℝ, |correctedBump x| ^ s := by
  have hcompact : HasCompactSupport correctedBump :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) correctedBump_tsupport_subset
  have hc : Continuous (fun x => |correctedBump x| ^ s) :=
    correctedBump_smooth.continuous.abs.rpow_const (fun _ => Or.inr hs.le)
  apply hc.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (hcompact.comp_left (g := fun y : ℝ => |y| ^ s) (by simp [Real.zero_rpow hs.ne'])) (fun x => Real.rpow_nonneg (abs_nonneg _) s)
  exact (Real.rpow_pos_of_pos (abs_pos.mpr (correctedBump_positive 0 (by norm_num)).ne') s).ne'

theorem affine_bump_power_integrable (m : ℕ) (hm : 0 < m) (c s : ℝ) (hs : 0 < s) :
    Integrable (fun x : ℝ => |correctedBump ((m : ℝ) * x + c)| ^ s) volume := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hcompact : HasCompactSupport correctedBump :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) correctedBump_tsupport_subset
  have hpower : HasCompactSupport (fun x => |correctedBump x| ^ s) :=
    hcompact.comp_left (g := fun y : ℝ => |y| ^ s) (by simp [Real.zero_rpow hs.ne'])
  have he := hpower.comp_homeomorph ((Homeomorph.mulLeft₀ (m : ℝ) hmR).trans (Homeomorph.addRight c))
  have hc : Continuous (fun x : ℝ => |correctedBump ((m : ℝ) * x + c)| ^ s) :=
    (correctedBump_smooth.continuous.comp (continuous_const.mul continuous_id |>.add continuous_const)).abs.rpow_const
      (fun _ => Or.inr hs.le)
  exact hc.integrable_of_hasCompactSupport he

theorem affine_bump_power_integral (m : ℕ) (hm : 0 < m) (c s : ℝ) :
    (∫ x : ℝ, |correctedBump ((m : ℝ) * x + c)| ^ s) =
      (m : ℝ)⁻¹ * ∫ x : ℝ, |correctedBump x| ^ s := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have he := Measure.integral_comp_mul_left (fun x : ℝ => |correctedBump (x + c)| ^ s) (m : ℝ)
  rw [integral_add_right_eq_self (fun x : ℝ => |correctedBump x| ^ s) c, abs_of_pos (inv_pos.mpr hmR), smul_eq_mul] at he
  exact he

theorem binaryBumpSum_power_integral (m : ℕ) (hm : 0 < m) (θ : Fin m → ℝ) (s : ℝ) (hs : 0 < s) :
    (∫ x : ℝ, |binaryBumpSum m θ x| ^ s) =
      (m : ℝ)⁻¹ * (∑ i, |θ i| ^ s) * ∫ x : ℝ, |correctedBump x| ^ s := by
  simp_rw [binaryBumpSum_abs_rpow m θ _ s hs]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul]
    have he : ∀ i : Fin m, (∫ x : ℝ, |correctedBump ((m : ℝ) * x - i.val - 1 / 2)| ^ s) =
        (m : ℝ)⁻¹ * ∫ x : ℝ, |correctedBump x| ^ s := by
      intro i
      simpa only [sub_eq_add_neg, add_assoc] using affine_bump_power_integral m hm (-(i.val : ℝ) - 1 / 2) s
    simp_rw [he]
    rw [← Finset.sum_mul]
    ring
  · intro i _
    have hi := (affine_bump_power_integrable m hm (-(i.val : ℝ) - 1 / 2) s hs).const_mul (|θ i| ^ s)
    simpa only [sub_eq_add_neg, add_assoc] using hi

theorem bumpAlternative_sub (m : ℕ) (p ε : ℝ) (θ η : Fin m → ℝ) (x : ℝ) :
    bumpAlternative m p ε θ x - bumpAlternative m p ε η x =
      (ε * (m : ℝ) ^ (-p)) * binaryBumpSum m (fun i => θ i - η i) x := by
  simp only [bumpAlternative, binaryBumpSum, sub_mul, Finset.sum_sub_distrib]
  ring

theorem bumpAlternative_loss_integral (m : ℕ) (hm : 0 < m) (p ε s : ℝ) (hε : 0 ≤ ε)
    (hs : 0 < s) (θ η : Fin m → ℝ) :
    (∫ x : ℝ, |bumpAlternative m p ε θ x - bumpAlternative m p ε η x| ^ s) =
      ε ^ s * (m : ℝ) ^ (-p * s - 1) * (∑ i, |θ i - η i| ^ s) *
        ∫ x : ℝ, |correctedBump x| ^ s := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hpoint (x : ℝ) : |bumpAlternative m p ε θ x - bumpAlternative m p ε η x| ^ s =
      (ε * (m : ℝ) ^ (-p)) ^ s * |binaryBumpSum m (fun i => θ i - η i) x| ^ s := by
    rw [bumpAlternative_sub, abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ ε * (m : ℝ) ^ (-p)),
      Real.mul_rpow (by positivity : 0 ≤ ε * (m : ℝ) ^ (-p)) (abs_nonneg _)]
  simp_rw [hpoint]
  rw [integral_const_mul, binaryBumpSum_power_integral m hm _ s hs,
    Real.mul_rpow hε (Real.rpow_nonneg hmR.le _), ← Real.rpow_mul hmR.le]
  have hp : (m : ℝ) ^ (-p * s) * (m : ℝ)⁻¹ = (m : ℝ) ^ (-p * s - 1) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hmR]
    congr 1
  calc
    _ = ε ^ s * ((m : ℝ) ^ (-p * s) * (m : ℝ)⁻¹) * (∑ i, |θ i - η i| ^ s) *
        ∫ x : ℝ, |correctedBump x| ^ s := by ring
    _ = _ := by rw [hp]

theorem bumpAlternative_loss_on_unit_interval (m : ℕ) (p ε s : ℝ) (hs : 0 < s) (θ η : Fin m → ℝ) :
    (∫ x in Ioo (0 : ℝ) 1, |bumpAlternative m p ε θ x - bumpAlternative m p ε η x| ^ s) =
      ∫ x : ℝ, |bumpAlternative m p ε θ x - bumpAlternative m p ε η x| ^ s := by
  symm
  have he := setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (μ := (volume : Measure ℝ)) (f := fun x => |bumpAlternative m p ε θ x - bumpAlternative m p ε η x| ^ s)
    MeasurableSet.univ (subset_univ (Ioo (0 : ℝ) 1)) (fun x hx => by
      have houtside : x ≤ 0 ∨ 1 ≤ x := by
        by_cases h0 : 0 < x
        · right
          exact le_of_not_gt (fun h1 => hx.2 ⟨h0, h1⟩)
        · exact Or.inl (le_of_not_gt h0)
      rw [bumpAlternative_sub, binaryBumpSum_zero_outside m _ x houtside,
        mul_zero, abs_zero, Real.zero_rpow hs.ne'])
  simpa only [Measure.restrict_univ] using he

def booleanBumpWeights {m : ℕ} (θ : Fin m → Bool) (i : Fin m) : ℝ := if θ i then 1 else 0

theorem booleanBumpWeights_bound {m : ℕ} (θ : Fin m → Bool) : ∀ i, |booleanBumpWeights θ i| ≤ 1 := by
  intro i
  unfold booleanBumpWeights
  split_ifs <;> norm_num

theorem booleanBumpWeights_hamming_sum {m : ℕ} (θ η : Fin m → Bool) (s : ℝ) (hs : 0 < s) :
    (∑ i, |booleanBumpWeights θ i - booleanBumpWeights η i| ^ s) = (hammingDist θ η : ℝ) := by
  classical
  have he : ∀ i, |booleanBumpWeights θ i - booleanBumpWeights η i| ^ s =
      if θ i ≠ η i then (1 : ℝ) else 0 := by
    intro i
    cases hθ : θ i <;> cases hη : η i <;>
      simp [booleanBumpWeights, hθ, hη, Real.zero_rpow hs.ne']
  simp only [he, hammingDist, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

/-- Exact Ls-power separation in the original domain, with the Hamming distance as its only code dependence. -/
theorem bumpAlternative_boolean_loss_identity (m : ℕ) (hm : 0 < m) (p ε s : ℝ)
    (hε : 0 ≤ ε) (hs : 0 < s) (θ η : Fin m → Bool) :
    (∫ x in Ioo (0 : ℝ) 1, |bumpAlternative m p ε (booleanBumpWeights θ) x -
        bumpAlternative m p ε (booleanBumpWeights η) x| ^ s) =
      ε ^ s * (m : ℝ) ^ (-p * s - 1) * (hammingDist θ η : ℝ) *
        ∫ x : ℝ, |correctedBump x| ^ s := by
  rw [bumpAlternative_loss_on_unit_interval m p ε s hs,
    bumpAlternative_loss_integral m hm p ε s hε hs, booleanBumpWeights_hamming_sum θ η s hs]

end Hurst
