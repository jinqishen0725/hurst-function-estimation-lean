import Hurst.WeightEnergyLimit
import Hurst.CorrelationLimit
import Mathlib.Analysis.Real.Sqrt

noncomputable section
open Filter
open scoped Topology
namespace Hurst

theorem abs_finset_sum_mul_le_sqrt_mul_sqrt
    {ι : Type*} [Fintype ι] (f g : ι → ℝ) :
    |∑ i, f i * g i| ≤ Real.sqrt (∑ i, f i ^ 2) * Real.sqrt (∑ i, g i ^ 2) := by
  rw [abs_le]
  constructor
  · have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (-f) g
    have h' := neg_le_neg h
    simpa only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_neg,
      neg_sq] using h'
  · exact Real.sum_mul_le_sqrt_mul_sqrt Finset.univ f g

/-- A fixed-shift cross energy has the same limit as the unshifted energy once
the shifted row is asymptotically equal in the scaled discrete L2 norm. -/
theorem weighted_cross_energy_tendsto_of_scaled_l2
    (κ : ℕ → Type*) [∀ n, Fintype (κ n)]
    (N : ℕ → ℝ) (w u : ∀ n, κ n → ℝ) (E : ℝ)
    (hN : ∀ᶠ n in atTop, 0 ≤ N n)
    (henergy : Tendsto (fun n => N n * ∑ i, w n i ^ 2) atTop (𝓝 E))
    (hshift : Tendsto (fun n => N n * ∑ i, (u n i - w n i) ^ 2)
      atTop (𝓝 0)) :
    Tendsto (fun n => N n * ∑ i, w n i * u n i) atTop (𝓝 E) := by
  let A := fun n => N n * ∑ i, w n i ^ 2
  let D := fun n => N n * ∑ i, (u n i - w n i) ^ 2
  let R := fun n => N n * ∑ i, w n i * (u n i - w n i)
  have hA0 : ∀ᶠ n in atTop, 0 ≤ A n := by
    filter_upwards [hN] with n hn
    exact mul_nonneg hn (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hD0 : ∀ᶠ n in atTop, 0 ≤ D n := by
    filter_upwards [hN] with n hn
    exact mul_nonneg hn (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hbound : ∀ᶠ n in atTop, |R n| ≤ Real.sqrt (A n) * Real.sqrt (D n) := by
    filter_upwards [hN] with n hn
    have hs := abs_finset_sum_mul_le_sqrt_mul_sqrt
      (fun i => Real.sqrt (N n) * w n i)
      (fun i => Real.sqrt (N n) * (u n i - w n i))
    have hsqrt : Real.sqrt (N n) ^ 2 = N n := Real.sq_sqrt hn
    have hleft : R n = ∑ i,
        (Real.sqrt (N n) * w n i) *
          (Real.sqrt (N n) * (u n i - w n i)) := by
      dsimp [R]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      have hroot : Real.sqrt (N n) * Real.sqrt (N n) = N n := by
        simpa only [pow_two] using hsqrt
      calc
        N n * (w n i * (u n i - w n i)) =
            (Real.sqrt (N n) * Real.sqrt (N n)) *
              (w n i * (u n i - w n i)) := by rw [hroot]
        _ = _ := by ring
    have hrightA : (∑ i, (Real.sqrt (N n) * w n i) ^ 2) = A n := by
      dsimp [A]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_pow, hsqrt]
    have hrightD : (∑ i, (Real.sqrt (N n) * (u n i - w n i)) ^ 2) = D n := by
      dsimp [D]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_pow, hsqrt]
    rw [hleft, ← hrightA, ← hrightD]
    exact hs
  have hR : Tendsto R atTop (𝓝 0) := by
    have hsA : Tendsto (fun n => Real.sqrt (A n)) atTop (𝓝 (Real.sqrt E)) :=
      Real.continuous_sqrt.continuousAt.tendsto.comp (by simpa only [A] using henergy)
    have hsD : Tendsto (fun n => Real.sqrt (D n)) atTop (𝓝 0) := by
      have hDt : Tendsto D atTop (𝓝 0) := by simpa only [D] using hshift
      change Tendsto ((fun x : ℝ => Real.sqrt x) ∘ D) atTop (𝓝 0)
      simpa only [Real.sqrt_zero] using
        Real.continuous_sqrt.continuousAt.tendsto.comp hDt
    have hprod : Tendsto (fun n => Real.sqrt (A n) * Real.sqrt (D n))
        atTop (𝓝 0) := by
      simpa only [mul_zero] using hsA.mul hsD
    apply tendsto_of_abs_sub_le_zero R (fun _ => 0)
      (fun n => Real.sqrt (A n) * Real.sqrt (D n)) 0 tendsto_const_nhds
      hprod
    · filter_upwards [hA0, hD0] with n hAn hDn
      exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    · filter_upwards [hbound] with n hn
      simpa only [sub_zero] using hn
  have hid : (fun n => N n * ∑ i, w n i * u n i) = fun n => A n + R n := by
    funext n
    dsimp [A, R]
    rw [← mul_add, ← Finset.sum_add_distrib]
    apply congrArg (fun z => N n * z)
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hid]
  simpa only [A, add_zero] using henergy.add hR

end Hurst
