import Hurst.LocalKernel
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Hurst

def continuousKernelGram (r : ℕ) (a b : ℝ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ :=
  fun i j => ∫ x in a..b, localKernel x * x ^ i.val * x ^ j.val

theorem continuousKernelGram_quadratic (r : ℕ) (a b : ℝ) (v : Fin (r + 1) → ℝ) :
    (∑ i, ∑ j, v i * continuousKernelGram r a b i j * v j) =
      ∫ x in a..b, localKernel x * (∑ k, v k * x ^ k.val) ^ 2 := by
  have hc : ∀ i j : Fin (r + 1), Continuous (fun x : ℝ => v i * (localKernel x * x ^ i.val * x ^ j.val) * v j) :=
    fun i j => (continuous_const.mul ((localKernel_smooth.continuous.mul (continuous_id.pow _)).mul (continuous_id.pow _))).mul continuous_const
  have he : ∀ i j : Fin (r + 1), v i * continuousKernelGram r a b i j * v j =
      ∫ x in a..b, v i * (localKernel x * x ^ i.val * x ^ j.val) * v j := by
    intro i j
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul]
    rfl
  simp only [he]
  have hinner (i : Fin (r + 1)) :
      (∑ j, ∫ x in a..b, v i * (localKernel x * x ^ i.val * x ^ j.val) * v j) =
        ∫ x in a..b, ∑ j, v i * (localKernel x * x ^ i.val * x ^ j.val) * v j :=
    (intervalIntegral.integral_finsetSum (fun j _ => (hc i j).intervalIntegrable a b)).symm
  simp_rw [hinner]
  rw [← intervalIntegral.integral_finsetSum (fun i _ =>
    (continuous_finsetSum Finset.univ (fun j _ => hc i j)).intervalIntegrable a b)]
  apply intervalIntegral.integral_congr
  intro x hx
  simp only [pow_two, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem continuousKernelGram_posDef (r : ℕ) (a b : ℝ) (ha : -1 ≤ a) (hb : b ≤ 1) (hab : a < b) :
    (continuousKernelGram r a b).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, continuousKernelGram]
    apply intervalIntegral.integral_congr
    intro x hx
    ring
  · intro v hv
    have he := kernel_polynomial_integral_pos v hv a b ha hb hab
    rw [← continuousKernelGram_quadratic] at he
    simpa only [dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum, mul_assoc] using he

theorem continuousKernelGram_continuous (r : ℕ) :
    Continuous (fun z : ℝ × ℝ => continuousKernelGram r z.1 z.2) := by
  apply continuous_matrix
  intro i j
  have hc : Continuous (fun x : ℝ => localKernel x * x ^ i.val * x ^ j.val) := by
    exact (localKernel_smooth.continuous.mul (continuous_id.pow _)).mul (continuous_id.pow _)
  have hp := intervalIntegral.continuous_primitive (μ := volume) (fun a b => hc.intervalIntegrable a b) 0
  have he : (fun z : ℝ × ℝ => continuousKernelGram r z.1 z.2 i j) =
      (fun z => (∫ x in (0 : ℝ)..z.2, localKernel x * x ^ i.val * x ^ j.val) -
        ∫ x in (0 : ℝ)..z.1, localKernel x * x ^ i.val * x ^ j.val) := by
    funext z
    exact (intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)).symm
  rw [he]
  exact (hp.comp continuous_snd).sub (hp.comp continuous_fst)

def kernelIntervalDomain : Set (ℝ × ℝ) :=
  {z | z.1 ∈ Icc (-1 : ℝ) 0 ∧ z.2 ∈ Icc (0 : ℝ) 1 ∧ 1 ≤ z.2 - z.1}

theorem kernelIntervalDomain_compact : IsCompact kernelIntervalDomain := by
  have he : kernelIntervalDomain = (Icc (-1 : ℝ) 0 ×ˢ Icc (0 : ℝ) 1) ∩ {z : ℝ × ℝ | 1 ≤ z.2 - z.1} := by
    ext z
    simp only [kernelIntervalDomain, mem_setOf_eq, mem_inter_iff, mem_prod]
    tauto
  rw [he]
  exact (isCompact_Icc.prod isCompact_Icc).inter_right (isClosed_le continuous_const (continuous_snd.sub continuous_fst))

theorem kernelIntervalDomain_actual (t b : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (hb : 0 < b) (hbhalf : b ≤ 1 / 2) :
    (max (-1) (-t / b), min 1 ((1 - t) / b)) ∈ kernelIntervalDomain := by
  have ht0 := ht.1
  have ht1 := ht.2
  have hlower : -t / b ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hb.le
  have hupper : 0 ≤ (1 - t) / b := div_nonneg (by linarith) hb.le
  refine ⟨⟨le_max_left _ _, max_le (by norm_num) hlower⟩,
    ⟨le_min (by norm_num) hupper, min_le_left _ _⟩, ?_⟩
  rcases le_total t (1 / 2) with htleft | htright
  · have h : 1 ≤ (1 - t) / b := (le_div_iff₀ hb).mpr (by linarith)
    rw [min_eq_left h]
    have hc : max (-1) (-t / b) ≤ 0 := max_le (by norm_num) hlower
    linarith
  · have h : -t / b ≤ -1 := (div_le_iff₀ hb).mpr (by linarith)
    rw [max_eq_left h]
    have hc : 0 ≤ min 1 ((1 - t) / b) := le_min (by norm_num) hupper
    linarith

theorem compact_support_interval_clamp (f : ℝ → ℝ) (hf : Continuous f)
    (hzero : ∀ x, 1 ≤ |x| → f x = 0) (a b : ℝ) :
    (∫ x in a..b, f x) = ∫ x in (max (-1) a)..(min 1 b), f x := by
  have hl : (∫ x in a..max (-1) a, f x) = 0 := by
    apply intervalIntegral.integral_zero_ae
    apply Filter.Eventually.of_forall
    intro x hx
    rw [uIoc_of_le (le_max_right _ _)] at hx
    by_cases he : -1 ≤ a
    · rw [max_eq_right he] at hx
      exact (not_lt_of_ge hx.2 hx.1).elim
    · rw [max_eq_left (le_of_not_ge he)] at hx
      exact hzero x (by rw [abs_of_nonpos (by linarith [hx.2])]; linarith [hx.2])
  have hu : (∫ x in min 1 b..b, f x) = 0 := by
    apply intervalIntegral.integral_zero_ae
    apply Filter.Eventually.of_forall
    intro x hx
    rw [uIoc_of_le (min_le_right _ _)] at hx
    by_cases he : b ≤ 1
    · rw [min_eq_right he] at hx
      exact (not_lt_of_ge hx.2 hx.1).elim
    · rw [min_eq_left (le_of_not_ge he)] at hx
      exact hzero x (by rw [abs_of_nonneg (by linarith [hx.1])]; linarith [hx.1])
  have h1 := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (hf.intervalIntegrable a (max (-1) a))
    (hf.intervalIntegrable (max (-1) a) (min 1 b))
  have h2 := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (hf.intervalIntegrable a (min 1 b))
    (hf.intervalIntegrable (min 1 b) b)
  rw [hl, zero_add] at h1
  rw [hu, add_zero, ← h1] at h2
  exact h2.symm

theorem continuousKernelGram_moment (r : ℕ) (a b : ℝ) (i j : Fin (r + 1)) :
    continuousKernelGram r a b i j = ∫ x in a..b, kernelMomentFunction (i.val + j.val) x := by
  apply intervalIntegral.integral_congr
  intro x hx
  simp only [kernelMomentFunction, pow_add]
  ring

end Hurst
