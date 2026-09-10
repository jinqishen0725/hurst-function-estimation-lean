import Hurst.KernelGram
import Hurst.UniformQuadrature
import Hurst.CompactInverse
import Mathlib.Analysis.Matrix.PosDef

noncomputable section
open Set MeasureTheory
open scoped BigOperators Matrix.Norms.Elementwise
namespace Hurst

def localDesignGram (r n q : ℕ) (b t : ℝ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ :=
  designGram (fun i : Fin (n - q) => ((n : ℝ) * b)⁻¹ * localKernel ((grid n i.val - t) / b))
    (fun i k => ((grid n i.val - t) / b) ^ k.val)

theorem localDesignGram_moment (r n q : ℕ) (b t : ℝ) (i j : Fin (r + 1)) :
    localDesignGram r n q b t i j =
      ((n : ℝ) * b)⁻¹ * ∑ k : Fin (n - q), kernelMomentFunction (i.val + j.val) ((grid n k.val - t) / b) := by
  unfold localDesignGram designGram
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [kernelMomentFunction, pow_add]
  ring

theorem localDesignGram_uniform_quadrature (r q : ℕ) :
    ∃ C > 0, ∀ n : ℕ, 0 < n → q ≤ n → ∀ b t : ℝ, 0 < b →
      ∀ i j : Fin (r + 1),
        |(localDesignGram r n q b t - continuousKernelGram r (max (-1) (-t / b)) (min 1 ((1 - t) / b))) i j| ≤
          C / ((n : ℝ) * b) := by
  choose B hB hbound using kernelMomentFunction_bounded
  let J (k : ℕ) := ∫ x : ℝ, |deriv (kernelMomentFunction k) x|
  have hJ : ∀ k, 0 ≤ J k := fun k => integral_nonneg (fun x => abs_nonneg _)
  let E (i j : Fin (r + 1)) := J (i.val + j.val) + q * B (i.val + j.val)
  have hE : ∀ i j, 0 ≤ E i j := fun i j => add_nonneg (hJ _) (mul_nonneg (Nat.cast_nonneg _) (hB _))
  let C := 1 + ∑ i, ∑ j, E i j
  have hC : 0 < C := by
    have hsum : 0 ≤ ∑ i, ∑ j, E i j := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hE i j))
    dsimp [C]
    linarith
  refine ⟨C, hC, ?_⟩
  intro n hn hq b t hb i j
  have heC : E i j ≤ C := by
    have h1 := Finset.single_le_sum (fun k _ => hE i k) (Finset.mem_univ j)
    have h2 : (∑ l, E i l) ≤ ∑ k, ∑ l, E k l := Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => hE k l)) (Finset.mem_univ i)
    dsimp [C]
    linarith
  have hderiv : ∀ x, HasDerivAt (kernelMomentFunction (i.val + j.val))
      (deriv (kernelMomentFunction (i.val + j.val)) x) x :=
    fun x => ((kernelMomentFunction_smooth _).differentiable (by simp) x).hasDerivAt
  have hquad := midpoint_design_quadrature_uniform _ _ hderiv (kernelMomentFunction_derivative_integrable _)
    (B (i.val + j.val)) (hbound _) n q hn hq b t hb
  have heq : continuousKernelGram r (max (-1) (-t / b)) (min 1 ((1 - t) / b)) i j =
      ∫ x in (-t / b)..((1 - t) / b), kernelMomentFunction (i.val + j.val) x := by
    rw [continuousKernelGram_moment]
    symm
    exact compact_support_interval_clamp _ (kernelMomentFunction_smooth _).continuous
      (fun x hx => by simp only [kernelMomentFunction, localKernel_zero x hx, zero_mul]) _ _
  simp only [Matrix.sub_apply, localDesignGram_moment, heq]
  exact hquad.trans (div_le_div_of_nonneg_right heC (mul_nonneg (Nat.cast_nonneg n) hb.le))

/-- A genuine uniform inverse bound for all valid midpoint designs, including t=0 and t=1. -/
theorem localDesignGram_uniform_inverse (r q : ℕ) :
    ∃ N₀ > 0, ∃ C ≥ 0, ∀ n : ℕ, 0 < n → q ≤ n → ∀ b t : ℝ,
      0 < b → b ≤ 1 / 2 → t ∈ Icc (0 : ℝ) 1 → N₀ ≤ (n : ℝ) * b →
      IsUnit (localDesignGram r n q b t).det ∧
        ∀ i j, |(localDesignGram r n q b t)⁻¹ i j| ≤ C := by
  let S := (fun z : ℝ × ℝ => continuousKernelGram r z.1 z.2) '' kernelIntervalDomain
  have hS : IsCompact S := kernelIntervalDomain_compact.image (continuousKernelGram_continuous r)
  have hdet : ∀ A ∈ S, A.det ≠ 0 := by
    rintro A ⟨z, hz, rfl⟩
    exact (continuousKernelGram_posDef r z.1 z.2 hz.1.1 hz.2.1.2 (by linarith [hz.2.2])).det_pos.ne'
  obtain ⟨δ, hδ, C, hC, hinv⟩ := matrix_inverse_uniform_near_compact S hS hdet
  obtain ⟨D, hD, hquad⟩ := localDesignGram_uniform_quadrature r q
  refine ⟨max 1 (D / δ), lt_of_lt_of_le zero_lt_one (le_max_left _ _), C, hC, ?_⟩
  intro n hn hq b t hb hbhalf ht hN
  let a := max (-1) (-t / b)
  let c := min 1 ((1 - t) / b)
  have hmem : continuousKernelGram r a c ∈ S :=
    mem_image_of_mem _ (kernelIntervalDomain_actual t b ht hb hbhalf)
  apply hinv _ hmem (localDesignGram r n q b t)
  apply (Matrix.norm_le_iff hδ.le).mpr
  intro i j
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsmall : D / ((n : ℝ) * b) ≤ δ := by
    apply (div_le_iff₀ (mul_pos hnR hb)).mpr
    have he := (div_le_iff₀ hδ).mp ((le_max_right _ _).trans hN)
    nlinarith
  exact (hquad n hn hq b t hb i j).trans hsmall

end Hurst
