import Hurst.EquivalentKernel
import Hurst.InteriorDesignLimit
import Hurst.UniformQuadrature

noncomputable section
set_option maxHeartbeats 800000
open Set MeasureTheory Filter
open scoped Topology
namespace Hurst

def kernelSquareMomentFunction (k : ℕ) (x : ℝ) : ℝ := localKernel x ^ 2 * x ^ k

theorem kernelSquareMomentFunction_smooth (k : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (kernelSquareMomentFunction k) :=
  localKernel_smooth.pow 2 |>.mul (contDiff_id.pow k)

theorem kernelSquareMomentFunction_compactSupport (k : ℕ) :
    HasCompactSupport (kernelSquareMomentFunction k) := by
  apply localKernel_compactSupport.mono
  intro x hx
  show localKernel x ≠ 0
  intro hzero
  exact hx (by simp [kernelSquareMomentFunction, hzero, pow_two])

theorem kernelSquareMomentFunction_derivative_integrable (k : ℕ) :
    Integrable (deriv (kernelSquareMomentFunction k)) := by
  have hc := (kernelSquareMomentFunction_smooth k).continuous_deriv (by simp)
  exact hc.integrable_of_hasCompactSupport (kernelSquareMomentFunction_compactSupport k).deriv

theorem kernelSquareMomentFunction_bounded (k : ℕ) :
    ∃ C ≥ 0, ∀ x : ℝ, |kernelSquareMomentFunction k x| ≤ C := by
  obtain ⟨C, hC⟩ := (kernelSquareMomentFunction_compactSupport k).exists_bound_of_continuousOn
    (kernelSquareMomentFunction_smooth k).continuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : kernelSquareMomentFunction k x = 0
  · simp only [hx, abs_zero]
    exact le_max_right _ _
  · exact (hC x (subset_closure hx)).trans (le_max_left _ _)

def kernelSquareMomentGrid (n q : ℕ) (δ t : ℝ) (k : ℕ) : ℝ :=
  ((n : ℝ) * δ)⁻¹ * ∑ i : Fin (n - q),
    kernelSquareMomentFunction k ((grid n i.val - t) / δ)

def kernelSquareMomentIntegral (k : ℕ) : ℝ :=
  ∫ x in (-1 : ℝ)..1, kernelSquareMomentFunction k x

theorem kernelSquareMomentGrid_tendsto (q k : ℕ) (t : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1) (δ : ℕ → ℝ)
    (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop) :
    Tendsto (fun n => kernelSquareMomentGrid n q (δ n) t k) atTop
      (𝓝 (kernelSquareMomentIntegral k)) := by
  obtain ⟨B, hB, hbound⟩ := kernelSquareMomentFunction_bounded k
  let C := (∫ x, |deriv (kernelSquareMomentFunction k) x|) + (q : ℝ) * B
  have hsmall : ∀ᶠ n in atTop, δ n ≤ t ∧ δ n ≤ 1 - t :=
    (hδ.eventually (gt_mem_nhds ht.1)).and
      (hδ.eventually (gt_mem_nhds (by linarith [ht.2] : 0 < 1 - t))) |>.mono
        (fun _ hn => ⟨hn.1.le, hn.2.le⟩)
  have hbound' : ∀ᶠ n in atTop,
      |kernelSquareMomentGrid n q (δ n) t k - kernelSquareMomentIntegral k| ≤
        C / ((n : ℝ) * δ n) := by
    filter_upwards [hδpos, hsmall, eventually_ge_atTop (q + 1)] with n hn hs hnq
    have hn0 : 0 < n := by omega
    have hquad := midpoint_design_quadrature_uniform (kernelSquareMomentFunction k)
      (deriv (kernelSquareMomentFunction k))
      (fun x => ((kernelSquareMomentFunction_smooth k).differentiable (by simp) x).hasDerivAt)
      (kernelSquareMomentFunction_derivative_integrable k) B hbound n q hn0 (by omega)
      (δ n) t hn
    have hleft : -t / δ n ≤ -1 := (div_le_iff₀ hn).mpr (by linarith)
    have hright : 1 ≤ (1 - t) / δ n := (le_div_iff₀ hn).mpr (by linarith)
    have hi : (∫ x in (-t / δ n)..((1 - t) / δ n), kernelSquareMomentFunction k x) =
        kernelSquareMomentIntegral k := by
      rw [compact_support_interval_clamp _ (kernelSquareMomentFunction_smooth k).continuous
        (fun x hx => by
          rw [kernelSquareMomentFunction, localKernel_zero x hx]
          norm_num), max_eq_left hleft, min_eq_left hright]
      rfl
    simpa only [kernelSquareMomentGrid, kernelSquareMomentIntegral, hi] using hquad
  have hzero : Tendsto (fun n : ℕ => C / ((n : ℝ) * δ n)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp hN).const_mul C
  have hsqueeze := squeeze_zero' (Eventually.of_forall (fun n => abs_nonneg
    (kernelSquareMomentGrid n q (δ n) t k - kernelSquareMomentIntegral k))) hbound' hzero
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using hsqueeze)

def equivalentKernelSquareEnergy (r : ℕ) : ℝ :=
  ∑ j : Fin (r + 1), ∑ k : Fin (r + 1),
    (continuousKernelGram r (-1) 1)⁻¹ 0 j *
      (continuousKernelGram r (-1) 1)⁻¹ 0 k *
        kernelSquareMomentIntegral (j.val + k.val)

theorem equivalentKernelSquareEnergy_eq_integral (r : ℕ) :
    equivalentKernelSquareEnergy r = ∫ x in (-1 : ℝ)..1, equivalentKernel r x ^ 2 := by
  let A := (continuousKernelGram r (-1) 1)⁻¹
  have hpoint (x : ℝ) : equivalentKernel r x ^ 2 =
      ∑ j : Fin (r + 1), ∑ k : Fin (r + 1),
        A 0 j * A 0 k * kernelSquareMomentFunction (j.val + k.val) x := by
    simp only [equivalentKernel, kernelSquareMomentFunction, A, pow_add, pow_two,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hint (j k : Fin (r + 1)) : IntervalIntegrable
      (fun x => A 0 j * A 0 k * kernelSquareMomentFunction (j.val + k.val) x)
      volume (-1) 1 := by
    exact ((continuous_const.mul continuous_const).mul
      (kernelSquareMomentFunction_smooth _).continuous).intervalIntegrable _ _
  have hterm (j k : Fin (r + 1)) :
      A 0 j * A 0 k * kernelSquareMomentIntegral (j.val + k.val) =
        ∫ x in (-1 : ℝ)..1,
          A 0 j * A 0 k * kernelSquareMomentFunction (j.val + k.val) x := by
    simp only [kernelSquareMomentIntegral]
    rw [intervalIntegral.integral_const_mul]
  change (∑ j : Fin (r + 1), ∑ k : Fin (r + 1),
    A 0 j * A 0 k * kernelSquareMomentIntegral (j.val + k.val)) = _
  simp_rw [hterm]
  have hinner (j : Fin (r + 1)) :
      (∑ k, ∫ x in (-1 : ℝ)..1,
        A 0 j * A 0 k * kernelSquareMomentFunction (j.val + k.val) x) =
      ∫ x in (-1 : ℝ)..1, ∑ k,
        A 0 j * A 0 k * kernelSquareMomentFunction (j.val + k.val) x :=
    (intervalIntegral.integral_finsetSum (fun k _ => hint j k)).symm
  simp_rw [hinner]
  have houter :
      (∑ j : Fin (r + 1), ∫ x in (-1 : ℝ)..1, ∑ k : Fin (r + 1),
        A 0 j * A 0 k * kernelSquareMomentFunction (j.val + k.val) x) =
      ∫ x in (-1 : ℝ)..1, ∑ j : Fin (r + 1), ∑ k : Fin (r + 1),
        A 0 j * A 0 k * kernelSquareMomentFunction (j.val + k.val) x :=
    by
      simpa only [Finset.sum_apply] using
        (intervalIntegral.integral_finsetSum (s := Finset.univ) (fun j _ =>
          IntervalIntegrable.sum Finset.univ (fun k _ => hint j k))).symm
  rw [houter]
  apply intervalIntegral.integral_congr
  intro x _
  exact (hpoint x).symm

theorem localPolynomialWeights_energy_identity (r n q : ℕ) (δ t : ℝ) :
    (n : ℝ) * δ * ∑ i, localPolynomialWeights r n q δ t i ^ 2 =
      ∑ j : Fin (r + 1), ∑ k : Fin (r + 1),
        (localDesignGram r n q δ t)⁻¹ 0 j *
          (localDesignGram r n q δ t)⁻¹ 0 k *
            kernelSquareMomentGrid n q δ t (j.val + k.val) := by
  simp only [localPolynomialWeights_formula, kernelSquareMomentGrid,
    kernelSquareMomentFunction, Finset.sum_mul, Finset.mul_sum, pow_two, pow_add]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  field_simp

theorem localPolynomialWeights_energy_tendsto (r q : ℕ) (t : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1) (δ : ℕ → ℝ)
    (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop) :
    Tendsto (fun (n : ℕ) => (n : ℝ) * δ n *
      ∑ i, localPolynomialWeights r n q (δ n) t i ^ 2) atTop
      (𝓝 (equivalentKernelSquareEnergy r)) := by
  rw [show equivalentKernelSquareEnergy r = ∑ j : Fin (r + 1), ∑ k : Fin (r + 1),
      (continuousKernelGram r (-1) 1)⁻¹ 0 j *
        (continuousKernelGram r (-1) 1)⁻¹ 0 k *
          kernelSquareMomentIntegral (j.val + k.val) by rfl]
  apply (tendsto_finset_sum Finset.univ (fun j _ =>
    tendsto_finset_sum Finset.univ (fun k _ =>
      (((tendsto_pi_nhds.mp (tendsto_pi_nhds.mp
        (localDesignGram_inverse_tendsto r q t ht δ hδpos hδ hN) 0) j).mul
        (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp
          (localDesignGram_inverse_tendsto r q t ht δ hδpos hδ hN) 0) k)).mul
        (kernelSquareMomentGrid_tendsto q (j.val + k.val) t ht δ hδpos hδ hN))))).congr'
  filter_upwards [] with n
  rw [localPolynomialWeights_energy_identity]

end Hurst
