import Hurst.InteriorKernelMoments
import Hurst.LocalWeights

noncomputable section
open Set MeasureTheory Filter
open scoped Topology Matrix.Norms.Elementwise
namespace Hurst

theorem localDesignGram_tendsto (r q : ℕ) (t : ℝ) (ht : t∈Ioo (0:ℝ) 1)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop,0<δ n)
    (hδ : Tendsto δ atTop (𝓝 0)) (hN : Tendsto (fun n : ℕ => (n:ℝ)*δ n) atTop atTop) :
    Tendsto (fun n => localDesignGram r n q (δ n) t) atTop (𝓝 (continuousKernelGram r (-1) 1)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  simpa only [localDesignGram_moment,continuousKernelGram_moment,kernelMomentGrid,kernelMomentIntegral]
    using kernelMomentGrid_tendsto q (i.val+j.val) t ht δ hδpos hδ hN

theorem localDesignGram_inverse_tendsto (r q : ℕ) (t : ℝ) (ht : t∈Ioo (0:ℝ) 1)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop,0<δ n)
    (hδ : Tendsto δ atTop (𝓝 0)) (hN : Tendsto (fun n : ℕ => (n:ℝ)*δ n) atTop atTop) :
    Tendsto (fun n => (localDesignGram r n q (δ n) t)⁻¹) atTop (𝓝 (continuousKernelGram r (-1) 1)⁻¹) := by
  have hd := (continuousKernelGram_posDef r (-1) 1 le_rfl le_rfl (by norm_num)).det_pos.ne'
  have hi : ContinuousAt (Inv.inv : Matrix (Fin (r+1)) (Fin (r+1)) ℝ → Matrix (Fin (r+1)) (Fin (r+1)) ℝ)
      (continuousKernelGram r (-1) 1) := by
    apply continuousAt_matrix_inv _ _
    convert continuousAt_inv₀ hd using 1
    exact funext (fun x : ℝ => Ring.inverse_eq_inv x)
  exact hi.tendsto.comp (localDesignGram_tendsto r q t ht δ hδpos hδ hN)

def equivalentKernelMoment (r k : ℕ) : ℝ :=
  ∑ j : Fin (r+1),(continuousKernelGram r (-1) 1)⁻¹ 0 j * kernelMomentIntegral (j.val+k)

theorem localPolynomialWeights_arbitrary_moment (r n q k : ℕ) (δ t : ℝ) :
    (∑ i,localPolynomialWeights r n q δ t i * ((grid n i.val-t)/δ)^k)=
      ∑ j : Fin (r+1),(localDesignGram r n q δ t)⁻¹ 0 j * kernelMomentGrid n q δ t (j.val+k) := by
  simp only [localPolynomialWeights_formula,kernelMomentGrid,kernelMomentFunction,pow_add]
  simp_rw [Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem localPolynomialWeights_moment_tendsto (r q k : ℕ) (t : ℝ) (ht : t∈Ioo (0:ℝ) 1)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop,0<δ n)
    (hδ : Tendsto δ atTop (𝓝 0)) (hN : Tendsto (fun n : ℕ => (n:ℝ)*δ n) atTop atTop) :
    Tendsto (fun n => ∑ i,localPolynomialWeights r n q (δ n) t i*((grid n i.val-t)/δ n)^k)
      atTop (𝓝 (equivalentKernelMoment r k)) := by
  simp only [localPolynomialWeights_arbitrary_moment,equivalentKernelMoment]
  apply tendsto_finset_sum
  intro j _
  have hi := (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp
    (localDesignGram_inverse_tendsto r q t ht δ hδpos hδ hN) 0) j)
  exact hi.mul (kernelMomentGrid_tendsto q (j.val+k) t ht δ hδpos hδ hN)

end Hurst
