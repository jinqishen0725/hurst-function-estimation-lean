import Hurst.EquivalentKernel

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace Hurst

/-- The rescaled discrete local-polynomial weights converge uniformly, over
all design indices, to the equivalent-kernel profile.  Indices outside the
kernel support cause no boundary problem because both sides vanish there. -/
theorem localPolynomialWeights_scaled_uniform_tendsto
    (r q : ℕ) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ i : Fin (n - q),
      |((n : ℝ) * δ n) * localPolynomialWeights r n q (δ n) t i -
        equivalentKernel r ((grid n i.val - t) / δ n)| ≤ ε := by
  obtain ⟨B, hB, hkernel⟩ := kernelMomentFunction_bounded 0
  let G := continuousKernelGram r (-1) 1
  let e : ℕ → ℝ := fun n => ∑ j : Fin (r + 1),
    |(localDesignGram r n q (δ n) t)⁻¹ 0 j - G⁻¹ 0 j|
  have he : Tendsto e atTop (𝓝 0) := by
    have hi := localDesignGram_inverse_tendsto r q t ht δ hδpos hδ hN
    dsimp [e]
    have hj : ∀ j : Fin (r + 1), Tendsto
        (fun n => |(localDesignGram r n q (δ n) t)⁻¹ 0 j - G⁻¹ 0 j|)
        atTop (𝓝 0) := by
      intro j
      dsimp [G]
      convert ((tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hi 0) j).sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => G⁻¹ 0 j) atTop (𝓝 (G⁻¹ 0 j)))).abs using 1 <;>
        simp [G]
    simpa only [Finset.sum_const_zero] using
      tendsto_finset_sum Finset.univ (fun j _ => hj j)
  intro ε hε
  have hden : 0 < B + 1 := by linarith
  have hevent : ∀ᶠ n : ℕ in atTop, e n < ε / (B + 1) :=
    he.eventually (Iio_mem_nhds (div_pos hε hden))
  filter_upwards [hδpos, eventually_ge_atTop (q + 1), hevent] with n hnδ hnq herr
  intro i
  have hn0 : 0 < n := by omega
  have hscale : ((n : ℝ) * δ n) * (((n : ℝ) * δ n)⁻¹) = 1 := by
    exact mul_inv_cancel₀ (mul_ne_zero (by exact_mod_cast hn0.ne') hnδ.ne')
  let x := (grid n i.val - t) / δ n
  by_cases hx : 1 ≤ |x|
  · have hk : localKernel x = 0 := localKernel_zero x hx
    simp only [localPolynomialWeights_formula, equivalentKernel, x, hk,
      mul_zero, zero_mul, sub_self, abs_zero]
    exact hε.le
  · have hx1 : |x| ≤ 1 := (lt_of_not_ge hx).le
    have hkB : localKernel x ≤ B := by
      have hh := hkernel x
      simpa only [kernelMomentFunction, pow_zero, mul_one,
        abs_of_nonneg (localKernel_nonneg x)] using hh
    have hsum :
        |∑ j : Fin (r + 1),
          ((localDesignGram r n q (δ n) t)⁻¹ 0 j - G⁻¹ 0 j) * x ^ j.val| ≤ e n := by
      calc
        _ ≤ ∑ j : Fin (r + 1),
            |((localDesignGram r n q (δ n) t)⁻¹ 0 j - G⁻¹ 0 j) * x ^ j.val| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j : Fin (r + 1),
            |(localDesignGram r n q (δ n) t)⁻¹ 0 j - G⁻¹ 0 j| := by
          apply Finset.sum_le_sum
          intro j _
          rw [abs_mul, abs_pow]
          exact mul_le_of_le_one_right (abs_nonneg _)
            (pow_le_one₀ (abs_nonneg _) hx1)
        _ = e n := rfl
    rw [localPolynomialWeights_formula, equivalentKernel]
    have hid :
        ((n : ℝ) * δ n) *
            (((n : ℝ) * δ n)⁻¹ * localKernel x *
              ∑ j : Fin (r + 1),
                (localDesignGram r n q (δ n) t)⁻¹ 0 j * x ^ j.val) -
          localKernel x * ∑ j : Fin (r + 1), G⁻¹ 0 j * x ^ j.val =
        localKernel x * ∑ j : Fin (r + 1),
          ((localDesignGram r n q (δ n) t)⁻¹ 0 j - G⁻¹ 0 j) * x ^ j.val := by
      calc
        _ = (((n : ℝ) * δ n) * ((n : ℝ) * δ n)⁻¹) * localKernel x *
              (∑ j : Fin (r + 1),
                (localDesignGram r n q (δ n) t)⁻¹ 0 j * x ^ j.val) -
              localKernel x * ∑ j : Fin (r + 1), G⁻¹ 0 j * x ^ j.val := by ring
        _ = localKernel x *
              (∑ j : Fin (r + 1),
                (localDesignGram r n q (δ n) t)⁻¹ 0 j * x ^ j.val) -
              localKernel x * ∑ j : Fin (r + 1), G⁻¹ 0 j * x ^ j.val := by rw [hscale]; ring
        _ = localKernel x *
              ((∑ j : Fin (r + 1),
                (localDesignGram r n q (δ n) t)⁻¹ 0 j * x ^ j.val) -
              ∑ j : Fin (r + 1), G⁻¹ 0 j * x ^ j.val) := by ring
        _ = _ := by
          rw [← Finset.sum_sub_distrib]
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          ring
    change |((n : ℝ) * δ n) *
        (((n : ℝ) * δ n)⁻¹ * localKernel x *
          ∑ j : Fin (r + 1),
            (localDesignGram r n q (δ n) t)⁻¹ 0 j * x ^ j.val) -
        localKernel x * ∑ j : Fin (r + 1), G⁻¹ 0 j * x ^ j.val| ≤ ε
    rw [hid, abs_mul, abs_of_nonneg (localKernel_nonneg x)]
    exact (calc
      localKernel x *
          |∑ j : Fin (r + 1),
            ((localDesignGram r n q (δ n) t)⁻¹ 0 j - G⁻¹ 0 j) * x ^ j.val|
          ≤ B * e n := mul_le_mul hkB hsum (abs_nonneg _) hB
      _ ≤ B * (ε / (B + 1)) :=
        mul_le_mul_of_nonneg_left herr.le hB
      _ < ε := by
        rw [show B * (ε / (B + 1)) = B * ε / (B + 1) by ring]
        exact (div_lt_iff₀ hden).2 (by nlinarith)
      ).le

end Hurst
