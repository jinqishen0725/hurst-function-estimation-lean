import Hurst.PaddedVariance

noncomputable section
open Filter Metric
open scoped Topology
namespace Hurst

theorem targetCoordinate_padding_dist_le
    {m d : ℕ} (hm : 0 < m) (i : Fin m) :
    dist (((i.val : ℝ) + 1) / m)
        ((((Fin.castAdd d i).val : ℝ) + 1) / (m + d)) ≤
      (d : ℝ) / m := by
  rw [Real.dist_eq]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hrR : (0 : ℝ) < m + d := by positivity
  have hi : ((i.val : ℝ) + 1) ≤ m := by exact_mod_cast (Nat.succ_le_iff.mpr i.isLt)
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  rw [Fin.val_castAdd]
  rw [abs_of_nonneg]
  · rw [le_div_iff₀ hmR]
    have hfrac : (((i.val : ℝ) + 1) / m -
        ((i.val : ℝ) + 1) / (m + d)) * m =
        ((i.val : ℝ) + 1) * (d : ℝ) / (m + d) := by
      field_simp
      ring
    rw [hfrac]
    apply (div_le_iff₀ hrR).2
    nlinarith
  · apply sub_nonneg.mpr
    apply div_le_div_of_nonneg_left (by positivity) hmR
    norm_num only [Nat.cast_add]
    linarith

/-- Uniform profile convergence survives right padding when the hole fraction
vanishes.  Filler coefficients are exactly the profile; target coordinates
move by at most `d/m`. -/
theorem paddedCoefficientRow_uniform_tendsto
    (m d : ℕ → ℕ) (c : ∀ n, Fin (m n) → ℝ) (g : ℝ → ℝ)
    (hm : ∀ᶠ n in atTop, 0 < m n)
    (hdm : Tendsto (fun n : ℕ => (d n : ℝ) / m n) atTop (𝓝 0))
    (hg : UniformContinuous g)
    (hc : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ i : Fin (m n),
      |c n i - g (((i.val : ℝ) + 1) / m n)| ≤ ε) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ i : Fin (m n + d n),
      |paddedCoefficientRow (c n) g (d n) i -
        g (((i.val : ℝ) + 1) / (m n + d n))| ≤ ε := by
  intro ε hε
  obtain ⟨η, hη, hUC⟩ := Metric.uniformContinuous_iff.mp hg (ε / 2) (half_pos hε)
  have hratio : ∀ᶠ n : ℕ in atTop, (d n : ℝ) / m n < η :=
    hdm.eventually (Iio_mem_nhds hη)
  have htarget := hc (ε / 2) (half_pos hε)
  filter_upwards [hm, hratio, htarget] with n hmn hdn hcn
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    rw [paddedCoefficientRow_castAdd]
    have hdist : dist (((j.val : ℝ) + 1) / m n)
        ((((Fin.castAdd (d n) j).val : ℝ) + 1) / (m n + d n)) < η :=
      (targetCoordinate_padding_dist_le hmn j).trans_lt hdn
    have hgclose := hUC hdist
    rw [Real.dist_eq] at hgclose
    calc
      |c n j - g ((((Fin.castAdd (d n) j).val : ℝ) + 1) / (m n + d n))| ≤
          |c n j - g (((j.val : ℝ) + 1) / m n)| +
          |g (((j.val : ℝ) + 1) / m n) -
            g ((((Fin.castAdd (d n) j).val : ℝ) + 1) / (m n + d n))| := by
              simpa only [sub_add_sub_cancel] using abs_add_le
                (c n j - g (((j.val : ℝ) + 1) / m n))
                (g (((j.val : ℝ) + 1) / m n) -
                  g ((((Fin.castAdd (d n) j).val : ℝ) + 1) / (m n + d n)))
      _ ≤ ε / 2 + ε / 2 := add_le_add (hcn j) hgclose.le
      _ = ε := by ring
  · intro j
    rw [paddedCoefficientRow_natAdd]
    rw [Fin.val_natAdd]
    simpa using hε.le

end Hurst
