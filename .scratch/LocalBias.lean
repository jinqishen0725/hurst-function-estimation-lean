import Hurst.HolderRegularity
import Hurst.LocalWeights

noncomputable section
open Set
open scoped BigOperators
namespace Hurst

theorem scaled_taylorJet (r : ℕ) (f : ℝ → ℝ) (t y b : ℝ) (hb : b ≠ 0) :
    taylorJet r f t y = ∑ k : Fin (r + 1),
      (iteratedDeriv k.val f t * b ^ k.val / (k.val.factorial : ℝ)) * ((y - t) / b) ^ k.val := by
  unfold taylorJet
  apply Finset.sum_congr rfl
  intro k hk
  rw [div_pow]
  have hbp := pow_ne_zero k.val hb
  field_simp

theorem localPolynomial_bias_from_remainder (r n q : ℕ) (b t p B : ℝ) (f : ℝ → ℝ)
    (hn : 0 < n) (_hq : q ≤ n) (hb : 0 < b) (hp : 0 ≤ p) (hB : 0 ≤ B)
    (hdet : IsUnit (localDesignGram r n q b t).det)
    (hrem : ∀ y ∈ Ioo (0 : ℝ) 1, |f y - taylorJet r f t y| ≤ B * |y - t| ^ p) :
    |smooth (localPolynomialWeights r n q b t) (fun i => f (grid n i.val)) - f t| ≤
      (∑ i, |localPolynomialWeights r n q b t i|) * (B * b ^ p) := by
  let β : Fin (r + 1) → ℝ := fun k => iteratedDeriv k.val f t * b ^ k.val / (k.val.factorial : ℝ)
  have hβ : β 0 = f t := by simp [β]
  rw [← hβ]
  apply direct_local_bias_on_support (0 : Fin (r + 1))
    (fun i : Fin (n - q) => ((n : ℝ) * b)⁻¹ * localKernel ((grid n i.val - t) / b))
    (fun i k => ((grid n i.val - t) / b) ^ k.val) β (fun i => f (grid n i.val)) (B * b ^ p)
    (by positivity) hdet
  intro i hi
  have hz : |(grid n i.val - t) / b| < 1 := by
    by_contra hz
    rw [localKernel_zero _ (le_of_not_gt hz), mul_zero] at hi
    exact hi rfl
  have hd : |grid n i.val - t| ≤ b := by
    rw [abs_div, abs_of_pos hb] at hz
    exact ((div_lt_one hb).mp hz).le
  have hy := grid_mem n i.val hn (lt_of_lt_of_le i.isLt (Nat.sub_le n q))
  have he := scaled_taylorJet r f t (grid n i.val) b hb.ne'
  change |f (grid n i.val) - ∑ k : Fin (r + 1),
    (iteratedDeriv k.val f t * b ^ k.val / (k.val.factorial : ℝ)) * ((grid n i.val - t) / b) ^ k.val| ≤ _
  rw [← he]
  exact (hrem _ hy).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) hd hp) hB)

theorem hurstHolder_localPolynomial_bias_interior (p : ℝ) (hp : 1 ≤ p) (q : ℕ) :
    ∃ N₀ > 0, ∃ C > 0, ∀ M : ℝ, 0 ≤ M → ∀ f ∈ hurstHolderClass p M,
      ∀ n : ℕ, 0 < n → q ≤ n → ∀ b t : ℝ, 0 < b → b ≤ 1 / 2 →
      t ∈ Ioo (0 : ℝ) 1 → N₀ ≤ (n : ℝ) * b →
      |smooth (localPolynomialWeights (Nat.ceil p - 1) n q b t) (fun i => f (grid n i.val)) - f t| ≤
        C * (1 + M) * b ^ p := by
  obtain ⟨N₀, hN₀, D, hD, hstable⟩ := localPolynomialWeights_uniform_stability (Nat.ceil p - 1) q
  obtain ⟨B, hB, hrem⟩ := hurstHolder_estimator_degree_remainder p hp
  refine ⟨N₀, hN₀, D * B, by positivity, ?_⟩
  intro M hM f hf n hn hq b t hb hbhalf ht hN
  obtain ⟨hdet, _, hsum, _⟩ := hstable n hn hq b t hb hbhalf ⟨ht.1.le, ht.2.le⟩ hN
  have hh := localPolynomial_bias_from_remainder (Nat.ceil p - 1) n q b t p (B * (1 + M)) f
    hn hq hb (by linarith) (by positivity) hdet (hrem M hM f hf t ht)
  calc
    _ ≤ (∑ i, |localPolynomialWeights (Nat.ceil p - 1) n q b t i|) * (B * (1 + M) * b ^ p) := hh
    _ ≤ D * (B * (1 + M) * b ^ p) := mul_le_mul_of_nonneg_right hsum (by positivity)
    _ = _ := by ring

theorem localDesignGram_continuous (r n q : ℕ) (b : ℝ) :
    Continuous (localDesignGram r n q b) := by
  have hK : Continuous localKernel := localKernel_smooth.continuous
  unfold localDesignGram designGram
  fun_prop

theorem localPolynomialWeights_continuousAt (r n q : ℕ) (b t : ℝ)
    (hdet : IsUnit (localDesignGram r n q b t).det) (i : Fin (n - q)) :
    ContinuousAt (fun u => localPolynomialWeights r n q b u i) t := by
  have hK : Continuous localKernel := localKernel_smooth.continuous
  have hi : ContinuousAt (fun u => (localDesignGram r n q b u)⁻¹) t := by
    apply (continuousAt_matrix_inv (localDesignGram r n q b t) ?_).comp
      (localDesignGram_continuous r n q b).continuousAt
    convert! continuousAt_inv₀ (isUnit_iff_ne_zero.mp hdet) using 1
    exact funext (fun x : ℝ => Ring.inverse_eq_inv x)
  have hz : Continuous (fun u : ℝ => (grid n i.val - u) / b) := by fun_prop
  simp only [localPolynomialWeights_formula]
  apply ContinuousAt.mul ((continuous_const.mul (hK.comp hz)).continuousAt)
  apply tendsto_finsetSum
  intro k hk
  have hik : ContinuousAt (fun u => (localDesignGram r n q b u)⁻¹ 0 k) t :=
    (continuous_apply k).continuousAt.comp ((continuous_apply 0).continuousAt.comp hi)
  exact hik.mul (hz.pow k.val).continuousAt

theorem continuousOn_bound_of_interior (F : ℝ → ℝ) (B : ℝ)
    (hF : ContinuousOn F (Icc (0 : ℝ) 1)) (hB : ∀ t ∈ Ioo (0 : ℝ) 1, F t ≤ B) :
    ∀ t ∈ Icc (0 : ℝ) 1, F t ≤ B := by
  have hmap : MapsTo F (Ioo (0 : ℝ) 1) (Iic B) := hB
  have hc : ContinuousOn F (closure (Ioo (0 : ℝ) 1)) := by
    simpa only [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] using hF
  simpa only [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1), closure_Iic, MapsTo, mem_Iic] using hmap.closure_of_continuousOn hc

theorem hurstHolder_localPolynomial_bias_closed (p : ℝ) (hp : 1 ≤ p) (q : ℕ) :
    ∃ N₀ > 0, ∃ C > 0, ∀ M : ℝ, 0 ≤ M → ∀ f ∈ hurstHolderClass p M,
      ∀ g : ℝ → ℝ, Continuous g → EqOn f g (Ioo (0 : ℝ) 1) →
      ∀ n : ℕ, 0 < n → q ≤ n → ∀ b : ℝ, 0 < b → b ≤ 1 / 2 → N₀ ≤ (n : ℝ) * b →
      ∀ t ∈ Icc (0 : ℝ) 1,
      |smooth (localPolynomialWeights (Nat.ceil p - 1) n q b t) (fun i => f (grid n i.val)) - g t| ≤
        C * (1 + M) * b ^ p := by
  obtain ⟨N₁, hN₁, C, hC, hbias⟩ := hurstHolder_localPolynomial_bias_interior p hp q
  obtain ⟨N₂, hN₂, D, hD, hstable⟩ := localPolynomialWeights_uniform_stability (Nat.ceil p - 1) q
  refine ⟨max N₁ N₂, lt_of_lt_of_le hN₁ (le_max_left _ _), C, hC, ?_⟩
  intro M hM f hf g hg he n hn hq b hb hbhalf hN
  apply continuousOn_bound_of_interior
  · intro t ht
    have hdet := (hstable n hn hq b t hb hbhalf ht ((le_max_right _ _).trans hN)).1
    have hw : ∀ i, ContinuousAt (fun u => localPolynomialWeights (Nat.ceil p - 1) n q b u i) t :=
      localPolynomialWeights_continuousAt _ n q b t hdet
    apply ContinuousAt.continuousWithinAt
    unfold smooth
    fun_prop
  · intro t ht
    rw [← he ht]
    exact hbias M hM f hf n hn hq b t hb hbhalf ht ((le_max_left _ _).trans hN)

/-- The original class itself supplies the endpoint extension used by the bias bound. -/
theorem hurstHolder_localPolynomial_bias (p : ℝ) (hp : 1 ≤ p) (q : ℕ) :
    ∃ N₀ > 0, ∃ C > 0, ∀ M : ℝ, 0 ≤ M → ∀ f ∈ hurstHolderClass p M,
      ∃ g : ℝ → ℝ, Continuous g ∧ EqOn f g (Ioo (0 : ℝ) 1) ∧
      MapsTo g (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) ∧
      ∀ n : ℕ, 0 < n → q ≤ n → ∀ b : ℝ, 0 < b → b ≤ 1 / 2 → N₀ ≤ (n : ℝ) * b →
      ∀ t ∈ Icc (0 : ℝ) 1,
      |smooth (localPolynomialWeights (Nat.ceil p - 1) n q b t) (fun i => f (grid n i.val)) - g t| ≤
        C * (1 + M) * b ^ p := by
  obtain ⟨N₀, hN₀, C, hC, hbias⟩ := hurstHolder_localPolynomial_bias_closed p hp q
  obtain ⟨D, hD, hext⟩ := hurstHolder_uniform_lipschitz_extension p hp
  refine ⟨N₀, hN₀, C, hC, ?_⟩
  intro M hM f hf
  obtain ⟨g, he, hg, hmap⟩ := hext M hM f hf
  exact ⟨g, hg.continuous, he, hmap, hbias M hM f hf g hg.continuous he⟩

end Hurst
