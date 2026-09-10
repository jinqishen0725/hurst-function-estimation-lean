import Hurst.SmoothTaylor
import Hurst.HolderSecond
import Hurst.LocalBias

noncomputable section
open Set
namespace Hurst

/-- Direct Taylor composition with a uniform quadratic remainder. -/
theorem hurstHolder_smooth_composite_quadratic (p a b M : ℝ) (phi : ℝ → ℝ)
    (hp : 2 ≤ p) (ha : 0 < a) (hb : b < 1) (hM : 0 ≤ M)
    (hphi : ContDiffOn ℝ (⊤ : ℕ∞) phi (Ioo (0 : ℝ) 1)) :
    ∃ C ≥ 0, ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) → ∀ x ∈ Ioo (0 : ℝ) 1, ∀ y ∈ Ioo (0 : ℝ) 1,
      |(phi ∘ f) y - taylorJet 1 (phi ∘ f) x y| ≤ C * |y - x| ^ 2 := by
  obtain ⟨R, hR, hr⟩ := smooth_uniform_quadratic_remainder phi hphi a b ha hb
  obtain ⟨D, hD, hd⟩ := smooth_uniform_iteratedDeriv_bound phi hphi a b ha hb 1
  obtain ⟨L, hL, hLip⟩ := hurstHolder_uniform_lower_derivative_lipschitz p (by linarith)
  obtain ⟨B, hB, hfrem⟩ := hurstHolder_quadratic_remainder p hp
  refine ⟨R * (L * (1 + M)) ^ 2 + D * (B * (1 + M)), by positivity, ?_⟩
  intro f hf hF x hx y hy
  have hk : 0 < Nat.floor p := by have := hurstHolder_floor_pos p (by linarith); omega
  have hdf : DifferentiableAt ℝ f x := by simpa only [iteratedDeriv_zero] using hf.2.1 0 hk x hx
  have hdp : DifferentiableAt ℝ phi (f x) := by
    simpa only [iteratedDeriv_zero] using smooth_differentiable_iteratedDeriv phi hphi 0 (f x) (hf.1 hx)
  have hderiv : deriv (phi ∘ f) x = deriv phi (f x) * deriv f x := (hdp.hasDerivAt.comp x hdf.hasDerivAt).deriv
  have hpR := hr (f x) (f y) (hF hx) (hF hy)
  have hfR := hfrem M hM f hf x hx y hy
  have hLip' := hLip M hM f hf 0 hk x hx y hy
  simp only [iteratedDeriv_zero] at hLip'
  have hpd : |deriv phi (f x)| ≤ D := by simpa only [iteratedDeriv_one] using hd (f x) (hF hx)
  have he : (phi ∘ f) y - taylorJet 1 (phi ∘ f) x y =
      (phi (f y) - phi (f x) - (f y - f x) * deriv phi (f x)) +
      deriv phi (f x) * (f y - f x - (y - x) * deriv f x) := by
    simp only [taylorJet, Fin.sum_univ_succ, iteratedDeriv_zero, iteratedDeriv_one]
    norm_num
    rw [hderiv]
    ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul]
  have hsq := pow_le_pow_left₀ (abs_nonneg _) hLip' 2
  have h1 := hpR.trans (mul_le_mul_of_nonneg_left hsq hR)
  have h2 := mul_le_mul hpd hfR (abs_nonneg _) hD
  exact (add_le_add h1 h2).trans_eq (by ring)

theorem continuous_extension_fixed_range (f g : ℝ → ℝ) (a b : ℝ) (hg : Continuous g)
    (he : EqOn f g (Ioo (0 : ℝ) 1)) (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b)) :
    MapsTo g (Icc (0 : ℝ) 1) (Icc a b) := by
  have hm : MapsTo g (Ioo (0 : ℝ) 1) (Icc a b) := by intro x hx; rw [← he hx]; exact hF hx
  simpa only [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1), closure_Icc] using hm.closure hg

/-- Full-interval linear local-polynomial bias for a smooth scalar transform. -/
theorem hurstHolder_smooth_composite_linear_bias (p a b M : ℝ) (phi : ℝ → ℝ) (q : ℕ)
    (hp : 2 ≤ p) (ha : 0 < a) (hb : b < 1) (hM : 0 ≤ M)
    (hphi : ContDiffOn ℝ (⊤ : ℕ∞) phi (Ioo (0 : ℝ) 1)) :
    ∃ N₀ > 0, ∃ C ≥ 0, ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) → ∀ g : ℝ → ℝ, Continuous g → EqOn f g (Ioo (0 : ℝ) 1) →
      ∀ n : ℕ, 0 < n → q ≤ n → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → N₀ ≤ (n : ℝ) * δ →
      ∀ t ∈ Icc (0 : ℝ) 1,
      |smooth (localPolynomialWeights 1 n q δ t) (fun i => phi (f (grid n i.val))) - phi (g t)| ≤ C * δ ^ 2 := by
  obtain ⟨B, hB, hrem⟩ := hurstHolder_smooth_composite_quadratic p a b M phi hp ha hb hM hphi
  obtain ⟨N₀, hN₀, D, hD, hstable⟩ := localPolynomialWeights_uniform_stability 1 q
  refine ⟨N₀, hN₀, D * B, by positivity, ?_⟩
  intro f hf hF g hg he n hn hq δ hδ hδhalf hN
  have hgmap := continuous_extension_fixed_range f g a b hg he hF
  have hpg : ContinuousOn (phi ∘ g) (Icc (0 : ℝ) 1) :=
    hphi.continuousOn.comp hg.continuousOn (fun t ht => ⟨ha.trans_le (hgmap ht).1, (hgmap ht).2.trans_lt hb⟩)
  apply continuousOn_bound_of_interior
  · intro t ht
    have hdet := (hstable n hn hq δ t hδ hδhalf ht hN).1
    have hw : ∀ i, ContinuousAt (fun u => localPolynomialWeights 1 n q δ u i) t :=
      localPolynomialWeights_continuousAt 1 n q δ t hdet
    have hs : ContinuousAt (fun u => smooth (localPolynomialWeights 1 n q δ u) (fun i => phi (f (grid n i.val)))) t := by
      unfold smooth
      fun_prop
    exact (hs.continuousWithinAt.sub (hpg t ht)).abs
  · intro t ht
    obtain ⟨hdet, _, hsum, _⟩ := hstable n hn hq δ t hδ hδhalf ⟨ht.1.le, ht.2.le⟩ hN
    have hh := localPolynomial_bias_from_remainder 1 n q δ t 2 B (phi ∘ f) hn hq hδ (by norm_num) hB hdet
      (by intro y hy; simpa only [Real.rpow_two] using hrem f hf hF t ht y hy)
    simp only [Real.rpow_two, Function.comp_apply, he ht] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_right hsum (by positivity : 0 ≤ B * δ ^ 2)).trans_eq (by ring))

end Hurst
