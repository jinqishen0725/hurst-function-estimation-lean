import Hurst.HolderComposition
import Hurst.SmoothCompositeQuadratic

noncomputable section
open Set
namespace Hurst

/-- Full p-order local-polynomial bias for a smooth scalar transform, including both endpoints. -/
theorem hurstHolder_smooth_composite_local_bias (p a b M : ℝ) (phi : ℝ → ℝ) (q : ℕ)
    (hp : 2 ≤ p) (ha : 0 < a) (hb : b < 1) (hM : 0 ≤ M)
    (hphi : ContDiffOn ℝ (⊤ : ℕ∞) phi (Ioo (0 : ℝ) 1)) :
    ∃ N₀ > 0, ∃ C ≥ 0, ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) → ∀ g : ℝ → ℝ, Continuous g → EqOn f g (Ioo (0 : ℝ) 1) →
      ∀ n : ℕ, 0 < n → q ≤ n → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → N₀ ≤ (n : ℝ) * δ →
      ∀ t ∈ Icc (0 : ℝ) 1,
      |smooth (localPolynomialWeights (Nat.ceil p - 1) n q δ t) (fun i => phi (f (grid n i.val))) - phi (g t)| ≤ C * δ ^ p := by
  obtain ⟨B, hB, hrem⟩ := hurstHolder_smooth_composite_remainder p a b M phi hp ha hb hM hphi
  obtain ⟨N₀, hN₀, D, hD, hstable⟩ := localPolynomialWeights_uniform_stability (Nat.ceil p - 1) q
  refine ⟨N₀, hN₀, D * B, by positivity, ?_⟩
  intro f hf hF g hg he n hn hq δ hδ hδhalf hN
  have hgmap := continuous_extension_fixed_range f g a b hg he hF
  have hpg : ContinuousOn (phi ∘ g) (Icc (0 : ℝ) 1) :=
    hphi.continuousOn.comp hg.continuousOn (fun t ht => ⟨ha.trans_le (hgmap ht).1, (hgmap ht).2.trans_lt hb⟩)
  apply continuousOn_bound_of_interior
  · intro t ht
    have hdet := (hstable n hn hq δ t hδ hδhalf ht hN).1
    have hw : ∀ i, ContinuousAt (fun u => localPolynomialWeights (Nat.ceil p - 1) n q δ u i) t :=
      localPolynomialWeights_continuousAt (Nat.ceil p - 1) n q δ t hdet
    have hs : ContinuousAt (fun u => smooth (localPolynomialWeights (Nat.ceil p - 1) n q δ u) (fun i => phi (f (grid n i.val)))) t := by
      unfold smooth
      fun_prop
    exact (hs.continuousWithinAt.sub (hpg t ht)).abs
  · intro t ht
    obtain ⟨hdet, _, hsum, _⟩ := hstable n hn hq δ t hδ hδhalf ⟨ht.1.le, ht.2.le⟩ hN
    have hh := localPolynomial_bias_from_remainder (Nat.ceil p - 1) n q δ t p B (phi ∘ f) hn hq hδ (by linarith) hB hdet
      (hrem f hf hF t ht)
    simp only [Function.comp_apply, he ht] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_right hsum (by positivity : 0 ≤ B * δ ^ p)).trans_eq (by ring))

end Hurst
