import Hurst.FullChainGeneralSigned
import Hurst.OptimalActiveRowDensity

/-!
# Blocker-3 audit: the unnormalized `hE2` premise is unsatisfiable

The old `FullChainEndpoint`/P5 chain carried

`hE2 : ∃ C ≥ 0, ∀ᶠ n in atTop, ∑ i j ρ n i j ^ 2 ≤ C`,

with `ρ n i j = featureCorrelation (actualQ1Obs …) (actualQ1Coeff … i)
(actualQ1Coeff … j)`.  Under the same chain's `hane` (nonzero coefficient
rows) every DIAGONAL entry equals `1`, so the double sum dominates the active
cardinality, which tends to infinity by window geometry.  The premise is
therefore False in the actual model for every `C` — this file records that
contradiction as a Lean theorem, in the audit style of
`verification/Session3PremiseAudit.lean` (which recorded the blocker-1/2
refutations).  The repaired chain (`Hurst.FullChainGeneralSigned`) uses the
NORMALIZED energy `S ^ (2ψ - 2) ∑ i j ρ ^ 2 ≤ C` instead, which is eventually
bounded by `hurstHolder_q1_actual_normalized_energy_eventually_bounded`.
-/

open Set Filter Topology
open scoped RealInnerProductSpace

namespace Hurst

variable {p M : ℝ}

/-- The correlation of a nondegenerate row with itself is exactly `1`. -/
theorem featureCorrelation_self {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (a : EuclideanSpace ℝ ι)
    (ha : ∑ i, a i • v i ≠ 0) :
    featureCorrelation v a a = 1 := by
  unfold featureCorrelation
  rw [real_inner_self_eq_norm_sq,
    show (‖∑ i, a i • v i‖ * ‖∑ i, a i • v i‖) = ‖∑ i, a i • v i‖ ^ 2 by ring,
    div_self (pow_ne_zero 2 (norm_ne_zero_iff.mpr ha))]

/-- **The blocker-3 contradiction.**  `hane` together with the unnormalized
bounded-total-correlation-energy premise is False at every admissible
bandwidth: the diagonal alone forces the double sum past every constant,
because the active cardinality tends to infinity. -/
theorem session4_unnormalized_hE2_impossible
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M) (r : ℕ) (t : ℝ)
    (δ : ℕ → ℝ)
    (hδpos : ∀ᶠ n : ℕ in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (ht : t ∈ Ioo (0 : ℝ) 1)
    (hane : ∀ (n : ℕ) (k : Fin (localWeightActiveSet n 1 (δ n) t).card),
      ∑ i, actualQ1Coeff n (δ n) t k i •
        actualQ1Obs f n (midpointSampleHurst f hf.1 n) i ≠ 0)
    (hE2 : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        ∑ j : Fin (localWeightActiveSet n 1 (δ n) t).card,
          (featureCorrelation (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
            (actualQ1Coeff n (δ n) t i) (actualQ1Coeff n (δ n) t j)) ^ 2 ≤ C) :
    False := by
  obtain ⟨C, hC0, hC⟩ := hE2
  have hcard := localWeightActiveSet_card_tendsto_atTop 1 t ht δ hδpos hδ0 hN
  have hcardR : Tendsto (fun n : ℕ =>
      ((localWeightActiveSet n 1 (δ n) t).card : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hcard
  have hbig : ∀ᶠ n : ℕ in atTop,
      (C + 1 : ℝ) < ((localWeightActiveSet n 1 (δ n) t).card : ℝ) :=
    hcardR.eventually_gt_atTop (C + 1)
  obtain ⟨n, hn⟩ := (hC.and hbig).exists
  obtain ⟨hCn, hbn⟩ := hn
  -- every diagonal entry equals one, so each inner row sum dominates 1
  have hone : ∀ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
      featureCorrelation (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
        (actualQ1Coeff n (δ n) t i) (actualQ1Coeff n (δ n) t i) = 1 :=
    fun i => featureCorrelation_self (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
      (actualQ1Coeff n (δ n) t i) (hane n i)
  have hinner : ∀ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
      (1 : ℝ) ≤ ∑ j : Fin (localWeightActiveSet n 1 (δ n) t).card,
        (featureCorrelation (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
          (actualQ1Coeff n (δ n) t i) (actualQ1Coeff n (δ n) t j)) ^ 2 := by
    intro i
    have h := Finset.single_le_sum
      (f := fun j : Fin (localWeightActiveSet n 1 (δ n) t).card =>
        (featureCorrelation (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
          (actualQ1Coeff n (δ n) t i) (actualQ1Coeff n (δ n) t j)) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    rw [hone i, one_pow] at h
    exact h
  have hcardsum : ((localWeightActiveSet n 1 (δ n) t).card : ℝ) ≤
      ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        ∑ j : Fin (localWeightActiveSet n 1 (δ n) t).card,
          (featureCorrelation (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
            (actualQ1Coeff n (δ n) t i) (actualQ1Coeff n (δ n) t j)) ^ 2 := by
    calc ((localWeightActiveSet n 1 (δ n) t).card : ℝ)
        = ∑ _i : Fin (localWeightActiveSet n 1 (δ n) t).card, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => hinner i
  linarith

end Hurst

#print axioms Hurst.featureCorrelation_self
#print axioms Hurst.session4_unnormalized_hE2_impossible
