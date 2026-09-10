import Hurst.WeightedEvenMomentBound
import Hurst.FeatureStandardGaussianArray
import Hurst.FeatureGroupedMoment

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace Hurst

theorem featureGaussian_colorClass_evenMoment_bound
    (hBS : BardetSurgailisLemmaOneScalar) (k : ℕ) (hk : 1 ≤ k)
    {ι κ E : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (w : κ → ℝ) (a : κ → EuclideanSpace ℝ ι)
    (ha0 : ∀ j, ∑ i, a j i • v i ≠ 0)
    {d : ℕ} (color : κ → Fin d) (c : Fin d)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε : ε < 1 / (2 * k : ℝ))
    (hsmall : ∀ i j, i ≠ j → color i = c → color j = c →
      |featureCorrelation v (a i) (a j)| ≤ ε)
    (Q : ℝ) (hQ : 0 ≤ Q)
    (hrow : ∀ i : {j : κ // color j = c},
      ∑ j ∈ Finset.univ.erase i,
        |featureCorrelation v (a i.val) (a j.val)| ^ 2 ≤ Q)
    (W : ℝ) (hW0 : 0 ≤ W) (hw : ∀ j, |w j| ≤ W) :
    ∃ D > 0,
      (∫ x, |colorClassSum color
        (fun j => w j * centeredGaussianLog
          (standardizedFeatureObservation v (a j) x)) c| ^ (2 * k)
        ∂featureGaussian v) ≤
        D * W ^ (2 * k) * (Fintype.card κ : ℝ) ^ k := by
  let κc := {j : κ // color j = c}
  by_cases hc : Nonempty κc
  · letI : Nonempty κc := hc
    let ac : κc → EuclideanSpace ℝ ι := fun j => a j.val
    let X : κc → EuclideanSpace ℝ ι → ℝ :=
      fun j => standardizedFeatureObservation v (ac j)
    have hgauss : HasGaussianLaw (fun x => fun j => X j x) (featureGaussian v) :=
      standardizedFeatureObservation_joint v ac
    have hstd : ∀ j, MeasurePreserving (X j) (featureGaussian v) (gaussianReal 0 1) :=
      fun j => standardizedFeatureObservation_law v (ac j) (ha0 j.val)
    have hBS' : BardetSurgailisLemmaOneScalarFor (featureGaussian v) X :=
      hBS (featureGaussian v) X
    have hcorr : ∀ i j : κc, i ≠ j →
        |cov[X i, X j; featureGaussian v]| ≤ ε := by
      intro i j hij
      rw [show cov[X i, X j; featureGaussian v] =
          featureCorrelation v (a i.val) (a j.val) by
        exact standardizedFeatureObservation_covariance v (a i.val) (a j.val)]
      exact hsmall i.val j.val (fun h => hij (Subtype.ext h)) i.property j.property
    have hrow' : ∀ i : κc,
        ∑ j ∈ Finset.univ.erase i, |cov[X i, X j; featureGaussian v]| ^ 2 ≤ Q := by
      intro i
      simpa only [X, ac, standardizedFeatureObservation_covariance] using hrow i
    obtain ⟨D, hD, hb⟩ := bardetSurgailis_weighted_evenMoment_bound k hk
      (featureGaussian v) X hBS' hgauss hstd ε hε0 hε hcorr Q hQ hrow'
      (fun j : κc => w j.val) W hW0 (fun j => hw j.val)
    refine ⟨D, hD, ?_⟩
    have hcard : (Fintype.card κc : ℝ) ^ k ≤ (Fintype.card κ : ℝ) ^ k := by
      exact pow_le_pow_left₀ (by positivity)
        (by exact_mod_cast Fintype.card_subtype_le (fun j : κ => color j = c)) _
    let Y : κ → EuclideanSpace ℝ ι → ℝ := fun j x =>
      w j * centeredGaussianLog (standardizedFeatureObservation v (a j) x)
    have hrewrite : ∀ x, colorClassSum color (fun j => Y j x) c =
        ∑ j : κc, Y j.val x := by
      intro x
      exact Finset.sum_subtype (Finset.univ.filter (fun j : κ => color j = c))
        (by simp) (fun j => Y j x)
    change (∫ x, |colorClassSum color (fun j => Y j x) c| ^ (2 * k)
      ∂featureGaussian v) ≤ _
    simp_rw [hrewrite]
    change (∫ x, |∑ j : κc, w j.val * centeredGaussianLog
      (standardizedFeatureObservation v (a j.val) x)| ^ (2 * k) ∂featureGaussian v) ≤ _
    exact hb.trans (mul_le_mul_of_nonneg_left hcard
      (mul_nonneg hD.le (pow_nonneg hW0 _)))
  · refine ⟨1, by norm_num, ?_⟩
    have hempty : IsEmpty κc := not_nonempty_iff.mp hc
    letI : IsEmpty κc := hempty
    have hz : ∀ x, colorClassSum color
        (fun j => w j * centeredGaussianLog
          (standardizedFeatureObservation v (a j) x)) c = 0 := by
      intro x
      rw [show colorClassSum color
          (fun j => w j * centeredGaussianLog
            (standardizedFeatureObservation v (a j) x)) c =
          ∑ j : κc, w j.val * centeredGaussianLog
            (standardizedFeatureObservation v (a j.val) x) by
        exact Finset.sum_subtype (Finset.univ.filter (fun j : κ => color j = c))
          (by simp) _]
      exact Finset.sum_of_isEmpty _
    simp_rw [hz]
    simp only [abs_zero, zero_pow (by omega : 2 * k ≠ 0), integral_zero]
    positivity

end Hurst
