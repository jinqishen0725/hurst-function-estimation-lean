import Hurst.UniformWeightedEvenMoment
import Hurst.DecayColoring
import Hurst.RestrictedCorrelationRow
import Hurst.FeatureGroupedMoment
import Hurst.FeatureStandardGaussianArray

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace Topology
namespace Hurst

theorem gaussianLogStatistic_uniform_evenMoment_of_coloring
    (hBS : BardetSurgailisLemmaOneScalar) (k : ℕ) (hk : 1 ≤ k)
    {d : ℕ} (hd : 0 < d) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε : ε < 1 / (2 * k : ℝ)) (Q : ℝ) (hQ : 0 ≤ Q) :
    ∃ D > 0, ∀ {ι κ E : Type}, ∀ [Fintype ι] [DecidableEq ι]
      [Fintype κ] [Nonempty κ] [DecidableEq κ]
      [NormedAddCommGroup E] [InnerProductSpace ℝ E],
      ∀ (v : ι → E) (w : κ → ℝ) (a : κ → EuclideanSpace ℝ ι),
      (∀ j, ∑ i, a j i • v i ≠ 0) → ∀ (color : κ → Fin d),
      (∀ i j, i ≠ j → color i = color j →
        |featureCorrelation v (a i) (a j)| ≤ ε) →
      (∀ c, ∀ i : {j : κ // color j = c},
        ∑ j ∈ Finset.univ.erase i,
          |featureCorrelation v (a i.val) (a j.val)| ^ 2 ≤ Q) →
      ∀ (W : ℝ), 0 ≤ W → (∀ j, |w j| ≤ W) →
      (∫ x, |gaussianLogStatistic w a x -
          (∫ y, gaussianLogStatistic w a y ∂featureGaussian v)| ^ (2 * k)
        ∂featureGaussian v) ≤
        D * W ^ (2 * k) * (Fintype.card κ : ℝ) ^ k := by
  obtain ⟨D0, hD0, hmom⟩ :=
    bardetSurgailis_uniform_weighted_evenMoment_bound hBS k hk ε hε0 hε Q hQ
  let D := (d : ℝ) ^ (2 * k) * D0
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro ι κ E _ _ _ _ _ _ _ v w a ha0 color hsmall hrow W hW0 hw
  let B := D0 * W ^ (2 * k) * (Fintype.card κ : ℝ) ^ k
  have hgroup : ∀ c,
      (∫ x, |colorClassSum color
        (fun j => w j * centeredGaussianLog
          (standardizedFeatureObservation v (a j) x)) c| ^ (2 * k)
        ∂featureGaussian v) ≤ B := by
    intro c
    let κc := {j : κ // color j = c}
    by_cases hc : Nonempty κc
    · letI : Nonempty κc := hc
      let ac : κc → EuclideanSpace ℝ ι := fun j => a j.val
      let X : κc → EuclideanSpace ℝ ι → ℝ :=
        fun j => standardizedFeatureObservation v (ac j)
      have hgauss := standardizedFeatureObservation_joint v ac
      have hstd : ∀ j, MeasurePreserving (X j) (featureGaussian v)
          (gaussianReal 0 1) :=
        fun j => standardizedFeatureObservation_law v (ac j) (ha0 j.val)
      have hcorr : ∀ i j : κc, i ≠ j →
          |cov[X i, X j; featureGaussian v]| ≤ ε := by
        intro i j hij
        rw [show cov[X i, X j; featureGaussian v] =
            featureCorrelation v (a i.val) (a j.val) by
          exact standardizedFeatureObservation_covariance v (a i.val) (a j.val)]
        exact hsmall i.val j.val (fun h => hij (Subtype.ext h))
          (i.property.trans j.property.symm)
      have hrow' : ∀ i : κc,
          ∑ j ∈ Finset.univ.erase i, |cov[X i, X j; featureGaussian v]| ^ 2 ≤ Q := by
        intro i
        simpa only [X, ac, standardizedFeatureObservation_covariance] using hrow c i
      have hb := hmom (featureGaussian v) X hgauss hstd hcorr hrow'
        (fun j : κc => w j.val) W hW0 (fun j => hw j.val)
      have hcard : (Fintype.card κc : ℝ) ^ k ≤ (Fintype.card κ : ℝ) ^ k :=
        pow_le_pow_left₀ (by positivity)
          (by exact_mod_cast Fintype.card_subtype_le (fun j : κ => color j = c)) _
      have hsum : ∀ x, colorClassSum color
          (fun j => w j * centeredGaussianLog
            (standardizedFeatureObservation v (a j) x)) c =
          ∑ j : κc, w j.val * centeredGaussianLog
            (standardizedFeatureObservation v (a j.val) x) := by
        intro x
        exact Finset.sum_subtype (Finset.univ.filter (fun j : κ => color j = c))
          (by simp) _
      simp_rw [hsum]
      exact hb.trans (mul_le_mul_of_nonneg_left hcard
        (mul_nonneg hD0.le (pow_nonneg hW0 _)))
    · have hempty : IsEmpty κc := not_nonempty_iff.mp hc
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
      dsimp only [B]
      positivity
  have hall := gaussianLogStatistic_centered_evenMoment_of_coloring
    v w a ha0 k hk color B hgroup
  apply hall.trans_eq
  dsimp only [B, D]
  ring

theorem gaussianLogStatistic_uniform_evenMoment_of_decay
    (hBS : BardetSurgailisLemmaOneScalar) (k : ℕ) (hk : 1 ≤ k)
    (u : ℕ → ℝ) (hu : Tendsto u atTop (nhds 0))
    (A : ℝ) (hA : 0 ≤ A) (ε : ℝ) (hε0 : 0 < ε)
    (hε : ε < 1 / (2 * k : ℝ)) (e : ℝ) (he : e ≤ ε / 2)
    (Q : ℝ) (hQ : 0 ≤ Q) :
    ∃ D > 0, ∀ {ι E : Type}, ∀ [Fintype ι] [DecidableEq ι]
      [NormedAddCommGroup E] [InnerProductSpace ℝ E],
      ∀ (n : ℕ), 0 < n → ∀ (v : ι → E) (w : Fin n → ℝ)
      (a : Fin n → EuclideanSpace ℝ ι),
      (∀ j, ∑ i, a j i • v i ≠ 0) →
      (∀ i j : Fin n,
        |featureCorrelation v (a i) (a j)| ≤ A * u (Nat.dist j.val i.val) + e) →
      (∀ i : Fin n, ∑ j, |featureCorrelation v (a i) (a j)| ^ 2 ≤ Q) →
      ∀ (W : ℝ), 0 ≤ W → (∀ j, |w j| ≤ W) →
      (∫ x, |gaussianLogStatistic w a x -
          (∫ y, gaussianLogStatistic w a y ∂featureGaussian v)| ^ (2 * k)
        ∂featureGaussian v) ≤ D * W ^ (2 * k) * (n : ℝ) ^ k := by
  obtain ⟨d, hd, hcolor⟩ :=
    exists_residueColor_small_correlation u hu A ε e hA hε0 he
  obtain ⟨D, hD, hcolored⟩ :=
    gaussianLogStatistic_uniform_evenMoment_of_coloring hBS k hk hd ε hε0.le hε Q hQ
  refine ⟨D, hD, ?_⟩
  intro ι E _ _ _ _ n hn v w a ha0 hpoint hrow W hW0 hw
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  let color : Fin n → Fin d := residueColor d hd
  have hsmall : ∀ i j : Fin n, i ≠ j → color i = color j →
      |featureCorrelation v (a i) (a j)| ≤ ε := by
    intro i j hij hc
    exact hcolor (fun i j => featureCorrelation v (a i) (a j)) hpoint i j hij hc
  have hrestricted : ∀ c, ∀ i : {j : Fin n // color j = c},
      ∑ j ∈ Finset.univ.erase i,
        |featureCorrelation v (a i.val) (a j.val)| ^ 2 ≤ Q := by
    intro c i
    exact (restricted_square_row_le_full
      (fun i j : Fin n => featureCorrelation v (a i) (a j))
      (fun j => color j = c) i).trans (hrow i.val)
  simpa only [Fintype.card_fin] using
    hcolored v w a ha0 color hsmall hrestricted W hW0 hw

end Hurst
