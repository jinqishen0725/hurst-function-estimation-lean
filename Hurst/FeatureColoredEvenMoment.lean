import Hurst.FeatureColorMoment

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace Hurst

/-- Full colored-array moment theorem for an actual Gaussian log statistic.
Different colors need not be independent. -/
theorem gaussianLogStatistic_centered_evenMoment_of_smallCorrelationColoring
    (hBS : BardetSurgailisLemmaOneScalar) (k : ℕ) (hk : 1 ≤ k)
    {ι κ E : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [Nonempty κ] [DecidableEq κ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (w : κ → ℝ) (a : κ → EuclideanSpace ℝ ι)
    (ha0 : ∀ j, ∑ i, a j i • v i ≠ 0)
    {d : ℕ} (color : κ → Fin d)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε : ε < 1 / (2 * k : ℝ))
    (hsmall : ∀ i j, i ≠ j → color i = color j →
      |featureCorrelation v (a i) (a j)| ≤ ε)
    (Q : ℝ) (hQ : 0 ≤ Q)
    (hrow : ∀ c, ∀ i : {j : κ // color j = c},
      ∑ j ∈ Finset.univ.erase i,
        |featureCorrelation v (a i.val) (a j.val)| ^ 2 ≤ Q)
    (W : ℝ) (hW0 : 0 ≤ W) (hw : ∀ j, |w j| ≤ W) :
    ∃ D > 0,
      (∫ x, |gaussianLogStatistic w a x -
          (∫ y, gaussianLogStatistic w a y ∂featureGaussian v)| ^ (2 * k)
        ∂featureGaussian v) ≤
        D * W ^ (2 * k) * (Fintype.card κ : ℝ) ^ k := by
  have hper : ∀ c : Fin d, ∃ D > 0,
      (∫ x, |colorClassSum color
        (fun j => w j * centeredGaussianLog
          (standardizedFeatureObservation v (a j) x)) c| ^ (2 * k)
        ∂featureGaussian v) ≤
        D * W ^ (2 * k) * (Fintype.card κ : ℝ) ^ k := by
    intro c
    exact featureGaussian_colorClass_evenMoment_bound hBS k hk v w a ha0 color c
      ε hε0 hε (fun i j hij hi hj => hsmall i j hij (hi.trans hj.symm))
      Q hQ (hrow c) W hW0 hw
  choose D hD hbound using hper
  let DT := 1 + ∑ c : Fin d, D c
  have hDT : 0 < DT := by
    dsimp only [DT]
    have hs : 0 ≤ ∑ c : Fin d, D c := Finset.sum_nonneg (fun c _ => (hD c).le)
    linarith
  have hd : 0 < d := by
    let j : κ := Classical.choice inferInstance
    have hj := (color j).isLt
    omega
  let B := DT * W ^ (2 * k) * (Fintype.card κ : ℝ) ^ k
  have hgroup : ∀ c,
      (∫ x, |colorClassSum color
        (fun j => w j * centeredGaussianLog
          (standardizedFeatureObservation v (a j) x)) c| ^ (2 * k)
        ∂featureGaussian v) ≤ B := by
    intro c
    apply (hbound c).trans
    dsimp only [B, DT]
    have hDc : D c ≤ 1 + ∑ u : Fin d, D u := by
      have hsingle : D c ≤ ∑ u : Fin d, D u :=
        Finset.single_le_sum (fun u _ => (hD u).le) (Finset.mem_univ c)
      linarith
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hDc (pow_nonneg hW0 _)) (by positivity)
  have hall := gaussianLogStatistic_centered_evenMoment_of_coloring v w a ha0 k hk color B hgroup
  let Dtot := (d : ℝ) ^ (2 * k) * DT
  have hDtot : 0 < Dtot := by
    dsimp only [Dtot]
    positivity
  refine ⟨Dtot, hDtot, ?_⟩
  apply hall.trans_eq
  dsimp only [B, Dtot]
  ring

end Hurst
