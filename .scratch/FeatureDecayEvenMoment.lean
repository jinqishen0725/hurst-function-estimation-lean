import Hurst.DecayColoring
import Hurst.RestrictedCorrelationRow

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace Topology
namespace Hurst

/-- End-to-end internal moment theorem from a vanishing pointwise correlation
profile and a uniform squared-correlation row bound. -/
theorem gaussianLogStatistic_centered_evenMoment_of_decay
    (hBS : BardetSurgailisLemmaOneScalar) (k : ℕ) (hk : 1 ≤ k)
    {ι E : Type} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n : ℕ) (hn : 0 < n)
    (v : ι → E) (w : Fin n → ℝ) (a : Fin n → EuclideanSpace ℝ ι)
    (ha0 : ∀ j, ∑ i, a j i • v i ≠ 0)
    (u : ℕ → ℝ) (hu : Tendsto u atTop (nhds 0))
    (A : ℝ) (hA : 0 ≤ A)
    (ε : ℝ) (hε0 : 0 < ε) (hε : ε < 1 / (2 * k : ℝ))
    (e : ℝ) (he : e ≤ ε / 2)
    (hpoint : ∀ i j : Fin n,
      |featureCorrelation v (a i) (a j)| ≤ A * u (Nat.dist j.val i.val) + e)
    (Q : ℝ) (hQ : 0 ≤ Q)
    (hrow : ∀ i : Fin n, ∑ j, |featureCorrelation v (a i) (a j)| ^ 2 ≤ Q)
    (W : ℝ) (hW0 : 0 ≤ W) (hw : ∀ j, |w j| ≤ W) :
    ∃ D > 0,
      (∫ x, |gaussianLogStatistic w a x -
          (∫ y, gaussianLogStatistic w a y ∂featureGaussian v)| ^ (2 * k)
        ∂featureGaussian v) ≤
        D * W ^ (2 * k) * (n : ℝ) ^ k := by
  obtain ⟨d, hd, hcolor⟩ :=
    exists_residueColor_small_correlation u hu A ε e hA hε0 he
  let color : Fin n → Fin d := residueColor d hd
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
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
    gaussianLogStatistic_centered_evenMoment_of_smallCorrelationColoring
      hBS k hk v w a ha0 color ε hε0.le hε hsmall Q hQ hrestricted W hW0 hw

end Hurst
