import Hurst.UniformFeatureDecayEvenMoment

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace Topology
namespace Hurst

theorem gaussianLogStatistic_restrict_support
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (S : Finset (Fin n)) (w : Fin n → ℝ)
    (a : Fin n → EuclideanSpace ℝ ι) (hw : ∀ i, i ∉ S → w i = 0) :
    gaussianLogStatistic w a =
      gaussianLogStatistic (fun i : {j // j ∈ S} => w i.val)
        (fun i : {j // j ∈ S} => a i.val) := by
  funext x
  unfold gaussianLogStatistic
  rw [show (∑ j : Fin n, w j * Real.log (⟪a j, x⟫ ^ 2)) =
      ∑ j ∈ S, w j * Real.log (⟪a j, x⟫ ^ 2) by
    symm
    apply Finset.sum_subset (Finset.subset_univ S)
    intro j _ hj
    simp [hw j hj]]
  exact Finset.sum_subtype S (fun _ => Iff.rfl) _

theorem gaussianLogStatistic_uniform_evenMoment_on_support
    (hBS : BardetSurgailisLemmaOneScalar) (k : ℕ) (hk : 1 ≤ k)
    (u : ℕ → ℝ) (hu : Tendsto u atTop (nhds 0))
    (A : ℝ) (hA : 0 ≤ A) (ε : ℝ) (hε0 : 0 < ε)
    (hε : ε < 1 / (2 * k : ℝ)) (e : ℝ) (he : e ≤ ε / 2)
    (Q : ℝ) (hQ : 0 ≤ Q) :
    ∃ D > 0, ∀ {ι E : Type}, ∀ [Fintype ι] [DecidableEq ι]
      [NormedAddCommGroup E] [InnerProductSpace ℝ E],
      ∀ (n : ℕ) (S : Finset (Fin n)) (v : ι → E) (w : Fin n → ℝ)
      (a : Fin n → EuclideanSpace ℝ ι),
      (∀ j, ∑ i, a j i • v i ≠ 0) →
      (∀ i j : Fin n,
        |featureCorrelation v (a i) (a j)| ≤ A * u (Nat.dist j.val i.val) + e) →
      (∀ i : Fin n, ∑ j, |featureCorrelation v (a i) (a j)| ^ 2 ≤ Q) →
      (∀ i, i ∉ S → w i = 0) →
      ∀ (W : ℝ), 0 ≤ W → (∀ j, |w j| ≤ W) →
      (∫ x, |gaussianLogStatistic w a x -
          (∫ y, gaussianLogStatistic w a y ∂featureGaussian v)| ^ (2 * k)
        ∂featureGaussian v) ≤
        D * W ^ (2 * k) * (S.card : ℝ) ^ k := by
  obtain ⟨d, hd, hcolor⟩ :=
    exists_residueColor_small_correlation u hu A ε e hA hε0 he
  obtain ⟨D, hD, hcolored⟩ :=
    gaussianLogStatistic_uniform_evenMoment_of_coloring hBS k hk hd ε hε0.le hε Q hQ
  refine ⟨D, hD, ?_⟩
  intro ι E _ _ _ _ n S v w a ha hpnt hrow hsupport W hW0 hw
  let κ := {j : Fin n // j ∈ S}
  by_cases hS : S.Nonempty
  · letI : Nonempty κ := ⟨⟨hS.choose, hS.choose_spec⟩⟩
    let color : κ → Fin d := fun i => residueColor d hd i.val
    let aS : κ → EuclideanSpace ℝ ι := fun i => a i.val
    let wS : κ → ℝ := fun i => w i.val
    have haS : ∀ j, ∑ i, aS j i • v i ≠ 0 := fun j => ha j.val
    have hsmall : ∀ i j : κ, i ≠ j → color i = color j →
        |featureCorrelation v (aS i) (aS j)| ≤ ε := by
      intro i j hij hc
      exact hcolor (fun i j => featureCorrelation v (a i) (a j)) hpnt i.val j.val
        (fun h => hij (Subtype.ext h)) hc
    have hrestricted : ∀ c, ∀ i : {j : κ // color j = c},
        ∑ j ∈ Finset.univ.erase i,
          |featureCorrelation v (aS i.val) (aS j.val)| ^ 2 ≤ Q := by
      intro c i
      calc
        _ ≤ ∑ j : κ, |featureCorrelation v (aS i.val) (aS j)| ^ 2 :=
          restricted_square_row_le_full
            (fun x y : κ => featureCorrelation v (aS x) (aS y))
            (fun j => color j = c) i
        _ = ∑ j ∈ S, |featureCorrelation v (a i.val.val) (a j)| ^ 2 := by
          dsimp only [aS, κ]
          exact (Finset.sum_subtype S (fun _ => Iff.rfl)
            (fun j => |featureCorrelation v (a i.val.val) (a j)| ^ 2)).symm
        _ ≤ ∑ j : Fin n, |featureCorrelation v (a i.val.val) (a j)| ^ 2 := by
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
            (fun _ _ _ => sq_nonneg _)
        _ ≤ Q := hrow i.val.val
    have hb := hcolored v wS aS haS color hsmall hrestricted W hW0
      (fun j => hw j.val)
    have hstat := gaussianLogStatistic_restrict_support S w a hsupport
    dsimp only [wS, aS, κ] at hb
    rw [← hstat] at hb
    simpa only [κ, Fintype.card_coe] using hb
  · have hSe : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    have hwz : w = 0 := by
      funext i
      exact hsupport i (by simp)
    subst w
    have hk0 : k ≠ 0 := by omega
    have h2k0 : 2 * k ≠ 0 := by omega
    simp [gaussianLogStatistic, hk0, h2k0]

end Hurst
