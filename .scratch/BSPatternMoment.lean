import Hurst.ExternalMomentBound
import Hurst.MomentExpansion

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace Hurst

theorem HermiteRankAtLeastTwo.const_mul {f : ℝ → ℝ}
    (hf : HermiteRankAtLeastTwo f) (c : ℝ) :
    HermiteRankAtLeastTwo (fun x => c * f x) := by
  refine ⟨hf.1.const_mul c, ?_⟩
  intro n hn
  have hi := hf.1.integrable_mul (standardGaussian_polynomial_memLp_two (gaussianHermite n))
  rw [show (fun x => c * f x * (gaussianHermite n).eval x) =
      fun x => c * (f x * (gaussianHermite n).eval x) by funext x; ring,
    integral_const_mul, hf.2 n hn, mul_zero]

def centeredLogPatternFunction {m : ℕ} {ι : Type*}
    (a : ι → ℝ) (q : MomentPattern m) (j : Fin q.1.val) (i : ι) (x : ℝ) : ℝ :=
  a i ^ momentMultiplicity q j * centeredGaussianLog x ^ momentMultiplicity q j

theorem centeredLogPatternFunction_memLp_two {m : ℕ} {ι : Type*}
    (a : ι → ℝ) (q : MomentPattern m) (j : Fin q.1.val) (i : ι) :
    MemLp (centeredLogPatternFunction a q j i) 2 (gaussianReal 0 1) := by
  unfold centeredLogPatternFunction
  exact (centeredGaussianLog_pow_memLp_two (momentMultiplicity q j)).const_mul _

theorem centeredLogPatternFunction_rank_singleton {m : ℕ} {ι : Type*}
    (a : ι → ℝ) (q : MomentPattern m) (j : Fin q.1.val)
    (hj : momentMultiplicity q j = 1) (i : ι) :
    HermiteRankAtLeastTwo (centeredLogPatternFunction a q j i) := by
  unfold centeredLogPatternFunction
  rw [hj]
  simpa only [pow_one] using
    centeredGaussianLog_rankAtLeastTwo.const_mul (a i)

/-- Applying the sole external lemma to one equality pattern. Repeated indices have
already been collected into powers by `MomentPattern`; precisely the singleton
blocks contribute Hermite rank two. -/
theorem bardetSurgailis_pattern_bound
    {m : ℕ} (q : MomentPattern m) (hv : 2 ≤ q.1.val)
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ι → Ω → ℝ)
    (hBS : BardetSurgailisLemmaOneScalarFor P X)
    (hGaussian : HasGaussianLaw (fun ω => fun i => X i ω) P)
    (hstandard : ∀ i, MeasurePreserving (X i) P (gaussianReal 0 1))
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε : ε < 1 / ((q.1.val : ℝ) - 1))
    (hcorr : ∀ i j, i ≠ j → |cov[X i, X j; P]| ≤ ε)
    (Q : ℝ) (hQ : 0 ≤ Q)
    (hrow : ∀ i, ∑ j ∈ Finset.univ.erase i, |cov[X i, X j; P]| ^ 2 ≤ Q)
    (a : ι → ℝ) (L : ℝ) (hL0 : 0 ≤ L)
    (hL : ∀ j i, eLpNorm (centeredLogPatternFunction a q j i) 2
      (gaussianReal 0 1) ≤ ENNReal.ofReal L) :
    ∃ C > 0,
      (∑ g : Fin q.1.val ↪ ι,
        |∫ ω, ∏ j : Fin q.1.val,
          (a (g j) * centeredGaussianLog (X (g j) ω)) ^ momentMultiplicity q j ∂P|) ≤
        C * L ^ q.1.val * (Fintype.card ι : ℝ) ^
          ((q.1.val : ℝ) -
            ((Finset.univ.filter (fun j => momentMultiplicity q j = 1)).card : ℝ) / 2) *
          Q ^ (((Finset.univ.filter (fun j => momentMultiplicity q j = 1)).card : ℝ) / 2) := by
  let A : Finset (Fin q.1.val) :=
    Finset.univ.filter (fun j => momentMultiplicity q j = 1)
  obtain ⟨C, hC, hbound⟩ := hBS hGaussian hstandard q.1.val A hv ε hε0 hε
  refine ⟨C, hC, ?_⟩
  let F : Fin q.1.val → ι → ℝ → ℝ := centeredLogPatternFunction a q
  have hmem : ∀ j i, MemLp (F j i) 2 (gaussianReal 0 1) := by
    intro j i
    exact centeredLogPatternFunction_memLp_two a q j i
  have hnorm : ∀ j i, eLpNorm (F j i) 2 (gaussianReal 0 1) ≤ ENNReal.ofReal L := by
    intro j i
    exact hL j i
  have hrank : ∀ j ∈ A, ∀ i, HermiteRankAtLeastTwo (F j i) := by
    intro j hj i
    exact centeredLogPatternFunction_rank_singleton a q j (Finset.mem_filter.mp hj).2 i
  have hb := hbound hcorr Q L hQ hL0 hrow F hmem hnorm hrank
  change _ ≤ C * L ^ q.1.val * (Fintype.card ι : ℝ) ^
      ((q.1.val : ℝ) - (A.card : ℝ) / 2) * Q ^ ((A.card : ℝ) / 2)
  convert hb using 1
  · apply Finset.sum_congr rfl
    intro g _
    congr 1
    apply integral_congr_ae
    filter_upwards [] with ω
    apply Finset.prod_congr rfl
    intro j _
    simp only [F, centeredLogPatternFunction, mul_pow]

end Hurst
