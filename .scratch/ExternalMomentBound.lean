import Hurst.GaussianLogHermite
import Mathlib.Probability.Moments.ComplexMGF

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace Hurst

/-- Hermite rank at least two, expressed only through the two coefficients used by
the scalar specialization of Bardet--Surgailis Lemma 1. -/
def HermiteRankAtLeastTwo (f : ℝ → ℝ) : Prop :=
  MemLp f 2 (gaussianReal 0 1) ∧
    ∀ n : ℕ, n < 2 →
      (∫ x, f x * (gaussianHermite n).eval x ∂gaussianReal 0 1) = 0

theorem centeredGaussianLog_rankAtLeastTwo :
    HermiteRankAtLeastTwo centeredGaussianLog := by
  refine ⟨centeredGaussianLog_memLp_two, ?_⟩
  intro n hn
  have hc := gaussianLog_hermite_rank_at_least_two n hn
  rw [gaussianLog_hermite_coefficient] at hc
  have hs : (Real.sqrt (n.factorial : ℝ))⁻¹ ≠ 0 :=
    inv_ne_zero (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.factorial_pos n))).ne'
  exact (mul_eq_zero.mp hc).resolve_left hs

/-- The sole external probability input used for finite loss moments.

This is the upper-bound form of Bardet--Surgailis Lemma 1 specialized to scalar,
standard Gaussian arrays and Hermite rank two. `Q` is any upper bound on the
off-diagonal squared-correlation rows. The first `α` functions have rank at least
two; the remaining functions only need an `L²` bound. -/
def BardetSurgailisBoundsFor {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ι → Ω → ℝ) : Prop :=
  ∀ (v : ℕ), ∀ A : Finset (Fin v), 2 ≤ v → ∀ ε : ℝ,
    0 ≤ ε → ε < 1 / ((v : ℝ) - 1) →
    ∃ C > 0, (∀ i j, i ≠ j → |cov[X i, X j; P]| ≤ ε) →
      ∀ (Q L : ℝ), 0 ≤ Q → 0 ≤ L →
      (∀ i, ∑ j ∈ Finset.univ.erase i, |cov[X i, X j; P]| ^ 2 ≤ Q) →
      ∀ (F : Fin v → ι → ℝ → ℝ),
      (∀ j i, MemLp (F j i) 2 (gaussianReal 0 1)) →
      (∀ j i, eLpNorm (F j i) 2 (gaussianReal 0 1) ≤ ENNReal.ofReal L) →
      (∀ j ∈ A, ∀ i, HermiteRankAtLeastTwo (F j i)) →
      (∑ g : Fin v ↪ ι,
        |∫ ω, ∏ j : Fin v, F j (g j) (X (g j) ω) ∂P|) ≤
        C * L ^ v * (Fintype.card ι : ℝ) ^ ((v : ℝ) - (A.card : ℝ) / 2) *
          Q ^ ((A.card : ℝ) / 2)

def BardetSurgailisLemmaOneScalarFor {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ι → Ω → ℝ) : Prop :=
  HasGaussianLaw (fun ω => fun i => X i ω) P →
  (∀ i, MeasurePreserving (X i) P (gaussianReal 0 1)) →
  BardetSurgailisBoundsFor P X

def BardetSurgailisLemmaOneScalar : Prop :=
  ∀ {ι Ω : Type}, ∀ [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω],
    ∀ (P : Measure Ω), ∀ [IsProbabilityMeasure P], ∀ (X : ι → Ω → ℝ),
      BardetSurgailisLemmaOneScalarFor P X

end Hurst
