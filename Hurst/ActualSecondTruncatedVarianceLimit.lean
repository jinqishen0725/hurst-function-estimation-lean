import Hurst.ActualSecondFixedLagCorrelation
import Hurst.ActualFirstTruncatedVarianceLimit

noncomputable section
open Set Filter
open scoped Topology RealInnerProductSpace
namespace Hurst

/-- Actual q=2 correlation at a fixed nonnegative integer lag, extended by
zero when the shifted index is outside the finite row. -/
def actualSecondLagCorrelation
    (f : ℝ → ℝ) (hf : ∀ x ∈ Ioo (0 : ℝ) 1, f x ∈ Ioo (0 : ℝ) 1)
    (n k : ℕ) (i : Fin (n - 2)) : ℝ :=
  if h : i.val + k < n - 2 then
    vectorCorrelation
      (gridSecondActual n (midpointSampleHurst f hf n) i)
      (gridSecondActual n (midpointSampleHurst f hf n) ⟨i.val + k, h⟩)
  else 0

/-- On the support of a fixed-lag product of local weights, actual q=2
correlations converge uniformly to the frozen q=2 correlation at `f t`. -/
theorem hurstHolder_grid_second_fixedLag_uniform_truncationCovariance
    (p a b M : ℝ) (r k K : ℕ)
    (hp : 2 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ : Tendsto δ atTop (nhds 0)) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ i,
      localPolynomialWeights r n 2 (δ n) t i *
        finZeroExtendedShift k
          (localPolynomialWeights r n 2 (δ n) t) i ≠ 0 →
      |gaussianLogTruncationCovariance K
          (actualSecondLagCorrelation f hf.1 n k i) -
        gaussianLogTruncationCovariance K
          (secondIncrementLagCorrelation (f t) k)| < ε := by
  apply eventually_uniform_of_subsequence_tendsto
    (fun n => n - 2)
    (fun n i => localPolynomialWeights r n 2 (δ n) t i *
      finZeroExtendedShift k
        (localPolynomialWeights r n 2 (δ n) t) i ≠ 0)
    (fun n i => gaussianLogTruncationCovariance K
      (actualSecondLagCorrelation f hf.1 n k i))
    (gaussianLogTruncationCovariance K
      (secondIncrementLagCorrelation (f t) k))
  intro φ hφmono i hi
  have hφtop : Tendsto φ atTop atTop := hφmono.tendsto_atTop
  have hvalid : ∀ n, (i n).val + k < φ n - 2 := by
    intro n
    by_contra hn
    have hz : finZeroExtendedShift k
        (localPolynomialWeights r (φ n) 2 (δ (φ n)) t) (i n) = 0 := by
      simp [finZeroExtendedShift, hn]
    exact hi n (mul_eq_zero_of_right _ hz)
  let j : ∀ n, Fin (φ n - 2) := fun n => ⟨(i n).val + k, hvalid n⟩
  have hiw : ∀ n,
      localPolynomialWeights r (φ n) 2 (δ (φ n)) t (i n) ≠ 0 := by
    intro n
    exact left_ne_zero_of_mul (hi n)
  have hjw : ∀ n,
      localPolynomialWeights r (φ n) 2 (δ (φ n)) t (j n) ≠ 0 := by
    intro n
    have hs : finZeroExtendedShift k
        (localPolynomialWeights r (φ n) 2 (δ (φ n)) t) (i n) =
          localPolynomialWeights r (φ n) 2 (δ (φ n)) t (j n) := by
      simp only [finZeroExtendedShift, dif_pos (hvalid n), j]
    rw [← hs]
    exact right_ne_zero_of_mul (hi n)
  have hit := localPolynomialWeights_nonzero_grid_tendsto r 2 t δ
    hδpos hδ φ hφtop i hiw
  have hjt := localPolynomialWeights_nonzero_grid_tendsto r 2 t δ
    hδpos hδ φ hφtop j hjw
  have hlag : ∀ᶠ n in atTop,
      grid (φ n) (j n).val = grid (φ n) (i n).val +
        (k : ℝ) * ((1 : ℝ) / φ n) := by
    exact Filter.Eventually.of_forall (fun n => by
      have hn : 0 < φ n := by have := (i n).isLt; omega
      dsimp only [j]
      unfold grid
      field_simp
      push_cast
      ring)
  have hcorr := hurstHolder_grid_second_fixedLag_correlation_tendsto
    p a b M hp ha hb hab hM f hf hF t ht k
    φ hφtop i j hit hjt (by simpa using hlag)
  have hcomp := (continuous_gaussianLogTruncationCovariance K).continuousAt.tendsto.comp hcorr
  apply hcomp.congr'
  exact Filter.Eventually.of_forall (fun n => by
    simp only [Function.comp_apply, actualSecondLagCorrelation,
      dif_pos (hvalid n), j])

/-- Every fixed q=2 lag contribution of the actual truncated variance has the
frozen covariance times equivalent-kernel energy as its limit. -/
theorem hurstHolder_grid_second_fixedLag_truncatedVariance_tendsto
    (p a b M : ℝ) (r k K : ℕ)
    (hp : 2 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ : Tendsto δ atTop (nhds 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop) :
    Tendsto (fun n : ℕ => (n : ℝ) * δ n * ∑ i,
      localPolynomialWeights r n 2 (δ n) t i *
        finZeroExtendedShift k
          (localPolynomialWeights r n 2 (δ n) t) i *
            gaussianLogTruncationCovariance K
              (actualSecondLagCorrelation f hf.1 n k i)) atTop
      (nhds ((∫ x in (-1 : ℝ)..1, equivalentKernel r x ^ 2) *
        gaussianLogTruncationCovariance K
          (secondIncrementLagCorrelation (f t) k))) := by
  exact localPolynomialWeights_fixedShift_truncationCovariance_tendsto_of_uniform
    r 2 k K t ht δ hδpos hδ hN
    (fun n i => actualSecondLagCorrelation f hf.1 n k i)
    (secondIncrementLagCorrelation (f t) k)
    (hurstHolder_grid_second_fixedLag_uniform_truncationCovariance
      p a b M r k K hp ha hb hab hM f hf hF t ht δ hδpos hδ)

/-- The symmetric q=2 contribution of a single nonnegative lag. -/
def actualSecondTruncatedLagContribution
    (r K : ℕ) (f : ℝ → ℝ)
    (hf : ∀ x ∈ Ioo (0 : ℝ) 1, f x ∈ Ioo (0 : ℝ) 1)
    (t : ℝ) (δ : ℕ → ℝ) (n k : ℕ) : ℝ :=
  (if k = 0 then 1 else 2) * ((n : ℝ) * δ n * ∑ i,
    localPolynomialWeights r n 2 (δ n) t i *
      finZeroExtendedShift k
        (localPolynomialWeights r n 2 (δ n) t) i *
          gaussianLogTruncationCovariance K
            (actualSecondLagCorrelation f hf n k i))

/-- For every fixed lag cutoff, the corresponding actual q=2 truncated
variance sum converges to the finite frozen long-run covariance sum. -/
theorem hurstHolder_grid_second_finiteLag_truncatedVariance_tendsto
    (p a b M : ℝ) (r K R : ℕ)
    (hp : 2 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ : Tendsto δ atTop (nhds 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop) :
    Tendsto (fun n => ∑ k ∈ Finset.range R,
      actualSecondTruncatedLagContribution r K f hf.1 t δ n k) atTop
      (nhds ((∫ x in (-1 : ℝ)..1, equivalentKernel r x ^ 2) *
        ∑ k ∈ Finset.range R, (if k = 0 then 1 else 2) *
          gaussianLogTruncationCovariance K
            (secondIncrementLagCorrelation (f t) k))) := by
  have hlag (k : ℕ) := hurstHolder_grid_second_fixedLag_truncatedVariance_tendsto
    p a b M r k K hp ha hb hab hM f hf hF t ht δ hδpos hδ hN
  have hterm (k : ℕ) : Tendsto
      (fun n => actualSecondTruncatedLagContribution r K f hf.1 t δ n k)
      atTop (nhds ((∫ x in (-1 : ℝ)..1, equivalentKernel r x ^ 2) *
        ((if k = 0 then 1 else 2) * gaussianLogTruncationCovariance K
          (secondIncrementLagCorrelation (f t) k)))) := by
    unfold actualSecondTruncatedLagContribution
    have hc := hlag k |>.const_mul (if k = 0 then 1 else 2)
    convert hc using 1 <;> ring
  have hs := tendsto_finsetSum (Finset.range R) (fun k _ => hterm k)
  convert hs using 1
  rw [Finset.mul_sum]

end Hurst
