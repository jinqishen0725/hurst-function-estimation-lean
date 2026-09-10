import Hurst.ActualFixedLagCorrelation
import Hurst.TruncatedCovarianceLimit
import Hurst.TriangularUniformization

noncomputable section
open Set Filter
open scoped Topology RealInnerProductSpace
namespace Hurst

/-- A nonzero local-polynomial weight lies in the shrinking kernel window, so
its midpoint-grid location converges to the target along every diverging sample
size sequence. -/
theorem localPolynomialWeights_nonzero_grid_tendsto
    (r q : ℕ) (t : ℝ) (δ : ℕ → ℝ)
    (hδpos : ∀ᶠ n in atTop, 0 < δ n) (hδ : Tendsto δ atTop (nhds 0))
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (i : ∀ n, Fin (N n - q))
    (hi : ∀ n, localPolynomialWeights r (N n) q (δ (N n)) t (i n) ≠ 0) :
    Tendsto (fun n => grid (N n) (i n).val) atTop (nhds t) := by
  have hpos : ∀ᶠ n in atTop, 0 < δ (N n) := hδpos.filter_mono hN
  have hsmall : ∀ᶠ n in atTop,
      |grid (N n) (i n).val - t| < δ (N n) := by
    filter_upwards [hpos] with n hn
    have hscaled : |(grid (N n) (i n).val - t) / δ (N n)| < 1 := by
      apply lt_of_not_ge
      intro hout
      exact hi n (localPolynomialWeights_zero r (N n) q (δ (N n)) t (i n) hout)
    rw [abs_div, abs_of_pos hn] at hscaled
    exact (div_lt_one hn).mp hscaled
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [Real.norm_eq_abs]
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun n => abs_nonneg _)
  · exact hsmall.mono (fun n hn => hn.le)
  · exact hδ.comp hN

/-- Actual q=1 correlation at a fixed nonnegative integer lag, extended by
zero when the shifted index is outside the finite row. -/
def actualStrideFirstLagCorrelation
    (f : ℝ → ℝ) (hf : ∀ x ∈ Ioo (0 : ℝ) 1, f x ∈ Ioo (0 : ℝ) 1)
    (n k : ℕ) (i : Fin (n - 1)) : ℝ :=
  if h : i.val + k < n - 1 then
    vectorCorrelation
      (gridStrideFirstActual n 1 (midpointSampleHurst f hf n) i)
      (gridStrideFirstActual n 1 (midpointSampleHurst f hf n)
        ⟨i.val + k, h⟩)
  else 0

/-- On the support of a fixed-lag product of local weights, actual q=1
correlations converge uniformly to the frozen correlation at `f t`. -/
theorem hurstHolder_stride_first_fixedLag_uniform_truncationCovariance
    (p a b M : ℝ) (r k K : ℕ)
    (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ : Tendsto δ atTop (nhds 0)) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ i,
      localPolynomialWeights r n 1 (δ n) t i *
        finZeroExtendedShift k
          (localPolynomialWeights r n 1 (δ n) t) i ≠ 0 →
      |gaussianLogTruncationCovariance K
          (actualStrideFirstLagCorrelation f hf.1 n k i) -
        gaussianLogTruncationCovariance K
          (firstIncrementLagCorrelation (f t) k)| < ε := by
  apply eventually_uniform_of_subsequence_tendsto
    (fun n => n - 1)
    (fun n i => localPolynomialWeights r n 1 (δ n) t i *
      finZeroExtendedShift k
        (localPolynomialWeights r n 1 (δ n) t) i ≠ 0)
    (fun n i => gaussianLogTruncationCovariance K
      (actualStrideFirstLagCorrelation f hf.1 n k i))
    (gaussianLogTruncationCovariance K
      (firstIncrementLagCorrelation (f t) k))
  intro φ hφmono i hi
  have hφtop : Tendsto φ atTop atTop := hφmono.tendsto_atTop
  have hvalid : ∀ n, (i n).val + k < φ n - 1 := by
    intro n
    by_contra hn
    have hz : finZeroExtendedShift k
        (localPolynomialWeights r (φ n) 1 (δ (φ n)) t) (i n) = 0 := by
      simp [finZeroExtendedShift, hn]
    exact hi n (mul_eq_zero_of_right _ hz)
  let j : ∀ n, Fin (φ n - 1) := fun n => ⟨(i n).val + k, hvalid n⟩
  have hiw : ∀ n,
      localPolynomialWeights r (φ n) 1 (δ (φ n)) t (i n) ≠ 0 := by
    intro n
    exact left_ne_zero_of_mul (hi n)
  have hjw : ∀ n,
      localPolynomialWeights r (φ n) 1 (δ (φ n)) t (j n) ≠ 0 := by
    intro n
    have hs : finZeroExtendedShift k
        (localPolynomialWeights r (φ n) 1 (δ (φ n)) t) (i n) =
          localPolynomialWeights r (φ n) 1 (δ (φ n)) t (j n) := by
      simp only [finZeroExtendedShift, dif_pos (hvalid n), j]
    rw [← hs]
    exact right_ne_zero_of_mul (hi n)
  have hit := localPolynomialWeights_nonzero_grid_tendsto r 1 t δ
    hδpos hδ φ hφtop i hiw
  have hjt := localPolynomialWeights_nonzero_grid_tendsto r 1 t δ
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
  have hcorr := hurstHolder_stride_first_fixedLag_correlation_tendsto
    p a b M hp ha hb hab hM f hf hF t ht 1 (by norm_num) k
    φ hφtop i j hit hjt (by simpa using hlag)
  have hcomp := (continuous_gaussianLogTruncationCovariance K).continuousAt.tendsto.comp hcorr
  apply hcomp.congr'
  exact Filter.Eventually.of_forall (fun n => by
    simp only [Function.comp_apply, actualStrideFirstLagCorrelation,
      dif_pos (hvalid n), j])

/-- Every fixed q=1 lag contribution of the actual truncated variance has the
frozen covariance times equivalent-kernel energy as its limit. -/
theorem hurstHolder_stride_first_fixedLag_truncatedVariance_tendsto
    (p a b M : ℝ) (r k K : ℕ)
    (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ : Tendsto δ atTop (nhds 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop) :
    Tendsto (fun n : ℕ => (n : ℝ) * δ n * ∑ i,
      localPolynomialWeights r n 1 (δ n) t i *
        finZeroExtendedShift k
          (localPolynomialWeights r n 1 (δ n) t) i *
            gaussianLogTruncationCovariance K
              (actualStrideFirstLagCorrelation f hf.1 n k i)) atTop
      (nhds ((∫ x in (-1 : ℝ)..1, equivalentKernel r x ^ 2) *
        gaussianLogTruncationCovariance K
          (firstIncrementLagCorrelation (f t) k))) := by
  exact localPolynomialWeights_fixedShift_truncationCovariance_tendsto_of_uniform
    r 1 k K t ht δ hδpos hδ hN
    (fun n i => actualStrideFirstLagCorrelation f hf.1 n k i)
    (firstIncrementLagCorrelation (f t) k)
    (hurstHolder_stride_first_fixedLag_uniform_truncationCovariance
      p a b M r k K hp ha hb hab hM f hf hF t ht δ hδpos hδ)

/-- The symmetric q=1 contribution of a single nonnegative lag. -/
def actualStrideFirstTruncatedLagContribution
    (r K : ℕ) (f : ℝ → ℝ)
    (hf : ∀ x ∈ Ioo (0 : ℝ) 1, f x ∈ Ioo (0 : ℝ) 1)
    (t : ℝ) (δ : ℕ → ℝ) (n k : ℕ) : ℝ :=
  (if k = 0 then 1 else 2) * ((n : ℝ) * δ n * ∑ i,
    localPolynomialWeights r n 1 (δ n) t i *
      finZeroExtendedShift k
        (localPolynomialWeights r n 1 (δ n) t) i *
          gaussianLogTruncationCovariance K
            (actualStrideFirstLagCorrelation f hf n k i))

/-- For every fixed lag cutoff, the corresponding actual q=1 truncated
variance sum converges to the finite frozen long-run covariance sum. -/
theorem hurstHolder_stride_first_finiteLag_truncatedVariance_tendsto
    (p a b M : ℝ) (r K R : ℕ)
    (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ : Tendsto δ atTop (nhds 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop) :
    Tendsto (fun n => ∑ k ∈ Finset.range R,
      actualStrideFirstTruncatedLagContribution r K f hf.1 t δ n k) atTop
      (nhds ((∫ x in (-1 : ℝ)..1, equivalentKernel r x ^ 2) *
        ∑ k ∈ Finset.range R, (if k = 0 then 1 else 2) *
          gaussianLogTruncationCovariance K
            (firstIncrementLagCorrelation (f t) k))) := by
  have hlag (k : ℕ) := hurstHolder_stride_first_fixedLag_truncatedVariance_tendsto
    p a b M r k K hp ha hb hab hM f hf hF t ht δ hδpos hδ hN
  have hterm (k : ℕ) : Tendsto
      (fun n => actualStrideFirstTruncatedLagContribution r K f hf.1 t δ n k)
      atTop (nhds ((∫ x in (-1 : ℝ)..1, equivalentKernel r x ^ 2) *
        ((if k = 0 then 1 else 2) * gaussianLogTruncationCovariance K
          (firstIncrementLagCorrelation (f t) k)))) := by
    unfold actualStrideFirstTruncatedLagContribution
    have hc := hlag k |>.const_mul (if k = 0 then 1 else 2)
    convert hc using 1 <;> ring
  have hs := tendsto_finsetSum (Finset.range R) (fun k _ => hterm k)
  convert hs using 1
  rw [Finset.mul_sum]

end Hurst
