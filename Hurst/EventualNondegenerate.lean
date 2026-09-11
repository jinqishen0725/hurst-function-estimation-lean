import Hurst.FeatureQuadraticSpectral
import Hurst.SpectralMatchingInterface
import Hurst.DistributionEventualTransfer

/-!
# Eventual nondegeneracy for the weighted feature quadratic statistic

The consumption theorem
`gaussianLogQuadraticStatistic_tendsto_secondChaos_of_decreasing_matching`
demands the *global* nondegeneracy hypothesis
`∀ n k, ∑ i, a n k i • v n i ≠ 0`, while the actual model only guarantees it
for large `n`.  This file closes that bookkeeping gap (F3) in three modules.

## 1. Zero-weight identities (exact objects)

`gaussianLogQuadraticStatistic v w a x = ∑ k, w k * (obs_k(x)^2 - 1)` carries
no normalizer (it does *not* divide by `∑ w²`), and
`weightedFeatureQuadraticMatrix v a w = CFC.sqrt R * Matrix.diagonal w * CFC.sqrt R`
is conjugation of the weight diagonal.  Consequently zeroing a single weight
`w k` does **not** leave either object invariant: it deletes exactly row `k`'s
centered contribution from the statistic
(`gaussianLogQuadraticStatistic_zeroWeight_row`) and the rank-one
`k`-diagonal conjugate from the matrix
(`weightedFeatureQuadraticMatrix_zeroWeight_row`).  Invariance holds only when
`w k = 0` already or the deleted contribution vanishes.  What the downstream
`centeredMatrixQuadratic` law actually consumes is not zero-weight invariance
of one array but *eventual equality of arrays*, which is the route taken here.

## 2. The padding construction

`safePaddedVector`, `safePaddedWeights`, `safePaddedCoefficients` replace the
finitely many rows with `n < N₀` by fixed degenerate-safe data: the weight
profile `fun _ => 1` and coefficient rows `fun _ i => if i = j then 1 else 0`
against a fixed feature vector `v₀` with `v₀ j ≠ 0`.  For those rows
`∑ i, a' n k i • v' n i = v₀ j ≠ 0` by construction
(`safePadded_nondegenerate`), and for `n ≥ N₀` the padded data is the original
data (`safePaddedVector_eq`, `safePaddedWeights_eq`,
`safePaddedCoefficients_eq`), which transports the matrix array and hence its
Hermitian eigenvalues (`safePadded_eigenvalues_eq`, via proof irrelevance).

## 3. The eventual-nondegeneracy corollary

`gaussianLogQuadraticStatistic_tendsto_secondChaos_of_eventually_nondegenerate`
applies the global consumption theorem to the padded array (transporting the
asymptotic coefficient and trace-square inputs across the eventual equality)
and then transfers the conclusion to the original statistic, first across the
measure-family change and then across the eventual equality of the statistics
themselves, using the repo's `tendstoInDistribution_congr_eventually`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix Filter
open scoped RealInnerProductSpace MatrixOrder Topology
namespace Hurst

variable {iota kappa E : Type*} [Fintype iota] [DecidableEq iota]
  [Fintype kappa] [DecidableEq kappa]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### A generic eventual row-transfer helper -/

/-- Convergence in distribution tolerates an eventually equal row array even
when the row probability laws vary: if eventually `X i = Y i` and `μ i = ν i`,
then `X` converges whenever `Y` does. -/
theorem tendstoInDistribution_of_eventually_row_eq
    {ι F : Type*} {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)]
    [TopologicalSpace F] [MeasurableSpace F] [OpensMeasurableSpace F]
    {μ ν : ∀ i, Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, IsProbabilityMeasure (ν i)]
    {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    (X Y : ∀ i, Ω i → F) (Z : Ω' → F) (l : Filter ι)
    (hY : TendstoInDistribution Y l Z ν μ')
    (hXmeas : ∀ i, AEMeasurable (X i) (μ i))
    (hfun : ∀ᶠ i in l, X i = Y i)
    (hmeas : ∀ᶠ i in l, μ i = ν i) :
    TendstoInDistribution X l Z μ μ' where
  forall_aemeasurable := hXmeas
  aemeasurable_limit := hY.aemeasurable_limit
  tendsto := by
    refine Tendsto.congr' ?_ hY.tendsto
    filter_upwards [hfun, hmeas] with i hfun hmeas
    exact Subtype.ext (by
      show Measure.map (Y i) (ν i) = Measure.map (X i) (μ i)
      rw [hfun, hmeas])

/-! ### 1. Zero-weight exact-object identities -/

/-- Deleting the weighted summand of one row: zeroing `w k` removes exactly
`w k * (obs_k(x)^2 - 1)` from the quadratic statistic.  In particular the
statistic is *not* invariant under zero-weighting a row (there is no
normalizer that would absorb the change). -/
theorem gaussianLogQuadraticStatistic_zeroWeight_row
    (v : iota → E) (a : kappa → EuclideanSpace ℝ iota) (w : kappa → ℝ)
    (k : kappa) (x : EuclideanSpace ℝ iota) :
    gaussianLogQuadraticStatistic v (Function.update w k 0) a x =
      gaussianLogQuadraticStatistic v w a x
        - w k * ((standardizedFeatureObservation v (a k) x) ^ 2 - 1) := by
  have hdel : (∑ i, w i * ((standardizedFeatureObservation v (a i) x) ^ 2 - 1))
      - ∑ i, Function.update w k 0 i
          * ((standardizedFeatureObservation v (a i) x) ^ 2 - 1)
      = w k * ((standardizedFeatureObservation v (a k) x) ^ 2 - 1) := by
    rw [← Finset.sum_sub_distrib]
    rw [Finset.sum_eq_single k]
    · simp [Function.update]
    · intro b _ hb
      simp [Function.update, hb]
    · simp
  simp only [gaussianLogQuadraticStatistic]
  linarith [hdel]

/-- Zeroing weight `w k` removes exactly the rank-one `k`-diagonal conjugate
from the weighted covariance matrix; the `k` row and column of the weight
contribution vanish but the rest of the matrix is untouched, so the matrix is
not invariant either. -/
theorem weightedFeatureQuadraticMatrix_zeroWeight_row
    (v : iota → E) (a : kappa → EuclideanSpace ℝ iota) (w : kappa → ℝ)
    (k : kappa) :
    weightedFeatureQuadraticMatrix v a (Function.update w k 0) =
      weightedFeatureQuadraticMatrix v a w
        - CFC.sqrt (Matrix.gram ℝ (fun l => standardizedFeatureVector v (a l)))
            * Matrix.single k k (w k)
            * CFC.sqrt (Matrix.gram ℝ (fun l => standardizedFeatureVector v (a l))) := by
  have hds : Matrix.diagonal w - Matrix.single k k (w k)
      = Matrix.diagonal (Function.update w k 0) := by
    ext i j
    by_cases hik : i = k
    · rw [hik]
      by_cases hij : j = k
      · simp [hij, Function.update]
      · simp [Ne.symm hij]
    · by_cases hij : i = j
      · have hjk : ¬(k = j) := fun h => hik (hij.trans h.symm)
        rw [hij]
        simp [hjk, Ne.symm hjk]
      · simp [hij, Ne.symm hik]
  simp only [weightedFeatureQuadraticMatrix]
  calc CFC.sqrt (Matrix.gram ℝ (fun l => standardizedFeatureVector v (a l)))
        * Matrix.diagonal (Function.update w k 0)
        * CFC.sqrt (Matrix.gram ℝ (fun l => standardizedFeatureVector v (a l)))
      = CFC.sqrt (Matrix.gram ℝ (fun l => standardizedFeatureVector v (a l)))
          * (Matrix.diagonal w - Matrix.single k k (w k))
          * CFC.sqrt (Matrix.gram ℝ (fun l => standardizedFeatureVector v (a l))) := by
        rw [hds]
    _ = CFC.sqrt (Matrix.gram ℝ (fun l => standardizedFeatureVector v (a l)))
          * Matrix.diagonal w
          * CFC.sqrt (Matrix.gram ℝ (fun l => standardizedFeatureVector v (a l)))
        - CFC.sqrt (Matrix.gram ℝ (fun l => standardizedFeatureVector v (a l)))
          * Matrix.single k k (w k)
          * CFC.sqrt (Matrix.gram ℝ (fun l => standardizedFeatureVector v (a l))) := by
        rw [mul_sub, sub_mul]

/-! ### 2. The padding construction -/

/-- Padded feature array: for `n < N₀` a fixed degenerate-safe vector `v₀`
(nonzero in coordinate `j`), for `n ≥ N₀` the original data. -/
def safePaddedVector (N₀ : ℕ) (v₀ : iota → E) (v : ℕ → iota → E) (n : ℕ) :
    iota → E :=
  if N₀ ≤ n then v n else v₀

/-- Padded weight profile: `1` on every padded row, original weights
elsewhere. -/
def safePaddedWeights (N₀ : ℕ) (m : ℕ → ℕ) (w : ∀ n, Fin (m n) → ℝ) (n : ℕ) :
    Fin (m n) → ℝ :=
  if N₀ ≤ n then w n else fun _ => 1

/-- Padded coefficient rows: the indicator of the fixed safe coordinate `j`
on every padded row, original coefficients elsewhere. -/
def safePaddedCoefficients (N₀ : ℕ) (j : iota) (m : ℕ → ℕ)
    (a : ∀ n, Fin (m n) → EuclideanSpace ℝ iota) (n : ℕ) :
    Fin (m n) → EuclideanSpace ℝ iota :=
  if N₀ ≤ n then a n else fun (_ : Fin (m n)) => EuclideanSpace.single j (1 : ℝ)

theorem safePaddedVector_eq {N₀ : ℕ} {v₀ : iota → E} {v : ℕ → iota → E}
    {n : ℕ} (hn : N₀ ≤ n) : safePaddedVector N₀ v₀ v n = v n := if_pos hn

theorem safePaddedWeights_eq {N₀ : ℕ} {m : ℕ → ℕ} {w : ∀ n, Fin (m n) → ℝ}
    {n : ℕ} (hn : N₀ ≤ n) : safePaddedWeights N₀ m w n = w n := if_pos hn

theorem safePaddedCoefficients_eq {N₀ : ℕ} {j : iota} {m : ℕ → ℕ}
    {a : ∀ n, Fin (m n) → EuclideanSpace ℝ iota} {n : ℕ} (hn : N₀ ≤ n) :
    safePaddedCoefficients N₀ j m a n = a n := if_pos hn

theorem safePaddedVector_lt {N₀ : ℕ} {v₀ : iota → E} {v : ℕ → iota → E}
    {n : ℕ} (hn : n < N₀) : safePaddedVector N₀ v₀ v n = v₀ :=
  if_neg (Nat.not_le.mpr hn)

theorem safePaddedWeights_lt {N₀ : ℕ} {m : ℕ → ℕ} {w : ∀ n, Fin (m n) → ℝ}
    {n : ℕ} (hn : n < N₀) : safePaddedWeights N₀ m w n = fun _ => 1 :=
  if_neg (Nat.not_le.mpr hn)

theorem safePaddedCoefficients_lt {N₀ : ℕ} {j : iota} {m : ℕ → ℕ}
    {a : ∀ n, Fin (m n) → EuclideanSpace ℝ iota} {n : ℕ} (hn : n < N₀) :
    safePaddedCoefficients N₀ j m a n = fun (_ : Fin (m n)) =>
      EuclideanSpace.single j (1 : ℝ) :=
  if_neg (Nat.not_le.mpr hn)

/-- Every row of the padded array is nondegenerate: the repaired rows read
off the single safe coordinate `j` of `v₀`, and the original rows are kept
precisely where they were nondegenerate. -/
theorem safePadded_nondegenerate (N₀ : ℕ) (j : iota) (v₀ : iota → E)
    (hv₀ : v₀ j ≠ 0) (m : ℕ → ℕ) (v : ℕ → iota → E)
    (w : ∀ n, Fin (m n) → ℝ) (a : ∀ n, Fin (m n) → EuclideanSpace ℝ iota)
    (ha : ∀ n ≥ N₀, ∀ k : Fin (m n), ∑ i, a n k i • v n i ≠ 0)
    (n : ℕ) (k : Fin (m n)) :
    ∑ i, safePaddedCoefficients N₀ j m a n k i
        • safePaddedVector N₀ v₀ v n i ≠ 0 := by
  rcases Nat.lt_or_ge n N₀ with hlt | hge
  · rw [safePaddedCoefficients_lt hlt, safePaddedVector_lt hlt]
    simp only [PiLp.single_apply, ite_smul, one_smul, zero_smul]
    simp
    exact hv₀
  · rw [safePaddedCoefficients_eq hge, safePaddedVector_eq hge]
    exact ha n hge k

/-- On the stabilized range the padded matrix array is the original one. -/
theorem safePadded_weightedFeatureQuadraticMatrix_eq (N₀ : ℕ) (j : iota)
    (v₀ : iota → E) (m : ℕ → ℕ) (v : ℕ → iota → E)
    (w : ∀ n, Fin (m n) → ℝ) (a : ∀ n, Fin (m n) → EuclideanSpace ℝ iota)
    {n : ℕ} (hn : N₀ ≤ n) :
    weightedFeatureQuadraticMatrix (safePaddedVector N₀ v₀ v n)
        (safePaddedCoefficients N₀ j m a n) (safePaddedWeights N₀ m w n)
      = weightedFeatureQuadraticMatrix (v n) (a n) (w n) := by
  rw [safePaddedVector_eq hn, safePaddedCoefficients_eq hn, safePaddedWeights_eq hn]

/-- The Hermitian eigenvalues are insensitive to the padding: past `N₀` the
padded and original matrices coincide, and `IsHermitian.eigenvalues` only
depends on the underlying matrix (proof irrelevance). -/
theorem safePadded_eigenvalues_eq (N₀ : ℕ) (j : iota) (v₀ : iota → E)
    (m : ℕ → ℕ) (v : ℕ → iota → E)
    (w : ∀ n, Fin (m n) → ℝ) (a : ∀ n, Fin (m n) → EuclideanSpace ℝ iota)
    {n : ℕ} (hn : N₀ ≤ n) :
    (weightedFeatureQuadraticMatrix_isHermitian
        (safePaddedVector N₀ v₀ v n) (safePaddedCoefficients N₀ j m a n)
        (safePaddedWeights N₀ m w n)).eigenvalues
      = (weightedFeatureQuadraticMatrix_isHermitian (v n) (a n) (w n)).eigenvalues := by
  -- Eigenvalues depend only on the underlying matrix (via the characteristic
  -- polynomial), so the padded and original matrices share them eventually.
  rw [Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff,
    safePadded_weightedFeatureQuadraticMatrix_eq N₀ j v₀ m v w a hn]

/-- Measurability of the quadratic statistic, measure-independently (it is a
polynomial in the observations), so that it may be invoked on rows whose
feature arrays have been repaired. -/
theorem measurable_gaussianLogQuadraticStatistic
    (v : iota → E) (a : kappa → EuclideanSpace ℝ iota) (w : kappa → ℝ) :
    Measurable (gaussianLogQuadraticStatistic v w a) := by
  have hF : Measurable (centeredSpectralSquares w) := by
    unfold centeredSpectralSquares
    exact Finset.measurable_sum _ fun k _ => by fun_prop
  have hL : Measurable (standardizedFeatureObservationMap v a) :=
    (standardizedFeatureObservationMap v a).continuous.measurable
  have heq : gaussianLogQuadraticStatistic v w a
      = fun x => centeredSpectralSquares w (standardizedFeatureObservationMap v a x) :=
    funext (gaussianLogQuadraticStatistic_factor_observationMap v a w)
  rw [heq]
  exact hF.comp hL

/-! ### 3. The eventual-nondegeneracy corollary -/

/-- The quadratic-statistic consumption theorem with only *eventual*
nondegeneracy: `∑ i, a n k i • v n i ≠ 0` is required solely for `n ≥ N₀`.
The finitely many failing rows are repaired by fixed degenerate-safe data
(weight `1`, coefficient rows reading off a single nonzero coordinate `j` of a
fixed vector `v₀`); the asymptotic spectral inputs are transported across the
resulting eventual equality, and the conclusion is transferred back to the
original statistic, which agrees with the padded one eventually. -/
theorem gaussianLogQuadraticStatistic_tendsto_secondChaos_of_eventually_nondegenerate
    (m : ℕ → ℕ)
    (v : ℕ → iota → E) (w : ∀ n, Fin (m n) → ℝ)
    (a : ∀ n, Fin (m n) → EuclideanSpace ℝ iota)
    (v₀ : iota → E) (j : iota) (hv₀ : v₀ j ≠ 0) (N₀ : ℕ)
    (ha : ∀ n ≥ N₀, ∀ k : Fin (m n), ∑ i, a n k i • v n i ≠ 0)
    {Theta : Type*} [MeasurableSpace Theta]
    (P' : Measure Theta) [IsProbabilityMeasure P']
    (Q : Theta → ℝ) (lambda : ℕ → ℝ)
    (hQ : IsSecondChaosSeriesLaw P' Q lambda)
    (hm : Tendsto m atTop atTop)
    (hcoeff : ∀ j' : ℕ, Tendsto (fun n ↦ if hj : j' < m n then
        (weightedFeatureQuadraticMatrix_isHermitian (v n) (a n) (w n)).eigenvalues
          ((decreasingSpectralPerm
            (weightedFeatureQuadraticMatrix_isHermitian (v n) (a n) (w n)).eigenvalues)
          ⟨j', hj⟩) else 0)
      atTop (𝓝 (lambda j')))
    (htr2 : Tendsto (fun n ↦ ∑ i : Fin (m n), ∑ j' : Fin (m n),
        w n i * w n j' * (featureCorrelation (v n) (a n i) (a n j')) ^ 2)
      atTop (𝓝 (∑' j' : ℕ, lambda j' ^ 2))) :
    TendstoInDistribution
      (fun (n : ℕ) x => gaussianLogQuadraticStatistic (v n) (w n) (a n) x)
      atTop Q (fun n => featureGaussian (v n)) P' := by
  have hev : ∀ n, N₀ ≤ n →
      safePaddedWeights N₀ m w n = w n
        ∧ safePaddedCoefficients N₀ j m a n = a n
        ∧ safePaddedVector N₀ v₀ v n = v n :=
    fun n hn => ⟨safePaddedWeights_eq hn, safePaddedCoefficients_eq hn,
      safePaddedVector_eq hn⟩
  -- The asymptotic inputs transport to the padded array.
  have hcoeff' : ∀ j' : ℕ, Tendsto (fun n ↦ if hj : j' < m n then
      (weightedFeatureQuadraticMatrix_isHermitian
        (safePaddedVector N₀ v₀ v n) (safePaddedCoefficients N₀ j m a n)
        (safePaddedWeights N₀ m w n)).eigenvalues
        ((decreasingSpectralPerm
          (weightedFeatureQuadraticMatrix_isHermitian
            (safePaddedVector N₀ v₀ v n) (safePaddedCoefficients N₀ j m a n)
            (safePaddedWeights N₀ m w n)).eigenvalues)
        ⟨j', hj⟩) else 0)
      atTop (𝓝 (lambda j')) := by
    intro j'
    refine Tendsto.congr' ?_ (hcoeff j')
    filter_upwards [Ici_mem_atTop N₀] with n hn
    rw [safePadded_eigenvalues_eq N₀ j v₀ m v w a hn]
  have htr2' : Tendsto (fun n ↦ ∑ i : Fin (m n), ∑ j' : Fin (m n),
      safePaddedWeights N₀ m w n i * safePaddedWeights N₀ m w n j'
        * (featureCorrelation (safePaddedVector N₀ v₀ v n)
            (safePaddedCoefficients N₀ j m a n i)
            (safePaddedCoefficients N₀ j m a n j')) ^ 2)
      atTop (𝓝 (∑' j' : ℕ, lambda j' ^ 2)) := by
    refine Tendsto.congr' ?_ htr2
    filter_upwards [Ici_mem_atTop N₀] with n hn
    rw [safePaddedWeights_eq hn, safePaddedVector_eq hn, safePaddedCoefficients_eq hn]
  -- The global consumption theorem applied to the padded array.
  have hpadded := gaussianLogQuadraticStatistic_tendsto_secondChaos_of_decreasing_matching
    m (safePaddedVector N₀ v₀ v) (safePaddedWeights N₀ m w)
    (safePaddedCoefficients N₀ j m a)
    (safePadded_nondegenerate N₀ j v₀ hv₀ m v w a ha)
    P' Q lambda hQ hm hcoeff' htr2'
  -- Step 1: repair the row measures (`featureGaussian` of the padded vector).
  have hstep1 : TendstoInDistribution
      (fun (n : ℕ) x => gaussianLogQuadraticStatistic (safePaddedVector N₀ v₀ v n)
        (safePaddedWeights N₀ m w n) (safePaddedCoefficients N₀ j m a n) x)
      atTop Q (fun n => featureGaussian (v n)) P' :=
    tendstoInDistribution_of_eventually_row_eq
      (fun n x => gaussianLogQuadraticStatistic (safePaddedVector N₀ v₀ v n)
        (safePaddedWeights N₀ m w n) (safePaddedCoefficients N₀ j m a n) x)
      (fun n x => gaussianLogQuadraticStatistic (safePaddedVector N₀ v₀ v n)
        (safePaddedWeights N₀ m w n) (safePaddedCoefficients N₀ j m a n) x)
      Q atTop hpadded
      (fun n => (measurable_gaussianLogQuadraticStatistic _ _ _).aemeasurable)
      (Eventually.of_forall fun _ => rfl)
      (by
        filter_upwards [Ici_mem_atTop N₀] with n hn
        rw [safePaddedVector_eq hn])
  -- Step 2: the original statistic agrees with the padded one eventually.
  exact tendstoInDistribution_congr_eventually
    (fun n => featureGaussian (v n)) P'
    (fun n x => gaussianLogQuadraticStatistic (safePaddedVector N₀ v₀ v n)
      (safePaddedWeights N₀ m w n) (safePaddedCoefficients N₀ j m a n) x)
    (fun n x => gaussianLogQuadraticStatistic (v n) (w n) (a n) x)
    Q atTop
    (fun n => (measurable_gaussianLogQuadraticStatistic _ _ _).aemeasurable)
    (by
      filter_upwards [Ici_mem_atTop N₀] with n hn
      obtain ⟨hw, hac, hv⟩ := hev n hn
      exact Eventually.of_forall fun x => by
        rw [hv, hw, hac])
    hstep1

end Hurst
