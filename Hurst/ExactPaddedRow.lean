import Hurst.PaddedAsymptotics
import Hurst.DenseRowOverride

noncomputable section
open Filter MeasureTheory
open scoped RealInnerProductSpace Topology
namespace Hurst

local instance (p : Prop) : Decidable p := Classical.propDecidable p

def emptyFeatureRow (E : Type*) : Fin 0 → E := fun i => Fin.elim0 i

/-- Turn a selected variable-size feature row into an exact `Fin N` row.
When the selected row fits, append independent unit directions and cast along
`m + (N-m) = N`; the irrelevant finite prefix falls back to a fully
independent row. -/
def exactPaddedFeatureRow
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ → ℕ) (u : ∀ n, Fin (m n) → E) (s : ℕ → ℕ)
    (N : ℕ) (i : Fin N) :
    WithLp 2 (E × Lp ℝ 2 (volume : Measure ℝ)) :=
  if h : m (s N) ≤ N then
    paddedFeatureRow (u (s N)) (N - m (s N))
      (finCongr (Nat.add_sub_of_le h).symm i)
  else
    paddedFeatureRow (emptyFeatureRow E) N
      (finCongr (Nat.zero_add N).symm i)

def exactPaddedCoefficientRow
    (m : ℕ → ℕ) (c : ∀ n, Fin (m n) → ℝ) (g : ℝ → ℝ)
    (s : ℕ → ℕ) (N : ℕ) (i : Fin N) : ℝ :=
  if h : m (s N) ≤ N then
    paddedCoefficientRow (c (s N)) g (N - m (s N))
      (finCongr (Nat.add_sub_of_le h).symm i)
  else g (((i.val : ℝ) + 1) / (N : ℝ))

@[simp] theorem exactPaddedFeatureRow_of_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ → ℕ) (u : ∀ n, Fin (m n) → E) (s : ℕ → ℕ)
    (N : ℕ) (h : m (s N) ≤ N) (i : Fin N) :
    exactPaddedFeatureRow m u s N i =
      paddedFeatureRow (u (s N)) (N - m (s N))
        (finCongr (Nat.add_sub_of_le h).symm i) := by
  simp [exactPaddedFeatureRow, h]

@[simp] theorem exactPaddedCoefficientRow_of_le
    (m : ℕ → ℕ) (c : ∀ n, Fin (m n) → ℝ) (g : ℝ → ℝ)
    (s : ℕ → ℕ) (N : ℕ) (h : m (s N) ≤ N) (i : Fin N) :
    exactPaddedCoefficientRow m c g s N i =
      paddedCoefficientRow (c (s N)) g (N - m (s N))
        (finCongr (Nat.add_sub_of_le h).symm i) := by
  simp [exactPaddedCoefficientRow, h]

theorem exactPaddedFeatureRow_norm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ → ℕ) (u : ∀ n, Fin (m n) → E)
    (hu : ∀ n i, ‖u n i‖ = 1) (s : ℕ → ℕ) (N : ℕ) :
    ∀ i, ‖exactPaddedFeatureRow m u s N i‖ = 1 := by
  intro i
  unfold exactPaddedFeatureRow
  split_ifs with h
  · exact paddedFeatureRow_norm (u (s N)) (hu (s N)) _ _
  · exact paddedFeatureRow_norm (emptyFeatureRow E) (fun i => Fin.elim0 i) _ _

/-- On every fitting row, exact-index correlations are the padded
correlations transported by the canonical `Fin` equivalence. -/
theorem exactPaddedFeatureRow_correlation_of_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ → ℕ) (u : ∀ n, Fin (m n) → E)
    (hu : ∀ n i, ‖u n i‖ = 1) (s : ℕ → ℕ)
    (N : ℕ) (h : m (s N) ≤ N) (i j : Fin N) :
    featureCorrelation (exactPaddedFeatureRow m u s N)
        (EuclideanSpace.basisFun (Fin N) ℝ i)
        (EuclideanSpace.basisFun (Fin N) ℝ j) =
      featureCorrelation
        (paddedFeatureRow (u (s N)) (N - m (s N)))
        (EuclideanSpace.basisFun (Fin (m (s N) + (N - m (s N)))) ℝ
          (finCongr (Nat.add_sub_of_le h).symm i))
        (EuclideanSpace.basisFun (Fin (m (s N) + (N - m (s N)))) ℝ
          (finCongr (Nat.add_sub_of_le h).symm j)) := by
  rw [featureCorrelation_basis_eq_inner_of_norm_one _
      (exactPaddedFeatureRow_norm m u hu s N),
    featureCorrelation_basis_eq_inner_of_norm_one _
      (paddedFeatureRow_norm (u (s N)) (hu (s N)) _)]
  simp only [exactPaddedFeatureRow_of_le m u s N h]

/-- Dense exact-row padding preserves a uniformly continuous scalar profile.
This is the coefficient-level form of B&S (3.9). -/
theorem exactPaddedCoefficientRow_uniform_tendsto
    (m : ℕ → ℕ) (c : ∀ n, Fin (m n) → ℝ) (g : ℝ → ℝ)
    (s : ℕ → ℕ) (hs : Tendsto s atTop atTop)
    (hm : ∀ᶠ n in atTop, 0 < m n)
    (hfit : ∀ᶠ N in atTop, m (s N) ≤ N)
    (hratio : Tendsto (fun N : ℕ => (m (s N) : ℝ) / (N : ℝ))
      atTop (𝓝 1))
    (hg : UniformContinuous g)
    (hc : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ i : Fin (m n),
      |c n i - g (((i.val : ℝ) + 1) / m n)| ≤ ε) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ i : Fin N,
      |exactPaddedCoefficientRow m c g s N i -
        g (((i.val : ℝ) + 1) / N)| ≤ ε := by
  let ms : ℕ → ℕ := fun N => m (s N)
  let d : ℕ → ℕ := fun N => N - ms N
  have hms : ∀ᶠ N in atTop, 0 < ms N := hm.filter_mono hs
  have hratio' : Tendsto (fun N : ℕ => (ms N : ℝ) / (ms N + d N : ℝ))
      atTop (𝓝 1) := by
    apply hratio.congr'
    filter_upwards [hfit] with N hN
    dsimp only [ms, d]
    rw [← Nat.cast_add, Nat.add_sub_of_le hN]
  have hdm := padding_to_retained_ratio_tendsto_zero ms d hms hratio'
  have hcsel : ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ i : Fin (ms N),
      |c (s N) i - g (((i.val : ℝ) + 1) / ms N)| ≤ ε := by
    intro ε hε
    exact (hc ε hε).filter_mono hs
  have hpad := paddedCoefficientRow_uniform_tendsto ms d
    (fun N => c (s N)) g hms hdm hg hcsel
  intro ε hε
  have hp := hpad ε hε
  filter_upwards [hfit, hp] with N hN hpN
  intro i
  have hEq : ms N + d N = N := by
    dsimp only [ms, d]
    exact Nat.add_sub_of_le hN
  have hi := hpN (finCongr hEq.symm i)
  have hEqR : (ms N : ℝ) + (d N : ℝ) = N := by exact_mod_cast hEq
  rw [hEqR] at hi
  rw [exactPaddedCoefficientRow_of_le m c g s N hN]
  simpa only [ms, d, finCongr_apply, Fin.val_cast] using hi

end Hurst
