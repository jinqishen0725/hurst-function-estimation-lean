import Hurst.FirstStrideNormalize
import Hurst.GridLogVariance
import Hurst.HolderRegularity

noncomputable section
open Set MeasureTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

def strideFirstLeft (n d : ℕ) (i : Fin (n-d)) : Fin n := ⟨i.val, by have := i.isLt; omega⟩
def strideFirstRight (n d : ℕ) (i : Fin (n-d)) : Fin n := ⟨i.val+d, by have := i.isLt; omega⟩

theorem grid_stride_first_step (n d : ℕ) (i : Fin (n-d)) :
    grid n (strideFirstRight n d i).val = grid n i.val+(d:ℝ)/n := by
  simp only [grid, strideFirstRight, Nat.cast_add]
  ring

def gridStrideFirstActual (n d : ℕ) (H : Fin n → Ioo (0:ℝ) 1) (i : Fin (n-d)) : Lp ℂ 2 (volume : Measure ℝ) :=
  normalizedVaryingIncrement (H (strideFirstLeft n d i)) (H (strideFirstRight n d i)) (grid n i.val) ((d:ℝ)/n)

def gridStrideFirstCoefficients (n d : ℕ) (i : Fin (n-d)) : EuclideanSpace ℝ (Fin n) :=
  observationDifferenceWeights (strideFirstLeft n d i) (strideFirstRight n d i)

theorem gridStrideFirst_feature_identity (n d : ℕ) (hn : 0 < n) (hd : 0 < d)
    (H : Fin n → Ioo (0:ℝ) 1) (i : Fin (n-d)) :
    (∑ j, gridStrideFirstCoefficients n d i j • gridObservationFeatures n H j) =
      ((d:ℝ)/n)^(H (strideFirstLeft n d i):ℝ) • gridStrideFirstActual n d H i := by
  rw [gridStrideFirstCoefficients, observationDifferenceWeights_feature]
  unfold gridObservationFeatures
  rw [grid_stride_first_step]
  exact varyingIncrement_normalized_identity _ _ _ _ (by positivity)

theorem hurstHolder_stride_first_covariance (p a b M : ℝ) (hp : 1 ≤ p)
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M) (d : ℕ) (hd : 0 < d) :
    ∃ C ≥ 0, ∀ n : ℕ, 0 < n → ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0:ℝ) 1) (Icc a b) → ∀ i j : Fin (n-d),
      |⟪gridStrideFirstActual n d (midpointSampleHurst f hf.1 n) i,
          gridStrideFirstActual n d (midpointSampleHurst f hf.1 n) j⟫-
       ⟪normalizedFrozenIncrement (midpointSampleHurst f hf.1 n (strideFirstLeft n d i)) (grid n i.val) ((d:ℝ)/n),
          normalizedFrozenIncrement (midpointSampleHurst f hf.1 n (strideFirstLeft n d j)) (grid n j.val) ((d:ℝ)/n)⟫| ≤
        gridCovarianceError b C n := by
  obtain ⟨D,hD,hLip⟩ := hurstHolder_uniform_lower_derivative_lipschitz p hp
  obtain ⟨C,hC,hcov⟩ := normalized_stride_covariance_perturbation a b (D*(1+M)*d) d
    (by exact_mod_cast (show 1 ≤ d by omega)) ha hb hab (by positivity)
  refine ⟨C,hC,?_⟩
  intro n hn f hf hF i j
  let H := midpointSampleHurst f hf.1 n
  have hloc (i : Fin (n-d)) : grid n i.val ∈ Icc (0:ℝ) 1 ∧ grid n i.val+(d:ℝ)/n ∈ Icc (0:ℝ) 1 := by
    have hl := grid_mem n i.val hn (strideFirstLeft n d i).isLt
    have hr := grid_mem n _ hn (strideFirstRight n d i).isLt
    rw [grid_stride_first_step] at hr
    exact ⟨⟨hl.1.le,hl.2.le⟩,⟨hr.1.le,hr.2.le⟩⟩
  have hmesh (i : Fin (n-d)) : halfMeshPoint n (grid n i.val+(d:ℝ)/n) := by
    rw [← grid_stride_first_step]
    exact halfMeshPoint_grid n _
  have hstep (i : Fin (n-d)) : |(H (strideFirstRight n d i):ℝ)-H (strideFirstLeft n d i)| ≤ (D*(1+M)*d)/n := by
    have hl := grid_mem n _ hn (strideFirstLeft n d i).isLt
    have hr := grid_mem n _ hn (strideFirstRight n d i).isLt
    have he := hLip M hM f hf 0 (by have := hurstHolder_floor_pos p hp; omega) _ hl _ hr
    simp only [iteratedDeriv_zero, grid_stride_first_step, strideFirstLeft, add_sub_cancel_left, abs_of_nonneg (by positivity : 0 ≤ (d:ℝ)/n)] at he
    change |f (grid n (strideFirstRight n d i).val)-f (grid n i.val)| ≤ _
    rw [grid_stride_first_step]
    exact he.trans_eq (by ring)
  exact hcov n hn (H (strideFirstLeft n d i)) (H (strideFirstRight n d i))
    (H (strideFirstLeft n d j)) (H (strideFirstRight n d j))
    (hF (grid_mem n _ hn (strideFirstLeft n d i).isLt)) (hF (grid_mem n _ hn (strideFirstRight n d i).isLt))
    (hF (grid_mem n _ hn (strideFirstLeft n d j).isLt)) (hF (grid_mem n _ hn (strideFirstRight n d j).isLt))
    _ _ (hloc i).1 (hloc i).2 (hloc j).1 (hloc j).2
    (halfMeshPoint_grid n _) (hmesh i) (halfMeshPoint_grid n _) (hmesh j) (hstep i) (hstep j)

end Hurst
