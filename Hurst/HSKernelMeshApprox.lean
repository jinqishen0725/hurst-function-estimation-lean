import Hurst.HSOperatorLayer3

/-!
# HS kernel mesh approximation: continuous kernels are `hsNorm`-approximated by
degenerate (finite-rank) mesh kernels

This file closes the mesh input of the compactness program (see the tail docstring of
`Hurst.HSOperatorLayer3`): for a continuous kernel `K` and `ε > 0` we partition
`Icc (-1) 1` into `n` half-open subintervals `I_i = [x_i, x_{i+1})`,
`x_i = -1 + 2i/n`, and approximate `K` by the piecewise-constant kernel

`meshKernel K n (x, y) = ∑_{i, j < n} K (x_i, x_j) • 1_{I_i} (x) • 1_{I_j} (y)`.

Uniform continuity of `K` on the compact square gives `|K - meshKernel K n| < ε/2`
off the null grid, the grid has measure zero, and hence
`∫∫ (K - meshKernel K n)² ≤ (ε/2)² · 4 = ε²`, i.e. `hsNorm (K - meshKernel K n) ≤ ε`.

## Main results

* `hsKernel_meshKernel` — the mesh kernel is a Hilbert–Schmidt kernel, in fact degenerate.
* `hsKernel_mesh_approx` — for every `ε > 0` there is a mesh kernel `K_n` with
  `hsNorm (K - K_n) ≤ ε`, and `K_n` is degenerate in exactly the shape consumed by
  `hsKernel_degenerate` (finite sum of `a ⊗ b` with `a, b` `L²(vol)`).
* `continuous_kernel_compact` — **continuous kernel ⇒ compact operator** (item (1) of the
  layer-3 gap report), via `isCompactOperator_TOp_limit` at the rate `1/(n+1)`.
-/

open MeasureTheory Measure Real Set
open scoped Real

noncomputable section

namespace HS

/-! ### The uniform grid on `[-1, 1]` -/

/-- The `i`-th grid point of the uniform partition of `[-1, 1]` into `n` pieces. -/
def gridPt (n : ℕ) (i : ℕ) : ℝ := -1 + (2 * (i : ℝ)) / (n : ℝ)

private theorem gridPt_le_gridPt {n : ℕ} (hn : 0 < n) {i k : ℕ} (h : i ≤ k) :
    gridPt n i ≤ gridPt n k := by
  have h2 : (2:ℝ) * i / (n:ℝ) ≤ (2:ℝ) * k / (n:ℝ) := by
    rw [div_le_div_iff_of_pos_right (by exact_mod_cast hn)]
    have h22 : (2:ℕ) * i ≤ (2:ℕ) * k := by omega
    exact_mod_cast h22
  simp only [gridPt]
  linarith

private theorem gridPt_lt_gridPt {n : ℕ} (hn : 0 < n) {i k : ℕ} (h : i < k) :
    gridPt n i < gridPt n k := by
  have h2 : (2:ℝ) * i / (n:ℝ) < (2:ℝ) * k / (n:ℝ) := by
    rw [div_lt_div_iff_of_pos_right (by exact_mod_cast hn)]
    have h22 : (2:ℕ) * i < (2:ℕ) * k := by omega
    exact_mod_cast h22
  simp only [gridPt]
  linarith

private theorem gridPt_mem_I {n : ℕ} (hn : 0 < n) {i : ℕ} (h : i ≤ n) : gridPt n i ∈ I := by
  have h0 : (0:ℝ) ≤ (2:ℝ) * i := by positivity
  have hdiv : (0:ℝ) ≤ (2:ℝ) * i / n := div_nonneg h0 (by exact_mod_cast hn.le)
  have h1 : (2:ℝ) * i / n ≤ 2 := by
    rw [div_le_iff₀ (by exact_mod_cast hn)]
    have h2 : (2:ℕ) * i ≤ (2:ℕ) * n := by omega
    exact_mod_cast h2
  simp only [gridPt]
  exact ⟨by linarith, by linarith⟩

private theorem gridCell_subset {n : ℕ} (hn : 0 < n) {i : ℕ} (h : i < n) :
    Set.Ico (gridPt n i) (gridPt n (i + 1)) ⊆ I := by
  have h1 : gridPt n i ∈ I := gridPt_mem_I hn (by omega)
  have h2 : gridPt n (i + 1) ∈ I := gridPt_mem_I hn (by omega)
  intro x hx
  obtain ⟨hx1, hx2⟩ := Set.mem_Ico.mp hx
  exact ⟨le_trans h1.1 hx1, le_trans hx2.le h2.2⟩

private theorem gridPt_zero (n : ℕ) : gridPt n 0 = -1 := by
  simp [gridPt]

private theorem gridPt_top {n : ℕ} (hn : 0 < n) : gridPt n n = 1 := by
  simp only [gridPt]
  have hnR : ((n:ℕ):ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  norm_num

/-- Every point of the half-open interval lies in a mesh cell `[x_i, x_{i+1})` whose
left endpoint is within `δ`. -/
private theorem exists_grid_cell {n : ℕ} (hn : 0 < n) {δ x : ℝ} (hmesh : (2:ℝ) ≤ δ * (n:ℝ))
    (hx : x ∈ Set.Ico (-1:ℝ) 1) :
    ∃ i : ℕ, i < n ∧ gridPt n i ≤ x ∧ x < gridPt n (i + 1) ∧ x - gridPt n i < δ := by
  have hnR : ((n:ℕ):ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnR' : (0:ℝ) < (n:ℝ) := Nat.cast_pos.mpr hn
  have hx1 : -1 ≤ x := hx.1
  have hx2 : x < 1 := hx.2
  set t := (x + 1) * (n:ℝ) / 2 with ht
  have ht0 : (0:ℝ) ≤ t := by
    rw [ht]
    exact div_nonneg (by nlinarith) (by positivity)
  have htn : t < (n:ℝ) := by
    rw [ht, div_lt_iff₀ (by norm_num : (0:ℝ) < 2)]
    calc (x + 1) * (n:ℝ) < 2 * (n:ℝ) := by nlinarith
      _ = (n:ℝ) * 2 := by ring
  have hfl : ((Nat.floor t : ℕ) : ℝ) ≤ t := Nat.floor_le ht0
  have hfl1 : t < ((Nat.floor t : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one t
  have hxe : x = -1 + (2:ℝ) * t / (n:ℝ) := by rw [ht]; field_simp; norm_num
  have hfloor : (2:ℝ) * ((Nat.floor t : ℕ) : ℝ) / (n:ℝ) ≤ (2:ℝ) * t / (n:ℝ) := by
    rw [div_le_div_iff_of_pos_right hnR']
    exact mul_le_mul_of_nonneg_left hfl zero_le_two
  have hfloor2 : (2:ℝ) * t / (n:ℝ) < (2:ℝ) * ((Nat.floor t + 1 : ℕ) : ℝ) / (n:ℝ) := by
    rw [div_lt_div_iff_of_pos_right hnR']
    have hcast : (((Nat.floor t + 1 : ℕ) : ℕ) : ℝ) = ((Nat.floor t : ℕ) : ℝ) + 1 := by
      push_cast
      ring
    rw [hcast]
    exact mul_lt_mul_of_pos_left hfl1 zero_lt_two
  have hxg : x - gridPt n (Nat.floor t) = (2:ℝ) * (t - ((Nat.floor t : ℕ) : ℝ)) / (n:ℝ) := by
    simp only [gridPt]
    rw [hxe]
    field_simp
    ring
  refine ⟨Nat.floor t, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast lt_of_le_of_lt hfl htn
  · simp only [gridPt]
    rw [hxe]
    linarith
  · simp only [gridPt]
    rw [hxe]
    linarith
  · have hlt1 : t - ((Nat.floor t : ℕ) : ℝ) < 1 := by linarith
    have h2n : (2:ℝ) / (n:ℝ) ≤ δ := (div_le_iff₀ hnR').mpr hmesh
    rw [hxg]
    refine lt_of_lt_of_le (div_lt_div_iff_of_pos_right hnR' |>.mpr ?_) h2n
    linarith

/-- Distinct mesh cells are disjoint (as left-closed right-open intervals). -/
private theorem not_mem_gridCell {n : ℕ} (hn : 0 < n) {i k : ℕ} (hik : k ≠ i) {x : ℝ}
    (hx : gridPt n i ≤ x) (hx' : x < gridPt n (i + 1)) :
    x ∉ Set.Ico (gridPt n k) (gridPt n (k + 1)) := by
  intro hmem
  obtain ⟨hm1, hm2⟩ := Set.mem_Ico.mp hmem
  by_cases hlt : k < i
  · have hle : gridPt n (k + 1) ≤ gridPt n i := gridPt_le_gridPt hn (by omega)
    exact absurd hm2 (by linarith [gridPt_lt_gridPt hn hlt, hle, hx])
  · have hik2 : i < k := by omega
    have hle : gridPt n (i + 1) ≤ gridPt n k := gridPt_le_gridPt hn (by omega)
    exact absurd hm1 (by linarith [hx', hle])

/-! ### Measure-zero helpers -/

/-- The Lebesgue measure of a finite set of reals is zero. -/
private theorem volume_finset_zero (s : Finset ℝ) : volume (s : Set ℝ) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
      have hset : ((insert a s : Finset ℝ) : Set ℝ) = {a} ∪ (s : Set ℝ) := by simp
      rw [hset]
      have h1 : volume ({a} ∪ (s : Set ℝ)) ≤ volume {a} + volume ((s : Set ℝ)) :=
        MeasureTheory.measure_union_le _ _
      simp only [Real.volume_singleton, ih, add_zero] at h1
      exact le_antisymm h1 (by simp)

/-- A function supported (via an indicator factor) on a `vol2`-null set vanishes a.e. -/
private theorem mul_indicator_ae_zero {N : Set (ℝ × ℝ)} {u : ℝ × ℝ → ℝ} (hN : vol2 N = 0) :
    (fun p => u p * Set.indicator N (fun _ : ℝ × ℝ => (1:ℝ)) p) =ᵐ[vol2]
      (fun _ : ℝ × ℝ => (0:ℝ)) := by
  have h' : ∀ᵐ p : ℝ × ℝ ∂vol2, u p * Set.indicator N (fun _ : ℝ × ℝ => (1:ℝ)) p = (0:ℝ) := by
    rw [MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null ?_ hN
    intro p hp
    by_contra hpn
    exact hp (by simp [Set.indicator_of_notMem hpn])
  exact h'

/-- A function supported (via an indicator factor) on a `vol2`-null set has zero integral. -/
private theorem integral_mul_indicator_eq_zero {N : Set (ℝ × ℝ)} {u : ℝ × ℝ → ℝ}
    (hN : vol2 N = 0) :
    ∫ p : ℝ × ℝ, u p * Set.indicator N (fun _ : ℝ × ℝ => (1:ℝ)) p ∂vol2 = 0 := by
  have h' : ∀ᵐ p : ℝ × ℝ ∂vol2, u p * Set.indicator N (fun _ : ℝ × ℝ => (1:ℝ)) p = (0:ℝ) := by
    rw [MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null ?_ hN
    intro p hp
    by_contra hpn
    exact hp (by simp [Set.indicator_of_notMem hpn])
  exact (MeasureTheory.integral_congr_ae h').trans (MeasureTheory.integral_zero _ _)

/-- Indicators of arbitrary measurable sets are `L²(vol)` (`vol` is finite). -/
private theorem memLp_indicator_cell {J : Set ℝ} (hJ : MeasurableSet J) :
    MemLp (Set.indicator J (fun _ : ℝ => (1:ℝ))) 2 vol := by
  have hme : Measurable (Set.indicator J (fun _ : ℝ => (1:ℝ))) :=
    measurable_const.indicator hJ
  have h2' : AEStronglyMeasurable
      (fun x : ℝ => (Set.indicator J (fun _ : ℝ => (1:ℝ)) x) ^ 2) vol := by
    have hm : AEStronglyMeasurable
        (fun x : ℝ => (Set.indicator J (fun _ : ℝ => (1:ℝ)) x) *
          (Set.indicator J (fun _ : ℝ => (1:ℝ)) x)) vol :=
      (hme.mul hme).aestronglyMeasurable
    exact hm.congr (Filter.Eventually.of_forall fun _x => (pow_two _).symm)
  refine memLp_two_of_aemeasurable hme.aestronglyMeasurable
    (Integrable.mono (integrable_const (1:ℝ)) h2' ?_)
  filter_upwards with x
  by_cases hx : x ∈ J <;> simp [hx]

/-- `hsNorm` is invariant under pointwise negation. -/
private theorem hsNorm_neg (u : ℝ × ℝ → ℝ) : hsNorm (fun p => -u p) = hsNorm u := by
  rw [hsNorm_def, hsNorm_def]
  refine congrArg Real.sqrt ?_
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => by simp)

/-! ### The mesh kernel -/

/-- The piecewise-constant mesh approximation of `K` on the uniform grid:
`∑_{i,j<n} K (x_i, x_j) · 1_{I_i}(x) · 1_{I_j}(y)`. -/
def meshKernel (K : ℝ × ℝ → ℝ) (n : ℕ) : ℝ × ℝ → ℝ := fun p =>
  ∑ q ∈ Finset.range n ×ˢ Finset.range n,
    K (gridPt n q.1, gridPt n q.2) *
      Set.indicator (Set.Ico (gridPt n q.1) (gridPt n (q.1 + 1))) (fun _ : ℝ => (1:ℝ)) p.1 *
      Set.indicator (Set.Ico (gridPt n q.2) (gridPt n (q.2 + 1))) (fun _ : ℝ => (1:ℝ)) p.2

/-- Collapse of the mesh sum at a point lying in the `(i, j)` cell. -/
private theorem meshKernel_eq_of_mem {K : ℝ × ℝ → ℝ} {n : ℕ} (hn : 0 < n) {i j : ℕ}
    (hi : i < n) (hj : j < n) {x y : ℝ} (hx : gridPt n i ≤ x) (hx' : x < gridPt n (i + 1))
    (hy : gridPt n j ≤ y) (hy' : y < gridPt n (j + 1)) :
    meshKernel K n (x, y) = K (gridPt n i, gridPt n j) := by
  simp only [meshKernel]
  refine (Finset.sum_eq_single_of_mem (i, j)
    (Finset.mem_product.mpr ⟨Finset.mem_range.mpr hi, Finset.mem_range.mpr hj⟩) ?_).trans ?_
  · intro q hq hne
    obtain ⟨hq1, hq2⟩ := Finset.mem_product.mp hq
    simp only [Finset.mem_range] at hq1 hq2
    by_cases hqi : q.1 = i
    · by_cases hqj : q.2 = j
      · exact absurd (by rw [show q = (q.1, q.2) from rfl, hqi, hqj]) hne
      · have hf : Set.indicator (Set.Ico (gridPt n q.2) (gridPt n (q.2 + 1)))
            (fun _ : ℝ => (1:ℝ)) y = 0 :=
          Set.indicator_of_notMem (not_mem_gridCell hn hqj hy hy') _
        simp [hf]
    · have hf : Set.indicator (Set.Ico (gridPt n q.1) (gridPt n (q.1 + 1)))
          (fun _ : ℝ => (1:ℝ)) x = 0 :=
        Set.indicator_of_notMem (not_mem_gridCell hn hqi hx hx') _
      simp [hf]
  · have hm1 : x ∈ Set.Ico (gridPt n i) (gridPt n (i + 1)) := ⟨hx, hx'⟩
    have hm2 : y ∈ Set.Ico (gridPt n j) (gridPt n (j + 1)) := ⟨hy, hy'⟩
    rw [Set.indicator_of_mem hm1, Set.indicator_of_mem hm2]
    simp

/-- One row of the mesh kernel, `K (x_i, x_j) • 1_{I_i}`, is `L²(vol)`. -/
private theorem memLp_meshRow (K : ℝ × ℝ → ℝ) (n : ℕ) (q : ℕ × ℕ) :
    MemLp (fun x : ℝ => K (gridPt n q.1, gridPt n q.2) *
      Set.indicator (Set.Ico (gridPt n q.1) (gridPt n (q.1 + 1))) (fun _ : ℝ => (1:ℝ)) x) 2 vol :=
  MemLp.const_smul
    (memLp_indicator_cell (J := Set.Ico (gridPt n q.1) (gridPt n (q.1 + 1)))
      measurableSet_Ico)
    (K (gridPt n q.1, gridPt n q.2))

theorem hsKernel_meshKernel (K : ℝ × ℝ → ℝ) (n : ℕ) : HSKernel (meshKernel K n) := by
  classical
  have hform : meshKernel K n = fun p => ∑ q ∈ Finset.range n ×ˢ Finset.range n,
      (fun q : ℕ × ℕ => K (gridPt n q.1, gridPt n q.2) •
        Set.indicator (Set.Ico (gridPt n q.1) (gridPt n (q.1 + 1))) (fun _ : ℝ => (1:ℝ))) q p.1 *
      ((fun q : ℕ × ℕ => Set.indicator (Set.Ico (gridPt n q.2) (gridPt n (q.2 + 1)))
        (fun _ : ℝ => (1:ℝ))) q p.2) := by
    funext p
    simp [meshKernel]
  rw [hform]
  refine hsKernel_degenerate (Finset.range n ×ˢ Finset.range n)
    (fun q : ℕ × ℕ => K (gridPt n q.1, gridPt n q.2) •
      Set.indicator (Set.Ico (gridPt n q.1) (gridPt n (q.1 + 1))) (fun _ : ℝ => (1:ℝ)))
    (fun q : ℕ × ℕ => Set.indicator (Set.Ico (gridPt n q.2) (gridPt n (q.2 + 1)))
      (fun _ : ℝ => (1:ℝ))) ?_ ?_
  · intro q
    exact memLp_meshRow K n q
  · intro q
    exact memLp_indicator_cell measurableSet_Ico

/-! ### The mesh approximation theorem -/

/-- **The mesh approximation lemma** (item (1) of the layer-3 gap report): a continuous
kernel is approximated in `hsNorm` by degenerate (finite-rank) mesh kernels of the form
`∑_{i,j<n} K (x_i, x_j) · 1_{I_i} ⊗ 1_{I_j}` with `x_i = -1 + 2i/n` and
`I_i = [x_i, x_{i+1})`. -/
theorem hsKernel_mesh_approx {K : ℝ × ℝ → ℝ} (hK : HSKernel K) (hKc : Continuous K) :
    ∀ ε > 0, ∃ L : ℝ × ℝ → ℝ, HSKernel L ∧ hsNorm (fun p => K p - L p) ≤ ε ∧
      ∃ (s : Finset (ℕ × ℕ)) (a b : ℕ × ℕ → ℝ → ℝ),
        (∀ q, MemLp (a q) 2 vol) ∧ (∀ q, MemLp (b q) 2 vol) ∧
        ∀ p, L p = ∑ q ∈ s, a q p.1 * b q p.2 := by
  intro ε hε
  have hε' : 0 < ε / 2 := by linarith
  -- uniform continuity of K on the compact square
  have hcomp : IsCompact (I ×ˢ I) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨δ, hδ, huc⟩ :=
    Metric.uniformContinuousOn_iff.mp (hcomp.uniformContinuousOn_of_continuous hKc.continuousOn)
      (ε / 2) hε'
  -- choose the mesh size
  obtain ⟨n, hn2⟩ := exists_nat_gt ((2:ℝ) / δ)
  have hn : 0 < n := by
    have h1 : (0:ℝ) < (2:ℝ) / δ := div_pos two_pos hδ
    exact Nat.cast_pos.mp (lt_trans h1 hn2)
  have hnR : (0:ℝ) < (n:ℝ) := Nat.cast_pos.mpr hn
  have hnδ : (2:ℝ) ≤ δ * (n:ℝ) := by
    have h2 := (div_lt_iff₀ hδ).mp hn2
    exact le_of_lt (mul_comm (n:ℝ) δ ▸ h2)
  refine ⟨meshKernel K n, hsKernel_meshKernel K n, ?_, Finset.range n ×ˢ Finset.range n,
    (fun q : ℕ × ℕ => K (gridPt n q.1, gridPt n q.2) •
      Set.indicator (Set.Ico (gridPt n q.1) (gridPt n (q.1 + 1))) (fun _ : ℝ => (1:ℝ))),
    (fun q : ℕ × ℕ => Set.indicator (Set.Ico (gridPt n q.2) (gridPt n (q.2 + 1)))
      (fun _ : ℝ => (1:ℝ))),
    fun q => memLp_meshRow K n q,
    fun q => memLp_indicator_cell measurableSet_Ico,
    fun p => by simp [meshKernel]⟩
  -- the four null bad-sets: grid column, grid row, and the two off-square strips
  set Gset : Set ℝ := ((Finset.range (n + 1)).image (gridPt n) : Set ℝ) with hGset
  have hGmeas : MeasurableSet Gset :=
    ((Finset.range (n + 1)).image (gridPt n)).finite_toSet.measurableSet
  have hGsub : Gset ⊆ I := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Finset.mem_image.mp hx
    simp only [Finset.mem_range] at hi
    rw [← hxi]
    exact gridPt_mem_I hn (by omega)
  have hvolG : vol Gset = 0 := by
    rw [Measure.restrict_apply hGmeas, Set.inter_eq_self_of_subset_left hGsub]
    exact volume_finset_zero _
  have hIc : vol (Iᶜ) = 0 := by rw [Measure.restrict_apply (measurableSet_Icc).compl]; simp
  have hN2 : vol2 (Gset ×ˢ I) = 0 := by rw [Measure.prod_prod, hvolG]; simp
  have hN3 : vol2 (I ×ˢ Gset) = 0 := by rw [Measure.prod_prod, hvolG]; simp
  have hN4 : vol2 (Iᶜ ×ˢ univ) = 0 := by rw [Measure.prod_prod, hIc]; simp
  have hN5 : vol2 (univ ×ˢ Iᶜ) = 0 := by rw [Measure.prod_prod, hIc]; simp
  -- the four error terms, each supported on a null set, and the pointwise majorizer
  set u2 : ℝ × ℝ → ℝ :=
    fun p => (K p - meshKernel K n p) ^ 2 * Set.indicator (Gset ×ˢ I) (fun _ : ℝ × ℝ => (1:ℝ)) p
    with hu2
  set u3 : ℝ × ℝ → ℝ :=
    fun p => (K p - meshKernel K n p) ^ 2 * Set.indicator (I ×ˢ Gset) (fun _ : ℝ × ℝ => (1:ℝ)) p
    with hu3
  set u4 : ℝ × ℝ → ℝ :=
    fun p => (K p - meshKernel K n p) ^ 2 * Set.indicator (Iᶜ ×ˢ univ) (fun _ : ℝ × ℝ => (1:ℝ)) p
    with hu4
  set u5 : ℝ × ℝ → ℝ :=
    fun p => (K p - meshKernel K n p) ^ 2 * Set.indicator (univ ×ˢ Iᶜ) (fun _ : ℝ × ℝ => (1:ℝ)) p
    with hu5
  have h2i : Integrable u2 vol2 :=
    (MeasureTheory.integrable_congr (mul_indicator_ae_zero hN2)).mpr
      (MeasureTheory.integrable_zero _ _ _)
  have h3i : Integrable u3 vol2 :=
    (MeasureTheory.integrable_congr (mul_indicator_ae_zero hN3)).mpr
      (MeasureTheory.integrable_zero _ _ _)
  have h4i : Integrable u4 vol2 :=
    (MeasureTheory.integrable_congr (mul_indicator_ae_zero hN4)).mpr
      (MeasureTheory.integrable_zero _ _ _)
  have h5i : Integrable u5 vol2 :=
    (MeasureTheory.integrable_congr (mul_indicator_ae_zero hN5)).mpr
      (MeasureTheory.integrable_zero _ _ _)
  set G : ℝ × ℝ → ℝ := (fun _ : ℝ × ℝ => ε ^ 2 / 4) + (u2 + (u3 + (u4 + u5))) with hGdef
  have hG : Integrable G vol2 := by
    rw [hGdef]
    exact (MeasureTheory.integrable_const _).add (h2i.add (h3i.add (h4i.add h5i)))
  -- the pointwise tower
  have hle : ∀ p : ℝ × ℝ, (K p - meshKernel K n p) ^ 2 ≤ G p := by
    intro p
    show (K p - meshKernel K n p) ^ 2 ≤ ε ^ 2 / 4 + (u2 p + (u3 p + (u4 p + u5 p)))
    have hpnn : ∀ N : Set (ℝ × ℝ),
        0 ≤ (K p - meshKernel K n p) ^ 2 * Set.indicator N (fun _ : ℝ × ℝ => (1:ℝ)) p := by
      intro N
      by_cases h : p ∈ N <;> simp [h, sq_nonneg]
    by_cases hp1 : p.1 ∈ I
    · by_cases hp2 : p.2 ∈ I
      · -- p on the square: either on a grid column/row (u2 or u3 fires) or a good point
        by_cases hg1 : p.1 ∈ Gset
        · have hm : p ∈ Gset ×ˢ I := ⟨hg1, hp2⟩
          have hfire : Set.indicator (Gset ×ˢ I) (fun _ : ℝ × ℝ => (1:ℝ)) p = 1 :=
            Set.indicator_of_mem hm _
          simp only [hu2, hu3, hu4, hu5, hfire, mul_one]
          linarith [hpnn (I ×ˢ Gset), hpnn (Iᶜ ×ˢ univ), hpnn (univ ×ˢ Iᶜ),
            sq_nonneg (K p - meshKernel K n p), (show (0:ℝ) ≤ ε ^ 2 / 4 by positivity)]
        · by_cases hg2 : p.2 ∈ Gset
          · have hm : p ∈ I ×ˢ Gset := ⟨hp1, hg2⟩
            have hfire : Set.indicator (I ×ˢ Gset) (fun _ : ℝ × ℝ => (1:ℝ)) p = 1 :=
              Set.indicator_of_mem hm _
            simp only [hu2, hu3, hu4, hu5, hfire, mul_one]
            linarith [hpnn (Gset ×ˢ I), hpnn (Iᶜ ×ˢ univ), hpnn (univ ×ˢ Iᶜ),
              sq_nonneg (K p - meshKernel K n p), (show (0:ℝ) ≤ ε ^ 2 / 4 by positivity)]
          · -- good point: collapse the mesh sum and use uniform continuity
            have hG0 : (-1:ℝ) ∈ Gset := by
              refine Finset.mem_image.mpr ⟨0, Finset.mem_range_succ_iff.mpr (by omega),
                gridPt_zero n⟩
            have hG1 : (1:ℝ) ∈ Gset := by
              refine Finset.mem_image.mpr ⟨n, Finset.self_mem_range_succ n, gridPt_top hn⟩
            have hp1Ico : p.1 ∈ Set.Ico (-1:ℝ) 1 :=
              ⟨hp1.1, lt_of_le_of_ne hp1.2 fun he => hg1 (by rw [he]; exact hG1)⟩
            have hp2Ico : p.2 ∈ Set.Ico (-1:ℝ) 1 :=
              ⟨hp2.1, lt_of_le_of_ne hp2.2 fun he => hg2 (by rw [he]; exact hG1)⟩
            obtain ⟨i, hi1, hi2, hi3, hi4⟩ := exists_grid_cell hn hnδ hp1Ico
            obtain ⟨j, hj1, hj2, hj3, hj4⟩ := exists_grid_cell hn hnδ hp2Ico
            have hcol : meshKernel K n p = K (gridPt n i, gridPt n j) :=
              meshKernel_eq_of_mem hn hi1 hj1 hi2 hi3 hj2 hj3
            have hd1 : dist (gridPt n i) p.1 < δ := by
              rw [Real.dist_eq, abs_of_nonpos (show gridPt n i - p.1 ≤ 0 by linarith [hi2])]
              linarith
            have hd2 : dist (gridPt n j) p.2 < δ := by
              rw [Real.dist_eq, abs_of_nonpos (show gridPt n j - p.2 ≤ 0 by linarith [hj2])]
              linarith
            have hdist : dist (gridPt n i, gridPt n j) p < δ := by
              rw [Prod.dist_eq]
              exact max_lt hd1 hd2
            have hmem1 : (gridPt n i, gridPt n j) ∈ I ×ˢ I :=
              ⟨gridPt_mem_I hn hi1.le, gridPt_mem_I hn hj1.le⟩
            have hmem2 : p ∈ I ×ˢ I := ⟨hp1, hp2⟩
            have habs : |K (gridPt n i, gridPt n j) - K p| < ε / 2 := by
              have hd0 := huc (gridPt n i, gridPt n j) hmem1 p hmem2 hdist
              rw [Real.dist_eq] at hd0
              exact hd0
            have htwo : |K p - K (gridPt n i, gridPt n j)| < ε / 2 := by
              rw [abs_sub_comm]; exact habs
            rcases abs_lt.mp htwo with ⟨ha1, ha2⟩
            simp only [hu2, hu3, hu4, hu5]
            rw [hcol]
            have hpnn' : ∀ N : Set (ℝ × ℝ),
                0 ≤ (K p - K (gridPt n i, gridPt n j)) ^ 2 *
                  Set.indicator N (fun _ : ℝ × ℝ => (1:ℝ)) p := by
              intro N
              by_cases h : p ∈ N <;> simp [h, sq_nonneg]
            have hsq : (K p - K (gridPt n i, gridPt n j)) ^ 2 < ε ^ 2 / 4 := by
              nlinarith
            linarith [hsq, hpnn' (Gset ×ˢ I), hpnn' (I ×ˢ Gset), hpnn' (Iᶜ ×ˢ univ),
              hpnn' (univ ×ˢ Iᶜ), (show (0:ℝ) ≤ ε ^ 2 / 4 by positivity)]
      · -- p.2 off the square: the other strip term fires
        have hm : p ∈ univ ×ˢ Iᶜ := ⟨Set.mem_univ _, by simpa using hp2⟩
        have hfire : Set.indicator (univ ×ˢ Iᶜ) (fun _ : ℝ × ℝ => (1:ℝ)) p = 1 :=
          Set.indicator_of_mem hm _
        simp only [hu2, hu3, hu4, hu5, hfire, mul_one]
        linarith [hpnn (Gset ×ˢ I), hpnn (I ×ˢ Gset), hpnn (Iᶜ ×ˢ univ),
          sq_nonneg (K p - meshKernel K n p), (show (0:ℝ) ≤ ε ^ 2 / 4 by positivity)]
    · by_cases hp2 : p.2 ∈ I
      · -- p.1 off the square: the strip term fires
        have hm : p ∈ Iᶜ ×ˢ univ := ⟨by simpa using hp1, Set.mem_univ _⟩
        have hfire : Set.indicator (Iᶜ ×ˢ univ) (fun _ : ℝ × ℝ => (1:ℝ)) p = 1 :=
          Set.indicator_of_mem hm _
        simp only [hu2, hu3, hu4, hu5, hfire, mul_one]
        linarith [hpnn (Gset ×ˢ I), hpnn (I ×ˢ Gset), hpnn (univ ×ˢ Iᶜ),
          sq_nonneg (K p - meshKernel K n p), (show (0:ℝ) ≤ ε ^ 2 / 4 by positivity)]
      · -- both coordinates off the square: a strip term fires
        have hm : p ∈ univ ×ˢ Iᶜ := ⟨Set.mem_univ _, by simpa using hp2⟩
        have hfire : Set.indicator (univ ×ˢ Iᶜ) (fun _ : ℝ × ℝ => (1:ℝ)) p = 1 :=
          Set.indicator_of_mem hm _
        simp only [hu2, hu3, hu4, hu5, hfire, mul_one]
        linarith [hpnn (Gset ×ˢ I), hpnn (I ×ˢ Gset), hpnn (Iᶜ ×ˢ univ),
          sq_nonneg (K p - meshKernel K n p), (show (0:ℝ) ≤ ε ^ 2 / 4 by positivity)]
  -- integrate the tower
  have hint : ∫ p : ℝ × ℝ, (K p - meshKernel K n p) ^ 2 ∂vol2 ≤ ∫ p : ℝ × ℝ, G p ∂vol2 :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun q => sq_nonneg _) hG
      (Filter.Eventually.of_forall hle)
  -- each null term integrates to zero
  have h2z : ∫ p : ℝ × ℝ, u2 p ∂vol2 = 0 := integral_mul_indicator_eq_zero hN2
  have h3z : ∫ p : ℝ × ℝ, u3 p ∂vol2 = 0 := integral_mul_indicator_eq_zero hN3
  have h4z : ∫ p : ℝ × ℝ, u4 p ∂vol2 = 0 := integral_mul_indicator_eq_zero hN4
  have h5z : ∫ p : ℝ × ℝ, u5 p ∂vol2 = 0 := integral_mul_indicator_eq_zero hN5
  -- vol2.univ = 4
  have hv4 : vol2.real univ = 4 := by
    rw [MeasureTheory.measureReal_def]
    have hI2 : vol univ = 2 := by
      rw [Measure.restrict_apply MeasurableSet.univ]
      simp [Real.volume_Icc]
      norm_num
    rw [← Set.univ_prod_univ, Measure.prod_prod, hI2]
    norm_num
  have hGint : ∫ p : ℝ × ℝ, G p ∂vol2 = ε ^ 2 / 4 * vol2.real univ := by
    have e1 : ∫ p : ℝ × ℝ, G p ∂vol2
        = ∫ a : ℝ × ℝ, (fun _ : ℝ × ℝ => ε ^ 2 / 4) a +
            (u2 + (u3 + (u4 + u5))) a ∂vol2 :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => rfl)
    have e2 : ∫ a : ℝ × ℝ, (u2 + (u3 + (u4 + u5))) a ∂vol2
        = ∫ a : ℝ × ℝ, u2 a + ((u3 + (u4 + u5)) a) ∂vol2 :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => rfl)
    have e3 : ∫ a : ℝ × ℝ, (u3 + (u4 + u5)) a ∂vol2
        = ∫ a : ℝ × ℝ, u3 a + ((u4 + u5) a) ∂vol2 :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => rfl)
    have e4 : ∫ a : ℝ × ℝ, (u4 + u5) a ∂vol2
        = ∫ a : ℝ × ℝ, u4 a + u5 a ∂vol2 :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => rfl)
    rw [e1, MeasureTheory.integral_add (MeasureTheory.integrable_const _)
        (h2i.add (h3i.add (h4i.add h5i))),
      e2, MeasureTheory.integral_add h2i (h3i.add (h4i.add h5i)),
      e3, MeasureTheory.integral_add h3i (h4i.add h5i),
      e4, MeasureTheory.integral_add h4i h5i,
      MeasureTheory.integral_const, h2z, h3z, h4z, h5z]
    simp only [hv4, smul_eq_mul, add_zero]
    ring
  -- conclude
  rw [hsNorm_def]
  calc Real.sqrt (∫ p : ℝ × ℝ, (K p - meshKernel K n p) ^ 2 ∂vol2)
      ≤ Real.sqrt (ε ^ 2 / 4 * vol2.real univ) :=
        Real.sqrt_le_sqrt (hint.trans (le_of_eq hGint))
    _ = Real.sqrt (ε ^ 2 / 4 * 4) := by rw [hv4]
    _ = Real.sqrt (ε ^ 2) := by norm_num
    _ = ε := Real.sqrt_sq hε.le

/-! ### Continuous kernel ⇒ compact operator -/

/-- **Continuous kernel ⇒ compact operator** (item (1) of the layer-3 gap report):
the operator `TOp K` of a continuous Hilbert–Schmidt kernel is compact, being the
operator-norm limit (at rate `1/(n+1)`) of the compact operators of the degenerate
mesh kernels. -/
theorem continuous_kernel_compact {K : ℝ × ℝ → ℝ} (hK : HSKernel K) (hKc : Continuous K) :
    IsCompactOperator (TOp K hK) := by
  classical
  have hall : ∀ n : ℕ, ∃ L : ℝ × ℝ → ℝ, HSKernel L ∧
      hsNorm (fun p => K p - L p) ≤ 1 / ((n:ℝ) + 1) ∧
      ∃ (s : Finset (ℕ × ℕ)) (a b : ℕ × ℕ → ℝ → ℝ),
        (∀ q, MemLp (a q) 2 vol) ∧ (∀ q, MemLp (b q) 2 vol) ∧
        ∀ p, L p = ∑ q ∈ s, a q p.1 * b q p.2 :=
    fun n => hsKernel_mesh_approx (ε := 1 / ((n:ℝ) + 1)) hK hKc (by positivity)
  choose L hLme hLnorm s a b hAmem hBmem hLform using hall
  have hTc : ∀ n : ℕ, IsCompactOperator (TOp (L n) (hLme n)) := by
    intro n
    have hsum : HSKernel (fun p => ∑ q ∈ s n, a n q p.1 * b n q p.2) :=
      hsKernel_degenerate (s n) (a n) (b n) (hAmem n) (hBmem n)
    have heq : TOp (L n) (hLme n) = TOp (fun p => ∑ q ∈ s n, a n q p.1 * b n q p.2) hsum :=
      TOp_congr (fun p => hLform n p) (hLme n) hsum
    rw [heq]
    exact isCompactOperator_TOp_degenerate (s n) (a n) (b n) (hAmem n) (hBmem n)
  have hTn : ∀ n : ℕ, ‖TOp (L n) (hLme n) - TOp K hK‖ ≤ (1:ℝ) / ((n:ℝ) + 1) := by
    intro n
    have hflip : hsNorm (L n - K) = hsNorm (fun p => K p - L n p) := by
      have hsub : (L n - K) = fun p : ℝ × ℝ => -(K p - L n p) := by
        funext p; simp
      rw [hsub, hsNorm_neg]
    calc ‖TOp (L n) (hLme n) - TOp K hK‖ ≤ hsNorm (L n - K) := TOp_norm_diff_le (hLme n) hK
      _ = hsNorm (fun p => K p - L n p) := hflip
      _ ≤ 1 / ((n:ℝ) + 1) := hLnorm n
  exact isCompactOperator_TOp_limit hK (fun n => TOp (L n) (hLme n)) hTc hTn

end HS

end
