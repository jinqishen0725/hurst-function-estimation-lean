import Hurst.DiscreteRieszCycleBridge
import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Order.UpperLower

noncomputable section

open Set MeasureTheory Filter Matrix
open Bornology
open scoped Topology Pointwise

namespace Hurst

/-- A positive physical cutoff tending to zero with the integer truncation
level. -/
def rieszCycleCutoff (R : ℕ) : ℝ := ((R + 1 : ℕ) : ℝ)⁻¹

theorem rieszCycleCutoff_pos (R : ℕ) : 0 < rieszCycleCutoff R := by
  unfold rieszCycleCutoff
  positivity

/-- The continuous capped Riesz kernel.  Capping the distance from below
removes every diagonal singularity while preserving the kernel away from a
strip of width `rieszCycleCutoff R`. -/
def truncatedRieszKernel (R : ℕ) (psi c x y : ℝ) : ℝ :=
  c * (max (rieszCycleCutoff R) |x - y|) ^ (-psi)

theorem continuous_truncatedRieszKernel (R : ℕ) (psi c : ℝ) :
    Continuous (fun p : ℝ × ℝ => truncatedRieszKernel R psi c p.1 p.2) := by
  let d : ℝ × ℝ → ℝ := fun p => max (rieszCycleCutoff R) |p.1 - p.2|
  have hd : Continuous d := by
    dsimp only [d]
    exact continuous_const.max
      (continuous_abs.comp (continuous_fst.sub continuous_snd))
  have hdpos : ∀ p, 0 < d p := by
    intro p
    exact (rieszCycleCutoff_pos R).trans_le (le_max_left _ _)
  unfold truncatedRieszKernel
  exact continuous_const.mul
    (hd.rpow_const (fun p => Or.inl (ne_of_gt (hdpos p))))

/-- The unindicated capped cyclic integrand.  It is used on the compact cube
`[-1,1]^k`; the indicated whole-space version below matches the article's
notation. -/
def weightedTruncatedRieszCycleIntegrand
    (k R : ℕ) (psi c : ℝ) (omega : ℝ → ℝ)
    (z : Fin k → ℝ) : ℝ :=
  ∏ i : Fin k, omega (z i) *
    truncatedRieszKernel R psi c (z i) (z (finCyclicSucc i))

theorem continuous_weightedTruncatedRieszCycleIntegrand
    (k R : ℕ) (psi c : ℝ) (omega : ℝ → ℝ)
    (homega : Continuous omega) :
    Continuous (weightedTruncatedRieszCycleIntegrand k R psi c omega) := by
  unfold weightedTruncatedRieszCycleIntegrand
  apply continuous_finset_prod
  intro i hi
  have hpair : Continuous (fun z : Fin k → ℝ =>
      (z i, z (finCyclicSucc i))) :=
    (continuous_apply i).prodMk (continuous_apply (finCyclicSucc i))
  have hkernel : Continuous (fun z : Fin k → ℝ =>
      truncatedRieszKernel R psi c (z i) (z (finCyclicSucc i))) := by
    convert (continuous_truncatedRieszKernel R psi c).comp hpair using 1
    funext z
    rfl
  exact (homega.comp (continuous_apply i)).mul hkernel

theorem integrableOn_weightedTruncatedRieszCycleIntegrand_cube
    (k R : ℕ) (psi c : ℝ) (omega : ℝ → ℝ)
    (homega : Continuous omega) :
    IntegrableOn (weightedTruncatedRieszCycleIntegrand k R psi c omega)
      (Set.Icc (fun _ : Fin k => (-1 : ℝ)) (fun _ => 1)) := by
  exact (continuous_weightedTruncatedRieszCycleIntegrand
    k R psi c omega homega).continuousOn.integrableOn_compact isCompact_Icc

/-- Unit cube in a finite real product. -/
def rieszUnitCube (k : ℕ) : Set (Fin k → ℝ) :=
  Set.Icc (fun _ => (0 : ℝ)) (fun _ => 1)

/-- The canonical integer lattice inside the real coordinate space. -/
def rieszIntegerLattice (k : ℕ) : Submodule ℤ (Fin k → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin k)))

theorem volume_frontier_rieszUnitCube (k : ℕ) :
    volume (frontier (rieszUnitCube k)) = 0 := by
  exact (ordConnected_Icc : (rieszUnitCube k).OrdConnected).null_frontier

/-- Direct specialization of mathlib's multidimensional regular-lattice
quadrature theorem to the unit cube.  This closes the abstract bounded
continuous product-grid step; the remaining fixed-cutoff work is only the
explicit affine reindexing from this lattice to the article's right-endpoint
grid and its vanishing boundary faces. -/
theorem tendsto_unitCube_lattice_tsum_div_pow_integral
    (k : ℕ) (F : (Fin k → ℝ) → ℝ) (hF : Continuous F) :
    Tendsto (fun n : ℕ =>
      (∑' x : ↑(rieszUnitCube k ∩
          (n : ℝ)⁻¹ • rieszIntegerLattice k), F x) /
        n ^ Fintype.card (Fin k)) atTop
      (𝓝 (∫ x in rieszUnitCube k, F x)) := by
  exact tendsto_tsum_div_pow_atTop_integral
    (rieszUnitCube k) F hF (Metric.isBounded_Icc _ _) measurableSet_Icc
      (volume_frontier_rieszUnitCube k)

/-- Affine coordinate change from `[0,1]^k` to `[-1,1]^k`. -/
def rieszUnitToSymmetricCube {k : ℕ} (y : Fin k → ℝ) : Fin k → ℝ :=
  fun i => 2 * y i - 1

theorem continuous_rieszUnitToSymmetricCube (k : ℕ) :
    Continuous (rieszUnitToSymmetricCube : (Fin k → ℝ) → (Fin k → ℝ)) := by
  apply continuous_pi
  intro i
  exact (continuous_apply i).const_mul 2 |>.sub continuous_const

/-- The fixed-cutoff cyclic integrand after the affine cube change. -/
def unitCubeWeightedTruncatedRieszIntegrand
    (k R : ℕ) (psi c : ℝ) (omega : ℝ → ℝ)
    (y : Fin k → ℝ) : ℝ :=
  weightedTruncatedRieszCycleIntegrand k R psi c omega
    (rieszUnitToSymmetricCube y)

theorem continuous_unitCubeWeightedTruncatedRieszIntegrand
    (k R : ℕ) (psi c : ℝ) (omega : ℝ → ℝ)
    (homega : Continuous omega) :
    Continuous (unitCubeWeightedTruncatedRieszIntegrand
      k R psi c omega) := by
  exact (continuous_weightedTruncatedRieszCycleIntegrand
    k R psi c omega homega).comp (continuous_rieszUnitToSymmetricCube k)

/-- Mathlib now supplies the full fixed-cutoff product-grid limit on the
affinely transformed unit cube. -/
theorem tendsto_unitCube_truncatedRiesz_lattice
    (k R : ℕ) (psi c : ℝ) (omega : ℝ → ℝ)
    (homega : Continuous omega) :
    Tendsto (fun n : ℕ =>
      (∑' y : ↑(rieszUnitCube k ∩
          (n : ℝ)⁻¹ • rieszIntegerLattice k),
        unitCubeWeightedTruncatedRieszIntegrand k R psi c omega y) /
        n ^ Fintype.card (Fin k)) atTop
      (𝓝 (∫ y in rieszUnitCube k,
        unitCubeWeightedTruncatedRieszIntegrand k R psi c omega y)) := by
  exact tendsto_unitCube_lattice_tsum_div_pow_integral k _
    (continuous_unitCubeWeightedTruncatedRieszIntegrand
      k R psi c omega homega)

/-- Whole-space indicated form of the capped cyclic integral. -/
def weightedTruncatedRieszCycleIntegral
    (k R : ℕ) (psi c : ℝ) (omega : ℝ → ℝ) : ℝ :=
  ∫ z : Fin k → ℝ, ∏ i : Fin k,
    (Icc (-1 : ℝ) 1).indicator omega (z i) *
      truncatedRieszKernel R psi c (z i) (z (finCyclicSucc i))

/-- The indicator of the product cube is exactly the product of the
one-dimensional indicators appearing in the article's cyclic integrand. -/
theorem symmetricCube_indicator_weightedTruncatedRieszCycleIntegrand
    (k R : ℕ) (psi c : ℝ) (omega : ℝ → ℝ)
    (z : Fin k → ℝ) :
    (Set.Icc (fun _ : Fin k => (-1 : ℝ)) (fun _ => 1)).indicator
        (weightedTruncatedRieszCycleIntegrand k R psi c omega) z =
      ∏ i : Fin k,
        (Icc (-1 : ℝ) 1).indicator omega (z i) *
          truncatedRieszKernel R psi c (z i)
            (z (finCyclicSucc i)) := by
  classical
  by_cases hz : z ∈ Set.Icc (fun _ : Fin k => (-1 : ℝ)) (fun _ => 1)
  · rw [Set.indicator_of_mem hz]
    unfold weightedTruncatedRieszCycleIntegrand
    apply Finset.prod_congr rfl
    intro i hi
    rw [Set.indicator_of_mem]
    exact ⟨hz.1 i, hz.2 i⟩
  · rw [Set.indicator_of_notMem hz]
    have hex : ∃ i : Fin k, z i ∉ Icc (-1 : ℝ) 1 := by
      by_contra! hall
      exact hz ⟨fun i => (hall i).1, fun i => (hall i).2⟩
    obtain ⟨i, hi⟩ := hex
    rw [Finset.prod_eq_zero (Finset.mem_univ i)]
    rw [Set.indicator_of_notMem hi, zero_mul]

/-- The unit-cube indicator transforms pointwise into the symmetric-cube
indicator under `y ↦ 2y - 1`. -/
theorem unitCube_indicator_affine_eq
    (k R : ℕ) (psi c : ℝ) (omega : ℝ → ℝ)
    (y : Fin k → ℝ) :
    (rieszUnitCube k).indicator
        (unitCubeWeightedTruncatedRieszIntegrand k R psi c omega) y =
      (Set.Icc (fun _ : Fin k => (-1 : ℝ)) (fun _ => 1)).indicator
        (weightedTruncatedRieszCycleIntegrand k R psi c omega)
        (rieszUnitToSymmetricCube y) := by
  classical
  by_cases hy : y ∈ rieszUnitCube k
  · have hTy : rieszUnitToSymmetricCube y ∈
        Set.Icc (fun _ : Fin k => (-1 : ℝ)) (fun _ => 1) := by
      constructor
      · intro i
        dsimp only [rieszUnitToSymmetricCube]
        have := hy.1 i
        linarith
      · intro i
        dsimp only [rieszUnitToSymmetricCube]
        have := hy.2 i
        linarith
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hTy]
    rfl
  · have hTy : rieszUnitToSymmetricCube y ∉
        Set.Icc (fun _ : Fin k => (-1 : ℝ)) (fun _ => 1) := by
      intro hT
      apply hy
      constructor
      · intro i
        have := hT.1 i
        dsimp only [rieszUnitToSymmetricCube] at this
        linarith
      · intro i
        have := hT.2 i
        dsimp only [rieszUnitToSymmetricCube] at this
        linarith
    rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hTy]

/-- Finite matrix obtained by sampling the capped physical kernel at the
article's active-row grid. -/
def weightedTruncatedRieszDiscreteMatrix
    (m R : ℕ) (S psi c : ℝ) (omega : ℝ → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  fun i j => S⁻¹ * omega (rieszCycleGridPoint m i) *
    truncatedRieszKernel R psi c
      (rieszCycleGridPoint m i) (rieszCycleGridPoint m j)

def weightedTruncatedRieszDiscreteCycleValue
    (m k R : ℕ) (S psi c : ℝ) (omega : ℝ → ℝ) : ℝ :=
  matrixClosedWalkCoordinateSum
    (weightedTruncatedRieszDiscreteMatrix m R S psi c omega) k

theorem weightedTruncatedRieszDiscreteCycleValue_eq_trace_pow
    (m k R : ℕ) (S psi c : ℝ) (omega : ℝ → ℝ) :
    weightedTruncatedRieszDiscreteCycleValue m k R S psi c omega =
      Matrix.trace
        ((weightedTruncatedRieszDiscreteMatrix m R S psi c omega) ^ k) := by
  exact matrixClosedWalkCoordinateSum_eq_trace_pow _ _

/-- Fixed-cutoff bounded-continuous product-grid quadrature.  This is the
first, and nonsingular, deterministic sublemma required by the cycle bridge. -/
def HasFixedCutoffRieszCycleQuadrature
    (m : ℕ → ℕ) (S : ℕ → ℝ) (psi c : ℝ)
    (omega : ℝ → ℝ) : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∀ R : ℕ,
    Tendsto (fun n => weightedTruncatedRieszDiscreteCycleValue
      (m n) k R (S n) psi c omega) atTop
      (𝓝 (weightedTruncatedRieszCycleIntegral k R psi c omega))

/-- The exact lattice sum appearing in the proved unit-cube theorem. -/
def unitCubeTruncatedRieszLatticeSum
    (m k R : ℕ) (psi c : ℝ) (omega : ℝ → ℝ) : ℝ :=
  (∑' y : ↑(rieszUnitCube k ∩
      (m : ℝ)⁻¹ • rieszIntegerLattice k),
    unitCubeWeightedTruncatedRieszIntegrand k R psi c omega y) /
      m ^ Fintype.card (Fin k)

theorem unitCubeTruncatedRieszLatticeSum_tendsto
    (k R : ℕ) (psi c : ℝ) (omega : ℝ → ℝ)
    (homega : Continuous omega) :
    Tendsto (fun m => unitCubeTruncatedRieszLatticeSum
      m k R psi c omega) atTop
      (𝓝 (∫ y in rieszUnitCube k,
        unitCubeWeightedTruncatedRieszIntegrand k R psi c omega y)) := by
  exact tendsto_unitCube_truncatedRiesz_lattice
    k R psi c omega homega

/-- Remaining finite reindex/boundary-face lemma for the fixed-cutoff step.
The factor `2^k` is the Jacobian of the affine map from the unit cube; this
statement includes the asymptotically equivalent `S⁻k` normalization and the
deletion of the lower boundary faces from the right-endpoint grid. -/
def HasFixedCutoffMatrixLatticeReindex
    (m : ℕ → ℕ) (S : ℕ → ℝ) (psi c : ℝ)
    (omega : ℝ → ℝ) : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∀ R : ℕ,
    Tendsto (fun n =>
      weightedTruncatedRieszDiscreteCycleValue
          (m n) k R (S n) psi c omega -
        2 ^ k * unitCubeTruncatedRieszLatticeSum
          (m n) k R psi c omega) atTop (𝓝 0)

/-- Remaining affine change-of-variables identity for capped integrands. -/
def HasTruncatedRieszAffineIntegralIdentity
    (psi c : ℝ) (omega : ℝ → ℝ) : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∀ R : ℕ,
    2 ^ k * (∫ y in rieszUnitCube k,
      unitCubeWeightedTruncatedRieszIntegrand k R psi c omega y) =
        weightedTruncatedRieszCycleIntegral k R psi c omega

/-- The capped cyclic integral satisfies the exact affine
change-of-variables identity.  This uses the finite-dimensional Haar scaling
formula, so the Jacobian is proved rather than assumed. -/
theorem hasTruncatedRieszAffineIntegralIdentity
    (psi c : ℝ) (omega : ℝ → ℝ) :
    HasTruncatedRieszAffineIntegralIdentity psi c omega := by
  intro k hk R
  let raw := weightedTruncatedRieszCycleIntegrand k R psi c omega
  let cube : Set (Fin k → ℝ) :=
    Set.Icc (fun _ => (-1 : ℝ)) (fun _ => 1)
  let shift : Fin k → ℝ := fun _ => (-1 : ℝ)
  let G : (Fin k → ℝ) → ℝ := cube.indicator raw
  have hset : (∫ y in rieszUnitCube k,
      unitCubeWeightedTruncatedRieszIntegrand k R psi c omega y) =
      ∫ y : Fin k → ℝ, G (rieszUnitToSymmetricCube y) := by
    calc
      _ = ∫ y : Fin k → ℝ, (rieszUnitCube k).indicator
          (unitCubeWeightedTruncatedRieszIntegrand
            k R psi c omega) y :=
        (integral_indicator measurableSet_Icc).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with y
        exact unitCube_indicator_affine_eq k R psi c omega y
  have hshape : ∀ y : Fin k → ℝ,
      G (rieszUnitToSymmetricCube y) =
        G ((2 : ℝ) • y + shift) := by
    intro y
    rfl
  have hscale := Measure.integral_comp_smul_of_nonneg volume
    (fun x : Fin k → ℝ => G (x + shift)) 2 (hR := by positivity)
  have htranslate : (∫ x : Fin k → ℝ, G (x + shift)) =
      ∫ x, G x := integral_add_right_eq_self G shift
  have hscale' :
      (∫ y : Fin k → ℝ, G (rieszUnitToSymmetricCube y)) =
        (2 ^ k)⁻¹ * ∫ x : Fin k → ℝ, G x := by
    calc
      _ = ∫ y : Fin k → ℝ, G ((2 : ℝ) • y + shift) := by
        apply integral_congr_ae
        filter_upwards [] with y
        exact hshape y
      _ = (2 ^ Module.finrank ℝ (Fin k → ℝ))⁻¹ •
          ∫ x : Fin k → ℝ, G (x + shift) := hscale
      _ = (2 ^ k)⁻¹ * ∫ x : Fin k → ℝ, G x := by
        rw [htranslate, Module.finrank_fin_fun]
        rfl
  have hG : (∫ x : Fin k → ℝ, G x) =
      weightedTruncatedRieszCycleIntegral k R psi c omega := by
    unfold G cube raw weightedTruncatedRieszCycleIntegral
    rw [integral_indicator measurableSet_Icc]
    rw [← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards [] with z
    exact symmetricCube_indicator_weightedTruncatedRieszCycleIntegrand
      k R psi c omega z
  rw [hset, hscale', hG]
  have hkpow : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

/-- The proved regular-lattice theorem plus the two explicit affine/reindex
lemmas yield fixed-cutoff matrix quadrature. -/
theorem hasFixedCutoffRieszCycleQuadrature_of_lattice
    (m : ℕ → ℕ) (S : ℕ → ℝ) (psi c : ℝ) (omega : ℝ → ℝ)
    (homega : Continuous omega)
    (hm : Tendsto m atTop atTop)
    (hreindex : HasFixedCutoffMatrixLatticeReindex m S psi c omega) :
    HasFixedCutoffRieszCycleQuadrature m S psi c omega := by
  intro k hk R
  have hlattice := (unitCubeTruncatedRieszLatticeSum_tendsto
    k R psi c omega homega).comp hm
  have hscaled := hlattice.const_mul (2 ^ k)
  have hdiff := hreindex k hk R
  have hadd := hscaled.add hdiff
  rw [hasTruncatedRieszAffineIntegralIdentity psi c omega k hk R] at hadd
  convert hadd using 1
  · funext n
    dsimp only [Function.comp_apply]
    ring_nf
  · simp only [add_zero]

/-- Uniform removal of the cutoff in the discrete cyclic sums.  The order of
quantifiers is the one needed for a triangular array: after choosing a large
cutoff level, the estimate holds eventually in the row index. -/
def HasUniformDiscreteRieszCutoffRemoval
    (m : ℕ → ℕ) (S : ℕ → ℝ) (psi c : ℝ)
    (omega : ℝ → ℝ) : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∀ eps > 0,
    ∀ᶠ R : ℕ in atTop, ∀ᶠ n : ℕ in atTop,
      |weightedRieszDiscreteCycleValue (m n) k (S n) psi c omega -
        weightedTruncatedRieszDiscreteCycleValue
          (m n) k R (S n) psi c omega| < eps

/-- Removal of the cutoff in the continuum cyclic integral. -/
def HasContinuumRieszCutoffRemoval (psi c : ℝ)
    (omega : ℝ → ℝ) : Prop :=
  ∀ k : ℕ, 2 ≤ k →
    Tendsto (fun R => weightedTruncatedRieszCycleIntegral
      k R psi c omega) atTop
      (𝓝 (weightedRieszCycleIntegral k psi c omega))

/-- A general three-epsilon lemma.  It turns fixed-truncation convergence,
uniform discrete cutoff removal, and continuum cutoff removal into convergence
of the untruncated triangular array. -/
theorem tendsto_of_fixed_truncation_of_uniform_removal
    (F : ℕ → ℝ) (G : ℕ → ℕ → ℝ) (g : ℕ → ℝ) (L : ℝ)
    (hfixed : ∀ R, Tendsto (G R) atTop (𝓝 (g R)))
    (hdisc : ∀ eps > 0, ∀ᶠ R : ℕ in atTop,
      ∀ᶠ n : ℕ in atTop, |F n - G R n| < eps)
    (hcont : Tendsto g atTop (𝓝 L)) :
    Tendsto F atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  intro eps heps
  have heps3 : 0 < eps / 3 := by linarith
  obtain ⟨Rdisc, hRdisc⟩ := eventually_atTop.1 (hdisc (eps / 3) heps3)
  obtain ⟨Rcont, hRcont⟩ :=
    Metric.tendsto_atTop.1 hcont (eps / 3) heps3
  let R := max Rdisc Rcont
  have hdiscR : ∀ᶠ n : ℕ in atTop, |F n - G R n| < eps / 3 :=
    hRdisc R (le_max_left _ _)
  have hcontR : dist (g R) L < eps / 3 :=
    hRcont R (le_max_right _ _)
  obtain ⟨Ndisc, hNdisc⟩ := eventually_atTop.1 hdiscR
  obtain ⟨Nfixed, hNfixed⟩ :=
    Metric.tendsto_atTop.1 (hfixed R) (eps / 3) heps3
  refine ⟨max Ndisc Nfixed, fun n hn => ?_⟩
  have hd := hNdisc n ((le_max_left _ _).trans hn)
  have hf := hNfixed n ((le_max_right _ _).trans hn)
  rw [Real.dist_eq] at hf hcontR ⊢
  calc
    |F n - L| ≤ |F n - G R n| + |G R n - L| :=
      abs_sub_le _ _ _
    _ ≤ |F n - G R n| +
        (|G R n - g R| + |g R - L|) := by
      linarith [abs_sub_le (G R n) (g R) L]
    _ = |F n - G R n| + |G R n - g R| + |g R - L| := by ring
    _ < eps := by linarith

/-- The three deterministic sublemmas imply the full cyclic quadrature
property.  Thus downstream code need not assume the composite quadrature
statement once these individually checkable facts have been supplied. -/
theorem hasWeightedRieszCycleQuadrature_of_truncation
    (m : ℕ → ℕ) (S : ℕ → ℝ) (psi c : ℝ) (omega : ℝ → ℝ)
    (hfixed : HasFixedCutoffRieszCycleQuadrature m S psi c omega)
    (hdisc : HasUniformDiscreteRieszCutoffRemoval m S psi c omega)
    (hcont : HasContinuumRieszCutoffRemoval psi c omega) :
    HasWeightedRieszCycleQuadrature m S psi c omega := by
  intro k hk
  apply tendsto_of_fixed_truncation_of_uniform_removal
    (fun n => weightedRieszDiscreteCycleValue
      (m n) k (S n) psi c omega)
    (fun R n => weightedTruncatedRieszDiscreteCycleValue
      (m n) k R (S n) psi c omega)
    (fun R => weightedTruncatedRieszCycleIntegral k R psi c omega)
    (weightedRieszCycleIntegral k psi c omega)
  · exact hfixed k hk
  · exact hdisc k hk
  · exact hcont k hk

end Hurst
