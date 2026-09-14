import Hurst.P1ActualPowerSums
import Hurst.ActualQuadratureFinal
import Hurst.P3SignedMatching
import Hurst.P4GaussianSeriesLaw
import Hurst.P6LawIdentification
import Hurst.NonnegWeightNegMass
import Hurst.EvenPeeling
import Hurst.FeatureQuadraticSpectral
import Hurst.DistributionVaryingLawTransfer

/-!
# Capstone v2: the NON-VACUOUS composition

This file lands the repaired capstone
`actualQ1LongStatistic_tendsto_secondChaos_v2`: the actual q1 long-memory
quadratic statistic converges in distribution to the CONSTRUCTED Gaussian
second-chaos law, with every defect of the audited pre-v2 capstone
(`Hurst.ActualSecondChaosComplete`, kept for the record) fixed:

* **DEFECT 1 (fixed here).**  The refutable `hcard : ∀ n, 0 < card n` is GONE.
  In fact `card n = 0` for `n = 1` (the row index type is `Fin (n - 1)`), so the
  ∀-form is unsatisfiable and D3
  (`Hurst.ActualQuadratureFinal.actualQ1LongStatistic_tendsto_secondChaos_signed`,
  which still carries it as `hm`) is uninstantiable on the actual data.  The fix
  is structural: the peeling input `hAbs` is produced by
  `cap2_paddedAbsRearranged_tendsto_of_eventualCard`, which requires only
  `Tendsto m atTop atTop` (card `→ ∞`, derived from `card / S → 2`, itself from
  the feasible window) by padding every row with ONE zero
  (`cap2ZeroPadRow`); zero rows make everything trivial, padded rows agree with
  the original ones in power sums (`cap2_sum_zeroPadRow_pow`) and in the
  decreasing rearrangement (`cap2_padRearranged_zeroPad`, for nonnegative rows).
  The intermediate endpoint
  `actualQ1LongStatistic_tendsto_secondChaos_signed_eventualCard` is exactly D3
  with `hm : ∀ n, 0 < card n` deleted (small `n` rows of size `0` are vacuous
  for `hane`/`hwnn` and handled trivially by the padding).
* **DEFECT 2 (fixed).**  The contradictory bandwidth window of the pre-audit
  capstone is replaced by the FEASIBLE window (B) of `Hurst.P1ActualPowerSums`:
  `δ n = n^{-γ}`, `0 < γ < 1`, `(1 - γ) * (2 - 2 * f t) < 2 - 2 * b`.  It is
  nonempty for EVERY `h := f t ≤ b < 1`: `feasibleBandwidth_window_nonempty`
  (proved in P1) exhibits `γ = (1 + L) / 2` with `L = (b - h) / (1 - h) ∈ [0, 1)`,
  for which `(1 - γ) * (2 - 2 h) = 1 - b < 2 - 2 b`.
* **DEFECT 3 (fixed).**  The limit law is no longer a bare hypothesis: `Q` is
  CONSTRUCTED from `Summable (lam ^ 2)` by
  `Hurst.P4GaussianSeriesLaw.exists_isSecondChaosSeriesLaw_gaussSeq` on the
  concrete space `gaussianSeqMeasure` (with the full a.s.-convergence field).
* **DEFECT 4 (documented, kept as the honest interface point).**  `hRiesz` —
  `∀ k ≥ 2, HasSum (fun j => lam j ^ k) (J_k)` with
  `J_k = weightedRieszCycleIntegral k (2 - 2 * f t) (f t * (2 * f t - 1))
  (equivalentKernel r)` — is the spectrum bridge of `IsWeightedRieszSpectrum`
  (its square-summability component is DERIVED from the `k = 2` instance).  It
  is P2's remaining construction obligation (`Hurst.P2SpectrumConstruction`):
  a `HasSum` statement about the enumeration-to-be of the Riesz operator's
  spectrum; it is discharged the moment P2's spectral enumeration lands.
  Everything else is theorem: P1's `actualQ1_eigenPowerSums_feasible` converges
  to the RIGHT-HAND side `J_k` for ALL `k ≥ 2`, and `hRiesz` merely transports
  the target to `∑' lam ^ k` — the `Even`-restriction of D3's `hPow` shape is
  free.
* **DEFECT 5 (fixed).**  `hwnn` — eventual entrywise nonnegativity of the
  spectral weights — is kept as an EXPLICIT ordinary hypothesis (the balanced
  degree-one regime of
  `Hurst.LocalLinearWeightsNonneg.localLinearWeight_nonneg` supplies it,
  criterion `μ1 * x i ≤ μ2`); through
  `Hurst.WeightedMatrixPSD.weightedFeatureQuadraticMatrix_eigenvalues_nonneg`
  it discharges `hNegMass` IDENTICALLY (the actual matrix is the PSD congruence
  `√R · diag w · √R`), the route (a) of `Hurst.NonnegWeightNegMass`.

## Joint instantiation (non-vacuousness)

Every hypothesis is satisfiable SIMULTANEOUSLY:

1. Ordinary model: take `f` constant (e.g. `f ≡ 0.9`), `p ≥ 1`, small `M > 0`,
   `a = b = 0.9` (`a ≤ b`, `b < 1`), `t = 1/2`.  Then `h := f t = 0.9 > 3/4`,
   `hf : f ∈ hurstHolderClass p M` (constants are smooth with vanishing
   Hölder seminorm), `hF : MapsTo` holds, `hlong` holds.
2. Feasible window (B): with `h = b` the witness `L = 0`, `γ = 1/2` satisfies
   `0 < γ < 1` and `(1 - γ)(2 - 2h) = 1 - b < 2 - 2b`; in general the P1
   witness `γ = (1 + L)/2` works for every `h ≤ b < 1`.  No condition of the
   form `γ < 4h - 3` appears anywhere in this file.
3. `hane` (row nondegeneracy): a genericity condition on the first-stride
   difference coefficient rows of a nondegenerate feature map — open and dense
   in the model data (the same ordinary condition consumed by the whole
   signed-interface chain); it is vacuous automatically on zero rows.
4. `hwnn` (weight nonnegativity): the balanced degree-one local-polynomial
   design satisfies the pointwise criterion `μ1 * x i ≤ μ2` of
   `Hurst.LocalLinearWeightsNonneg.localLinearWeight_nonneg`, hence
   `localLinearWeights_nonnegWeights` packages exactly the required eventual
   entrywise nonnegativity (balanced symmetric windows have `μ1 = 0`).
5. `hlam`/`hRiesz`: the antitone nonnegative Riesz spectrum with cyclic-trace
   power sums `J_k` — the P2 construction obligation (DEFECT 4 above), the
   single remaining hypothesis of the composition.
6. `hcard`: NOT a hypothesis — derived eventually (`card / S → 2` from the
   window via `localWeightActiveSet_card_ratio_tendsto_two`), with small `n`
   handled trivially by the padding.
7. `hQ`: NOT a hypothesis — constructed from `Summable (lam ^ 2)` (derived from
   `hRiesz` at `k = 2`) by P4's `exists_isSecondChaosSeriesLaw_gaussSeq`.

Hence the capstone's conclusion is non-vacuous: for every instance of
(1)-(5) it produces a concrete law `Q` on `gaussianSeqMeasure` that the actual
statistic converges to, in `TendstoInDistribution`.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Set Filter MeasureTheory Matrix ProbabilityTheory
open scoped Topology RealInnerProductSpace Matrix.Norms.Frobenius

namespace Hurst

/-! ## The one-zero padding toolbox (the DEFECT-1 fix, general form) -/

/-- Case split for the padded index set `Fin (m + 1)`. -/
private theorem cap2_castAdd_or_natAdd {m : ℕ} (i : Fin (m + 1)) :
    (∃ j : Fin m, i = Fin.castAdd 1 j) ∨ ∃ j : Fin 1, i = Fin.natAdd m j := by
  by_cases h : (i : ℕ) < m
  · refine Or.inl ⟨⟨(i : ℕ), h⟩, Fin.ext ?_⟩
    simp
  · refine Or.inr ⟨⟨0, by omega⟩, Fin.ext ?_⟩
    have h1 := i.isLt
    simp only [Fin.val_natAdd]
    omega

/-- The row `g : Fin m → ℝ` padded with ONE zero to size `m + 1`. -/
def cap2ZeroPadRow {m : ℕ} (g : Fin m → ℝ) : Fin (m + 1) → ℝ :=
  Fin.append g (fun _ : Fin 1 => (0 : ℝ))

theorem cap2ZeroPadRow_castAdd {m : ℕ} (g : Fin m → ℝ) (j : Fin m) :
    cap2ZeroPadRow g (Fin.castAdd 1 j) = g j := Fin.append_left _ _ j

theorem cap2ZeroPadRow_natAdd {m : ℕ} (g : Fin m → ℝ) (j : Fin 1) :
    cap2ZeroPadRow g (Fin.natAdd m j) = 0 := by
  simp [cap2ZeroPadRow]

theorem cap2ZeroPadRow_nonneg {m : ℕ} (g : Fin m → ℝ) (hg : ∀ i, 0 ≤ g i)
    (i : Fin (m + 1)) : 0 ≤ cap2ZeroPadRow g i := by
  rcases cap2_castAdd_or_natAdd i with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · rw [cap2ZeroPadRow_castAdd]; exact hg a
  · rw [cap2ZeroPadRow_natAdd]

/-- Power sums are unchanged by the one-zero padding (`k ≥ 1`). -/
theorem cap2_sum_zeroPadRow_pow {m : ℕ} (g : Fin m → ℝ) {k : ℕ} (hk : 1 ≤ k) :
    (∑ i : Fin (m + 1), (cap2ZeroPadRow g i) ^ k) = ∑ i : Fin m, g i ^ k := by
  have hk0 : k ≠ 0 := by omega
  have hsub : (∑ i ∈ Finset.univ.filter (fun i : Fin (m + 1) => (i : ℕ) < m),
        (cap2ZeroPadRow g i) ^ k)
      = (∑ i : Fin (m + 1), (cap2ZeroPadRow g i) ^ k) := by
    refine Finset.sum_subset (s₁ := Finset.univ.filter (fun i : Fin (m + 1) => (i : ℕ) < m))
      (s₂ := Finset.univ) (fun i _ => Finset.mem_univ i) ?_
    intro i _ hi
    have him : ¬((i : ℕ) < m) := fun h' =>
      hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h'⟩)
    have hsplit : i = Fin.natAdd m (⟨0, by omega⟩ : Fin 1) := by
      refine Fin.ext ?_
      have h1 := i.isLt
      simp only [Fin.val_natAdd]
      omega
    rw [hsplit, cap2ZeroPadRow_natAdd, zero_pow hk0]
  rw [← hsub]
  refine Finset.sum_bij
    (fun (a : Fin (m + 1)) (ha : a ∈ Finset.univ.filter
        (fun i : Fin (m + 1) => (i : ℕ) < m)) =>
      (⟨(a : ℕ), (Finset.mem_filter.mp ha).2⟩ : Fin m))
    (fun _ _ => Finset.mem_univ _)
    (fun a _ b _ hEq => Fin.ext (by simpa using congrArg Fin.val hEq))
    (fun b _ =>
      ⟨(⟨(b : ℕ), by have := b.isLt; omega⟩ :
          Fin (m + 1)),
        Finset.mem_filter.mpr ⟨Finset.mem_univ (⟨(b : ℕ),
          by have := b.isLt; omega⟩ : Fin (m + 1)), by have := b.isLt; omega⟩,
        rfl⟩)
    (fun a ha => ?_)
  have hlt : (a : ℕ) < m := (Finset.mem_filter.mp ha).2
  show (cap2ZeroPadRow g a) ^ k = g (⟨(a : ℕ), hlt⟩ : Fin m) ^ k
  conv_lhs => rw [show a = Fin.castAdd 1 (⟨(a : ℕ), hlt⟩ : Fin m) from
    Fin.ext (by simp)]
  rw [cap2ZeroPadRow_castAdd]

/-- The canonical decreasing rearrangement of the padded row. -/
def cap2PaddedSorted {m : ℕ} (g : Fin m → ℝ) : Fin (m + 1) → ℝ :=
  Fin.append (fun j => g (decreasingSpectralPerm g j)) (fun _ : Fin 1 => (0 : ℝ))

theorem cap2PaddedSorted_castAdd {m : ℕ} (g : Fin m → ℝ) (j : Fin m) :
    cap2PaddedSorted g (Fin.castAdd 1 j) = g (decreasingSpectralPerm g j) :=
  Fin.append_left _ _ j

theorem cap2PaddedSorted_natAdd {m : ℕ} (g : Fin m → ℝ) (j : Fin 1) :
    cap2PaddedSorted g (Fin.natAdd m j) = 0 := by
  simp [cap2PaddedSorted]

/-- The block permutation of the padded index set: rearrange the first `m`
indices by the decreasing spectral permutation, keep the padded index fixed. -/
def cap2BlockPermEquiv {m : ℕ} (g : Fin m → ℝ) : Equiv.Perm (Fin (m + 1)) :=
  finSumFinEquiv.symm.trans
    ((Equiv.sumCongr (decreasingSpectralPerm g) (Equiv.refl (Fin 1))).trans
      finSumFinEquiv)

theorem cap2BlockPermEquiv_castAdd {m : ℕ} (g : Fin m → ℝ) (a : Fin m) :
    cap2BlockPermEquiv g (Fin.castAdd 1 a) =
      Fin.castAdd 1 (decreasingSpectralPerm g a) := by
  simp only [cap2BlockPermEquiv, Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd,
    Equiv.sumCongr_apply, Sum.map_inl, finSumFinEquiv_apply_left]

theorem cap2BlockPermEquiv_natAdd {m : ℕ} (g : Fin m → ℝ) (a : Fin 1) :
    cap2BlockPermEquiv g (Fin.natAdd m a) = Fin.natAdd m a := by
  simp only [cap2BlockPermEquiv, Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd,
    Equiv.sumCongr_apply, Sum.map_inr, Equiv.refl_apply, finSumFinEquiv_apply_right]

theorem cap2ZeroPadRow_cap2BlockPerm {m : ℕ} (g : Fin m → ℝ) (i : Fin (m + 1)) :
    cap2ZeroPadRow g (cap2BlockPermEquiv g i) = cap2PaddedSorted g i := by
  rcases cap2_castAdd_or_natAdd i with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · rw [cap2BlockPermEquiv_castAdd, cap2ZeroPadRow_castAdd, cap2PaddedSorted_castAdd]
  · rw [cap2BlockPermEquiv_natAdd, cap2ZeroPadRow_natAdd, cap2PaddedSorted_natAdd]

theorem cap2PaddedSorted_antitone {m : ℕ} (g : Fin m → ℝ) (hg : ∀ i, 0 ≤ g i) :
    Antitone (cap2PaddedSorted g) := by
  intro i j hij
  rcases cap2_castAdd_or_natAdd i with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · rcases cap2_castAdd_or_natAdd j with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · simp only [cap2PaddedSorted_castAdd]
      exact decreasingSpectralPerm_antitone g
        (Fin.le_def.mpr (by
          have h := Fin.le_def.mp hij
          simpa [Fin.val_castAdd] using h))
    · rw [cap2PaddedSorted_castAdd, cap2PaddedSorted_natAdd]
      exact hg (decreasingSpectralPerm g a)
  · rcases cap2_castAdd_or_natAdd j with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · have h := Fin.le_def.mp hij
      have h1 := (⟨0, by omega⟩ : Fin 1).isLt
      have h2 := b.isLt
      simp only [Fin.val_natAdd, Fin.val_castAdd] at h
      omega
    · rw [cap2PaddedSorted_natAdd, cap2PaddedSorted_natAdd]

/-- **The padded decreasing rearrangement is padding-invariant** (nonnegative
rows). -/
theorem cap2_padRearranged_zeroPad {m : ℕ} (g : Fin m → ℝ) (hg : ∀ i, 0 ≤ g i)
    (c : ℕ) : padRearranged (cap2ZeroPadRow g) c = padRearranged g c := by
  by_cases hc : c < m + 1
  · have hkey := eq_decreasingSpectralPerm_of_antitone_rearrangement
      (cap2PaddedSorted_antitone g hg) (cap2BlockPermEquiv g)
      (fun i => (cap2ZeroPadRow_cap2BlockPerm g i).symm) (⟨c, hc⟩)
    simp only [padRearranged]
    rw [dif_pos hc, ← hkey]
    by_cases hcm : c < m
    · have hcast : (⟨c, hc⟩ : Fin (m + 1)) = Fin.castAdd 1 (⟨c, hcm⟩ : Fin m) :=
        Fin.ext (by simp)
      rw [dif_pos hcm, hcast, cap2PaddedSorted_castAdd]
    · have hcm : c = m := by omega
      have hcast : (⟨c, hc⟩ : Fin (m + 1)) = Fin.natAdd m (⟨0, by omega⟩ : Fin 1) := by
        refine Fin.ext ?_
        simp only [Fin.val_natAdd]
        omega
      rw [dif_neg (by omega : ¬(c < m)), hcast, cap2PaddedSorted_natAdd]
  · simp only [padRearranged]
    rw [dif_neg hc, dif_neg (by omega : ¬(c < m))]

/-- **DEFECT-1 FIX (general form).**  `paddedAbsRearranged_tendsto` with the
refutable `∀ n, 0 < m n` hypothesis replaced by `Tendsto m atTop atTop`: the
rows are padded with one zero (`cap2ZeroPadRow`), which leaves every power sum
(`cap2_sum_zeroPadRow_pow`) and every entry of the decreasing rearrangement
(`cap2_padRearranged_zeroPad`) unchanged.  Sizes `m n + 1` are positive for ALL
`n`, so the peeling induction applies unconditionally. -/
theorem cap2_paddedAbsRearranged_tendsto_of_eventualCard
    (m : ℕ → ℕ) (x : ∀ n, Fin (m n) → ℝ) (lam : ℕ → ℝ)
    (hmtop : Tendsto m atTop atTop)
    (hl : Antitone lam ∧ ∀ j, 0 ≤ lam j ∧ Summable (fun j => lam j ^ 2))
    (hp : ∀ k : ℕ, 2 ≤ k → Even k → Tendsto (fun n => ∑ i : Fin (m n), x n i ^ k) atTop
      (𝓝 (∑' j, lam j ^ k))) :
    ∀ j : ℕ, Tendsto (fun n : ℕ => padRearranged (fun i : Fin (m n) => |x n i|) j)
      atTop (𝓝 (lam j)) := by
  intro j
  have hm0 : ∀ n : ℕ, 0 < m n + 1 := fun n => Nat.zero_lt_succ _
  have hmtop' : Tendsto (fun n : ℕ => m n + 1) atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro β
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hmtop.eventually_ge_atTop (β - 1))
    exact ⟨N, fun a ha => by have := hN a ha; omega⟩
  have hpadsum : ∀ (n k : ℕ), 1 ≤ k →
      (∑ i : Fin (m n + 1), (cap2ZeroPadRow (fun i : Fin (m n) => |x n i|) i) ^ k)
        = ∑ i : Fin (m n), |x n i| ^ k :=
    fun n k hk => cap2_sum_zeroPadRow_pow _ hk
  have hp' : ∀ k : ℕ, 2 ≤ k → Even k → Tendsto (fun n : ℕ =>
      ∑ i : Fin (m n + 1), (cap2ZeroPadRow (fun i : Fin (m n) => |x n i|) i) ^ k)
      atTop (𝓝 (∑' j : ℕ, lam j ^ k)) := by
    intro k hk hev
    refine Tendsto.congr (fun n => ?_) (hp k hk hev)
    rw [hpadsum n k (by omega)]
    exact (even_pow_sum_abs_congr (fun i : Fin (m n) => x n i) hev).symm
  have hpadded := paddedAbsRearranged_tendsto (fun n : ℕ => m n + 1)
    (fun n i => cap2ZeroPadRow (fun i : Fin (m n) => |x n i|) i) lam hm0 hmtop' hl hp'
  have hnn : ∀ (n : ℕ) (i : Fin (m n + 1)),
      0 ≤ cap2ZeroPadRow (fun i : Fin (m n) => |x n i|) i :=
    fun n i => cap2ZeroPadRow_nonneg _ (fun i => abs_nonneg _) i
  have habsId : ∀ n : ℕ,
      (fun i : Fin (m n + 1) => |cap2ZeroPadRow (fun i : Fin (m n) => |x n i|) i|)
        = (fun i : Fin (m n + 1) => cap2ZeroPadRow (fun i : Fin (m n) => |x n i|) i) :=
    fun n => funext fun i => abs_of_nonneg (hnn n i)
  refine Tendsto.congr' (Filter.Eventually.of_forall fun n => ?_) (hpadded j)
  rw [habsId n, cap2_padRearranged_zeroPad (fun i : Fin (m n) => |x n i|)
    (fun i => abs_nonneg _) j]

/-! ## The polynomial bandwidth `δ n = n^{-γ}` (feasible-window data) -/

/-- `n^{-γ}` is eventually positive. -/
private theorem cap2_powDelta_pos (γ : ℝ) (_hγ0 : 0 < γ) :
    ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) ^ (-γ) := by
  filter_upwards [eventually_ge_atTop 1] with n hn1
  exact Real.rpow_pos_of_pos (by exact_mod_cast hn1) _

/-- `n^{-γ} → 0`. -/
private theorem cap2_powDelta_tendsto_zero (γ : ℝ) (hγ0 : 0 < γ) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (-γ)) atTop (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ γ) atTop atTop :=
    (tendsto_rpow_atTop hγ0).comp tendsto_natCast_atTop_atTop
  have hbase : Tendsto (fun n : ℕ => ((n : ℝ) ^ γ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hpow
  refine hbase.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn1
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  rw [Real.rpow_neg hnR.le]

/-- `n * n^{-γ} = n^{1-γ} → ∞` for `γ < 1`. -/
private theorem cap2_mul_powDelta_tendsto_atTop (γ : ℝ) (hγ1 : γ < 1) :
    Tendsto (fun n : ℕ => (n : ℝ) * (n : ℝ) ^ (-γ)) atTop atTop := by
  have h : Tendsto (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) - γ)) atTop atTop :=
    (tendsto_rpow_atTop (show (0 : ℝ) < 1 - γ by linarith)).comp
      tendsto_natCast_atTop_atTop
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [show ((1 : ℝ) - γ) = ((1 : ℝ) + (-γ)) by ring,
    Real.rpow_add hnR (1 : ℝ) (-γ), Real.rpow_one]

/-! ## D3 without the refutable `hm` (the DEFECT-1-fixed signed endpoint) -/

set_option maxHeartbeats 10000000 in
/-- **The signed endpoint of the corrected route, DEFECT-1-fixed.**  This is
`Hurst.ActualQuadratureFinal.actualQ1LongStatistic_tendsto_secondChaos_signed`
with the hypothesis `hm : ∀ n, 0 < (localWeightActiveSet n 1 (δ n) t).card`
DELETED: that hypothesis is unsatisfiable (`card n = 0` at `n = 1`, the row
index type being `Fin (n - 1)`), which is DEFECT 1 of the audited capstone.
The only place D3's proof consumed `hm` is the `hAbs` peeling input, here
supplied by `cap2_paddedAbsRearranged_tendsto_of_eventualCard` from the DERIVED
eventual nonemptiness (`card / S → 2` ⇒ `card → ∞`) — small `n` rows of size
`0` are vacuous for `hane` and handled trivially by the padding. -/
theorem actualQ1LongStatistic_tendsto_secondChaos_signed_eventualCard
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M) (r : ℕ) (t : ℝ)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (ht : t ∈ Ioo (0 : ℝ) 1)
    {Theta : Type*} [MeasurableSpace Theta]
    (P' : Measure Theta) [IsProbabilityMeasure P']
    (Q : Theta → ℝ) (lam : ℕ → ℝ)
    (hQ : IsSecondChaosSeriesLaw P' Q lam)
    (hlam : Antitone lam ∧ ∀ j, 0 ≤ lam j ∧ Summable (fun j => lam j ^ 2))
    (hPow : ∀ k : ℕ, 2 ≤ k → Even k → Tendsto
      (fun n : ℕ => ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        (actualQ1Hermitian f hf r n (δ n) t).eigenvalues i ^ k)
      atTop (𝓝 (∑' j : ℕ, lam j ^ k)))
    (hane : ∀ (n : ℕ) (k : Fin (localWeightActiveSet n 1 (δ n) t).card),
      ∑ i, actualQ1Coeff n (δ n) t k i •
        actualQ1Obs f n (midpointSampleHurst f hf.1 n) i ≠ 0)
    (hNegMass : Tendsto (fun n : ℕ =>
      ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        (min ((actualQ1Hermitian f hf r n (δ n) t).eigenvalues i) 0) ^ 2)
      atTop (𝓝 0)) :
    TendstoInDistribution
      (fun (n : ℕ) x => gaussianLogQuadraticStatistic
        (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
        (actualQ1SpectralWeight f r n (δ n) t)
        (actualQ1Coeff n (δ n) t) x)
      atTop Q (fun n => featureGaussian
        (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) P' := by
  -- the exact eigenvalue binding (as in the D3 packaging)
  have hEv : ∀ n : ℕ, actualQ1Hermitian f hf r n (δ n) t
      = weightedFeatureQuadraticMatrix_isHermitian
          (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
          (actualQ1Coeff n (δ n) t)
          (actualQ1SpectralWeight f r n (δ n) t) := fun _ => rfl
  have hPt : ∀ (n : ℕ) (i : Fin (localWeightActiveSet n 1 (δ n) t).card),
      (actualQ1Hermitian f hf r n (δ n) t).eigenvalues i
        = (weightedFeatureQuadraticMatrix_isHermitian
            (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
            (actualQ1Coeff n (δ n) t)
            (actualQ1SpectralWeight f r n (δ n) t)).eigenvalues i := fun n i =>
    congrArg (fun H : (weightedFeatureQuadraticMatrix
        (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
        (actualQ1Coeff n (δ n) t)
        (actualQ1SpectralWeight f r n (δ n) t)).IsHermitian =>
      H.eigenvalues i) (hEv n)
  -- the even power sums, in the explicit weightedFeatureQuadraticMatrix form
  have hPowW : ∀ k : ℕ, 2 ≤ k → Even k → Tendsto (fun n : ℕ =>
      ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        (weightedFeatureQuadraticMatrix_isHermitian
            (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
            (actualQ1Coeff n (δ n) t)
            (actualQ1SpectralWeight f r n (δ n) t)).eigenvalues i ^ k)
      atTop (𝓝 (∑' j : ℕ, lam j ^ k)) := by
    intro k hk hev
    refine Tendsto.congr (fun n => Finset.sum_congr rfl fun i _ => ?_)
      (hPow k hk hev)
    exact congrArg (fun z : ℝ => z ^ k) (hPt n i)
  -- the active-card cardinality tends to infinity (DERIVED: card / S → 2)
  have hmtop : Tendsto (fun n : ℕ => (localWeightActiveSet n 1 (δ n) t).card)
      atTop atTop := by
    obtain ⟨_, hratio⟩ := localWeightActiveSet_card_ratio_tendsto_two 1
      t ht δ hδpos hδ0 hN
    rw [Filter.tendsto_atTop_atTop]
    intro N
    have hall : ∀ᶠ n : ℕ in atTop, (1 : ℝ) <
        ((localWeightActiveSet n 1 (δ n) t).card : ℝ) / ((n : ℝ) * δ n) ∧
        (N : ℝ) ≤ (n : ℝ) * δ n ∧ (1 : ℝ) ≤ (n : ℝ) * δ n := by
      filter_upwards [hratio.eventually_const_lt one_lt_two,
        hN.eventually_ge_atTop (N : ℝ), hN.eventually_ge_atTop 1] with n h1 h2 h3
      exact ⟨h1, h2, h3⟩
    obtain ⟨i, hi⟩ := Filter.eventually_atTop.mp hall
    refine ⟨i, fun a ha => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hi a ha
    have hS0 : (0 : ℝ) < (a : ℝ) * δ a := by linarith
    have hle : ((a : ℝ) * δ a) ≤ (localWeightActiveSet a 1 (δ a) t).card := by
      have hfac : ((localWeightActiveSet a 1 (δ a) t).card : ℝ)
          = ((localWeightActiveSet a 1 (δ a) t).card : ℝ) / ((a : ℝ) * δ a) *
            ((a : ℝ) * δ a) :=
        (div_mul_cancel₀ ((localWeightActiveSet a 1 (δ a) t).card : ℝ)
          (ne_of_gt hS0)).symm
      rw [hfac]
      exact le_trans (by rw [one_mul])
        (le_of_lt (mul_lt_mul_of_pos_right h1 hS0))
    exact_mod_cast (h2.trans hle)
  -- hAbs: the DEFECT-1-FIXED peeling input (eventual nonemptiness suffices)
  have hAbsW : ∀ j : ℕ, Tendsto (fun n : ℕ => padRearranged
      (fun i : Fin (localWeightActiveSet n 1 (δ n) t).card =>
        |(weightedFeatureQuadraticMatrix_isHermitian
            (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
            (actualQ1Coeff n (δ n) t)
            (actualQ1SpectralWeight f r n (δ n) t)).eigenvalues i|) j)
      atTop (𝓝 (lam j)) :=
    cap2_paddedAbsRearranged_tendsto_of_eventualCard
      (fun n : ℕ => (localWeightActiveSet n 1 (δ n) t).card)
      (fun n i => (weightedFeatureQuadraticMatrix_isHermitian
          (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
          (actualQ1Coeff n (δ n) t)
          (actualQ1SpectralWeight f r n (δ n) t)).eigenvalues i)
      lam hmtop hlam hPowW
  -- hNegMass: transported to the explicit eigenvalue form
  have hNegMassW : Tendsto (fun n : ℕ =>
      ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        (min ((weightedFeatureQuadraticMatrix_isHermitian
            (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
            (actualQ1Coeff n (δ n) t)
            (actualQ1SpectralWeight f r n (δ n) t)).eigenvalues i) 0) ^ 2)
      atTop (𝓝 0) := by
    refine Tendsto.congr (fun n => Finset.sum_congr rfl fun i _ => ?_) hNegMass
    exact congrArg (fun z : ℝ => (min z 0) ^ 2) (hPt n i)
  -- the matrix-level signed packaging (no `hm` anywhere)
  have hmatrix := centeredMatrixQuadratic_tendsto_secondChaos_of_signedMatching
    (fun n : ℕ => (localWeightActiveSet n 1 (δ n) t).card)
    (fun n => weightedFeatureQuadraticMatrix
        (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
        (actualQ1Coeff n (δ n) t)
        (actualQ1SpectralWeight f r n (δ n) t))
    (fun n => weightedFeatureQuadraticMatrix_isHermitian
        (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
        (actualQ1Coeff n (δ n) t)
        (actualQ1SpectralWeight f r n (δ n) t))
    P' Q lam hQ hmtop hAbsW (hPowW 2 (by norm_num) ⟨1, by norm_num⟩) hNegMassW
  -- transfer: the statistic is a.s.-equal to the centered matrix quadratic
  refine tendstoInDistribution_of_identDistrib_rows_varying
    (fun n => featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))
    (fun n => ProbabilityTheory.stdGaussian
      (EuclideanSpace ℝ (Fin (localWeightActiveSet n 1 (δ n) t).card)))
    P'
    (fun n x => gaussianLogQuadraticStatistic
      (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
      (actualQ1SpectralWeight f r n (δ n) t)
      (actualQ1Coeff n (δ n) t) x)
    (fun n => centeredMatrixQuadratic (weightedFeatureQuadraticMatrix
        (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
        (actualQ1Coeff n (δ n) t)
        (actualQ1SpectralWeight f r n (δ n) t)))
    Q atTop ?_ hmatrix
  intro n
  exact (gaussianLogQuadraticStatistic_identDistrib_normalizedCoordinates
      (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
      (actualQ1Coeff n (δ n) t)
      (actualQ1SpectralWeight f r n (δ n) t)).trans
    (centeredSpectralSquares_featureGaussian_identDistrib_centeredMatrixQuadratic
      (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
      (actualQ1Coeff n (δ n) t)
      (actualQ1SpectralWeight f r n (δ n) t) (hane n))

/-! ## THE CAPSTONE V2 -/

set_option maxHeartbeats 10000000 in
/-- **THE CAPSTONE V2 (non-vacuous).**  Under the ordinary model data, the
FEASIBLE bandwidth window (B) — `δ n = n^{-γ}`, `0 < γ < 1` (witness
`γ = (1 + L)/2`, `L = (b - h)/(1 - h)`, satisfiable for EVERY `h ≤ b < 1`),
`(1 - γ) * (2 - 2 * f t) < 2 - 2 * b` — and the honest interface hypotheses

* `hlam` : the antitone nonnegative Riesz target spectrum,
* `hRiesz` : the spectrum bridge `∑' lam ^ k = J_k` (P2's construction
  obligation, DEFECT 4 — the only remaining hypothesis; a `HasSum` statement
  about the enumeration-to-be of the Riesz operator's spectrum),
* `hane` : ordinary row nondegeneracy (generic; vacuous on zero rows),
* `hwnn` : eventual entrywise nonnegativity of the spectral weights (the
  balanced degree-one regime, DEFECT 5),

the CONSTRUCTED second-chaos law `Q` of
`Hurst.P4GaussianSeriesLaw.exists_isSecondChaosSeriesLaw_gaussSeq` (DEFECT 3 —
built from `Summable (lam ^ 2)`, itself derived from `hRiesz` at `k = 2`)
satisfies: the actual q1 long-memory quadratic statistic converges to `Q` in
distribution.  There is NO `hcard` hypothesis (DEFECT 1: eventual
nonemptiness is derived from `card / S → 2`, small `n` trivial by padding) and
NO `hQ` hypothesis. -/
theorem actualQ1LongStatistic_tendsto_secondChaos_v2
    (p a b M : ℝ) (r : ℕ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (hM : 0 ≤ M) (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hgrid : (1 - γ) * (2 - 2 * f t) < 2 - 2 * b)
    (lam : ℕ → ℝ)
    (hlam : Antitone lam ∧ ∀ j, 0 ≤ lam j)
    (hRiesz : ∀ k : ℕ, 2 ≤ k → HasSum (fun j => lam j ^ k)
      (weightedRieszCycleIntegral k (2 - 2 * f t) (f t * (2 * f t - 1))
        (equivalentKernel r)))
    (hane : ∀ (n : ℕ) (k : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card),
      ∑ i, actualQ1Coeff n ((n : ℝ) ^ (-γ)) t k i •
        actualQ1Obs f n (midpointSampleHurst f hf.1 n) i ≠ 0)
    (hwnn : ∀ᶠ n : ℕ in atTop,
      ∀ i : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
      0 ≤ actualQ1SpectralWeight f r n ((n : ℝ) ^ (-γ)) t i) :
    ∃ Q : (ℕ → ℝ) → ℝ, IsSecondChaosSeriesLaw gaussianSeqMeasure Q lam ∧
      TendstoInDistribution
        (fun (n : ℕ) x => gaussianLogQuadraticStatistic
          (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
          (actualQ1SpectralWeight f r n ((n : ℝ) ^ (-γ)) t)
          (actualQ1Coeff n ((n : ℝ) ^ (-γ)) t) x)
        atTop Q (fun n => featureGaussian
          (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) gaussianSeqMeasure := by
  -- DEFECT 3: the law is CONSTRUCTED (P4) from the square-summability of lam,
  -- itself derived from the hRiesz bridge at k = 2
  have hlam2 : Summable (fun j : ℕ => lam j ^ 2) := (hRiesz 2 (by norm_num)).summable
  obtain ⟨Q, hQ⟩ := exists_isSecondChaosSeriesLaw_gaussSeq lam hlam2
  refine ⟨Q, hQ, ?_⟩
  -- the feasible-window polynomial-bandwidth data
  have hδpos : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) ^ (-γ) := cap2_powDelta_pos γ hγ0
  have hδ0 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-γ)) atTop (𝓝 0) :=
    cap2_powDelta_tendsto_zero γ hγ0
  have hN : Tendsto (fun n : ℕ => (n : ℝ) * ((n : ℝ) ^ (-γ))) atTop atTop :=
    cap2_mul_powDelta_tendsto_atTop γ hγ1
  -- hPow: P1's power sums (ALL k ≥ 2, feasible window) + the hRiesz bridge
  have hPow : ∀ k : ℕ, 2 ≤ k → Even k → Tendsto
      (fun n : ℕ => ∑ i : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
        (actualQ1Hermitian f hf r n ((n : ℝ) ^ (-γ)) t).eigenvalues i ^ k)
      atTop (𝓝 (∑' j : ℕ, lam j ^ k)) := by
    intro k hk _
    have hP1 := actualQ1_eigenPowerSums_feasible p a b M r hp ha hb hab hM f hf hF
      t ht hlong γ hγ0 hγ1 hgrid k hk
    rw [(hRiesz k hk).tsum_eq]
    exact hP1
  -- hNegMass: discharged by hwnn via the PSD congruence (WeightedMatrixPSD)
  have hEv : ∀ n : ℕ, actualQ1Hermitian f hf r n ((n : ℝ) ^ (-γ)) t
      = weightedFeatureQuadraticMatrix_isHermitian
          (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
          (actualQ1Coeff n ((n : ℝ) ^ (-γ)) t)
          (actualQ1SpectralWeight f r n ((n : ℝ) ^ (-γ)) t) := fun _ => rfl
  have hPt : ∀ (n : ℕ) (i : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card),
      (actualQ1Hermitian f hf r n ((n : ℝ) ^ (-γ)) t).eigenvalues i
        = (weightedFeatureQuadraticMatrix_isHermitian
            (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
            (actualQ1Coeff n ((n : ℝ) ^ (-γ)) t)
            (actualQ1SpectralWeight f r n ((n : ℝ) ^ (-γ)) t)).eigenvalues i :=
    fun n i => congrArg (fun H : (weightedFeatureQuadraticMatrix
        (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
        (actualQ1Coeff n ((n : ℝ) ^ (-γ)) t)
        (actualQ1SpectralWeight f r n ((n : ℝ) ^ (-γ)) t)).IsHermitian =>
      H.eigenvalues i) (hEv n)
  have hNegMass : Tendsto (fun n : ℕ =>
      ∑ i : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
        (min ((actualQ1Hermitian f hf r n ((n : ℝ) ^ (-γ)) t).eigenvalues i) 0) ^ 2)
      atTop (𝓝 0) := by
    have hstep : ∀ᶠ n : ℕ in atTop,
        (∑ i : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
          (min ((actualQ1Hermitian f hf r n ((n : ℝ) ^ (-γ)) t).eigenvalues i) 0) ^ 2)
        = 0 := by
      filter_upwards [hwnn] with n hwn
      refine Finset.sum_eq_zero fun i _ => ?_
      have h0 : 0 ≤ (weightedFeatureQuadraticMatrix_isHermitian
          (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
          (actualQ1Coeff n ((n : ℝ) ^ (-γ)) t)
          (actualQ1SpectralWeight f r n ((n : ℝ) ^ (-γ)) t)).eigenvalues i :=
        weightedFeatureQuadraticMatrix_eigenvalues_nonneg
          (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
          (actualQ1Coeff n ((n : ℝ) ^ (-γ)) t)
          (actualQ1SpectralWeight f r n ((n : ℝ) ^ (-γ)) t) hwn i
      rw [← hPt n i, min_eq_right h0]
      ring
    exact tendsto_nhds_of_eventually_eq hstep
  -- the composition through the DEFECT-1-fixed signed endpoint
  exact actualQ1LongStatistic_tendsto_secondChaos_signed_eventualCard f hf r t
    (fun n : ℕ => (n : ℝ) ^ (-γ)) hδpos hδ0 hN ht gaussianSeqMeasure Q lam hQ
    ⟨hlam.1, fun j => ⟨hlam.2 j, hlam2⟩⟩ hPow hane hNegMass

end Hurst
