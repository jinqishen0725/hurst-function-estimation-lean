import Hurst.ActualQuadratureConfluence
import Hurst.ActualSecondChaosComplete
import Hurst.FarWordAssembly

/-!
# P1: actual-matrix eigenvalue power sums under the FEASIBLE bandwidth window

This module is the Lean realization of PACKAGE P1 (deliverables W1, W4, W5 of
`direct_proofs/22_long_memory_repair_lean_handoff.md`): the actual-matrix
eigenvalue power sums converge to the weighted Riesz cycle integrals `J_k` for
EVERY fixed power `k ≥ 2`, with **no dimension-weighted perturbation rate**
(the old `hPert` is gone) and **no full-row nonemptiness hypothesis** (the old
`hcard : ∀ n, 0 < card n` is gone).

## The exact bandwidth window (feasible window (B))

Fix the actual q1 long-memory model data `p a b M r f t` as in
`Hurst.ActualQuadratureConfluence` (`f ∈ hurstHolderClass p M` bounded on
`(0,1)` with values in `[a, b]`, `t ∈ (0,1)` interior, `h := f t > 3/4`,
`ψ := 2 - 2 * f t ∈ (0, 1/2)`, `c := f t * (2 * f t - 1) > 0`).  The ONLY
bandwidth requirement of this module is

    0 < γ < 1      and      (1 - γ) * ψ < 2 - 2 * b,                (B)

i.e. `δ n = n^{-γ}`, `S n = n * δ n = n^{1-γ} → ∞`.  Since `h = f t ≤ b < 1`,
(B) is nonempty: with `L := (b - h) / (1 - h) ∈ [0, 1)` every `γ ∈ (L, 1)`
works (e.g. `γ = (1 + L) / 2`); this is `feasibleBandwidth_window_nonempty`
below.  The old window `γ < 4 * h - 3` together with
`4 * b + 1 - 4 * h < γ * (5 - 4 * h)` of the pre-audit capstone was
CONTRADICTORY (`capstone_bandwidth_window_impossible`); it is not used here,
and nothing in this module compares `γ` with `4 * h - 3`.

## The R-choice (the cutoff, not the bandwidth)

The truncation radius is `R n = ⌊S n^{(4 * h - 3) / 2}⌋ + 1`, chosen inside
`Hurst.poly_cutoff_satisfiable`; its exponent `θ := (4 * h - 3) / 2 > 0` needs
ONLY `h > 3/4`, so the cutoff bound
`S^{2ψ - 2} * card * (2 R + 1) ≤ 15 * S^{θ + 3 - 4h} → 0`
(exponent `θ + 3 - 4h = θ - (1 - 2ψ) < 0`) is available simultaneously with
any `γ` satisfying (B).  `θ` controls the truncation, `γ` controls the
bandwidth; the two never conflict.  This is the feasible R-choice bundle
`p1_feasibleBandwidth_cutoff_and_envelope` (the repaired
`polyBandwidth_cutoff_and_envelope`, with the contradictory `hγcut` replaced
by the honest `hγ1 : γ < 1`).

## The dimension-free trace engine (W4)

The transfer from mesh energy to trace powers uses
`Hurst.abs_trace_pow_sub_le_frob` (`Hurst.FarWordAssembly`):

    |tr(A ^ k) - tr(T ^ k)| ≤ k * M ^ (k - 1) * ‖A - T‖_F   (‖A‖, ‖T‖ ≤ M),

which carries NO dimension factor (no `√card`).  Consumed with
`‖A_n - T_n‖_F → 0` from `actualQ1_meshEnergy_tendsto_zero` — the UNWEIGHTED
(corrected) mesh-energy convergence discharged from the PROVED kernel theorem
`hurstHolder_q1_actual_weighted_kernel_hilbertSchmidt_to_riesz` with the
feasible R-choice above — this replaces the old dimension-weighted
perturbation rate `hPert` in its entirety.  The wrapper is
`p1_trace_pow_sub_tendsto_zero_of_frobenius`.

## Nonemptiness (W2, at this layer)

Every statement here is total in `n` (the matrices are defined for all `n`,
including `card n = 0`, where the eigenvalue sum is empty and everything is
trivial), and all asymptotic identifications are made through `∀ᶠ n in atTop`
congruences.  Eventual nonemptiness `0 < card n` is DERIVED from the window
via `localWeightActiveSet_card_ratio_tendsto_two` (`card n / S n → 2`, so
`card n → ∞`); no `∀ n, 0 < card n` hypothesis appears.

## The limit (W5)

`J_k := weightedRieszCycleIntegral k ψ c (equivalentKernel r)`, the absolutely
convergent cyclic integral `c^k ∫ ∏ ω(x_j) |x_j - x_{j+1}|^{-ψ}`.  The
comparison trace converges to `J_k` through
`hasWeightedRieszCycleQuadrature_instance` (which needs exactly
`card n → ∞`, `card n / S n → 2`, `0 < ψ < 1/2`, and continuity/boundedness of
`ω` on `[-1,1]`) and `weightedRieszDiscrete_trace_pow_tendsto`; the eigenvalue
identification is the finite-dimensional chain
`hermitian_trace_pow_eq_sum_eigenvalues_pow` +
`trace_pow_weightedFeatureQuadraticMatrix_eq` +
`actualQ1_diagonalCorrelation_eq`.

## Contents

* `feasibleBandwidth_window_nonempty` : window (B) is nonempty for
  `h ≤ b < 1` (explicit witness);
* `p1_feasibleBandwidth_cutoff_and_envelope` : under (B), the feasible
  R-choice satisfies the cutoff AND the ∀-form tail-envelope hypotheses of the
  kernel-energy theorem simultaneously;
* `p1_trace_pow_sub_tendsto_zero_of_frobenius` : W4, the generic
  dimension-free asymptotic transfer;
* `actualQ1_trace_pow_feasible` : DELIVERABLE (1) — for every `k ≥ 2`,
  `|tr(A_n ^ k) - tr(T_n ^ k)| → 0` under the feasible bandwidth;
* `actualQ1_eigenPowerSums_feasible` : DELIVERABLE (2) — for every `k ≥ 2`,
  `∑_i (actualQ1Hermitian ...).eigenvalues i ^ k → J_k`.

Neither deliverable has `hcard`, `hγcut`, `hγdec`, `hPert`, `hFrozenPert`,
`hwnn`, `hRiesz` or `hQ` among its hypotheses.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Set MeasureTheory Filter Matrix Real
open scoped Topology RealInnerProductSpace Matrix.Norms.Frobenius

namespace Hurst

/-! ## W1: the feasible bandwidth window and its cutoff/envelope bundle -/

/-- `n^{-γ}` is eventually positive. -/
private theorem p1_powDelta_pos (γ : ℝ) (_hγ0 : 0 < γ) :
    ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) ^ (-γ) := by
  filter_upwards [eventually_ge_atTop 1] with n hn1
  exact Real.rpow_pos_of_pos (by exact_mod_cast hn1) _

/-- `n^{-γ} → 0`. -/
private theorem p1_powDelta_tendsto_zero (γ : ℝ) (hγ0 : 0 < γ) :
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
private theorem p1_mul_powDelta_tendsto_atTop (γ : ℝ) (hγ1 : γ < 1) :
    Tendsto (fun n : ℕ => (n : ℝ) * (n : ℝ) ^ (-γ)) atTop atTop := by
  have h : Tendsto (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) - γ)) atTop atTop :=
    (tendsto_rpow_atTop (show (0 : ℝ) < 1 - γ by linarith)).comp
      tendsto_natCast_atTop_atTop
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [show ((1 : ℝ) - γ) = ((1 : ℝ) + (-γ)) by ring,
    Real.rpow_add hnR (1 : ℝ) (-γ), Real.rpow_one]

/-- **The feasible bandwidth window is nonempty (W1).**  For `h ≤ b < 1` the
window `0 < γ < 1 ∧ (1 - γ) * (2 - 2 * h) < 2 - 2 * b` contains, e.g., the
explicit point `γ = (1 + L) / 2` with `L = (b - h) / (1 - h) ∈ [0, 1)`, for
which `(1 - γ) * (2 - 2 * h) = 1 - b < 2 - 2 * b`.  No condition of the form
`γ < 4 * h - 3` is needed. -/
theorem feasibleBandwidth_window_nonempty (h b : ℝ) (hhb : h ≤ b) (hb1 : b < 1) :
    ∃ γ : ℝ, 0 < γ ∧ γ < 1 ∧ (1 - γ) * (2 - 2 * h) < 2 - 2 * b := by
  have h1h : 0 < 1 - h := by linarith
  have hL0 : 0 ≤ (b - h) / (1 - h) := div_nonneg (by linarith) h1h.le
  have hL1 : (b - h) / (1 - h) < 1 := (div_lt_iff₀ h1h).mpr (by linarith)
  refine ⟨(1 + (b - h) / (1 - h)) / 2, by linarith, by linarith, ?_⟩
  have hkey : (1 - (1 + (b - h) / (1 - h)) / 2) * (2 - 2 * h) = 1 - b := by
    field_simp
    ring
  rw [hkey]
  linarith

/-- **The feasible-bandwidth cutoff/envelope bundle (W1, repaired).**  For the
polynomial bandwidth `δ n = n^{-γ}` with `0 < γ < 1` (the window point itself;
the grid-rate condition `(1 - γ) * (2 - 2 * h0) < 2 - 2 * b` is the OTHER half
of window (B)), the single choice `R n = ⌊S n^{(4 * h0 - 3) / 2}⌋ + 1`
(`S n = n * n^{-γ}`) simultaneously satisfies:
* the ordinary cutoff `S^{2ψ - 2} * card * (2 R + 1) → 0` (via
  `poly_cutoff_satisfiable`, whose proof needs only `h0 > 3/4` — the
  `γ < 4 * h0 - 3` comparison of the old bundle is nowhere required), and
* the ∀-form tail-envelope hypothesis of the kernel-energy theorem, via
  `secondChaosTailFreePart_tendsto_zero_powBandwidth` (which already takes the
  feasible-window data `hγ0`, `hγ1`, `hgrid`). -/
theorem p1_feasibleBandwidth_cutoff_and_envelope
    (b M h0 γ : ℝ) (hM : 0 ≤ M)
    (hh0 : 3 / 4 < h0) (hh01 : h0 < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hgrid : (1 - γ) * (2 - 2 * h0) < 2 - 2 * b)
    (card : ℕ → ℕ)
    (hcardub : ∀ᶠ n in atTop, (card n : ℝ) ≤ 3 * ((n : ℝ) * (n : ℝ) ^ (-γ))) :
    ∃ R : ℕ → ℕ, (∀ᶠ n in atTop, 1 ≤ R n) ∧
      Tendsto (fun n : ℕ => (R n : ℝ)) atTop atTop ∧
      Tendsto (fun n : ℕ => ((n : ℝ) * (n : ℝ) ^ (-γ)) ^ (2 * (2 - 2 * h0) - 2) *
        (card n : ℝ) * (2 * (R n : ℝ) + 1)) atTop (𝓝 0) ∧
      ∀ Ccov ≥ 0, ∀ Ctail ≥ 0, ∀ L > 0, Tendsto (fun n : ℕ =>
        q1ActualLongTailEnvelope b Ccov Ctail L M h0 n ((n : ℝ) ^ (-γ))
          ((n : ℝ) * (n : ℝ) ^ (-γ)) (R n)) atTop (𝓝 0) := by
  obtain ⟨R, hR1, hRtop, hcut⟩ := poly_cutoff_satisfiable h0 card
    (fun n : ℕ => (n : ℝ) * (n : ℝ) ^ (-γ)) (p1_mul_powDelta_tendsto_atTop γ hγ1)
    hcardub hh0
  refine ⟨R, hR1, hRtop, hcut, ?_⟩
  intro Ccov hCcov Ctail hCtail L hL
  have hfree := secondChaosTailFreePart_tendsto_zero_powBandwidth b Ccov Ctail L M
    h0 γ hCcov hCtail hL hM hh0 hh01 hγ0 hγ1 hgrid
  -- 16 / (R + 1) → 0 from R → ∞
  have hRinf : Tendsto (fun n : ℕ => (R n : ℝ) + 1) atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro β
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hRtop.eventually_ge_atTop (β - 1))
    exact ⟨N, fun a ha => by have hle := hN a ha; linarith⟩
  have hRterm : Tendsto (fun n : ℕ => 16 * ((R n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp hRinf).const_mul 16
  have hsum : Tendsto (fun n : ℕ =>
      secondChaosTailFreePart b Ccov Ctail L M h0 n ((n : ℝ) ^ (-γ))
        ((n : ℝ) * (n : ℝ) ^ (-γ)) + 16 * ((R n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa using hfree.add hRterm
  refine Tendsto.congr (fun n => ?_) hsum
  rw [q1ActualLongTailEnvelope_eq_free]

/-! ## W4: the dimension-free trace-power transfer -/

/-- **W4 wrapper: the trace-power difference dies with the Frobenius
difference (NO dimension factor).**  If the two matrix arrays are eventually
Frobenius-bounded by a common constant `C` and `‖A n - G n‖_F → 0`, then for
every fixed `k ≥ 2` the absolute trace-power difference tends to zero.  This
is `abs_trace_pow_sub_le_frob` (`k * C ^ (k - 1) * ‖A - G‖_F` bound, with the
DIFFERENCE the only small factor) plus the squeeze; contrast the old
`mesh_frobenius_trace_pow_tendsto`, whose `√(2 / card)` bookkeeping forced the
dimension-weighted rate `hPert`. -/
theorem p1_trace_pow_sub_tendsto_zero_of_frobenius
    (m : ℕ → ℕ)
    (A G : ∀ n, Matrix (Fin (m n)) (Fin (m n)) ℝ)
    (C : ℝ)
    (hC : ∀ᶠ n in atTop, max ‖A n‖ ‖G n‖ ≤ C)
    (hΔ : Tendsto (fun n : ℕ => ‖A n - G n‖) atTop (𝓝 0))
    (k : ℕ) (hk : 2 ≤ k) :
    Tendsto (fun n : ℕ => |Matrix.trace ((A n) ^ k) - Matrix.trace ((G n) ^ k)|)
      atTop (𝓝 0) := by
  obtain ⟨C', hC'0, hC'⟩ : ∃ C', 0 ≤ C' ∧ ∀ᶠ n in atTop, max ‖A n‖ ‖G n‖ ≤ C' :=
    ⟨max C 0, by positivity, hC.mono fun n h => le_trans h (le_max_left _ _)⟩
  have hscales : (0 : ℝ) ≤ (k : ℝ) * C' ^ (k - 1) :=
    mul_nonneg (Nat.cast_nonneg k) (pow_nonneg hC'0 _)
  refine squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_
    (by simpa using hΔ.const_mul ((k : ℝ) * C' ^ (k - 1)))
  filter_upwards [hC'] with n hCn
  exact abs_trace_pow_sub_le_frob (A n) (G n) k hk _ (le_trans (le_max_left _ _) hCn)
    (le_trans (le_max_right _ _) hCn)

/-- From `|d| → 0` to `d → 0` (sandwich between `-|d|` and `|d|`). -/
private theorem p1_tendsto_zero_of_abs {d : ℕ → ℝ}
    (h : Tendsto (fun n => |d n|) atTop (𝓝 0)) : Tendsto d atTop (𝓝 0) := by
  have hneg : Tendsto (fun n => -|d n|) atTop (𝓝 0) := by
    simpa using h.neg
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hneg h
    (Eventually.of_forall fun n => neg_abs_le _) (Eventually.of_forall fun n => le_abs_self _)

/-! ## Deliverable (1): the trace-power difference under the feasible window -/

/-- **DELIVERABLE (1) (`actualQ1_trace_pow_feasible`).**  Under the FEASIBLE
bandwidth window (B) — `δ n = n^{-γ}`, `0 < γ < 1`, `(1 - γ) * (2 - 2 * f t) <
2 - 2 * b` — for every fixed `k ≥ 2` the absolute trace-power difference
between the mesh-normalized actual matrix `A_n` =
`actualQ1NormalizedActualMatrix` and the Riesz quadrature matrix `T_n` =
`actualQ1RieszMatrix` tends to zero.  This mirrors the W1–W5 written proof:
the mesh energy (unweighted) tends to zero by the PROVED kernel theorem with
the feasible R-choice `R n = ⌊S n^{(4h-3)/2}⌋ + 1`, and W4 transfers it to the
trace powers WITHOUT any dimension factor.  No `hcard`, no `hPert`, no
`hγcut`/`hγdec`. -/
theorem actualQ1_trace_pow_feasible
    (p a b M : ℝ) (r : ℕ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (hM : 0 ≤ M) (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hgrid : (1 - γ) * (2 - 2 * f t) < 2 - 2 * b)
    (k : ℕ) (hk : 2 ≤ k) :
    Tendsto (fun n : ℕ => |Matrix.trace
          ((actualQ1NormalizedActualMatrix f hf r n ((n : ℝ) ^ (-γ)) t) ^ k) -
        Matrix.trace ((actualQ1RieszMatrix f r n ((n : ℝ) ^ (-γ)) t) ^ k)|)
      atTop (𝓝 0) := by
  have hftb : f t ≤ b := (hF ht).2
  have hft1 : f t < 1 := lt_of_le_of_lt hftb hb
  -- the polynomial bandwidth data
  have hδpos : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) ^ (-γ) := p1_powDelta_pos γ hγ0
  have hδ0 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-γ)) atTop (𝓝 0) :=
    p1_powDelta_tendsto_zero γ hγ0
  have hN : Tendsto (fun n : ℕ => (n : ℝ) * (n : ℝ) ^ (-γ)) atTop atTop :=
    p1_mul_powDelta_tendsto_atTop γ hγ1
  obtain ⟨hcardpos, hratio⟩ := localWeightActiveSet_card_ratio_tendsto_two 1 t ht
    (fun n : ℕ => (n : ℝ) ^ (-γ)) hδpos hδ0 hN
  -- eventual `card ≤ 3 * S` (eventual nonemptiness is `hcardpos`; no global
  -- `∀ n, 0 < card` is assumed anywhere)
  have hcardub : ∀ᶠ n : ℕ in atTop,
      ((localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card : ℝ)
        ≤ 3 * ((n : ℝ) * (n : ℝ) ^ (-γ)) := by
    filter_upwards [hcardpos, hδpos,
      hratio.eventually_lt_const (show ((2 : ℝ) < 3) by norm_num)] with n hcard hδ hlt
    have hn : 0 < n := by
      have hlt2 := (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t ⟨0, hcard⟩).isLt
      omega
    have hS0 : (0 : ℝ) < (n : ℝ) * (n : ℝ) ^ (-γ) := mul_pos (by exact_mod_cast hn) hδ
    have hle := (div_lt_iff₀ hS0).mp hlt
    linarith
  -- the feasible R-choice: cutoff and envelope hold simultaneously
  obtain ⟨R, hR1, hRtop, hcut, henv⟩ :=
    p1_feasibleBandwidth_cutoff_and_envelope b M (f t) γ hM hlong hft1 hγ0 hγ1
      hgrid (fun n : ℕ => (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card) hcardub
  have hEmesh := actualQ1_meshEnergy_tendsto_zero p a b M r hp ha hb hab hM f hf hF
    t ht hlong (fun n : ℕ => (n : ℝ) ^ (-γ)) hδpos hδ0 hN R hR1 hcut henv
  -- the uniform Frobenius bound, discharged entrywise (Bω from
  -- `equivalentKernel_bounded`; Cref from `rankRieszKernel_energy_le_const`)
  obtain ⟨Bω, hBω0, hBω⟩ := equivalentKernel_bounded r
  have hpsi0 : 0 ≤ 2 - 2 * f t := by linarith
  have hpsihalf : 2 - 2 * f t < 1 / 2 := by linarith
  have hCref : ∀ (S : ℝ) (m : ℕ), 1 ≤ S → (m : ℝ) ≤ 3 * S →
      realScaleMeshEnergy S
        (rankRieszKernel S (2 - 2 * f t) (f t * (2 * f t - 1)) :
          Fin m → Fin m → ℝ)
        ≤ 2 * (f t * (2 * f t - 1)) ^ 2 *
          (3 + 3 * 4 ^ (1 - 2 * (2 - 2 * f t)) / (1 - 2 * (2 - 2 * f t))) :=
    fun S m hS hm =>
    rankRieszKernel_energy_le_const S (2 - 2 * f t) (f t * (2 * f t - 1)) hS hm
      hpsi0 hpsihalf
  obtain ⟨C, hC0, hCbnd⟩ := actualQ1UniformFrobeniusBound_of_bounded f hf r
    (fun n : ℕ => (n : ℝ) ^ (-γ)) t ht hδpos hδ0 hN Bω (fun z hz => hBω z) _ hCref hEmesh
  have hΔ := actualQ1_frobenius_norm_tendsto_zero f hf r
    (fun n : ℕ => (n : ℝ) ^ (-γ)) t hδpos hEmesh
  exact p1_trace_pow_sub_tendsto_zero_of_frobenius
    (fun n : ℕ => (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card)
    (fun n => actualQ1NormalizedActualMatrix f hf r n ((n : ℝ) ^ (-γ)) t)
    (fun n => actualQ1RieszMatrix f r n ((n : ℝ) ^ (-γ)) t)
    C hCbnd hΔ k hk

/-! ## Deliverable (2): all eigenvalue power sums converge to `J_k` -/

/-- **DELIVERABLE (2) (`actualQ1_eigenPowerSums_feasible`).**  Under the
FEASIBLE bandwidth window (B), for every fixed `k ≥ 2` the eigenvalue power
sums of the actual q1 Hermitian spectral matrix converge to the weighted Riesz
cycle integral `J_k = weightedRieszCycleIntegral k ψ c (equivalentKernel r)`
with `ψ = 2 - 2 * f t` and `c = f t * (2 * f t - 1)`:

    ∑_i (actualQ1Hermitian f hf r n (δ n) t).eigenvalues i ^ k → J_k.

Route (W5 of the written handoff): the quadrature theorem gives
`tr(T_n ^ k) → J_k`; Deliverable (1) gives `tr(A_n ^ k) - tr(T_n ^ k) → 0`
(dimension-free, W4); and the finite-dimensional trace-eigenvalue identity
(`hermitian_trace_pow_eq_sum_eigenvalues_pow`,
`trace_pow_weightedFeatureQuadraticMatrix_eq`,
`actualQ1_diagonalCorrelation_eq`) identifies the eigenvalue power sum with
`tr(A_n ^ k)` EVENTUALLY (from `card n > 0` and `δ n > 0`, both derived from
the window — no full-row hypothesis).  Hypothesis-free of `hcard`, `hPert`,
`hγcut`, `hγdec`, `hwnn`, `hRiesz`, `hQ`. -/
theorem actualQ1_eigenPowerSums_feasible
    (p a b M : ℝ) (r : ℕ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (hM : 0 ≤ M) (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hgrid : (1 - γ) * (2 - 2 * f t) < 2 - 2 * b)
    (k : ℕ) (hk : 2 ≤ k) :
    Tendsto (fun n : ℕ =>
        ∑ i : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
          (actualQ1Hermitian f hf r n ((n : ℝ) ^ (-γ)) t).eigenvalues i ^ k)
      atTop (𝓝 (weightedRieszCycleIntegral k (2 - 2 * f t)
        (f t * (2 * f t - 1)) (equivalentKernel r))) := by
  have hftb : f t ≤ b := (hF ht).2
  have hft1 : f t < 1 := lt_of_le_of_lt hftb hb
  have hδpos : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) ^ (-γ) := p1_powDelta_pos γ hγ0
  have hδ0 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-γ)) atTop (𝓝 0) :=
    p1_powDelta_tendsto_zero γ hγ0
  have hN : Tendsto (fun n : ℕ => (n : ℝ) * (n : ℝ) ^ (-γ)) atTop atTop :=
    p1_mul_powDelta_tendsto_atTop γ hγ1
  obtain ⟨hcardpos, hratio⟩ := localWeightActiveSet_card_ratio_tendsto_two 1 t ht
    (fun n : ℕ => (n : ℝ) ^ (-γ)) hδpos hδ0 hN
  -- the active card tends to infinity (eventual nonemptiness, from the window)
  have hmtop : Tendsto (fun n : ℕ =>
      (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card) atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro N
    have hall : ∀ᶠ n : ℕ in atTop, (1 : ℝ) <
        ((localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card : ℝ) /
          ((n : ℝ) * (n : ℝ) ^ (-γ)) ∧
        (N : ℝ) ≤ (n : ℝ) * (n : ℝ) ^ (-γ) ∧ (1 : ℝ) ≤ (n : ℝ) * (n : ℝ) ^ (-γ) := by
      filter_upwards [hratio.eventually_const_lt one_lt_two,
        hN.eventually_ge_atTop (N : ℝ), hN.eventually_ge_atTop 1] with n h1 h2 h3
      exact ⟨h1, h2, h3⟩
    obtain ⟨i, hi⟩ := Filter.eventually_atTop.mp hall
    refine ⟨i, fun a ha => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hi a ha
    have hS0 : (0 : ℝ) < (a : ℝ) * (a : ℝ) ^ (-γ) := by linarith
    have heq : ((localWeightActiveSet a 1 ((a : ℝ) ^ (-γ)) t).card : ℝ)
        = ((localWeightActiveSet a 1 ((a : ℝ) ^ (-γ)) t).card : ℝ) /
            ((a : ℝ) * (a : ℝ) ^ (-γ)) * ((a : ℝ) * (a : ℝ) ^ (-γ)) := by
      rw [div_mul_cancel₀
        (a := ((localWeightActiveSet a 1 ((a : ℝ) ^ (-γ)) t).card : ℝ))
        (h := by linarith)]
    have hle : ((a : ℝ) * (a : ℝ) ^ (-γ))
        ≤ (localWeightActiveSet a 1 ((a : ℝ) ^ (-γ)) t).card := by
      rw [heq]
      exact le_trans (by rw [one_mul]) (le_of_lt (mul_lt_mul_of_pos_right h1 hS0))
    exact_mod_cast (h2.trans hle)
  -- the quadrature instance along the active grid
  obtain ⟨Bω, hBω0, hBω⟩ := equivalentKernel_bounded r
  have hpsi0 : 0 < 2 - 2 * f t := by linarith
  have hpsihalf : 2 * (2 - 2 * f t) < 1 := by linarith
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) * (n : ℝ) ^ (-γ) ∧
      0 < (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card := by
    filter_upwards [hcardpos, hδpos, Filter.eventually_ge_atTop 1] with n hcard hδ hn
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    exact ⟨mul_pos hnR hδ, hcard⟩
  have hquad := hasWeightedRieszCycleQuadrature_instance
    (fun n : ℕ => (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card)
    (fun n : ℕ => (n : ℝ) * (n : ℝ) ^ (-γ)) (2 - 2 * f t) (f t * (2 * f t - 1)) Bω
    (equivalentKernel r) hmtop hratio hpos hpsi0 hpsihalf
    (equivalentKernel_continuous r) (fun z hz => hBω z)
  have hG : Tendsto (fun n : ℕ => Matrix.trace
      ((actualQ1RieszMatrix f r n ((n : ℝ) ^ (-γ)) t) ^ k)) atTop
      (𝓝 (weightedRieszCycleIntegral k (2 - 2 * f t) (f t * (2 * f t - 1))
        (equivalentKernel r))) := by
    show Tendsto (fun n : ℕ => Matrix.trace
      ((weightedRieszDiscreteMatrix
          (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card
          ((n : ℝ) * (n : ℝ) ^ (-γ)) (2 - 2 * f t) (f t * (2 * f t - 1))
          (equivalentKernel r)) ^ k)) atTop _
    exact weightedRieszDiscrete_trace_pow_tendsto _ _ _ _ _ hquad k hk
  -- Deliverable (1): the dimension-free trace-difference convergence
  have habsdiff := actualQ1_trace_pow_feasible p a b M r hp ha hb hab hM f hf hF
    t ht hlong γ hγ0 hγ1 hgrid k hk
  have hd : Tendsto (fun n : ℕ => Matrix.trace
        ((actualQ1NormalizedActualMatrix f hf r n ((n : ℝ) ^ (-γ)) t) ^ k) -
      Matrix.trace ((actualQ1RieszMatrix f r n ((n : ℝ) ^ (-γ)) t) ^ k)) atTop
      (𝓝 0) :=
    p1_tendsto_zero_of_abs habsdiff
  -- the trace-eigenvalue identification, eventually
  have htr : ∀ᶠ n : ℕ in atTop,
      (∑ i : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
          (actualQ1Hermitian f hf r n ((n : ℝ) ^ (-γ)) t).eigenvalues i ^ k)
        = Matrix.trace
          ((actualQ1NormalizedActualMatrix f hf r n ((n : ℝ) ^ (-γ)) t) ^ k) := by
    filter_upwards [hcardpos, hδpos] with n hcard hδ
    have hn : 0 < n := by
      have hlt := (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t ⟨0, hcard⟩).isLt
      omega
    rw [← hermitian_trace_pow_eq_sum_eigenvalues_pow
      (actualQ1Hermitian f hf r n ((n : ℝ) ^ (-γ)) t) k]
    rw [trace_pow_weightedFeatureQuadraticMatrix_eq
      (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
      (actualQ1Coeff n ((n : ℝ) ^ (-γ)) t)
      (actualQ1SpectralWeight f r n ((n : ℝ) ^ (-γ)) t) k]
    rw [actualQ1_diagonalCorrelation_eq f hf r n hn ((n : ℝ) ^ (-γ)) t hδ]
  refine Tendsto.congr' (htr.mono fun n h => h.symm) ?_
  have hfin : Tendsto (fun n : ℕ =>
      (Matrix.trace ((actualQ1NormalizedActualMatrix f hf r n ((n : ℝ) ^ (-γ)) t) ^ k)
        - Matrix.trace ((actualQ1RieszMatrix f r n ((n : ℝ) ^ (-γ)) t) ^ k))
      + Matrix.trace ((actualQ1RieszMatrix f r n ((n : ℝ) ^ (-γ)) t) ^ k)) atTop
      (𝓝 (weightedRieszCycleIntegral k (2 - 2 * f t) (f t * (2 * f t - 1))
        (equivalentKernel r))) := by
    simpa using hd.add hG
  exact Tendsto.congr (fun _ => by ring) hfin

end Hurst
