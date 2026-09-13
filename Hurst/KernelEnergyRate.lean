import Hurst.FirstLongWeightedKernel
import Hurst.FirstLongRealScaleHilbertSchmidt

/-!
# Dimension-weighted kernel energy rate

This file packages the quantitative estimate chain inside
`hurstHolder_q1_actual_weighted_kernel_hilbertSchmidt_to_riesz`
(`Hurst.ActualFirstLongWeightedKernel`) into the dimension-weighted rate
consumed as `hPert` by `Hurst.ActualQuadratureConfluence`:

`card n * realScaleMeshEnergy S n (u*A - v*B) -> 0` (card ~ 2 S, S -> ∞).

## Phase-1 findings: the unweighted proof is fully quantitative

The energy -> 0 proof of
`hurstHolder_q1_actual_weighted_kernel_hilbertSchmidt_to_riesz` is a squeeze
whose every upper bound carries an explicit constant-power mesh factor:

* Band, actual side: `realScaleMeshBandEnergy_scaled_le`
  (`Hurst.FirstLongRealScaleHilbertSchmidt`) gives
  `bandEnergy S R (fun i j => S^ψ * r i j) ≤ S^(2ψ-2) * card * (2R+1)`
  for `|r| ≤ 1`; the band convergence consumes the explicit cutoff
  `hcut : S^(2ψ-2) * card * (2R+1) -> 0`
  (`hurstHolder_q1_actual_correlation_band_energy_tendsto_zero`,
  `Hurst.ActualFirstLongBandEnergy`).
* Band, Riesz side: `rankRieszKernel_band_energy_le`
  (`Hurst.FirstLongRieszEnergy`) gives
  `bandEnergy S R (rankRieszKernel S ψ c) ≤ c² * S^(2ψ-2) * card * (2R+1)`.
* Off diagonal: the pair-level envelope bound
  (`hurstHolder_q1_active_scaled_actual_tail_error_le_envelope` +
  `scaled_tail_error_to_relative_riesz`, `Hurst.ActualFirstLongHilbertSchmidt`)
  gives `|A - B| ≤ e * |B|` off the band with `e = q1ActualLongTailEnvelope / c`,
  and `realScaleMesh_off_le_of_relative` turns this into
  `offdiag ≤ e² * realScaleMeshEnergy S B ≤ e² * Cref` with `Cref` the constant
  of `rankRieszKernel_energy_le_const`.
* Gluing: `realScaleMeshEnergy_sub_tendsto_zero_of_relative` uses
  `energy(A - B) ≤ 2*bandA + 2*bandB + e² * Cref` (pointwise lemma
  `realScaleMeshEnergy_eq_band_add_off` + `realScaleMeshBandEnergy_sub_le`).
* Weight step: `realScaleMeshEnergy_left_weight_sub_le`
  (`Hurst.FirstLongWeightedKernel`) gives the explicit
  `energy(u*A - v*B) ≤ 2U² * energy(A - B) + 2w² * energy(B)` for `|u| ≤ U` and
  a uniform weight error `|u - v| ≤ w`.

Hence `card * energy` obeys the same chain with each bound multiplied by the
eventually bounded factor `card` (card ≤ 3S by `localWeightActiveSet_card`).
The weighted rate follows from three strengthened deterministic inputs, each a
free-parameter choice one power of `S` / `√card` stronger than the existing
hypotheses:

1. `S * (S^(2ψ-2) * card * (2R+1)) -> 0` (strengthened cutoff; R is free) gives
   the weighted band bounds (`kernelBandActual_card_tendsto_zero_of_cut`,
   `kernelBandRiesz_card_tendsto_zero_of_cut`);
2. `card * e² -> 0`, i.e. tail envelope `= o(card^{-1/2})` (strengthened form of
   `henv`; the envelope is linear in δ, R⁻¹ and `gridCovarianceError`);
3. `card * w² -> 0` for the rank-uniform weight error (quantitative upgrade of
   `localPolynomialWeights_active_rank_uniform_tendsto`).

`kernelEnergy_card_rate` consumes exactly these, named hypothesis by hypothesis.

## Main contents

* `realScaleMeshEnergy_card_sub_le` : pointwise weighted band+off gluing;
* `realScaleMeshEnergy_card_sub_tendsto_zero_of_relative` : weighted analogue of
  `realScaleMeshEnergy_sub_tendsto_zero_of_relative`;
* `card_mul_band_tendsto_zero_of_bound`, and its concrete instantiations
  `kernelBandActual_card_tendsto_zero_of_cut`,
  `kernelBandRiesz_card_tendsto_zero_of_cut` : band bridges from the
  strengthened cutoff;
* `realScaleMeshEnergy_card_left_weight_sub_tendsto_zero` : weighted weight step;
* `kernelEnergy_card_rate` : the `hPert`-shaped conclusion.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace Hurst

/-! ## Pointwise weighted gluing (band + relative off diagonal) -/

/-- Weighted form of the pointwise bound behind
`realScaleMeshEnergy_sub_tendsto_zero_of_relative`: multiplying the
band + relative-off-diagonal decomposition by an eventually bounded factor
`κ` scales the whole chain. -/
theorem realScaleMeshEnergy_card_sub_le {m R : ℕ}
    (S κ e C : ℝ) (hκ : 0 ≤ κ) (he : 0 ≤ e)
    (A B : Fin m → Fin m → ℝ)
    (hoff : ∀ i j, R < Nat.dist j.val i.val →
      |A i j - B i j| ≤ e * |B i j|)
    (hB : realScaleMeshEnergy S B ≤ C) :
    κ * realScaleMeshEnergy S (fun i j => A i j - B i j) ≤
      κ * (2 * realScaleMeshBandEnergy S R A +
        2 * realScaleMeshBandEnergy S R B + e ^ 2 * C) := by
  have hsplit := realScaleMeshEnergy_eq_band_add_off (R := R) S
    (fun i j => A i j - B i j)
  have hband := realScaleMeshBandEnergy_sub_le (S := S) (R := R) A B
  have hoffbd := realScaleMesh_off_le_of_relative S (R := R) A B e he hoff
  have hoffC : S⁻¹ ^ 2 * ∑ i : Fin m,
      ∑ j ∈ Finset.univ.filter
        (fun j : Fin m => ¬ Nat.dist j.val i.val ≤ R),
          (A i j - B i j) ^ 2 ≤ e ^ 2 * C :=
    hoffbd.trans (mul_le_mul_of_nonneg_left hB (sq_nonneg e))
  calc κ * realScaleMeshEnergy S (fun i j => A i j - B i j)
      = κ * (realScaleMeshBandEnergy S R (fun i j => A i j - B i j) +
          S⁻¹ ^ 2 * ∑ i : Fin m,
            ∑ j ∈ Finset.univ.filter
              (fun j : Fin m => ¬ Nat.dist j.val i.val ≤ R),
                (A i j - B i j) ^ 2) := by rw [hsplit]
    _ ≤ κ * ((2 * realScaleMeshBandEnergy S R A +
          2 * realScaleMeshBandEnergy S R B) + e ^ 2 * C) :=
      mul_le_mul_of_nonneg_left (add_le_add hband hoffC) hκ
    _ = κ * (2 * realScaleMeshBandEnergy S R A +
        2 * realScaleMeshBandEnergy S R B + e ^ 2 * C) := by ring

/-- Filter form: the weighted analogue of
`realScaleMeshEnergy_sub_tendsto_zero_of_relative`.  The two weighted band
hypotheses and the weighted envelope rate `κ * e² -> 0` replace the unweighted
`hAnear`/`hBnear`/`herr`; the reference-energy bound `hBbound` is the same
`Cref`-shaped hypothesis as in the unweighted theorem. -/
theorem realScaleMeshEnergy_card_sub_tendsto_zero_of_relative
    (m R : ℕ → ℕ) (S κ : ℕ → ℝ)
    (A B : ∀ n, Fin (m n) → Fin (m n) → ℝ)
    (e : ℕ → ℝ) (C : ℝ)
    (_hC : 0 ≤ C)
    (hκ : ∀ᶠ n in atTop, 0 ≤ κ n)
    (hoff : ∀ᶠ n in atTop, ∀ i j,
      R n < Nat.dist j.val i.val →
        |A n i j - B n i j| ≤ e n * |B n i j|)
    (he : ∀ᶠ n in atTop, 0 ≤ e n)
    (hBbound : ∀ᶠ n in atTop, realScaleMeshEnergy (S n) (B n) ≤ C)
    (hκbandA : Tendsto (fun n => κ n *
      realScaleMeshBandEnergy (S n) (R n) (A n)) atTop (𝓝 0))
    (hκbandB : Tendsto (fun n => κ n *
      realScaleMeshBandEnergy (S n) (R n) (B n)) atTop (𝓝 0))
    (hκe : Tendsto (fun n => κ n * e n ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => κ n * realScaleMeshEnergy (S n)
      (fun i j => A n i j - B n i j)) atTop (𝓝 0) := by
  have hg : Tendsto (fun n => κ n * (2 * realScaleMeshBandEnergy (S n) (R n)
        (A n) + 2 * realScaleMeshBandEnergy (S n) (R n) (B n) +
        e n ^ 2 * C)) atTop (𝓝 0) := by
    have hsum := ((hκbandA.const_mul 2).add
      (hκbandB.const_mul 2)).add (hκe.mul_const C)
    have hlim : (2 : ℝ) * 0 + 2 * 0 + 0 * C = 0 := by norm_num
    rw [hlim] at hsum
    exact Tendsto.congr (fun _ => by ring) hsum
  apply squeeze_zero'
  · filter_upwards [hκ] with n hκn
    exact mul_nonneg hκn (mul_nonneg (sq_nonneg _)
      (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _))
  · filter_upwards [hκ, hoff, he, hBbound] with n hκn hoffn hen hBn
    exact realScaleMeshEnergy_card_sub_le (S n) (κ n) (e n) C hκn hen
      (A n) (B n) hoffn hBn
  · exact hg

/-! ## Band bridges from the strengthened cutoff -/

/-- If `κ` is eventually at most `K * S` and the band energy of `X` is at most
`cst * cut` with `S * cut -> 0`, then `κ * bandEnergy -> 0`.  This is the
one-line bridge turning the strengthened cutoff `S * hcut -> 0` into the
weighted band bounds. -/
theorem card_mul_band_tendsto_zero_of_bound
    (m R : ℕ → ℕ) (S κ : ℕ → ℝ) (K cst : ℝ) (cut : ℕ → ℝ)
    (X : ∀ n, Fin (m n) → Fin (m n) → ℝ)
    (hcst : 0 ≤ cst)
    (hκ : ∀ᶠ n in atTop, 0 ≤ κ n ∧ κ n ≤ K * S n)
    (hcut0 : ∀ᶠ n in atTop, 0 ≤ cut n)
    (hband : ∀ᶠ n in atTop,
      realScaleMeshBandEnergy (S n) (R n) (X n) ≤ cst * cut n)
    (hcutS : Tendsto (fun n => S n * cut n) atTop (𝓝 0)) :
    Tendsto (fun n => κ n * realScaleMeshBandEnergy (S n) (R n) (X n))
      atTop (𝓝 0) := by
  have hupper : Tendsto (fun n => cst * K * (S n * cut n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hcutS.const_mul (cst * K)
  apply squeeze_zero'
  · filter_upwards [hκ] with n hκn
    exact mul_nonneg hκn.1 (mul_nonneg (sq_nonneg _)
      (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _))
  · filter_upwards [hκ, hcut0, hband] with n hκn hcutn hbandn
    calc κ n * realScaleMeshBandEnergy (S n) (R n) (X n)
        ≤ κ n * (cst * cut n) := mul_le_mul_of_nonneg_left hbandn hκn.1
      _ ≤ K * S n * (cst * cut n) :=
        mul_le_mul_of_nonneg_right hκn.2 (mul_nonneg hcst hcutn)
      _ = cst * K * (S n * cut n) := by ring
  · exact hupper

/-- **Band bridge, actual side.**  With `κ = card` (eventually `≤ 3S` by
`localWeightActiveSet_card`), the A-side band bound
`realScaleMeshBandEnergy_scaled_le` and the STRENGTHENED cutoff
`S * (S^(2ψ-2) * card * (2R+1)) -> 0` (one power of `S` stronger than `hcut`;
`R` is a free parameter) give the weighted band bound. -/
theorem kernelBandActual_card_tendsto_zero_of_cut
    (m R : ℕ → ℕ) (S : ℕ → ℝ) (ψ : ℝ)
    (r : ∀ n, Fin (m n) → Fin (m n) → ℝ)
    (hS : ∀ᶠ n in atTop, 0 < S n)
    (hcard : ∀ᶠ n in atTop, (m n : ℝ) ≤ 3 * S n)
    (hr : ∀ᶠ n in atTop, ∀ i j, |r n i j| ≤ 1)
    (hcutS : Tendsto (fun n => S n * (S n ^ (2 * ψ - 2) *
      (m n : ℝ) * (2 * (R n : ℝ) + 1))) atTop (𝓝 0)) :
    Tendsto (fun n => (m n : ℝ) * realScaleMeshBandEnergy (S n) (R n)
      (fun i j => S n ^ ψ * r n i j)) atTop (𝓝 0) := by
  have hcut0 : ∀ᶠ n in atTop, 0 ≤ S n ^ (2 * ψ - 2) *
      (m n : ℝ) * (2 * (R n : ℝ) + 1) := by
    filter_upwards [hS] with n hSn
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hSn.le _)
      (Nat.cast_nonneg (m n))) (by positivity)
  have hκpair : ∀ᶠ n in atTop, 0 ≤ (m n : ℝ) ∧ (m n : ℝ) ≤ 3 * S n := by
    filter_upwards [hcard] with n hc
    exact ⟨Nat.cast_nonneg (m n), hc⟩
  refine card_mul_band_tendsto_zero_of_bound m R S (fun n => (m n : ℝ)) 3 1
    (fun n => S n ^ (2 * ψ - 2) * (m n : ℝ) * (2 * (R n : ℝ) + 1))
    (fun n => fun i j => S n ^ ψ * r n i j) (by norm_num) hκpair hcut0 ?_ hcutS
  filter_upwards [hS, hr] with n hSn hrn
  exact (realScaleMeshBandEnergy_scaled_le (S n) ψ hSn (r n) hrn).trans
    (by rw [one_mul])

/-- **Band bridge, Riesz side.**  Same bridge on the reference side via
`rankRieszKernel_band_energy_le` (bound `c² * S^(2ψ-2) * card * (2R+1)`). -/
theorem kernelBandRiesz_card_tendsto_zero_of_cut
    (m R : ℕ → ℕ) (S : ℕ → ℝ) (ψ c : ℝ)
    (hS : ∀ᶠ n in atTop, 0 < S n)
    (hψ0 : 0 ≤ ψ)
    (hcard : ∀ᶠ n in atTop, (m n : ℝ) ≤ 3 * S n)
    (hcutS : Tendsto (fun n => S n * (S n ^ (2 * ψ - 2) *
      (m n : ℝ) * (2 * (R n : ℝ) + 1))) atTop (𝓝 0)) :
    Tendsto (fun n => (m n : ℝ) * realScaleMeshBandEnergy (S n) (R n)
      (rankRieszKernel (S n) ψ c : Fin (m n) → Fin (m n) → ℝ)) atTop (𝓝 0) := by
  have hcut0 : ∀ᶠ n in atTop, 0 ≤ S n ^ (2 * ψ - 2) *
      (m n : ℝ) * (2 * (R n : ℝ) + 1) := by
    filter_upwards [hS] with n hSn
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hSn.le _)
      (Nat.cast_nonneg (m n))) (by positivity)
  have hκpair : ∀ᶠ n in atTop, 0 ≤ (m n : ℝ) ∧ (m n : ℝ) ≤ 3 * S n := by
    filter_upwards [hcard] with n hc
    exact ⟨Nat.cast_nonneg (m n), hc⟩
  refine card_mul_band_tendsto_zero_of_bound m R S (fun n => (m n : ℝ)) 3
    (c ^ 2) (fun n => S n ^ (2 * ψ - 2) * (m n : ℝ) * (2 * (R n : ℝ) + 1))
    (fun n => (rankRieszKernel (S n) ψ c : Fin (m n) → Fin (m n) → ℝ))
    (sq_nonneg c) hκpair hcut0 ?_ hcutS
  filter_upwards [hS] with n hSn
  exact rankRieszKernel_band_energy_le (S n) ψ c hSn hψ0

/-! ## Weighted weight step -/

/-- Weighted form of `realScaleMeshEnergy_left_weight_sub_tendsto_zero`:
with the weight-error measured at the rate `κ * w² -> 0` (the quantitative
upgrade of the rank-uniform convergence
`localPolynomialWeights_active_rank_uniform_tendsto`), the dimension-weighted
energy of `u*A - v*B` is driven by the dimension-weighted energy of `A - B`. -/
theorem realScaleMeshEnergy_card_left_weight_sub_tendsto_zero
    (m : ℕ → ℕ) (S κ : ℕ → ℝ)
    (A B : ∀ n, Fin (m n) → Fin (m n) → ℝ)
    (u v : ∀ n, Fin (m n) → ℝ) (U C : ℝ) (w : ℕ → ℝ)
    (_hC : 0 ≤ C)
    (hκ : ∀ᶠ n in atTop, 0 ≤ κ n)
    (hu : ∀ᶠ n in atTop, ∀ i, |u n i| ≤ U)
    (huv : ∀ᶠ n in atTop, ∀ i, |u n i - v n i| ≤ w n)
    (hκw : Tendsto (fun n => κ n * w n ^ 2) atTop (𝓝 0))
    (hκAB : Tendsto (fun n => κ n * realScaleMeshEnergy (S n)
      (fun i j => A n i j - B n i j)) atTop (𝓝 0))
    (hBbound : ∀ᶠ n in atTop, realScaleMeshEnergy (S n) (B n) ≤ C) :
    Tendsto (fun n => κ n * realScaleMeshEnergy (S n)
      (fun i j => u n i * A n i j - v n i * B n i j)) atTop (𝓝 0) := by
  have hg : Tendsto (fun n => 2 * U ^ 2 * (κ n * realScaleMeshEnergy (S n)
        (fun i j => A n i j - B n i j)) +
      2 * (κ n * w n ^ 2 * C)) atTop (𝓝 0) := by
    have hsum := (hκAB.const_mul (2 * U ^ 2)).add (hκw.mul_const (2 * C))
    have hlim : (2 * U ^ 2) * 0 + 0 * (2 * C) = 0 := by norm_num
    rw [hlim] at hsum
    exact Tendsto.congr (fun _ => by ring) hsum
  apply squeeze_zero'
  · filter_upwards [hκ] with n hκn
    exact mul_nonneg hκn (mul_nonneg (sq_nonneg _)
      (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _))
  · filter_upwards [hκ, hu, huv, hBbound] with n hκn hun huvn hBn
    have hle := realScaleMeshEnergy_left_weight_sub_le (S n) (A n) (B n)
      (u n) (v n) U (w n) hun huvn
    have hstep : 2 * U ^ 2 * realScaleMeshEnergy (S n)
          (fun i j => A n i j - B n i j) +
        2 * w n ^ 2 * realScaleMeshEnergy (S n) (B n) ≤
        2 * U ^ 2 * realScaleMeshEnergy (S n)
          (fun i j => A n i j - B n i j) + 2 * w n ^ 2 * C :=
      add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hBn
          (by positivity : (0 : ℝ) ≤ 2 * w n ^ 2))
    calc κ n * realScaleMeshEnergy (S n)
          (fun i j => u n i * A n i j - v n i * B n i j) ≤
        κ n * (2 * U ^ 2 * realScaleMeshEnergy (S n)
            (fun i j => A n i j - B n i j) +
          2 * w n ^ 2 * realScaleMeshEnergy (S n) (B n)) :=
      mul_le_mul_of_nonneg_left hle hκn
    _ ≤ κ n * (2 * U ^ 2 * realScaleMeshEnergy (S n)
          (fun i j => A n i j - B n i j) + 2 * w n ^ 2 * C) :=
      mul_le_mul_of_nonneg_left hstep hκn
    _ = 2 * U ^ 2 * (κ n * realScaleMeshEnergy (S n)
          (fun i j => A n i j - B n i j)) +
        2 * (κ n * w n ^ 2 * C) := by ring
  · exact hg

/-! ## The dimension-weighted rate -/

/-- **The dimension-weighted kernel energy rate (the `hPert` production).**
Consuming the quantitative bounds of the proof of
`hurstHolder_q1_actual_weighted_kernel_hilbertSchmidt_to_riesz`, in their
dimension-weighted forms, the conclusion is exactly the `hPert` hypothesis of
`actualQ1_trace_pow_tendsto`:

`κ n * realScaleMeshEnergy (S n) (fun i j => u n i * A n i j - v n i * B n i j) → 0`.

Hypothesis provenance (named ingredient by ingredient):

* `hu` : the weight bound in `Hurst.FirstLongWeightedKernel.lean`
  (`U = D + 1` from `equivalentKernel_bounded`, lines 64–88 of
  `ActualFirstLongWeightedKernel.lean`);
* `huv`, `hκw` : the QUANTITATIVE upgrade of
  `localPolynomialWeights_active_rank_uniform_tendsto`
  (`Hurst.ActiveWeightProfile`): the weight error must be `o(card^{-1/2})`
  uniformly in the row index; the existing hypothesis only gives `∀ ε > 0`;
* `hκbandA` : `kernelBandActual_card_tendsto_zero_of_cut` from the
  strengthened cutoff `S * hcut -> 0` (A-side band bound
  `realScaleMeshBandEnergy_scaled_le`, cutoff `hcut` as in
  `hurstHolder_q1_actual_kernel_hilbertSchmidt_to_riesz_closed`);
* `hκbandB` : `kernelBandRiesz_card_tendsto_zero_of_cut` from the same
  strengthened cutoff (via `rankRieszKernel_band_energy_le`);
* `hoff` : `hurstHolder_q1_active_scaled_actual_tail_error_le_envelope` +
  `scaled_tail_error_to_relative_riesz` +
  `localWeightActiveIndex_physical_dist_eq_rank_dist`
  (`Hurst.ActualFirstLongHilbertSchmidt.lean`, the `hoff` block);
* `he`, `hκe` : `e n = q1ActualLongTailEnvelope ... / c`; the envelope -> 0 is
  `henv`; the weighted rate `κ * e² -> 0` (envelope `= o(card^{-1/2})`) is the
  strengthened deterministic input;
* `hBbound` : `rankRieszKernel_energy_le_const` with
  `C = Cref = 2 * c² * (3 + 3 * 4^(1-2ψ) / (1 - 2ψ))` (as discharged in
  `hurstHolder_q1_actual_kernel_hilbertSchmidt_to_riesz_closed`).

With `κ n = (localWeightActiveSet n 1 (δ n) t).card`, `S n = (n : ℝ) * δ n`,
`A n = actualQ1WeightedActualKernel`, `B n = actualQ1WeightedRieszKernel`,
`u n = actualQ1ChainWeight`, `v n = equivalentKernel r ∘ rieszCycleGridPoint`,
this is precisely the `hPert` Tendsto of
`Hurst.ActualQuadratureConfluence`. -/
theorem kernelEnergy_card_rate
    (m R : ℕ → ℕ) (S κ : ℕ → ℝ)
    (A B : ∀ n, Fin (m n) → Fin (m n) → ℝ)
    (u v : ∀ n, Fin (m n) → ℝ)
    (U C : ℝ) (w e : ℕ → ℝ)
    (hC : 0 ≤ C)
    (hκ : ∀ᶠ n in atTop, 0 ≤ κ n)
    -- (W1) row-weight bound (`hu` of FirstLongWeightedKernel.lean)
    (hu : ∀ᶠ n in atTop, ∀ i, |u n i| ≤ U)
    -- (W2) weighted rank-uniform weight error
    (huv : ∀ᶠ n in atTop, ∀ i, |u n i - v n i| ≤ w n)
    (hκw : Tendsto (fun n => κ n * w n ^ 2) atTop (𝓝 0))
    -- (B) weighted band bounds (from `S * hcut -> 0`)
    (hκbandA : Tendsto (fun n => κ n *
      realScaleMeshBandEnergy (S n) (R n) (A n)) atTop (𝓝 0))
    (hκbandB : Tendsto (fun n => κ n *
      realScaleMeshBandEnergy (S n) (R n) (B n)) atTop (𝓝 0))
    -- (O) relative off-diagonal envelope (`hurstHolder_q1_active_scaled_actual_tail_error_le_envelope`)
    (hoff : ∀ᶠ n in atTop, ∀ i j,
      R n < Nat.dist j.val i.val →
        |A n i j - B n i j| ≤ e n * |B n i j|)
    (he : ∀ᶠ n in atTop, 0 ≤ e n)
    -- (E) weighted envelope rate (`card * (envelope/c)² -> 0`)
    (hκe : Tendsto (fun n => κ n * e n ^ 2) atTop (𝓝 0))
    -- (R) reference energy constant (`rankRieszKernel_energy_le_const`, Cref)
    (hBbound : ∀ᶠ n in atTop, realScaleMeshEnergy (S n) (B n) ≤ C) :
    Tendsto (fun n => κ n * realScaleMeshEnergy (S n)
      (fun i j => u n i * A n i j - v n i * B n i j)) atTop (𝓝 0) := by
  have hκAB := realScaleMeshEnergy_card_sub_tendsto_zero_of_relative
    m R S κ A B e C hC hκ hoff he hBbound hκbandA hκbandB hκe
  exact realScaleMeshEnergy_card_left_weight_sub_tendsto_zero
    m S κ A B u v U C w hC hκ hu huv hκw hκAB hBbound

end Hurst
