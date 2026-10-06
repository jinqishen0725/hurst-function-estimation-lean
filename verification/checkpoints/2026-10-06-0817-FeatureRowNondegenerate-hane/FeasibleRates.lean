import Hurst.FullChainGeneralSigned
import Hurst.FeatureRowNondegenerate
import Hurst.KernelEnergyRateDischarge
import Hurst.FirstScaleLongRates
import Hurst.LocalWeightSupport
import Hurst.PackingAsymptotics

/-!
# Feasible scalar rates: the explicit `R` instantiation at the feasible bandwidth

This file closes the last model-side gap of
`Hurst.FullChainGeneralSigned.actualQ1_knownScaleH_fullChain_generalSigned`: the
scalar-rate premises `hR` / `hcut` / `hEnv` are instantiated at the explicit rate

`R n = ⌊n ^ β⌋₊`  (in Lean: `fun n => (⌊(n : ℝ) ^ β⌋₊ : ℕ)`)

under the feasible bandwidth `δ n = n ^ (-γ)`.

## The hand-derived exponent arithmetic (math first; this is the contract-table
update for the rows `hR`/`hcut`/`hEnv` of the resolution table in
`Hurst.FullChainGeneralSigned`)

Fix `0 < γ < 1`, write `ψ = 2 - 2 * f t` (so `3 / 4 < f t < 1` gives
`0 < ψ < 1 / 2`), `δ n = n ^ (-γ)`, `S n = n * δ n = n ^ (1 - γ)`,
`R n = ⌊n ^ β⌋₊`, and fix the rate window `0 < β < (1 - γ) * (1 - 2 * ψ)`
(note `1 - 2 * ψ = 4 * f t - 3 > 0` by the long-memory band `3 / 4 < f t`,
so the window is nonempty).

**(a) `hR`:** `n ^ β → ∞` (`Real.tendsto_rpow_atTop` composed with the natural
cast), and `⌊·⌋₊` is monotone with `M ≤ ⌊x⌋₊ ↔ (M : ℝ) ≤ x` for `0 ≤ x`
(`Nat.le_floor_iff`), so `(R n : ℝ) → ∞`.

**(b) `hcut`:** for `n ≥ 1` we have `1 ≤ n ^ (1 - γ)` (`Real.one_le_rpow`), so
`localWeightActiveSet_card` applies and gives `card ≤ 3 * S`.  Also
`⌊n ^ β⌋₊ ≤ n ^ β` (`Nat.floor_le`) and `2 * ⌊n ^ β⌋₊ + 1 ≤ 3 * n ^ β` because
`n ^ β ≥ 1`.  Hence the cut rate satisfies

```
S ^ (2ψ - 2) * card * (2 R + 1) ≤ 3 S ^ (2ψ - 2) * S * 3 n ^ β
  = 9 * n ^ ((1 - γ) * (2ψ - 1) + β) → 0,
```

because the exponent `(1 - γ) * (2ψ - 1) + β = (1 - γ) * (3 - 4 f t) + β < 0`
is exactly the β-window: `β < (1 - γ) * (4 f t - 3) = -(1 - γ) * (2ψ - 1)`.

**(c) `hEnv` (for EVERY fixed `Ccov ≥ 0`, `Ctail ≥ 0`, `L > 0`):** with
`D = 2 * L * (1 + M) * δ` and `E = D * log n`, the exact decomposition
`q1ActualLongTailEnvelope_eq` (free part + `16 / (R + 1)`) and the definition of
the free part reduce the claim to five terms, each vanishing:

1. `18 * Ctail * D * (1 + exp E * E) → 0`: `D → 0` (fixed constants times
   `n ^ (-γ)`, `γ > 0`), `E = 2 L (1 + M) * (log n) / n ^ γ → 0`
   (`nat_log_power_div_rpow_tendsto γ hγ0 1`), `exp E → exp 0 = 1`
   (continuity), so the second factor tends to `1 + 1 * 0 = 1`;
2. `9 * exp E * E → 9 * 1 * 0 = 0`;
3. `16 / (R + 1) → 0` by (a);
4. `(3 / 2) * D → 0`;
5. `4 * (2 S) ^ ψ * gridCovarianceError b Ccov n`
   `= 4 * 2 ^ ψ * Ccov * ((1 + log 2n) * n ^ ((1 - γ) ψ - 1)`
   `+ (1 + log 2n) * n ^ ((1 - γ) ψ + 2b - 2))`, where
   `(2 S) ^ ψ = 2 ^ ψ * (n ^ (1 - γ)) ^ ψ = 2 ^ ψ * n ^ ((1 - γ) ψ)`:
   - the `n ^ (-1)` exponent `(1 - γ) ψ - 1 < 1/2 - 1 < 0` (uses `ψ < 1/2`
     from the long-memory band and `1 - γ < 1`);
   - the `n ^ (2b - 2)` exponent `(1 - γ) ψ + 2b - 2 < 0` is EXACTLY `hgrid`
     (`(1 - γ) * (2 - 2 f t) < 2 - 2 * b`);
   - the logarithmic factor `(1 + log 2n) * n ^ r → 0` for `r < 0` is
     `mesh_log_power_rpow_tendsto r hr 1`.

Every term is linear in the fixed constants, and no two existentially chosen
witnesses are coupled: the envelope theorem holds for all fixed constants at
once.
-/

set_option maxHeartbeats 1200000

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Real
open scoped Topology RealInnerProductSpace

namespace Hurst

/-! ## The explicit rate `R n = ⌊n ^ β⌋` tends to infinity -/

/-- The explicit rate `R n = ⌊n ^ β⌋₊` diverges for `β > 0`. -/
theorem feasibleR_nat_tendsto (β : ℝ) (hβ : 0 < β) :
    Tendsto (fun n : ℕ => (⌊(n : ℝ) ^ β⌋₊ : ℕ)) atTop atTop := by
  have hrpow : Tendsto (fun n : ℕ => ((n : ℝ) ^ β)) atTop atTop :=
    (tendsto_rpow_atTop hβ).comp tendsto_natCast_atTop_atTop
  refine tendsto_atTop_atTop.2 fun M => ?_
  have hkey : ∀ᶠ n : ℕ in atTop, (M : ℝ) ≤ (n : ℝ) ^ β :=
    hrpow.eventually_ge_atTop (M : ℝ)
  obtain ⟨N, hN⟩ : ∃ i : ℕ, ∀ n : ℕ, i ≤ n → (M : ℝ) ≤ (n : ℝ) ^ β :=
    Filter.eventually_atTop.1 hkey
  exact ⟨N, fun n hn0 => Nat.le_floor (hN n hn0)⟩

/-- The real-valued version consumed by `hR`. -/
theorem feasibleR_tendsto_atTop (β : ℝ) (hβ : 0 < β) :
    Tendsto (fun n : ℕ => ((⌊(n : ℝ) ^ β⌋₊ : ℕ) : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_iff.mpr (feasibleR_nat_tendsto β hβ)

/-! ## Mesh helpers at the feasible bandwidth -/

/-- `(n : ℝ) * n ^ (-γ) = n ^ (1 - γ)` — the mesh in closed form. -/
private theorem fr_mesh_eq (γ : ℝ) {n : ℕ} (hn0 : 0 < (n : ℝ)) :
    (n : ℝ) * ((n : ℝ) ^ (-γ)) = (n : ℝ) ^ (1 - γ) := by
  have h1 : (n : ℝ) * ((n : ℝ) ^ (-γ)) = ((n : ℝ) ^ (1 : ℝ)) * ((n : ℝ) ^ (-γ)) := by
    rw [Real.rpow_one]
  have hexp : (1 : ℝ) + (-γ) = 1 - γ := by ring
  rw [h1, ← Real.rpow_add hn0, hexp]

/-- The mesh is eventually at least `1` (for `γ < 1`), which feeds the
`localWeightActiveSet_card` hypothesis. -/
private theorem fr_mesh_ge_one (γ : ℝ) (hγ1 : γ < 1) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ (n : ℝ) * ((n : ℝ) ^ (-γ)) := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [fr_mesh_eq γ hn0]
  exact Real.one_le_rpow (by exact_mod_cast hn) (by linarith)

/-! ## The cut rate at the explicit `R` -/

/-- **The cut rate at the explicit `R n = ⌊n ^ β⌋₊`.**  For `γ < 1` and the
β-window `β < (1 - γ) * (1 - 2 * (2 - 2 * f t))`, the cut rate
`S ^ (2ψ - 2) * card * (2 R + 1)` (with `S = n * n ^ (-γ)`,
`ψ = 2 - 2 * f t`) vanishes: eventually `card ≤ 3 * S` and
`2 ⌊n ^ β⌋₊ + 1 ≤ 3 * n ^ β`, giving the bound `9 * n ^ ((1 - γ) * (2ψ - 1) + β)`
whose exponent is negative by the β-window. -/
theorem feasibleR_cut_tendsto (f : ℝ → ℝ) (t γ β : ℝ)
    (hγ1 : γ < 1) (hβ0 : 0 < β) (hβ : β < (1 - γ) * (1 - 2 * (2 - 2 * f t))) :
    Tendsto (fun n : ℕ =>
      ((n : ℝ) * ((n : ℝ) ^ (-γ))) ^ (2 * (2 - 2 * f t) - 2) *
        ((localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card : ℝ) *
        (2 * ((⌊(n : ℝ) ^ β⌋₊ : ℕ) : ℝ) + 1)) atTop (𝓝 0) := by
  -- the exponent of the final bound
  have hEneg : (1 - γ) * (2 * (2 - 2 * f t) - 1) + β < 0 := by
    have h1 : (1 - γ) * (2 * (2 - 2 * f t) - 1)
        = -((1 - γ) * (1 - 2 * (2 - 2 * f t))) := by ring
    rw [h1]
    linarith [hβ]
  have hbound : Tendsto (fun n : ℕ =>
      (9 : ℝ) * (n : ℝ) ^ ((1 - γ) * (2 * (2 - 2 * f t) - 1) + β)) atTop (𝓝 0) :=
    (by simpa only [mul_zero] using
      (tendsto_rpow_neg_of_atTop (fun n : ℕ => (n : ℝ)) _
        hEneg tendsto_natCast_atTop_atTop).const_mul 9)
  refine squeeze_zero' ?_ ?_ hbound
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hS : 0 < (n : ℝ) * ((n : ℝ) ^ (-γ)) :=
      mul_pos hn0 (Real.rpow_pos_of_pos hn0 _)
    have hnonneg : 0 ≤ 2 * ((⌊(n : ℝ) ^ β⌋₊ : ℕ) : ℝ) + 1 := by
      have h1 : (1 : ℝ) ≤ (n : ℝ) ^ β :=
        Real.one_le_rpow (by exact_mod_cast hn) hβ0.le
      have h2 : ((1 : ℕ) : ℝ) ≤ (n : ℝ) ^ β := by simpa using h1
      have hf : (1 : ℕ) ≤ (⌊(n : ℝ) ^ β⌋₊ : ℕ) := Nat.le_floor h2
      have h3 : ((1 : ℕ) : ℝ) ≤ ((⌊(n : ℝ) ^ β⌋₊ : ℕ) : ℝ) := by exact_mod_cast hf
      linarith
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hS.le (2 * (2 - 2 * f t) - 2))
      (by exact_mod_cast Nat.zero_le _)) hnonneg
  · filter_upwards [eventually_ge_atTop 1, fr_mesh_ge_one γ hγ1] with n hn hmesh
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hS : 0 < (n : ℝ) * ((n : ℝ) ^ (-γ)) :=
      mul_pos hn0 (Real.rpow_pos_of_pos hn0 _)
    have hδ : 0 < (n : ℝ) ^ (-γ) := Real.rpow_pos_of_pos hn0 _
    have hcard := localWeightActiveSet_card n 1 (by omega) ((n : ℝ) ^ (-γ)) t hδ hmesh
    -- `2 ⌊n^β⌋₊ + 1 ≤ 3 n^β` for `n ≥ 1`
    have hRb : 2 * ((⌊(n : ℝ) ^ β⌋₊ : ℕ) : ℝ) + 1 ≤ 3 * (n : ℝ) ^ β := by
      have h1 : ((⌊(n : ℝ) ^ β⌋₊ : ℕ) : ℝ) ≤ (n : ℝ) ^ β :=
        Nat.floor_le (Real.rpow_nonneg hn0.le β)
      have h2 : (1 : ℝ) ≤ (n : ℝ) ^ β :=
        Real.one_le_rpow (by exact_mod_cast hn) (show (0 : ℝ) ≤ β by linarith)
      linarith
    have hRnn : 0 ≤ 2 * ((⌊(n : ℝ) ^ β⌋₊ : ℕ) : ℝ) + 1 := by linarith
    calc ((n : ℝ) * ((n : ℝ) ^ (-γ))) ^ (2 * (2 - 2 * f t) - 2) *
          ((localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card : ℝ) *
          (2 * ((⌊(n : ℝ) ^ β⌋₊ : ℕ) : ℝ) + 1)
        ≤ ((n : ℝ) * ((n : ℝ) ^ (-γ))) ^ (2 * (2 - 2 * f t) - 2) *
            (3 * ((n : ℝ) * ((n : ℝ) ^ (-γ)))) *
            (2 * ((⌊(n : ℝ) ^ β⌋₊ : ℕ) : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hcard
              (Real.rpow_nonneg hS.le (2 * (2 - 2 * f t) - 2))) hRnn
      _ ≤ ((n : ℝ) * ((n : ℝ) ^ (-γ))) ^ (2 * (2 - 2 * f t) - 2) *
            (3 * ((n : ℝ) * ((n : ℝ) ^ (-γ)))) *
            (3 * (n : ℝ) ^ β) :=
          mul_le_mul_of_nonneg_left hRb
            (mul_nonneg (Real.rpow_nonneg hS.le (2 * (2 - 2 * f t) - 2))
              (by linarith : (0 : ℝ) ≤ 3 * ((n : ℝ) * ((n : ℝ) ^ (-γ)))))
      _ = 9 * ((n : ℝ) * ((n : ℝ) ^ (-γ))) ^ ((2 * (2 - 2 * f t) - 2) + 1) *
            (n : ℝ) ^ β := by
          rw [Real.rpow_add hS, Real.rpow_one]; ring
      _ = 9 * (n : ℝ) ^ ((1 - γ) * (2 * (2 - 2 * f t) - 1)) * (n : ℝ) ^ β := by
          rw [fr_mesh_eq γ hn0, ← Real.rpow_mul hn0.le]
          exact congrArg (fun z : ℝ => 9 * ((n : ℝ) ^ z) * ((n : ℝ) ^ β)) (by ring)
      _ = 9 * (n : ℝ) ^ ((1 - γ) * (2 * (2 - 2 * f t) - 1) + β) := by
          rw [Real.rpow_add hn0]; ring

/-! ## The long-tail envelope at the explicit `R` -/

/-- **The long-tail envelope at the explicit `R n = ⌊n ^ β⌋₊`, for every fixed
constants.**  With `D = 2 L (1 + M) n ^ (-γ)` and `E = D * log n`, the exact
decomposition `q1ActualLongTailEnvelope_eq` reduces the envelope to five
vanishing terms:
1. `18 * Ctail * D * (1 + exp E * E) → 0` (`D → 0`, `E → 0`, `exp E → 1`);
2. `9 * exp E * E → 0`;
3. `16 / (R + 1) → 0` (by `feasibleR_tendsto_atTop`);
4. `(3 / 2) * D → 0`;
5. `4 * (2 S) ^ ψ * gridCovarianceError b Ccov n → 0`: the `n ^ (-1)` exponent
   `(1 - γ) ψ - 1 < 0` needs `ψ < 1/2` (long-memory band), and the
   `n ^ (2 b - 2)` exponent `(1 - γ) ψ + 2 b - 2 < 0` is exactly `hgrid`.

The statement holds for ALL fixed real `Ccov`, `Ctail`, `L` (the envelope is
linear in them), so it instantiates the endpoint's `∀ Ccov ≥ 0, ∀ Ctail ≥ 0,
∀ L > 0` envelope premise verbatim. -/
theorem feasibleR_env_tendsto (b Ccov Ctail L M h0 γ β : ℝ)
    (hγ0 : 0 < γ)
    (hψpos : 0 < 2 - 2 * h0) (hψhalf : 2 - 2 * h0 < 1 / 2)
    (hgrid : (1 - γ) * (2 - 2 * h0) < 2 - 2 * b)
    (hβ0 : 0 < β) :
    Tendsto (fun n : ℕ =>
      q1ActualLongTailEnvelope b Ccov Ctail L M h0 n ((n : ℝ) ^ (-γ))
        ((n : ℝ) * ((n : ℝ) ^ (-γ))) (⌊(n : ℝ) ^ β⌋₊)) atTop (𝓝 0) := by
  have hP : (1 - γ) * (2 - 2 * h0) < 1 / 2 := by
    have h3 : (1 - γ) * (2 - 2 * h0) ≤ 1 * (2 - 2 * h0) :=
      mul_le_mul_of_nonneg_right (by linarith) hψpos.le
    linarith
  -- the two exponents of the grid term are negative
  have hr1 : (1 - γ) * (2 - 2 * h0) + (-1 : ℝ) < 0 := by linarith [hP]
  have hr2 : (1 - γ) * (2 - 2 * h0) + (2 * b - 2) < 0 := by linarith [hgrid]
  -- the log-power rates (k = 1, `^ 1` stripped)
  have hsub1 := mesh_log_power_rpow_tendsto
    ((1 - γ) * (2 - 2 * h0) + (-1 : ℝ)) hr1 1
  have hsub2 := mesh_log_power_rpow_tendsto
    ((1 - γ) * (2 - 2 * h0) + (2 * b - 2)) hr2 1
  simp only [pow_one] at hsub1 hsub2
  -- `D → 0` and `E = D * log n → 0`
  have hD0 : Tendsto (fun n : ℕ => (2 * L * (1 + M)) * ((n : ℝ) ^ (-γ))) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => ((n : ℝ) ^ (-γ))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hγ0).comp tendsto_natCast_atTop_atTop
    have h2 := h.const_mul (2 * L * (1 + M))
    rwa [mul_zero] at h2
  have hE0 : Tendsto (fun n : ℕ =>
      ((2 * L * (1 + M)) * ((n : ℝ) ^ (-γ))) * Real.log n) atTop (𝓝 0) := by
    have hlog := nat_log_power_div_rpow_tendsto γ hγ0 1
    simp only [pow_one] at hlog
    have hsrc : Tendsto (fun n : ℕ =>
        (2 * L * (1 + M)) * (Real.log (n : ℝ) / (n : ℝ) ^ γ)) atTop (𝓝 0) := by
      have h2 := hlog.const_mul (2 * L * (1 + M))
      rwa [mul_zero] at h2
    refine Tendsto.congr' ?_ hsrc
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hneg : (n : ℝ) ^ (-γ) = ((n : ℝ) ^ γ)⁻¹ := Real.rpow_neg hn0.le γ
    rw [hneg, div_eq_inv_mul]
    ring
  -- `exp E → 1`
  have hexp1 : Tendsto (fun n : ℕ =>
      Real.exp ((2 * L * (1 + M) * ((n : ℝ) ^ (-γ))) * Real.log n)) atTop (𝓝 1) := by
    have h := (Real.continuous_exp.tendsto (0 : ℝ)).comp hE0
    simpa only [Function.comp_def, Real.exp_zero] using h
  -- term 1: `18 * Ctail * D * (1 + exp E * E) → 0`
  have hfac : Tendsto (fun n : ℕ => (1 : ℝ) +
      Real.exp ((2 * L * (1 + M) * ((n : ℝ) ^ (-γ))) * Real.log n) *
      ((2 * L * (1 + M) * ((n : ℝ) ^ (-γ))) * Real.log n)) atTop (𝓝 ((1 : ℝ) + 1 * 0)) := by
    refine Tendsto.add ?_ (hexp1.mul hE0)
    exact tendsto_const_nhds
  have hD1 : Tendsto (fun n : ℕ =>
      18 * Ctail * (2 * L * (1 + M) * ((n : ℝ) ^ (-γ)))) atTop (𝓝 0) := by
    have h2 := hD0.const_mul (18 * Ctail)
    rwa [mul_zero] at h2
  have hterm1 : Tendsto (fun n : ℕ => 18 * Ctail * (2 * L * (1 + M) * ((n : ℝ) ^ (-γ))) *
      (1 + Real.exp ((2 * L * (1 + M) * ((n : ℝ) ^ (-γ))) * Real.log n) *
        ((2 * L * (1 + M) * ((n : ℝ) ^ (-γ))) * Real.log n))) atTop (𝓝 0) := by
    have hp : Tendsto (fun n : ℕ => 18 * Ctail * (2 * L * (1 + M) * ((n : ℝ) ^ (-γ))) *
        (1 + Real.exp ((2 * L * (1 + M) * ((n : ℝ) ^ (-γ))) * Real.log n) *
          ((2 * L * (1 + M) * ((n : ℝ) ^ (-γ))) * Real.log n)))
        atTop (𝓝 (0 * ((1 : ℝ) + 1 * 0))) := hD1.mul hfac
    rwa [zero_mul] at hp
  -- term 2: `9 * exp E * E → 0`
  have hp2 : Tendsto (fun n : ℕ => (9 : ℝ) *
      (Real.exp ((2 * L * (1 + M) * ((n : ℝ) ^ (-γ))) * Real.log n) *
        ((2 * L * (1 + M) * ((n : ℝ) ^ (-γ))) * Real.log n))) atTop (𝓝 ((9 : ℝ) * (1 * 0))) :=
    (hexp1.mul hE0).const_mul 9
  have hterm2 : Tendsto (fun n : ℕ => 9 * Real.exp ((2 * L * (1 + M) * ((n : ℝ) ^ (-γ))) *
      Real.log n) * ((2 * L * (1 + M) * ((n : ℝ) ^ (-γ))) * Real.log n)) atTop (𝓝 0) := by
    rw [mul_zero, mul_zero] at hp2
    refine hp2.congr' ?_
    filter_upwards with n
    ring
  -- term 4: `(3 / 2) * D → 0`
  have hterm4 : Tendsto (fun n : ℕ =>
      (3 / 2 : ℝ) * (2 * L * (1 + M) * ((n : ℝ) ^ (-γ)))) atTop (𝓝 0) := by
    have h4 := hD0.const_mul (3 / 2 : ℝ)
    rwa [mul_zero] at h4
  -- term 3: `16 / (R + 1) → 0`
  have hterm3 : Tendsto (fun n : ℕ =>
      16 * (((⌊(n : ℝ) ^ β⌋₊ : ℕ) + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) := by
    have hR1 : Tendsto (fun n : ℕ => ((⌊(n : ℝ) ^ β⌋₊ : ℕ) : ℝ) + 1) atTop atTop :=
      (feasibleR_tendsto_atTop β hβ0).atTop_add tendsto_const_nhds
    have hmul := (tendsto_inv_atTop_zero.comp hR1).const_mul 16
    rw [mul_zero] at hmul
    refine hmul.congr' ?_
    filter_upwards with n
    simp only [Function.comp_apply]
    push_cast
    ring
  -- term 5: the grid term, in split log-power form
  have hunfold : ∀ n : ℕ, 1 ≤ n →
      4 * (2 * ((n : ℝ) * ((n : ℝ) ^ (-γ)))) ^ (2 - 2 * h0) *
        gridCovarianceError b Ccov n
      = (4 * (2 : ℝ) ^ (2 - 2 * h0) * Ccov) *
        ((1 + Real.log (2 * (n : ℝ))) *
            (n : ℝ) ^ ((1 - γ) * (2 - 2 * h0) + (-1 : ℝ)) +
          (1 + Real.log (2 * (n : ℝ))) *
            (n : ℝ) ^ ((1 - γ) * (2 - 2 * h0) + (2 * b - 2))) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hS := fr_mesh_eq γ hn0
    have hA : (2 * ((n : ℝ) * ((n : ℝ) ^ (-γ)))) ^ (2 - 2 * h0)
        = (2 : ℝ) ^ (2 - 2 * h0) * ((n : ℝ) * ((n : ℝ) ^ (-γ))) ^ (2 - 2 * h0) :=
      Real.mul_rpow (by norm_num) (by positivity)
    rw [hA, hS, ← Real.rpow_mul hn0.le]
    simp only [gridCovarianceError]
    rw [Real.rpow_add hn0, Real.rpow_add hn0]
    ring
  have hcore0 : Tendsto (fun n : ℕ => (4 * (2 : ℝ) ^ (2 - 2 * h0) * Ccov) *
      ((1 + Real.log (2 * (n : ℝ))) *
          (n : ℝ) ^ ((1 - γ) * (2 - 2 * h0) + (-1 : ℝ)) +
        (1 + Real.log (2 * (n : ℝ))) *
          (n : ℝ) ^ ((1 - γ) * (2 - 2 * h0) + (2 * b - 2)))) atTop (𝓝 0) := by
    have hc := (hsub1.add hsub2).const_mul (4 * (2 : ℝ) ^ (2 - 2 * h0) * Ccov)
    rw [add_zero, mul_zero] at hc
    exact hc
  have hterm5 : Tendsto (fun n : ℕ =>
      4 * (2 * ((n : ℝ) * ((n : ℝ) ^ (-γ)))) ^ (2 - 2 * h0) *
        gridCovarianceError b Ccov n) atTop (𝓝 0) := by
    refine hcore0.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (hunfold n hn).symm
  -- assemble: envelope = free part + 16/(R+1), the free part is the 4-term sum
  have hdecomp : ∀ n : ℕ, q1ActualLongTailEnvelope b Ccov Ctail L M h0 n
      ((n : ℝ) ^ (-γ)) ((n : ℝ) * ((n : ℝ) ^ (-γ))) (⌊(n : ℝ) ^ β⌋₊)
      = q1TailEnvelopeFreePart b Ccov Ctail L M h0 n ((n : ℝ) ^ (-γ))
          ((n : ℝ) * ((n : ℝ) ^ (-γ))) +
        16 * (((⌊(n : ℝ) ^ β⌋₊ : ℕ) + 1 : ℕ) : ℝ)⁻¹ :=
    fun n => q1ActualLongTailEnvelope_eq b Ccov Ctail L M h0 n _ _ _
  have hfree : ∀ n : ℕ, q1TailEnvelopeFreePart b Ccov Ctail L M h0 n
      ((n : ℝ) ^ (-γ)) ((n : ℝ) * ((n : ℝ) ^ (-γ)))
      = 18 * Ctail * (2 * L * (1 + M) * ((n : ℝ) ^ (-γ))) *
          (1 + Real.exp ((2 * L * (1 + M) * ((n : ℝ) ^ (-γ))) * Real.log n) *
            ((2 * L * (1 + M) * ((n : ℝ) ^ (-γ))) * Real.log n)) +
        9 * Real.exp ((2 * L * (1 + M) * ((n : ℝ) ^ (-γ))) * Real.log n) *
          ((2 * L * (1 + M) * ((n : ℝ) ^ (-γ))) * Real.log n) +
        (3 / 2 : ℝ) * (2 * L * (1 + M) * ((n : ℝ) ^ (-γ))) +
        4 * (2 * ((n : ℝ) * ((n : ℝ) ^ (-γ)))) ^ (2 - 2 * h0) *
          gridCovarianceError b Ccov n := by
    intro n
    unfold q1TailEnvelopeFreePart
    ring
  have hsum0 : Tendsto (fun n : ℕ =>
      18 * Ctail * (2 * L * (1 + M) * ((n : ℝ) ^ (-γ))) *
          (1 + Real.exp ((2 * L * (1 + M) * ((n : ℝ) ^ (-γ))) * Real.log n) *
            ((2 * L * (1 + M) * ((n : ℝ) ^ (-γ))) * Real.log n)) +
        9 * Real.exp ((2 * L * (1 + M) * ((n : ℝ) ^ (-γ))) * Real.log n) *
          ((2 * L * (1 + M) * ((n : ℝ) ^ (-γ))) * Real.log n) +
        16 * (((⌊(n : ℝ) ^ β⌋₊ : ℕ) + 1 : ℕ) : ℝ)⁻¹ +
        (3 / 2 : ℝ) * (2 * L * (1 + M) * ((n : ℝ) ^ (-γ))) +
        4 * (2 * ((n : ℝ) * ((n : ℝ) ^ (-γ)))) ^ (2 - 2 * h0) *
          gridCovarianceError b Ccov n) atTop (𝓝 0) := by
    have h := ((hterm1.add hterm2).add hterm3).add (hterm4.add hterm5)
    simp only [zero_add] at h
    refine h.congr' ?_
    filter_upwards with n
    ring
  refine hsum0.congr' ?_
  filter_upwards with n
  rw [hdecomp n, hfree n]
  ring

/-! ## The full-resolution endpoint variants -/

/-- **The full-chain endpoint with the scalar rates fully instantiated**
(`hR`/`hcut`/`hEnv` discharged at the explicit rate `R n = ⌊n ^ β⌋₊`).

This is the concrete-`R` version of
`Hurst.FullChainGeneralSigned.actualQ1_knownScaleH_fullChain_generalSigned`:
the three scalar-rate premises are replaced by the rate window
`0 < β < (1 - γ) * (1 - 2 * (2 - 2 * f t))` (nonempty since
`1 - 2 * (2 - 2 * f t) = 4 * f t - 3 > 0` under `hlong`); the envelope premise
holds for every fixed constants by linearity.  The remaining premises are the
model window, `hgrid`, the center-band data and the E5 drift data (`hane` is
discharged internally by `Hurst.FeatureRowNondegenerate.actualQ1_hane_all`). -/
theorem actualQ1_knownScaleH_fullChain_generalSigned_scalarRates
    (p a b M : ℝ) (r : ℕ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hgrid : (1 - γ) * (2 - 2 * f t) < 2 - 2 * b)
    (β : ℝ) (hβ0 : 0 < β) (hβ : β < (1 - γ) * (1 - 2 * (2 - 2 * f t)))
    (cσ d : ℝ) (hd : 0 < d)
    (hband : ∀ᶠ n : ℕ in atTop,
      d ≤ (cσ - ∫ y, p5KnownScaleLogStatistic f r n ((n : ℝ) ^ (-γ)) t y ∂
            featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) /
          (2 * Real.log n)
      ∧ (cσ - ∫ y, p5KnownScaleLogStatistic f r n ((n : ℝ) ^ (-γ)) t y ∂
            featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) /
          (2 * Real.log n)
        ≤ 1 - d)
    (hE5 : (1 - γ) * (2 - 2 * f t) < γ * 1)
    (C : ℝ) (hC : 0 ≤ C)
    (hBias : ∀ᶠ n : ℕ in atTop,
      |∫ y, p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ y ∂
          featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)) - f t|
        ≤ C * ((n : ℝ) ^ (-γ))) :
    ∃ Q : (ℕ → ℝ) → ℝ,
      IsWeightedRieszSecondChaosLaw gaussianSeqMeasure Q (2 - 2 * f t)
        (f t * (2 * f t - 1)) (equivalentKernel r) ∧
      TendstoInDistribution
        (fun (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) =>
          seamScaleC f t (fun m => ((m : ℝ) ^ (-γ))) n *
            (p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ x - f t))
        atTop (fun ω => -Q ω)
        (fun n => featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))
        gaussianSeqMeasure := by
  have hfb : f t < 1 := lt_of_le_of_lt (hF ht).2 hb
  have hψpos : 0 < 2 - 2 * f t := by linarith
  have hψhalf : 2 - 2 * f t < 1 / 2 := by linarith
  have hane : ∀ (n : ℕ) (k : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card),
      ∑ i, actualQ1Coeff n ((n : ℝ) ^ (-γ)) t k i •
        actualQ1Obs f n (midpointSampleHurst f hf.1 n) i ≠ 0 :=
    fun n k => actualQ1_hane_all f hf ((n : ℝ) ^ (-γ)) t n k
  have hR := feasibleR_tendsto_atTop β hβ0
  have hcut := feasibleR_cut_tendsto f t γ β hγ1 hβ0 hβ
  have hEnv : ∀ Ccov ≥ 0, ∀ Ctail ≥ 0, ∀ L > 0,
      Tendsto (fun n : ℕ =>
        q1ActualLongTailEnvelope b Ccov Ctail L M (f t) n ((n : ℝ) ^ (-γ))
          ((n : ℝ) * ((n : ℝ) ^ (-γ))) ((⌊(n : ℝ) ^ β⌋₊ : ℕ))) atTop (𝓝 0) :=
    fun Ccov _ Ctail _ L _ =>
      feasibleR_env_tendsto b Ccov Ctail L M (f t) γ β hγ0 hψpos hψhalf hgrid hβ0
  exact actualQ1_knownScaleH_fullChain_generalSigned p a b M r hp ha hb hab hM f hf hF
    t ht hlong γ hγ0 hγ1 hgrid hane (fun n => (⌊(n : ℝ) ^ β⌋₊ : ℕ)) hR hcut hEnv
    cσ d hd hband hE5 C hC hBias

/-! ## The feasible instance `γ = f t` (E5 window and b-band both free) -/

/-- **The feasible instance `γ = f t` with the scalar rates fully
instantiated.**  At the bandwidth `δ n = n ^ (-(f t))` the E5 window
`(1 - f t) * (2 - 2 * f t) < f t` (i.e. `ψ² < f t`) and the grid window
`(1 - f t) * (2 - 2 * f t) < 2 - 2 * b` (i.e. the b-band
`(1 - f t) ^ 2 < 1 - b`) follow from the long-memory band `3 / 4 < f t` and
the b-band datum by arithmetic alone, and the scalar rates are instantiated at
`R n = ⌊n ^ β⌋₊` under the window `0 < β < (1 - f t) * (4 * f t - 3)`.  The
remaining premises are the model window, the b-band datum, the β
window, the center-band data and the E5 bias envelope (`hane` is discharged
internally by `Hurst.FeatureRowNondegenerate.actualQ1_hane_all`). -/
theorem actualQ1_knownScaleH_fullChain_generalSigned_feasible
    (p a b M : ℝ) (r : ℕ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (hbband : (1 - f t) ^ 2 < 1 - b)
    (β : ℝ) (hβ0 : 0 < β) (hβ : β < (1 - f t) * (4 * f t - 3))
    (cσ d : ℝ) (hd : 0 < d)
    (hband : ∀ᶠ n : ℕ in atTop,
      d ≤ (cσ - ∫ y, p5KnownScaleLogStatistic f r n ((n : ℝ) ^ (-(f t))) t y ∂
            featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) /
          (2 * Real.log n)
      ∧ (cσ - ∫ y, p5KnownScaleLogStatistic f r n ((n : ℝ) ^ (-(f t))) t y ∂
            featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) /
          (2 * Real.log n)
        ≤ 1 - d)
    (C : ℝ) (hC : 0 ≤ C)
    (hBias : ∀ᶠ n : ℕ in atTop,
      |∫ y, p5KnownScaleEstimator f r n ((n : ℝ) ^ (-(f t))) t cσ y ∂
          featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)) - f t|
        ≤ C * ((n : ℝ) ^ (-(f t)))) :
    ∃ Q : (ℕ → ℝ) → ℝ,
      IsWeightedRieszSecondChaosLaw gaussianSeqMeasure Q (2 - 2 * f t)
        (f t * (2 * f t - 1)) (equivalentKernel r) ∧
      TendstoInDistribution
        (fun (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) =>
          seamScaleC f t (fun m => ((m : ℝ) ^ (-(f t)))) n *
            (p5KnownScaleEstimator f r n ((n : ℝ) ^ (-(f t))) t cσ x - f t))
        atTop (fun ω => -Q ω)
        (fun n => featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))
        gaussianSeqMeasure := by
  have hft : f t ∈ Ioo (0 : ℝ) 1 := hf.1 ht
  have hft1 : (f t : ℝ) < 1 := hft.2
  have hbd : (1 - f t) * (1 - f t) < 1 - b := by simpa only [pow_two] using hbband
  -- the grid window at `γ = f t` is the b-band datum
  have hgrid : (1 - f t) * (2 - 2 * f t) < 2 - 2 * b := by
    have h2 : (1 - f t) * (2 - 2 * f t) = 2 * ((1 - f t) * (1 - f t)) := by ring
    rw [h2]
    linarith [hbd]
  -- the E5 window at `γ = f t` is `ψ² < f t`, discharged from `hlong`
  have hE5 : (1 - f t) * (2 - 2 * f t) < f t * 1 := by
    have hq : (0 : ℝ) ≤ 1 - f t := by linarith
    have hq1 : 1 - f t ≤ 1 / 4 := by linarith
    have hsq : (1 - f t) * (1 - f t) ≤ (1 - f t) * (1 / 4) :=
      mul_le_mul_of_nonneg_left hq1 hq
    have hsq2 : (1 - f t) * (1 / 4) ≤ (1 : ℝ) / 16 := by
      have h := mul_le_mul_of_nonneg_right hq1 (show (0 : ℝ) ≤ 1 / 4 by norm_num)
      rwa [show ((1 : ℝ) / 4) * (1 / 4) = (1 : ℝ) / 16 by norm_num] at h
    have e : (1 - f t) * (2 - 2 * f t) = 2 * ((1 - f t) * (1 - f t)) := by ring
    rw [e]
    linarith
  have hane : ∀ (n : ℕ) (k : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-(f t))) t).card),
      ∑ i, actualQ1Coeff n ((n : ℝ) ^ (-(f t))) t k i •
        actualQ1Obs f n (midpointSampleHurst f hf.1 n) i ≠ 0 :=
    fun n k => actualQ1_hane_all f hf ((n : ℝ) ^ (-(f t))) t n k
  -- the β window in the `1 - 2ψ` shape
  have hβ' : β < (1 - f t) * (1 - 2 * (2 - 2 * f t)) := by
    have hw : (1 - f t) * (4 * f t - 3) = (1 - f t) * (1 - 2 * (2 - 2 * f t)) := by ring
    rw [← hw]
    exact hβ
  exact actualQ1_knownScaleH_fullChain_generalSigned_scalarRates p a b M r hp ha hb hab hM
    f hf hF t ht hlong (f t) hft.1 hft1 hgrid β hβ0 hβ' cσ d hd hband hE5 C hC hBias

end Hurst
