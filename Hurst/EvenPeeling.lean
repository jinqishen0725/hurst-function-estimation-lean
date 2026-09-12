import Hurst.TailExtraction
import Hurst.SpectralMatchingSort
import Hurst.PeelingSubtraction
import Hurst.ResidualMax
import Hurst.TailExtractionArray
import Hurst.PeelingInduction

/-!
# Signed-spectrum peeling: the peeling chain on `|x|` with even power sums only

The actual weighted matrices may have SIGNED eigenvalues (local-polynomial
weights are sign-changing; cf. `Hurst.WeightedMatrixPSD`), so the array of
eigenvalues `x n i` cannot be assumed nonnegative.  For SIGNED spectra the even
power sums of `λ` coincide with the even power sums of `|λ|`:
`Σ_i λ_i ^ k = Σ_i |λ_i| ^ k` for even `k`.  Since the Riesz target spectrum
`lam` is NONNEGATIVE, the whole peeling chain can be run on the nonnegative
array `y n i := |x n i|` with the power-sum hypotheses supplied only at EVEN
exponents `k ≥ 2`.  Even exponents are cofinal in `atTop`, and every
extraction/contradiction argument only ever pairs `k` with `k - 2` (which stays
even), so every ingredient of the peeling chain survives.

Contents (each level copies-adapts its all-`k` upstream counterpart):

* `abs_pow_even`, `even_pow_sum_abs_congr` : Step 0, the even-power bridge;
* `tendsto_le_of_eventually_even_le` : squeeze lemma for inequalities that hold
  only along even indices;
* `tail_array_even_forall_eventually_le`, `tail_array_even_max_eventually_le`,
  `tail_array_even_max_eventually_ge` : even-`k` max extraction, both halves
  (adapted from `Hurst.TailExtractionArray`);
* `residualTailPowerSum_even_tendsto` : even-`k` residual subtraction (adapted
  from `Hurst.PeelingInduction.residualTailPowerSum_restricted_tendsto`);
* `paddedEvenRearranged_tendsto` : the peeling induction for nonnegative arrays
  with even-`k` power sums only;
* `paddedAbsRearranged_tendsto` : the main signed-spectrum matching theorem —
  for every `j`, `padRearranged (fun i => |x n i|) j → lam j`.
-/

namespace Hurst

open Filter Topology

/-! ## Step 0: the even-power bridge -/

/-- On even powers the absolute value is transparent: `|a| ^ k = a ^ k` for
even `k`. -/
theorem abs_pow_even {a : ℝ} {k : ℕ} (hk : Even k) : |a| ^ k = a ^ k := by
  rcases hk with ⟨r, hr⟩
  subst hr
  have hb : ∀ b : ℝ, b ^ (r + r) = (b ^ 2) ^ r := by
    intro b
    rw [← two_mul, pow_mul]
  rw [hb, hb, sq_abs]

/-- For even `k`, the `k`-th power sums of `|xv|` and of `xv` agree. -/
theorem even_pow_sum_abs_congr {m : ℕ} (xv : Fin m → ℝ) {k : ℕ} (hk : Even k) :
    ∑ i : Fin m, |xv i| ^ k = ∑ i : Fin m, xv i ^ k :=
  Finset.sum_congr rfl fun _ _ => abs_pow_even hk

/-! ## Squeezing along even indices -/

/-- If `a k → L`, `b k → c`, and `a k ≤ b k` for all sufficiently large EVEN
`k`, then `L ≤ c`.  Even indices are cofinal, so this is the even-`k` variant
of `le_of_tendsto_of_tendsto`. -/
theorem tendsto_le_of_eventually_even_le {a b : ℕ → ℝ} {L c : ℝ}
    (ha : Tendsto a atTop (𝓝 L)) (hb : Tendsto b atTop (𝓝 c))
    (h : ∀ᶠ k in atTop, Even k → a k ≤ b k) : L ≤ c := by
  by_contra hcon
  have hgc : c < L := lt_of_not_ge hcon
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.1
    (ha.eventually_const_lt (show L - (L - c) / 3 < L by linarith))
  obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.1
    (hb.eventually_lt_const (show (c : ℝ) < c + (L - c) / 3 by linarith))
  obtain ⟨N3, hN3⟩ := Filter.eventually_atTop.1 h
  set t := max (max N1 N2) N3 with ht
  have hkeven : Even (2 * t) := ⟨t, by ring⟩
  have h1 := hN1 (2 * t) (by omega)
  have h2 := hN2 (2 * t) (by omega)
  have h3 := hN3 (2 * t) (by omega) hkeven
  linarith

/-! ## Even-`k` max extraction (copy-adapt of `Hurst.TailExtractionArray`) -/

variable {m : ℕ → ℕ} {y : ∀ n, Fin (m n) → ℝ} {lam : ℕ → ℝ} {J : ℕ}

/-- Single-coordinate ε-form, upper half, from EVEN-`k` power sums only: each
observed coordinate is eventually at most `lam J + ε`. -/
theorem tail_array_even_forall_eventually_le
    (_hm : ∀ n, 0 < m n) (hb : ∀ n i, 0 ≤ y n i)
    (hy : ∀ k : ℕ, 2 ≤ k → Even k → Tendsto (fun n => ∑ i : Fin (m n), y n i ^ k) atTop
      (𝓝 (tailPowerSum lam J k)))
    (hl : Antitone lam ∧ ∀ j, 0 ≤ lam j ∧ Summable (fun j => lam j ^ 2)) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ i, y n i ≤ lam J + ε := by
  intro ε hε
  obtain ⟨hlam, hpoint⟩ := hl
  have hnn : ∀ j, 0 ≤ lam j := fun j => (hpoint j).1
  have hsum : Summable (fun j => lam j ^ 2) := (hpoint 0).2
  -- Choose an EVEN `k ≥ 2` with `(tailPowerSum lam J k) ^ (1/k) < lam J + ε`.
  obtain ⟨k, hk2, hkeven, hroot⟩ :
      ∃ k : ℕ, 2 ≤ k ∧ Even k ∧ (tailPowerSum lam J k) ^ ((k : ℝ) ⁻¹) < lam J + ε := by
    obtain ⟨K, hK⟩ := Filter.eventually_atTop.1
      ((tailPowerSum_root_eventually hlam hnn hsum J ε hε).and (Filter.eventually_ge_atTop 2))
    exact ⟨2 * max 2 K, by omega, ⟨max 2 K, by ring⟩, (hK _ (by omega)).1.2⟩
  have hL0 : (0 : ℝ) < lam J + ε := by linarith [hnn J]
  have hS0 : 0 ≤ tailPowerSum lam J k := by
    simp only [tailPowerSum]
    exact tsum_nonneg fun d => pow_nonneg (hnn (J + d)) k
  have hroot0 : 0 ≤ (tailPowerSum lam J k) ^ ((k : ℝ) ⁻¹) := Real.rpow_nonneg hS0 _
  -- Convert the root bound into `S_k < (lam J + ε) ^ k`.
  have hkey : tailPowerSum lam J k < (lam J + ε) ^ k := by
    have h1 := Real.rpow_lt_rpow hroot0 hroot
      (show (0 : ℝ) < (k : ℝ) by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_two hk2)
    have e1 : ((tailPowerSum lam J k) ^ ((k : ℝ) ⁻¹)) ^ (k : ℝ) = tailPowerSum lam J k := by
      rw [← Real.rpow_mul hS0, inv_mul_cancel₀ (a := (k : ℝ))
        (by exact_mod_cast ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two hk2) : (k : ℝ) ≠ 0),
        Real.rpow_one]
    rw [Real.rpow_natCast (lam J + ε) k, e1] at h1
    exact h1
  -- Pass to the finite power sums, then to single coordinates.
  have hfin := (hy k hk2 hkeven).eventually_lt_const hkey
  refine hfin.mono fun n hn i => ?_
  have hsingle : y n i ^ k ≤ ∑ j : Fin (m n), y n j ^ k :=
    Finset.single_le_sum (fun j _ => pow_nonneg (hb n j) k) (Finset.mem_univ i)
  have hpow : y n i ^ k < (lam J + ε) ^ k := lt_of_le_of_lt hsingle hn
  by_contra hcon
  exact absurd hpow (not_lt.2 (pow_le_pow_left₀ hL0.le (not_le.1 hcon).le k))

/-- Supremum ε-form, upper half, from EVEN-`k` power sums only. -/
theorem tail_array_even_max_eventually_le
    (hm : ∀ n, 0 < m n) (hb : ∀ n i, 0 ≤ y n i)
    (hy : ∀ k : ℕ, 2 ≤ k → Even k → Tendsto (fun n => ∑ i : Fin (m n), y n i ^ k) atTop
      (𝓝 (tailPowerSum lam J k)))
    (hl : Antitone lam ∧ ∀ j, 0 ≤ lam j ∧ Summable (fun j => lam j ^ 2)) :
    ∀ ε > 0, ∀ᶠ n in atTop, ⨆ i, y n i ≤ lam J + ε :=
  fun ε hε => (tail_array_even_forall_eventually_le hm hb hy hl ε hε).mono fun n hn => by
    haveI : Nonempty (Fin (m n)) := ⟨⟨0, hm n⟩⟩
    exact ciSup_le hn

/-- **Even-`k` array max extraction, lower half.**  Under EVEN-`k` convergent
power sums against an antitone summable-square profile `lam` with `lam J > 0`,
the coordinate suprema are eventually at least `lam J - ε` for every `ε > 0`
with `2 * ε < lam J`.  The `k`-scaling contradiction only pairs `k` with
`k - 2`, so the even restriction is preserved. -/
theorem tail_array_even_max_eventually_ge
    (_hm : ∀ n, 0 < m n) (hb : ∀ n i, 0 ≤ y n i)
    (hy : ∀ k : ℕ, 2 ≤ k → Even k → Tendsto (fun n => ∑ i : Fin (m n), y n i ^ k) atTop
      (𝓝 (tailPowerSum lam J k)))
    (hl : Antitone lam ∧ ∀ j, 0 ≤ lam j ∧ Summable (fun j => lam j ^ 2))
    (hpos : 0 < lam J) :
    ∀ ε > 0, 2 * ε < lam J → ∀ᶠ n in atTop, lam J - ε ≤ ⨆ i, y n i := by
  intro ε hε htwo
  obtain ⟨hlam, hpoint⟩ := hl
  have hnn : ∀ j, 0 ≤ lam j := fun j => (hpoint j).1
  have hsum : Summable (fun j => lam j ^ 2) := (hpoint 0).2
  have hsumJ2 : Summable (fun d : ℕ => lam (J + d) ^ 2) :=
    Summable.of_nonneg_of_le (fun d => pow_nonneg (hnn (J + d)) 2)
      (fun d => pow_le_pow_left₀ (hnn (J + d)) (hlam (Nat.le_add_left d J)) 2) hsum
  have hS₂nn : 0 ≤ tailPowerSum lam J 2 := by
    simp only [tailPowerSum]
    exact tsum_nonneg fun d => pow_nonneg (hnn (J + d)) 2
  have hS₂pos : 0 < tailPowerSum lam J 2 := by
    have hsplit := (hsumJ2.sum_add_tsum_nat_add 1).symm
    have hnn' : 0 ≤ ∑' d : ℕ, lam (J + (d + 1)) ^ 2 :=
      tsum_nonneg fun d => pow_nonneg (hnn (J + (d + 1))) 2
    have hr0 : ∑ d ∈ Finset.range 1, lam (J + d) ^ 2 = lam J ^ 2 := by
      rw [Finset.sum_range_one, Nat.add_zero]
    calc (0 : ℝ) < lam J ^ 2 := pow_pos hpos 2
      _ ≤ ∑' d : ℕ, lam (J + d) ^ 2 := by rw [hsplit]; linarith
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  push Not at hcon
  set c : ℝ := lam J - ε with hcdef
  set S₂ : ℝ := tailPowerSum lam J 2 with hS₂def
  have hcpos : 0 < c := by linarith
  have hSk_nn : ∀ k : ℕ, 0 ≤ tailPowerSum lam J k := fun k => by
    simp only [tailPowerSum]
    exact tsum_nonneg fun d => pow_nonneg (hnn (J + d)) k
  -- The bad rows squeeze every EVEN `k`-th power sum by `c ^ (k - 2) * (S₂ + δ)`.
  have hkey : ∀ k : ℕ, 2 ≤ k → Even k → ∀ δ : ℝ, δ > 0 →
      tailPowerSum lam J k ≤ c ^ (k - 2) * (S₂ + δ) := by
    intro k hk hkeven δ hδ
    -- Row-wise bound under `⨆ i, y n i < c`.
    have hbnd : ∀ n : ℕ, ⨆ i, y n i < c →
        ∑ i : Fin (m n), y n i ^ k ≤ c ^ (k - 2) * ∑ i : Fin (m n), y n i ^ 2 := by
      intro n hsup
      have hnnx : ∀ i : Fin (m n), y n i < c := fun i =>
        lt_of_le_of_lt (le_ciSup (Set.finite_range (y n)).bddAbove i) hsup
      calc ∑ i : Fin (m n), y n i ^ k
          = ∑ i : Fin (m n), y n i ^ (k - 2) * y n i ^ 2 := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← pow_add, Nat.sub_add_cancel hk]
        _ ≤ ∑ i : Fin (m n), c ^ (k - 2) * y n i ^ 2 :=
            Finset.sum_le_sum fun i _ =>
              mul_le_mul_of_nonneg_right
                (pow_le_pow_left₀ (hb n i) (hnnx i).le (k - 2)) (pow_nonneg (hb n i) 2)
        _ = c ^ (k - 2) * ∑ i : Fin (m n), y n i ^ 2 := by rw [Finset.mul_sum]
    by_contra hge
    have hgt : c ^ (k - 2) * (S₂ + δ) < tailPowerSum lam J k := not_le.mp hge
    obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.1
      (Filter.Tendsto.eventually_const_lt hgt (hy k hk hkeven))
    have hgt2 : S₂ < S₂ + δ := by linarith
    obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.1
      ((hy 2 (Nat.le_refl 2) (by exact ⟨1, by norm_num⟩)).eventually_le_const hgt2)
    obtain ⟨n, hnN, hnmax⟩ := frequently_atTop.1 hcon (max N1 N2)
    have hn1 := hN1 n (le_trans (le_max_left N1 N2) hnN)
    have hn2 := hN2 n (le_trans (le_max_right N1 N2) hnN)
    have h3 := hbnd n hnmax
    have h4 : c ^ (k - 2) * ∑ i : Fin (m n), y n i ^ 2 ≤ c ^ (k - 2) * (S₂ + δ) :=
      mul_le_mul_of_nonneg_left hn2 (pow_nonneg hcpos.le (k - 2))
    exact absurd (le_trans h3 h4) (not_le.mpr hn1)
  -- Pass to the `k`-th roots and let EVEN `k → ∞`.
  have hroot : ∀ k : ℕ, 2 ≤ k → Even k → ∀ δ : ℝ, δ > 0 →
      (tailPowerSum lam J k) ^ ((k : ℝ) ⁻¹) ≤ (c ^ (k - 2) * (S₂ + δ)) ^ ((k : ℝ) ⁻¹) := by
    intro k hk hkeven δ hδ
    have hklt : (0 : ℕ) < k := by omega
    have hkinv : 0 ≤ ((k : ℝ) ⁻¹) := le_of_lt (inv_pos.2 (Nat.cast_pos.2 hklt))
    exact Real.rpow_le_rpow (hSk_nn k) (hkey k hk hkeven δ hδ) hkinv
  have hL : Tendsto (fun k : ℕ => (tailPowerSum lam J k) ^ ((k : ℝ) ⁻¹)) atTop
      (𝓝 (lam J)) := tailPowerSum_root_tendsto hlam hnn hsum J
  have hR : ∀ δ : ℝ, δ > 0 →
      Tendsto (fun k : ℕ => (c ^ (k - 2) * (S₂ + δ)) ^ ((k : ℝ) ⁻¹)) atTop (𝓝 c) := by
    intro δ hδ
    have hSδnn : 0 ≤ S₂ + δ := by linarith
    have hSδpos : 0 < S₂ + δ := by linarith
    have hinv0 : Tendsto (fun k : ℕ => ((k : ℝ) ⁻¹)) atTop (𝓝 0) :=
      Filter.Tendsto.inv_tendsto_atTop tendsto_natCast_atTop_atTop
    have hSδroot : Tendsto (fun k : ℕ => (S₂ + δ) ^ ((k : ℝ) ⁻¹)) atTop (𝓝 1) := by
      have hstep : ∀ k : ℕ, (S₂ + δ) ^ ((k : ℝ) ⁻¹)
          = Real.exp (Real.log (S₂ + δ) * ((k : ℝ) ⁻¹)) := fun k =>
        Real.rpow_def_of_pos hSδpos _
      have h1 : Tendsto (fun k : ℕ => Real.log (S₂ + δ) * ((k : ℝ) ⁻¹)) atTop
          (𝓝 (Real.log (S₂ + δ) * 0)) := hinv0.const_mul _
      rw [mul_zero] at h1
      have h2 : Tendsto (fun k : ℕ =>
            Real.exp (Real.log (S₂ + δ) * ((k : ℝ) ⁻¹))) atTop (𝓝 1) := by
        have hcomp := Filter.Tendsto.comp
          Real.continuous_exp.continuousAt.tendsto h1
        rw [Real.exp_zero] at hcomp
        exact hcomp
      simpa only [hstep] using h2
    -- rewrite the root as `c ^ ((k-2)/k) * (S₂ + δ) ^ (1/k)`
    have heq : ∀ k : ℕ, (c ^ (k - 2) * (S₂ + δ)) ^ ((k : ℝ) ⁻¹)
        = c ^ (((k - 2 : ℕ) : ℝ) * ((k : ℝ) ⁻¹)) * (S₂ + δ) ^ ((k : ℝ) ⁻¹) := by
      intro k
      have e1 : c ^ (k - 2) = c ^ ((k - 2 : ℕ) : ℝ) := by rw [Real.rpow_natCast]
      rw [e1, Real.mul_rpow (Real.rpow_nonneg hcpos.le ((k - 2 : ℕ) : ℝ)) hSδnn,
        ← Real.rpow_mul hcpos.le ((k - 2 : ℕ) : ℝ) ((k : ℝ) ⁻¹)]
    have hdiv : Tendsto (fun k : ℕ => ((k - 2 : ℕ) : ℝ) * ((k : ℝ) ⁻¹)) atTop (𝓝 1) := by
      have h2 : Tendsto (fun k : ℕ => 1 - 2 * ((k : ℝ) ⁻¹)) atTop (𝓝 1) := by
        simpa using (hinv0.const_mul 2).const_sub 1
      refine h2.congr' (Filter.eventually_atTop.2 ⟨2, fun k hk1 => ?_⟩)
      show 1 - 2 * ((k : ℝ) ⁻¹) = ((k - 2 : ℕ) : ℝ) * ((k : ℝ) ⁻¹)
      have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      have hcast : ((k - 2 : ℕ) : ℝ) = (k : ℝ) - 2 := by
        have h2' : ((k - 2 : ℕ) : ℝ) + ((2 : ℕ) : ℝ) = ((k : ℕ) : ℝ) := by
          have h4 : ((k - 2 : ℕ) + 2 : ℕ) = k := Nat.sub_add_cancel hk1
          rw [← Nat.cast_add, h4]
        have h5 : ((2 : ℕ) : ℝ) = 2 := Nat.cast_two
        linarith
      rw [hcast, sub_mul, mul_inv_cancel₀ hk0]
    have hexp : Tendsto (fun k : ℕ => c ^ (((k - 2 : ℕ) : ℝ) * ((k : ℝ) ⁻¹))) atTop
        (𝓝 c) := by
      have hstep : ∀ k : ℕ, c ^ (((k - 2 : ℕ) : ℝ) * ((k : ℝ) ⁻¹))
          = Real.exp (Real.log c * (((k - 2 : ℕ) : ℝ) * ((k : ℝ) ⁻¹))) := fun k =>
        Real.rpow_def_of_pos hcpos _
      have h1 : Tendsto (fun k : ℕ => Real.log c * (((k - 2 : ℕ) : ℝ) * ((k : ℝ) ⁻¹))) atTop
          (𝓝 (Real.log c * 1)) := hdiv.const_mul _
      rw [mul_one] at h1
      have h2 : Tendsto (fun k : ℕ =>
            Real.exp (Real.log c * (((k - 2 : ℕ) : ℝ) * ((k : ℝ) ⁻¹)))) atTop
          (𝓝 c) := by
        have hcomp := Filter.Tendsto.comp
          Real.continuous_exp.continuousAt.tendsto h1
        rw [Real.exp_log hcpos] at hcomp
        exact hcomp
      simpa only [hstep] using h2
    have hprod := hexp.mul hSδroot
    rw [mul_one] at hprod
    simp only [heq]
    exact hprod
  -- Squeeze along EVEN indices only.
  have hle : lam J ≤ c := by
    have hR1 := hR (1 : ℝ) one_pos
    refine tendsto_le_of_eventually_even_le hL hR1 ?_
    exact Filter.eventually_atTop.2 ⟨2, fun k hk hkev => hroot k hk hkev 1 one_pos⟩
  linarith

/-! ## Even-`k` residual subtraction (copy-adapt of `Hurst.PeelingInduction`) -/

/-- **Residual power-sum lemma, even-`k` form with restricted induction
hypothesis.**  If the EVEN power sums of `x n` converge to those of `lam` and
every padded rearranged entry at levels `c < J` converges, then the EVEN power
sums of the residual array (top `J` entries removed) converge to
`tailPowerSum lam J k`. -/
theorem residualTailPowerSum_even_tendsto
    (m : ℕ → ℕ) (_hm : ∀ n, 0 < m n) (x : ∀ n, Fin (m n) → ℝ) (lam : ℕ → ℝ)
    (hl : Antitone lam ∧ ∀ j, 0 ≤ lam j ∧ Summable (fun j => lam j ^ 2))
    (hp : ∀ k : ℕ, 2 ≤ k → Even k → Tendsto (fun n => ∑ i : Fin (m n), x n i ^ k) atTop
      (𝓝 (∑' j : ℕ, lam j ^ k)))
    (J k : ℕ) (hk : 2 ≤ k) (hkeven : Even k)
    (hip : ∀ c : ℕ, c < J → Tendsto (fun n => padRearranged (x n) c) atTop (𝓝 (lam c))) :
    Tendsto (fun n => ∑ i : Fin (m n), spectralResidual J (x n) i ^ k) atTop
      (𝓝 (tailPowerSum lam J k)) := by
  have hlam := hl.1
  have hnn : ∀ j, 0 ≤ lam j := fun j => (hl.2 j).1
  have hsum : Summable (fun j => lam j ^ 2) := (hl.2 0).2
  have h2k : k ≠ 0 := by omega
  have hsumk := summable_pow_of_square hlam hnn hk hsum
  have hlimval : (∑' j : ℕ, if J ≤ j then lam j ^ k else (0:ℝ))
      = tailPowerSum lam J k := by
    show (∑' j : ℕ, if J ≤ j then lam j ^ k else (0:ℝ))
      = ∑' d : ℕ, lam (J + d) ^ k
    exact tsum_pow_if_eq_shift hnn hsumk
  rw [← hlimval]
  have hsplit : ∀ n : ℕ,
      (∑ i : Fin (m n), (if J ≤ specDescendingRank (x n) i then x n i else (0:ℝ)) ^ k)
        + ∑ c ∈ Finset.range J, (padRearranged (x n) c) ^ k
      = ∑ i : Fin (m n), x n i ^ k := fun n => resid_split (m n) (x n) J k h2k
  have htoplim : Tendsto (fun n => ∑ c ∈ Finset.range J, (padRearranged (x n) c) ^ k)
      atTop (𝓝 (∑ c ∈ Finset.range J, lam c ^ k)) :=
    tendsto_finsetSum _ fun c hc => Tendsto.pow (hip c (Finset.mem_range.mp hc)) k
  have hseries : (∑' j : ℕ, lam j ^ k)
      = (∑ c ∈ Finset.range J, lam c ^ k) + ∑' d : ℕ, lam (J + d) ^ k := by
    have hs := hsumk.sum_add_tsum_nat_add J
    have hconv : (∑' d : ℕ, lam (d + J) ^ k) = (∑' d : ℕ, lam (J + d) ^ k) :=
      tsum_congr fun d => congrArg (fun z => z ^ k) (congrArg lam (Nat.add_comm d J))
    rw [← hs, hconv]
  have hlimval2 : (∑' j : ℕ, if J ≤ j then lam j ^ k else (0:ℝ))
      = (∑' j : ℕ, lam j ^ k) - ∑ c ∈ Finset.range J, lam c ^ k := by
    rw [tsum_pow_if_eq_shift hnn hsumk, hseries]
    ring
  have hfin : Tendsto (fun n => (∑ i : Fin (m n), x n i ^ k)
        - ∑ c ∈ Finset.range J, (padRearranged (x n) c) ^ k)
      atTop (𝓝 ((∑' j : ℕ, lam j ^ k) - ∑ c ∈ Finset.range J, lam c ^ k)) :=
    Tendsto.sub (hp k hk hkeven) htoplim
  have hfun : ∀ n : ℕ, (∑ i : Fin (m n), x n i ^ k)
        - ∑ c ∈ Finset.range J, (padRearranged (x n) c) ^ k
      = ∑ i : Fin (m n),
        (if J ≤ specDescendingRank (x n) i then x n i else (0:ℝ)) ^ k := by
    intro n
    have hsn := hsplit n
    linarith
  rw [hlimval2]
  exact Tendsto.congr hfun hfin

/-! ## The peeling induction with even-`k` power sums only -/

/-- **Even-`k` peeling induction.**  If the power sums of nonnegative arrays
`y n` converge to those of an antitone, nonnegative, square-summable profile
`lam` at every EVEN exponent `k ≥ 2`, then every padded decreasingly
rearranged entry converges to the corresponding entry of `lam`. -/
theorem paddedEvenRearranged_tendsto (m : ℕ → ℕ) (y : ∀ n, Fin (m n) → ℝ) (lam : ℕ → ℝ)
    (hm : ∀ n, 0 < m n) (hmtop : Tendsto m atTop atTop)
    (hb : ∀ n i, 0 ≤ y n i)
    (hl : Antitone lam ∧ ∀ j, 0 ≤ lam j ∧ Summable (fun j => lam j ^ 2))
    (hp : ∀ k : ℕ, 2 ≤ k → Even k → Tendsto (fun n => ∑ i : Fin (m n), y n i ^ k) atTop
      (𝓝 (∑' j, lam j ^ k))) :
    ∀ j : ℕ, Tendsto (fun n => padRearranged (y n) j) atTop (𝓝 (lam j)) := by
  -- The induction step at level `j`, assuming convergence below `j`.
  have hstep : ∀ j : ℕ,
      (∀ c : ℕ, c < j → Tendsto (fun n => padRearranged (y n) c) atTop (𝓝 (lam c))) →
      Tendsto (fun n => padRearranged (y n) j) atTop (𝓝 (lam j)) := by
    intro j ih
    -- The residual array is nonnegative.
    have hb' : ∀ n i, 0 ≤ spectralResidual j (y n) i := fun n i => by
      rw [spectralResidual_apply]
      by_cases h : j ≤ specDescendingRank (y n) i
      · rw [if_pos h]; exact hb n i
      · rw [if_neg h]
    -- Residual power sums converge to the `j`-tail power sums at even `k`.
    have hy : ∀ k : ℕ, 2 ≤ k → Even k → Tendsto
        (fun n => ∑ i : Fin (m n), spectralResidual j (y n) i ^ k) atTop
        (𝓝 (tailPowerSum lam j k)) :=
      fun k hk hkev => residualTailPowerSum_even_tendsto m hm y lam hl hp j k hk hkev ih
    -- Eventually `j ≤ m n`, so the residual supremum is the `j`-th padded entry.
    have hev : ∀ᶠ n in atTop,
        (⨆ i : Fin (m n), spectralResidual j (y n) i) = padRearranged (y n) j := by
      filter_upwards [Filter.Tendsto.eventually_ge_atTop hmtop j] with n hn
      exact iSup_spectralResidual_eq_padRearranged j (y n) (hb n) hn
    by_cases hj0 : lam j = 0
    · -- Zero case: `lam j = 0`; the positivity-free upper half suffices.
      have hle := tail_array_even_max_eventually_le hm hb' hy hl
      have hdist : ∀ ε > 0, ∀ᶠ n in atTop, dist (padRearranged (y n) j) (lam j) < ε := by
        intro ε hε
        filter_upwards [hle (ε / 2) (by linarith), hev] with n hsupn hEq
        have hsupnn : 0 ≤ (⨆ i : Fin (m n), spectralResidual j (y n) i) :=
          (hb' n ⟨0, hm n⟩).trans
            (le_ciSup (Set.finite_range (spectralResidual j (y n))).bddAbove ⟨0, hm n⟩)
        rw [Real.dist_eq, ← hEq, hj0, sub_zero, abs_lt]
        constructor <;> linarith
      exact Metric.tendsto_atTop.mpr fun ε hε => Filter.eventually_atTop.1 (hdist ε hε)
    · -- Positive case: combine both ε-halves of even-`k` max extraction.
      have hpos : 0 < lam j := lt_of_le_of_ne ((hl.2 j).1) (Ne.symm hj0)
      have hsup : ∀ n : ℕ, (0 : ℝ) ≤ ⨆ i, spectralResidual j (y n) i := fun n => by
        have h1 := le_ciSup (Set.finite_range (spectralResidual j (y n))).bddAbove
          ⟨0, hm n⟩
        exact (hb' n ⟨0, hm n⟩).trans h1
      have hdist : ∀ ε > 0, ∀ᶠ n in atTop, dist (padRearranged (y n) j) (lam j) < ε := by
        intro ε hε
        have hd1 : (0 : ℝ) < ε / 2 := by linarith
        have hd2 : (0 : ℝ) < lam j / 4 := by linarith
        have hd3 : ε / 2 < ε := by linarith
        have hd4 : lam j / 4 < lam j := by linarith
        set δ : ℝ := min (ε / 2) (lam j / 4) with hδdef
        have hd : 0 < δ := lt_min hd1 hd2
        have hlt : 2 * δ < lam j := by
          have h5 : δ ≤ lam j / 4 := min_le_right _ _
          linarith
        have hle : δ < ε := lt_of_le_of_lt (min_le_left _ _) hd3
        have h1 := tail_array_even_max_eventually_ge hm hb' hy hl hpos δ hd hlt
        have h2 := tail_array_even_max_eventually_le hm hb' hy hl δ hd
        filter_upwards [h1, h2, hev] with n hn1 hn2 hEq
        have h3 : 0 ≤ (⨆ i, spectralResidual j (y n) i) := hsup n
        rw [Real.dist_eq, ← hEq, abs_lt]
        constructor <;> linarith
      exact Metric.tendsto_atTop.mpr fun ε hε => Filter.eventually_atTop.1 (hdist ε hε)
  -- Promote to all levels by bounded induction.
  have hall : ∀ N : ℕ, ∀ c : ℕ, c ≤ N →
      Tendsto (fun n => padRearranged (y n) c) atTop (𝓝 (lam c)) := by
    intro N
    induction N with
    | zero =>
      intro c hc
      have hc0 : c = 0 := le_antisymm hc (Nat.zero_le c)
      subst hc0
      exact hstep 0 (fun q hq => absurd hq (Nat.not_lt_zero q))
    | succ N ih =>
      intro c hc
      by_cases heq : c = N + 1
      · subst heq
        exact hstep (N + 1) (fun q hq => ih q (by omega))
      · exact ih c (by omega)
  intro j
  exact hall j j (Nat.le_refl j)

/-! ## The signed-spectrum matching theorem -/

/-- **Coefficientwise convergence of the padded decreasing rearrangement of
`|x|`, from even power sums of signed data.**  If `x n : Fin (m n) → ℝ` has
SIGNED entries with `m n → ∞`, and its EVEN power sums (`k ≥ 2`, `Even k`)
converge to those of a nonnegative antitone square-summable profile `lam`, then
every padded decreasingly rearranged entry of `|x n|` converges to `lam j`.

For signed spectra, even power sums of `λ` equal even power sums of `|λ|`, so
this is the matching theorem for the signed spectral data against a nonnegative
Riesz target spectrum. -/
theorem paddedAbsRearranged_tendsto (m : ℕ → ℕ) (x : ∀ n, Fin (m n) → ℝ) (lam : ℕ → ℝ)
    (hm : ∀ n, 0 < m n) (hmtop : Tendsto m atTop atTop)
    (hl : Antitone lam ∧ ∀ j, 0 ≤ lam j ∧ Summable (fun j => lam j ^ 2))
    (hp : ∀ k : ℕ, 2 ≤ k → Even k → Tendsto (fun n => ∑ i : Fin (m n), x n i ^ k) atTop
      (𝓝 (∑' j, lam j ^ k))) :
    ∀ j : ℕ, Tendsto (fun n => padRearranged (fun i => |x n i|) j) atTop (𝓝 (lam j)) := by
  refine paddedEvenRearranged_tendsto m (fun n i => |x n i|) lam hm hmtop
    (fun n i => abs_nonneg (x n i)) hl fun k hk hkev => ?_
  refine Tendsto.congr ?_ (hp k hk hkev)
  intro n
  exact (even_pow_sum_abs_congr (x n) hkev).symm

end Hurst
