import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Helpers for the power-sum peeling matching lemma

This file collects the elementary real-analysis and infinite-sum facts used by
`Hurst/PowerSumMatching.lean`:

* real `k`-th root manipulations (`u ^ (k⁻¹) ≤ v ↔ u ≤ v ^ k`);
* Bernoulli's inequality and the k-th-root limit `Q ^ (k⁻¹) → 1`;
* frequently/eventually transfer lemmas for limits on `ℕ`;
* summability of eventually vanishing sequences and real tsum comparison
  helpers in the current `SummationFilter` API;
* the deterministic tail k-th-root limit: for a decreasing, nonnegative, `ℓ²`
  sequence `lambda`, the tail power sums `T J k = ∑' i, lambda (i + J) ^ k`
  satisfy `(T J k) ^ (1/k) → lambda J`.  This is the analytic heart of the
  peeling argument: the k-th roots of the tail power sums recover the leading
  tail entry, so the full tail of `lambda` is determined by its power sums.
-/

noncomputable section
open Finset Filter Set Metric
open scoped Topology
namespace Hurst

/-! ### Real power lemmas -/

/-- Bernoulli's inequality: for `t ≥ 0`, `(1 + t) ^ k ≥ 1 + k * t`. -/
theorem one_add_pow_ge_add_mul {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    1 + k * t ≤ (1 + t) ^ k := by
  induction k with
  | zero => simpa using (le_refl 1 : (1 : ℝ) ≤ 1)
  | succ k ih =>
    have h1 : (1 + k * t) * (1 + t) ≤ (1 + t) ^ k * (1 + t) :=
      mul_le_mul_of_nonneg_right ih (add_nonneg zero_le_one ht)
    have h2 : 1 + ((k : ℝ) + 1) * t ≤ (1 + k * t) * (1 + t) := by
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith [sq_nonneg t]
    rw [pow_succ, Nat.cast_add, Nat.cast_one]
    calc (1 : ℝ) + ((k : ℝ) + 1) * t ≤ (1 + k * t) * (1 + t) := h2
      _ ≤ (1 + t) ^ k * (1 + t) := h1

/-- For `a ≥ 0` and `k > 0`, `(a ^ k) ^ (k⁻¹) = a`. -/
theorem real_pow_rpow_inv {a : ℝ} (ha : 0 ≤ a) {k : ℕ} (hk : 0 < k) :
    (a ^ k) ^ ((k : ℝ)⁻¹) = a := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ha (k : ℝ) ((k : ℝ)⁻¹),
    mul_inv_cancel₀ (a := (k : ℝ)) (Nat.cast_ne_zero.mpr hk.ne'), Real.rpow_one]

/-- The `k`-th root is the inverse of the `k`-th power on nonnegative reals:
`u ^ (k⁻¹) ≤ v ↔ u ≤ v ^ k`. -/
theorem real_rpow_inv_nat_le {k : ℕ} (hk : 0 < k) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    u ^ ((k : ℝ)⁻¹) ≤ v ↔ u ≤ v ^ (k : ℝ) := by
  constructor
  · intro h
    have h1 : (u ^ ((k : ℝ)⁻¹)) ^ ((k : ℝ)) ≤ v ^ ((k : ℝ)) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hu _) h (Nat.cast_nonneg k)
    rw [← Real.rpow_mul hu ((k : ℝ)⁻¹) ((k : ℝ)),
      inv_mul_cancel₀ (a := (k : ℝ)) (Nat.cast_ne_zero.mpr hk.ne'), Real.rpow_one] at h1
    exact h1
  · intro h
    have h1 : u ^ ((k : ℝ)⁻¹) ≤ (v ^ (k : ℝ)) ^ ((k : ℝ)⁻¹) :=
      Real.rpow_le_rpow hu h (inv_nonneg.mpr (Nat.cast_nonneg k))
    rw [← Real.rpow_mul hv (k : ℝ) ((k : ℝ)⁻¹),
      mul_inv_cancel₀ (a := (k : ℝ)) (Nat.cast_ne_zero.mpr hk.ne'), Real.rpow_one] at h1
    exact h1

/-- Strict base monotonicity of natural powers on nonnegative reals. -/
theorem pow_lt_pow_left_real {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
    ∀ n : ℕ, 0 < n → x ^ n < y ^ n := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      simpa using hxy
    · have hy0 : (0 : ℝ) < y := lt_of_le_of_lt hx hxy
      have hmono : x ^ n ≤ y ^ n := pow_le_pow_left₀ hx hxy.le n
      rw [pow_succ, pow_succ]
      calc x ^ n * x ≤ y ^ n * x := mul_le_mul_of_nonneg_right hmono hx
        _ < y ^ n * y := mul_lt_mul_of_pos_left hxy (pow_pos hy0 n)

/-- The k-th-root limit of a constant: `Q ^ (k⁻¹) → 1` for `Q ≥ 1`. -/
theorem tendsto_rpow_inv_nat_nhds_one {Q : ℝ} (hQ : 1 ≤ Q) :
    Tendsto (fun k : ℕ => Q ^ ((k : ℝ)⁻¹)) atTop (𝓝 1) := by
  have hQ0 : (0 : ℝ) ≤ Q := le_trans zero_le_one hQ
  have hone : ∀ k : ℕ, 1 ≤ Q ^ ((k : ℝ)⁻¹) := by
    intro k
    have hle : (1 : ℝ) ^ ((k : ℝ)⁻¹) ≤ Q ^ ((k : ℝ)⁻¹) :=
      Real.rpow_le_rpow zero_le_one hQ (inv_nonneg.mpr (Nat.cast_nonneg k))
    rwa [Real.one_rpow] at hle
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  have hε2 : (0 : ℝ) < ε / 2 := div_pos hε two_pos
  obtain ⟨K, hKpos, hK⟩ : ∃ K : ℕ, 0 < K ∧ ∀ k : ℕ, K ≤ k → Q ≤ (1 + ε / 2) ^ k := by
    refine ⟨Nat.ceil (Q / (ε / 2)) + 1, Nat.succ_pos _, fun k hk => ?_⟩
    have h1 : ((Nat.ceil (Q / (ε / 2)) : ℕ) : ℝ) ≤ (k : ℝ) :=
      Nat.cast_le.mpr (le_trans (Nat.le_succ _) hk)
    have h2 : Q / (ε / 2) ≤ (k : ℝ) := le_trans (Nat.le_ceil _) h1
    have h3 : Q ≤ (k : ℝ) * (ε / 2) := (div_le_iff₀ hε2).mp h2
    calc Q ≤ (k : ℝ) * (ε / 2) := h3
      _ ≤ 1 + (k : ℝ) * (ε / 2) := by linarith
      _ ≤ (1 + ε / 2) ^ k := by linarith [one_add_pow_ge_add_mul hε2.le k]
  refine Filter.eventually_atTop.mpr ⟨K, fun k hk => ?_⟩
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr (lt_of_lt_of_le hKpos hk)
  have hroot : Q ^ ((k : ℝ)⁻¹) ≤ 1 + ε / 2 := by
    refine (real_rpow_inv_nat_le (k := k) (Nat.cast_pos.mp hkpos) hQ0 (by linarith)).mpr ?_
    rw [Real.rpow_natCast]
    exact hK k hk
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hone k))]
  linarith

/-! ### Frequently/eventually transfer lemmas -/

/-- A frequent lower bound on a convergent sequence bounds the limit from
below. -/
theorem tendsto_ge_of_frequently_le {u : ℕ → ℝ} {L c : ℝ}
    (hT : Tendsto u atTop (𝓝 L)) (hf : ∃ᶠ n in atTop, c ≤ u n) : c ≤ L := by
  by_contra hcon
  have hLc : L < c := lt_of_not_ge hcon
  obtain ⟨d, hLd, hdc⟩ := exists_between hLc
  have hev : ∀ᶠ n in atTop, u n < d := by
    refine (Metric.tendsto_nhds.mp hT (d - L) (sub_pos.mpr hLd)).mono fun n hn => ?_
    rw [Real.dist_eq] at hn
    have habs := abs_lt.mp hn
    linarith
  refine absurd hf (Filter.not_frequently.mpr (hev.mono fun n hn hle => ?_))
  exact absurd hle (not_le.mpr (by linarith))

/-- If `u ≤ v` frequently, `u → L` and `v → M`, then `L ≤ M`. -/
theorem tendsto_le_of_frequently_le {u v : ℕ → ℝ} {L M : ℝ}
    (hu : Tendsto u atTop (𝓝 L)) (hv : Tendsto v atTop (𝓝 M))
    (hf : ∃ᶠ n in atTop, u n ≤ v n) : L ≤ M := by
  by_contra hcon
  have hML : M < L := lt_of_not_ge hcon
  obtain ⟨d, hMd, hdL⟩ := exists_between hML
  have hev1 : ∀ᶠ n in atTop, v n < d :=
    (Metric.tendsto_nhds.mp hv (d - M) (sub_pos.mpr hMd)).mono fun n hn => by
      rw [Real.dist_eq] at hn
      have habs := abs_lt.mp hn
      linarith
  have hev2 : ∀ᶠ n in atTop, d < u n :=
    (Metric.tendsto_nhds.mp hu (L - d) (sub_pos.mpr hdL)).mono fun n hn => by
      rw [Real.dist_eq] at hn
      have habs := abs_lt.mp hn
      linarith
  refine absurd hf (Filter.not_frequently.mpr ((hev1.and hev2).mono fun n h => ?_))
  rcases h with ⟨h1, h2⟩
  exact not_le.mpr (by linarith)

/-- An eventually true property holds at some index `≥ n`. -/
theorem eventually_atTop_exists_ge {p : ℕ → Prop} (h : ∀ᶠ k in atTop, p k) (n : ℕ) :
    ∃ k, n ≤ k ∧ p k := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h
  exact ⟨max n N, by omega, hN _ (by omega)⟩

/-! ### Infinite-sum helpers for real sequences -/

/-- A real sequence vanishing from some index on is summable. -/
theorem summable_of_eventually_eq_zero {f : ℕ → ℝ} (h : ∃ N : ℕ, ∀ i, N ≤ i → f i = 0) :
    Summable f := by
  obtain ⟨N, hN⟩ := h
  refine summable_of_hasFiniteSupport ?_
  have hsub : Function.support f ⊆ Set.Iio N := by
    intro i hi
    have hfne : f i ≠ 0 := Function.mem_support.mp hi
    by_contra hlt
    exact hfne (hN i (not_lt.mp (fun hmem => hlt (Set.mem_Iio.mpr hmem))))
  exact Set.Finite.subset (Set.finite_Iio N) hsub

/-- Scaling a summable real sequence by a constant. -/
theorem Summable.const_mul_real {f : ℕ → ℝ} (c : ℝ) (hf : Summable f) :
    Summable (fun i : ℕ => c * f i) := by
  have h := hf.smul_const c
  have heq : (fun i : ℕ => f i • c) = (fun i : ℕ => c * f i) := by
    funext i; simp [mul_comm]
  rwa [heq] at h

/-- The tsum of a scaled sequence is the scaled tsum. -/
theorem tsum_const_mul_real {f : ℕ → ℝ} (c : ℝ) (hf : Summable f) :
    ∑' i : ℕ, c * f i = c * ∑' i : ℕ, f i := by
  have h2 := hf.hasSum.smul_const c
  have heq : (fun i : ℕ => f i • c) = (fun i : ℕ => c * f i) := by
    funext i; simp [mul_comm]
  rw [heq, smul_eq_mul, mul_comm] at h2
  exact h2.tsum_eq

/-- A nonnegative tsum dominates its first term. -/
theorem tsum_ge_term_of_nonneg {g : ℕ → ℝ} (hg : Summable g) (hnn : ∀ i, 0 ≤ g i) :
    g 0 ≤ ∑' i : ℕ, g i := by
  have h1 := hg.sum_add_tsum_nat_add 1
  rw [Finset.sum_range_one] at h1
  have h2 : 0 ≤ ∑' i : ℕ, g (i + 1) := tsum_nonneg fun i => hnn (i + 1)
  linarith

/-- Pointwise domination by a constant multiple transfers to tsums. -/
theorem tsum_le_const_mul_tsum {f g : ℕ → ℝ} (c : ℝ) (hf : Summable f) (hg : Summable g)
    (h : ∀ i, f i ≤ c * g i) : ∑' i : ℕ, f i ≤ c * ∑' i : ℕ, g i := by
  have h2 : HasSum (fun i : ℕ => c * g i) (c * ∑' i : ℕ, g i) := by
    have h3 := hg.hasSum.smul_const c
    have heq : (fun i : ℕ => g i • c) = (fun i : ℕ => c * g i) := by
      funext i; simp [mul_comm]
    rw [heq, smul_eq_mul, mul_comm] at h3
    exact h3
  exact hasSum_le h hf.hasSum h2

/-! ### The tail k-th-root limit -/

/-- The tail power sums of a decreasing nonnegative `ℓ²` sequence are summable
in the index, for every power `k ≥ 2`. -/
theorem tailPowerSum_summable {lambda : ℕ → ℝ} (hanti : Antitone lambda)
    (hnn : ∀ j, 0 ≤ lambda j) (hsq : Summable (fun j : ℕ => lambda j ^ 2))
    (J k : ℕ) (hk : 2 ≤ k) :
    Summable (fun i : ℕ => lambda (i + J) ^ k) := by
  have hsqJ : Summable (fun i : ℕ => lambda (i + J) ^ 2) :=
    Summable.of_nonneg_of_le (fun i => sq_nonneg _)
      (fun i => pow_le_pow_left₀ (hnn _) (hanti (by omega)) 2) hsq
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hcmp : ∀ i : ℕ, lambda (i + J) ^ (m + 2) ≤ lambda J ^ m * lambda (i + J) ^ 2 := by
    intro i
    have h1 : lambda (i + J) ≤ lambda J := hanti (by omega)
    have h2 : 0 ≤ lambda (i + J) := hnn _
    calc lambda (i + J) ^ (m + 2) = lambda (i + J) ^ m * lambda (i + J) ^ 2 := by
          rw [pow_add]
      _ ≤ lambda J ^ m * lambda (i + J) ^ 2 := by
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h2 h1 m) (pow_nonneg h2 2)
  refine Summable.of_nonneg_of_le (fun i => pow_nonneg (hnn (i + J)) (m + 2)) hcmp ?_
  have hfun : (fun i : ℕ => lambda J ^ m * lambda (i + J) ^ 2)
      = (fun i : ℕ => lambda (i + J) ^ 2 • lambda J ^ m) := by
    funext i; simp [smul_eq_mul, mul_comm]
  rw [hfun]
  exact hsqJ.smul_const (lambda J ^ m)

/-- The power sums of a decreasing nonnegative `ℓ²` sequence are summable, for
every power `k ≥ 2`. -/
theorem powerSum_summable {lambda : ℕ → ℝ} (hanti : Antitone lambda)
    (hnn : ∀ j, 0 ≤ lambda j) (hsq : Summable (fun j : ℕ => lambda j ^ 2))
    (k : ℕ) (hk : 2 ≤ k) :
    Summable (fun j : ℕ => lambda j ^ k) :=
  tailPowerSum_summable hanti hnn hsq 0 k hk

/-- Tail splitting identity: head plus shifted tail equals the full power sum. -/
theorem tailPowerSum_split {lambda : ℕ → ℝ} (hanti : Antitone lambda)
    (hnn : ∀ j, 0 ≤ lambda j) (hsq : Summable (fun j : ℕ => lambda j ^ 2))
    (J k : ℕ) (hk : 2 ≤ k) :
    (∑ i ∈ Finset.range J, lambda i ^ k) + ∑' i : ℕ, lambda (i + J) ^ k
      = ∑' i : ℕ, lambda i ^ k :=
  (powerSum_summable hanti hnn hsq k hk).sum_add_tsum_nat_add J

set_option maxHeartbeats 3000000 in
/-- **The tail k-th-root limit.**  For a decreasing, nonnegative, `ℓ²` sequence
`lambda`, the `k`-th root of the tail power sums converges to the leading tail
entry: `(∑' i, lambda (i + J) ^ k) ^ (1/k) → lambda J`. -/
theorem tailPowerSum_root_tendsto {lambda : ℕ → ℝ} (hanti : Antitone lambda)
    (hnn : ∀ j, 0 ≤ lambda j) (hsq : Summable (fun j : ℕ => lambda j ^ 2)) (J : ℕ) :
    Tendsto (fun k : ℕ => (∑' i : ℕ, lambda (i + J) ^ k) ^ ((k : ℝ)⁻¹))
      atTop (𝓝 (lambda J)) := by
  by_cases ha : lambda J = 0
  · -- Zero case: every tail entry vanishes, the roots are eventually `0`.
    have hall : ∀ i : ℕ, lambda (i + J) = 0 := by
      intro i
      have h1 : lambda (i + J) ≤ lambda J := hanti (by omega)
      have h2 : 0 ≤ lambda (i + J) := hnn _
      linarith
    have hT0 : ∀ k : ℕ, 2 ≤ k → (∑' i : ℕ, lambda (i + J) ^ k) = 0 := by
      intro k hk
      have heq : (∑' i : ℕ, lambda (i + J) ^ k) = ∑' i : ℕ, (0 : ℝ) := by
        refine tsum_congr fun i => ?_
        rw [hall i]
        exact zero_pow (show k ≠ 0 by linarith)
      rw [heq, tsum_zero]
    have hconst : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (lambda J)) := by
      rw [ha]
      exact tendsto_const_nhds
    have hev : ∀ᶠ k : ℕ in atTop,
        (0 : ℝ) = (∑' i : ℕ, lambda (i + J) ^ k) ^ ((k : ℝ)⁻¹) := by
      refine (Filter.eventually_ge_atTop 2).mono fun k hk => ?_
      rw [hT0 k hk]
      exact (Real.zero_rpow
        (inv_ne_zero (Nat.cast_ne_zero.mpr (show (0 : ℕ) < k by linarith).ne'))).symm
    exact Tendsto.congr' hev hconst
  · -- Positive case.
    have ha0 : 0 < lambda J := lt_of_le_of_ne (hnn J) (Ne.symm ha)
    have ha2 : (0 : ℝ) ≤ lambda J / 2 := div_nonneg ha0.le two_pos.le
    have ha2pos : (0 : ℝ) < lambda J / 2 := div_pos ha0 two_pos
    have hsqJ : Summable (fun i : ℕ => lambda (i + J) ^ 2) :=
      Summable.of_nonneg_of_le (fun i => sq_nonneg _)
        (fun i => pow_le_pow_left₀ (hnn _) (hanti (by omega)) 2) hsq
    have hsumT : ∀ k : ℕ, 2 ≤ k → Summable (fun i : ℕ => lambda (i + J) ^ k) :=
      tailPowerSum_summable hanti hnn hsq J
    have hTk : ∀ k : ℕ, (0 : ℝ) ≤ ∑' i : ℕ, lambda (i + J) ^ k := fun k =>
      tsum_nonneg fun i => pow_nonneg (hnn (i + J)) k
    -- lambda → 0
    have hlam0 : Tendsto (fun j : ℕ => lambda j) atTop (𝓝 (0 : ℝ)) := by
      have h2 := hsq.tendsto_atTop_zero
      have h3 : Tendsto (fun j : ℕ => Real.sqrt (lambda j ^ 2)) atTop (𝓝 (Real.sqrt 0)) :=
        (Real.continuous_sqrt.continuousAt.tendsto).comp h2
      have h4 : (fun j : ℕ => Real.sqrt (lambda j ^ 2)) = (fun j : ℕ => lambda j) := by
        funext j; rw [Real.sqrt_sq (hnn j)]
      rw [h4, Real.sqrt_zero] at h3
      exact h3
    -- threshold index: beyond it all values are below lambda J / 2
    obtain ⟨N, hN⟩ : ∃ N, ∀ j, N ≤ j → lambda j < lambda J / 2 := by
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
        (Metric.tendsto_nhds.mp hlam0 (lambda J / 2) ha2pos)
      refine ⟨N, fun j hj => ?_⟩
      have hd := hN j hj
      rw [Real.dist_eq] at hd
      have habs := abs_lt.mp hd
      have := hnn j
      linarith
    -- lower bound on the tail sums
    have hlower : ∀ k : ℕ, 2 ≤ k → lambda J ^ k ≤ ∑' i : ℕ, lambda (i + J) ^ k := by
      intro k hk
      have h1 := tsum_ge_term_of_nonneg (hsumT k hk) (fun i => pow_nonneg (hnn (i + J)) k)
      rwa [Nat.zero_add] at h1
    -- upper bound: eventually the tail sum is below (lambda J + epsilon) ^ k
    have hupper : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
        2 ≤ k ∧ (∑' i : ℕ, lambda (i + J) ^ k) ≤ (lambda J + ε) ^ k := by
      intro ε hε
      -- abstract cut index N₀ above both J and the threshold index N
      obtain ⟨N₀, hJN, hNN⟩ : ∃ N₀ : ℕ, J ≤ N₀ ∧ N ≤ N₀ :=
        ⟨max J N, le_max_left _ _, le_max_right _ _⟩
      -- the uniform bound T k ≤ C * lambda J ^ k for k ≥ 2
      have hbound : ∀ k : ℕ, 2 ≤ k →
          ∑' i : ℕ, lambda (i + J) ^ k
            ≤ (((N₀ : ℕ) : ℝ) + (∑' i : ℕ, lambda (i + J) ^ 2) / lambda J ^ 2)
              * lambda J ^ k := by
        intro k hk
        obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
        have hJNi : ∀ i : ℕ, i + J ≤ i + N₀ := fun i => Nat.add_le_add_left hJN i
        have hsplit := (hsumT (m + 2) (by omega)).sum_add_tsum_nat_add (N₀ - J)
        have hidx : ∀ i : ℕ, lambda ((i + (N₀ - J)) + J) ^ (m + 2)
            = lambda (i + N₀) ^ (m + 2) := fun i =>
          congrArg (fun z => z ^ (m + 2)) (by
            rw [Nat.add_assoc, Nat.sub_add_cancel hJN])
        have hsplit' : ∑ i ∈ Finset.range (N₀ - J), lambda (i + J) ^ (m + 2)
            + ∑' i : ℕ, lambda (i + N₀) ^ (m + 2)
              = ∑' i : ℕ, lambda (i + J) ^ (m + 2) := by
          rw [← hsplit, tsum_congr hidx]
        -- head part: at most N₀ * a ^ (m + 2)
        have hrange : ∑ i ∈ Finset.range (N₀ - J), lambda (i + J) ^ (m + 2)
            ≤ ((N₀ : ℕ) : ℝ) * lambda J ^ (m + 2) := by
          have h1 : ∑ i ∈ Finset.range (N₀ - J), lambda (i + J) ^ (m + 2)
              ≤ (Finset.range (N₀ - J)).card • (lambda J ^ (m + 2) : ℝ) :=
            Finset.sum_le_card_nsmul _ _ (lambda J ^ (m + 2)) (fun i _ =>
              pow_le_pow_left₀ (hnn _) (hanti (Nat.le_add_left J i)) _)
          rw [Finset.card_range, nsmul_eq_mul] at h1
          calc ∑ i ∈ Finset.range (N₀ - J), lambda (i + J) ^ (m + 2) ≤ _ := h1
            _ ≤ ((N₀ : ℕ) : ℝ) * lambda J ^ (m + 2) :=
                mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega))
                  (pow_nonneg (le_of_lt ha0) _)
        -- tail part: at most (a/2) ^ m * (total tail square sum)
        have htail : ∑' i : ℕ, lambda (i + N₀) ^ (m + 2)
            ≤ (lambda J / 2) ^ m * ∑' i : ℕ, lambda (i + J) ^ 2 := by
          have hsqN₀ : Summable (fun i : ℕ => lambda (i + N₀) ^ 2) :=
            Summable.of_nonneg_of_le (fun i => sq_nonneg _)
              (fun i => pow_le_pow_left₀ (hnn _) (hanti (hJNi i)) 2) hsqJ
          have hsumN₀ : Summable (fun i : ℕ => lambda (i + N₀) ^ (m + 2)) := by
            refine Summable.of_nonneg_of_le (fun i => pow_nonneg (hnn (i + N₀)) (m + 2))
              (fun i => ?_) (Summable.const_mul_real (lambda J ^ m) hsqN₀)
            have hle : lambda (i + N₀) ≤ lambda J :=
              hanti (hJN.trans (Nat.le_add_left N₀ i))
            rw [pow_add]
            exact mul_le_mul_of_nonneg_right
              (pow_le_pow_left₀ (hnn (i + N₀)) hle m) (pow_nonneg (hnn (i + N₀)) 2)
          have hcmp : ∀ i : ℕ, lambda (i + N₀) ^ (m + 2)
              ≤ (lambda J / 2) ^ m * lambda (i + N₀) ^ 2 := by
            intro i
            have hlt : lambda (i + N₀) < lambda J / 2 :=
              hN _ (le_trans hNN (Nat.le_add_left N₀ i))
            rw [pow_add]
            exact mul_le_mul_of_nonneg_right
              (pow_le_pow_left₀ (hnn (i + N₀)) hlt.le m) (pow_nonneg (hnn (i + N₀)) 2)
          have htailsum : ∑' i : ℕ, lambda (i + N₀) ^ 2
              ≤ ∑' i : ℕ, lambda (i + J) ^ 2 := by
            have hle : ∀ i : ℕ, lambda (i + N₀) ^ 2 ≤ lambda (i + J) ^ 2 :=
              fun i => pow_le_pow_left₀ (hnn _) (hanti (hJNi i)) 2
            have h := tsum_le_const_mul_tsum 1 hsqN₀ hsqJ (fun i => by
              rw [one_mul]; exact hle i)
            rwa [one_mul] at h
          calc ∑' i : ℕ, lambda (i + N₀) ^ (m + 2)
              ≤ (lambda J / 2) ^ m * ∑' i : ℕ, lambda (i + N₀) ^ 2 :=
                tsum_le_const_mul_tsum ((lambda J / 2) ^ m) hsumN₀ hsqN₀ hcmp
            _ ≤ (lambda J / 2) ^ m * ∑' i : ℕ, lambda (i + J) ^ 2 :=
                mul_le_mul_of_nonneg_left htailsum (pow_nonneg ha2 m)
        -- combine
        have hcomb : (lambda J / 2) ^ m * ∑' i : ℕ, lambda (i + J) ^ 2
            ≤ lambda J ^ (m + 2) * ((∑' i : ℕ, lambda (i + J) ^ 2) / lambda J ^ 2) := by
          have h1 : (lambda J / 2) ^ m ≤ lambda J ^ m :=
            pow_le_pow_left₀ ha2
              (div_le_self (le_of_lt ha0) (by norm_num : (1 : ℝ) ≤ 2)) m
          have h2 : lambda J ^ (m + 2) = lambda J ^ m * lambda J ^ 2 := by rw [pow_add]
          have h4 : lambda J ^ m * (∑' i : ℕ, lambda (i + J) ^ 2)
              = lambda J ^ m * lambda J ^ 2
                * ((∑' i : ℕ, lambda (i + J) ^ 2) / lambda J ^ 2) := by
            field_simp
          calc (lambda J / 2) ^ m * ∑' i : ℕ, lambda (i + J) ^ 2
              ≤ lambda J ^ m * ∑' i : ℕ, lambda (i + J) ^ 2 :=
                mul_le_mul_of_nonneg_right h1
                  (tsum_nonneg fun i => sq_nonneg (lambda (i + J)))
            _ = lambda J ^ m * lambda J ^ 2
                * ((∑' i : ℕ, lambda (i + J) ^ 2) / lambda J ^ 2) := h4
            _ = lambda J ^ (m + 2)
                * ((∑' i : ℕ, lambda (i + J) ^ 2) / lambda J ^ 2) := by rw [h2]
        have hC : (((N₀ : ℕ) : ℝ)
              + (∑' i : ℕ, lambda (i + J) ^ 2) / lambda J ^ 2)
              * lambda J ^ (m + 2)
            = ((N₀ : ℕ) : ℝ) * lambda J ^ (m + 2)
              + lambda J ^ (m + 2)
                * ((∑' i : ℕ, lambda (i + J) ^ 2) / lambda J ^ 2) := by ring
        linarith
      -- eventual C ≤ (1 + ε/a)^k
      have ht : 0 < ε / lambda J := div_pos hε ha0
      have hexact : lambda J * (1 + ε / lambda J) = lambda J + ε := by field_simp
      obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
          (((N₀ : ℕ) : ℝ) + (∑' i : ℕ, lambda (i + J) ^ 2) / lambda J ^ 2)
            ≤ (1 + ε / lambda J) ^ k := by
        refine ⟨Nat.ceil ((((N₀ : ℕ) : ℝ)
            + (∑' i : ℕ, lambda (i + J) ^ 2) / lambda J ^ 2) / (ε / lambda J)) + 1,
          fun k hk => ?_⟩
        have h1 : (((N₀ : ℕ) : ℝ)
              + (∑' i : ℕ, lambda (i + J) ^ 2) / lambda J ^ 2)
            ≤ (k : ℝ) * (ε / lambda J) := by
          have h2 : ((((N₀ : ℕ) : ℝ)
                + (∑' i : ℕ, lambda (i + J) ^ 2) / lambda J ^ 2) / (ε / lambda J))
              ≤ (Nat.ceil ((((N₀ : ℕ) : ℝ)
                  + (∑' i : ℕ, lambda (i + J) ^ 2) / lambda J ^ 2) / (ε / lambda J)) : ℕ) :=
            Nat.le_ceil _
          have h3 : ((Nat.ceil ((((N₀ : ℕ) : ℝ)
                    + (∑' i : ℕ, lambda (i + J) ^ 2) / lambda J ^ 2)
                  / (ε / lambda J)) : ℕ) : ℝ) ≤ (k : ℝ) :=
            Nat.cast_le.mpr (le_trans (Nat.le_succ _) hk)
          have h4 : ((((N₀ : ℕ) : ℝ)
                + (∑' i : ℕ, lambda (i + J) ^ 2) / lambda J ^ 2) / (ε / lambda J))
              ≤ (k : ℝ) := le_trans h2 h3
          linarith [(div_le_iff₀ ht).mp h4]
        calc (((N₀ : ℕ) : ℝ)
              + (∑' i : ℕ, lambda (i + J) ^ 2) / lambda J ^ 2)
            ≤ (k : ℝ) * (ε / lambda J) := h1
          _ ≤ 1 + (k : ℝ) * (ε / lambda J) := by linarith
          _ ≤ (1 + ε / lambda J) ^ k := by linarith [one_add_pow_ge_add_mul ht.le k]
      refine Filter.eventually_atTop.mpr ⟨max K 2, fun k hk => ?_⟩
      have hk2 : 2 ≤ k := le_trans (le_max_right _ _) hk
      refine ⟨hk2, ?_⟩
      have hKk := hK k (le_trans (le_max_left _ _) hk)
      have hbd := hbound k hk2
      have hpos : (0 : ℝ) ≤ lambda J ^ k := pow_nonneg (le_of_lt ha0) k
      calc ∑' i : ℕ, lambda (i + J) ^ k
          ≤ (((N₀ : ℕ) : ℝ)
              + (∑' i : ℕ, lambda (i + J) ^ 2) / lambda J ^ 2) * lambda J ^ k := hbd
        _ ≤ (1 + ε / lambda J) ^ k * lambda J ^ k :=
            mul_le_mul_of_nonneg_right hKk hpos
        _ = (lambda J * (1 + ε / lambda J)) ^ k := by
            rw [mul_pow]; ring
        _ = (lambda J + ε) ^ k := by rw [hexact]
    -- squeeze the k-th roots
    refine Metric.tendsto_nhds.mpr fun δ hδ => ?_
    refine (hupper (δ / 2) (div_pos hδ two_pos)).mono fun k hk => ?_
    obtain ⟨hk2, hkup⟩ := hk
    have hlo : lambda J ≤ (∑' i : ℕ, lambda (i + J) ^ k) ^ ((k : ℝ)⁻¹) := by
      have h1 : lambda J ^ k ≤ ∑' i : ℕ, lambda (i + J) ^ k := hlower k hk2
      have h2 : (lambda J ^ k) ^ ((k : ℝ)⁻¹)
          ≤ (∑' i : ℕ, lambda (i + J) ^ k) ^ ((k : ℝ)⁻¹) :=
        Real.rpow_le_rpow (pow_nonneg (le_of_lt ha0) k) h1
          (inv_nonneg.mpr (Nat.cast_nonneg k))
      rwa [real_pow_rpow_inv (le_of_lt ha0) (by linarith)] at h2
    have hup : (∑' i : ℕ, lambda (i + J) ^ k) ^ ((k : ℝ)⁻¹) ≤ lambda J + δ / 2 := by
      have hiff : (∑' i : ℕ, lambda (i + J) ^ k) ^ ((k : ℝ)⁻¹) ≤ lambda J + δ / 2
          ↔ (∑' i : ℕ, lambda (i + J) ^ k) ≤ (lambda J + δ / 2) ^ (k : ℝ) :=
        real_rpow_inv_nat_le (k := k) (by linarith) (hTk k) (by linarith)
      refine hiff.mpr ?_
      rw [Real.rpow_natCast]
      exact hkup
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hlo)]
    linarith

end Hurst
