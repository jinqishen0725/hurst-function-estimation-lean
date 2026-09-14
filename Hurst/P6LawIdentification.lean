import Hurst.P4GaussianSeriesLaw
import Hurst.ExternalSecondChaosLimit
import Mathlib.Probability.Independence.CharacteristicFunction

/-!
# P6: Law identification support for the constructed second-chaos law

Support for file 23, steps E1-E3, on the *constructed* probability space
`gaussianSeqMeasure` of `Hurst.P4GaussianSeriesLaw` (Ω = ℕ → ℝ, coordinates
`gaussianSeqVar j x = x j` iid standard Gaussian, `Q` the `L²` limit).

* (E2, moments) Raw even moments of the standard Gaussian via the Stein
  identity `polynomialGaussianIntegral_X_mul`, giving the centered-square
  moments `E[(Z²-1)²] = 2`, `E[(Z²-1)³] = 8`, `E[(Z²-1)⁴] = 60`
  (`gaussianReal_centeredSquare_*`), and the finite-sum fourth moment
  `E[S_K⁴] = 12(∑λ²)² + 48∑λ⁴` (`gaussSeq_finset_pow_four`; file 23 E1
  formula with the classical coefficient 12).  The L⁴ tail bound follows.
* (E1, nondegeneracy) If the `L²` limit `Q` is almost surely constant then
  every `λ_j = 0` (`gaussSeriesLimit_ae_const_forces_zero`); equivalently
  `λ ≠ 0` forces `Q` nondegenerate.
* (E3, characteristic function) The characteristic function of the finite
  partial sums factors over the independent coordinates
  (`charFun_gaussPartial`); the single-variable factor is the pushforward
  characteristic function of the centered square.  The closed-form
  `(1 - 2itλ)^(-1/2)` expression would require the complex Gaussian
  integral and is reported as a gap.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Hurst

/-! ### Raw moments of the standard Gaussian (Stein recursion) -/

/-- Stein recursion for raw moments of `gaussianReal 0 1`. -/
theorem gaussianReal_integral_X_pow_succ_succ (k : ℕ) :
    (∫ x : ℝ, x ^ (k + 2) ∂gaussianReal 0 1)
      = (k + 1 : ℝ) * ∫ x : ℝ, x ^ k ∂gaussianReal 0 1 := by
  have hA : (∫ x : ℝ, x ^ (k + 2) ∂gaussianReal 0 1)
      = (Real.sqrt (2 * Real.pi))⁻¹ * polynomialGaussianIntegral
          (Polynomial.X ^ (k + 2)) := by
    rw [standardGaussian_weight_integral]
    congr 1
    congr 1
    funext x
    simp
  have hB : (∫ x : ℝ, x ^ k ∂gaussianReal 0 1)
      = (Real.sqrt (2 * Real.pi))⁻¹ * polynomialGaussianIntegral
          (Polynomial.X ^ k) := by
    rw [standardGaussian_weight_integral]
    congr 1
    congr 1
    funext x
    simp
  have hstep : polynomialGaussianIntegral (Polynomial.X ^ (k + 2))
      = polynomialGaussianIntegral (Polynomial.X * Polynomial.X ^ (k + 1)) := by
    congr 1
    rw [pow_succ']
  rw [hA, hstep, polynomialGaussianIntegral_X_mul]
  have hder : (Polynomial.X ^ (k + 1)).derivative
      = Polynomial.C ((k + 1 : ℕ) : ℝ) * Polynomial.X ^ k := by
    rw [Polynomial.derivative_X_pow, Nat.add_sub_cancel]
  rw [hder, polynomialGaussianIntegral_C_mul, hB]
  push_cast
  ring

theorem gaussianReal_integral_X_pow_zero :
    (∫ x : ℝ, x ^ 0 ∂gaussianReal 0 1) = 1 := by
  simp

theorem gaussianReal_integral_X_sq :
    (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1) = 1 := by
  have h := gaussianReal_integral_X_pow_succ_succ 0
  rw [gaussianReal_integral_X_pow_zero] at h
  simpa using h

theorem gaussianReal_integral_X_pow_four :
    (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1) = 3 := by
  have h := gaussianReal_integral_X_pow_succ_succ 2
  rw [gaussianReal_integral_X_sq] at h
  norm_num at h
  exact h

theorem gaussianReal_integral_X_pow_six :
    (∫ x : ℝ, x ^ 6 ∂gaussianReal 0 1) = 15 := by
  have h := gaussianReal_integral_X_pow_succ_succ 4
  rw [gaussianReal_integral_X_pow_four] at h
  norm_num at h
  exact h

theorem gaussianReal_integral_X_pow_eight :
    (∫ x : ℝ, x ^ 8 ∂gaussianReal 0 1) = 105 := by
  have h := gaussianReal_integral_X_pow_succ_succ 6
  rw [gaussianReal_integral_X_pow_six] at h
  norm_num at h
  exact h

/-- Integrability of bare monomials under `gaussianReal 0 1`. -/
theorem gaussianReal_integrable_pow (k : ℕ) :
    Integrable (fun z : ℝ => z ^ k) (gaussianReal 0 1) := by
  have h := standardGaussian_polynomial_integrable (Polynomial.X ^ k)
  refine Integrable.congr h (Eventually.of_forall fun z => ?_)
  simp [Polynomial.eval_pow, Polynomial.eval_X]

/-- Integrability of constant multiples of monomials under
`gaussianReal 0 1`. -/
theorem gaussianReal_integrable_const_mul_pow (a : ℝ) (k : ℕ) :
    Integrable (fun z : ℝ => a * z ^ k) (gaussianReal 0 1) := by
  have h := standardGaussian_polynomial_integrable
    (Polynomial.C a * Polynomial.X ^ k)
  refine Integrable.congr h (Eventually.of_forall fun z => ?_)
  simp [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]

/-- Transport integrability across a pointwise equality. -/
theorem gaussianReal_integrable_congr {f g : ℝ → ℝ}
    (h : Integrable f (gaussianReal 0 1)) (hfg : ∀ z, f z = g z) :
    Integrable g (gaussianReal 0 1) :=
  h.congr (Eventually.of_forall fun z => hfg z)

/-! ### Centered-square moments (file 23 E1 data: 2, 8, 60) -/

theorem gaussianReal_integrable_one :
    Integrable (fun _z : ℝ => (1:ℝ)) (gaussianReal 0 1) := integrable_const 1

theorem gaussianReal_integrable_quad :
    Integrable (fun z : ℝ => z ^ 4 - 2 * z ^ 2) (gaussianReal 0 1) :=
  gaussianReal_integrable_congr
    ((gaussianReal_integrable_pow 4).sub (gaussianReal_integrable_const_mul_pow 2 2))
    (fun z => by simp [Pi.sub_apply])

theorem gaussianReal_integrable_cubA :
    Integrable (fun z : ℝ => z ^ 6 - 3 * z ^ 4) (gaussianReal 0 1) :=
  gaussianReal_integrable_congr
    ((gaussianReal_integrable_pow 6).sub (gaussianReal_integrable_const_mul_pow 3 4))
    (fun z => by simp [Pi.sub_apply])

theorem gaussianReal_integrable_cubB :
    Integrable (fun z : ℝ => z ^ 6 - 3 * z ^ 4 + 3 * z ^ 2) (gaussianReal 0 1) :=
  gaussianReal_integrable_congr
    (gaussianReal_integrable_cubA.add (gaussianReal_integrable_const_mul_pow 3 2))
    (fun z => by simp [Pi.add_apply])

theorem gaussianReal_integrable_quartA :
    Integrable (fun z : ℝ => z ^ 8 - 4 * z ^ 6) (gaussianReal 0 1) :=
  gaussianReal_integrable_congr
    ((gaussianReal_integrable_pow 8).sub (gaussianReal_integrable_const_mul_pow 4 6))
    (fun z => by simp [Pi.sub_apply])

theorem gaussianReal_integrable_quartB :
    Integrable (fun z : ℝ => z ^ 8 - 4 * z ^ 6 + 6 * z ^ 4) (gaussianReal 0 1) :=
  gaussianReal_integrable_congr
    (gaussianReal_integrable_quartA.add (gaussianReal_integrable_const_mul_pow 6 4))
    (fun z => by simp [Pi.add_apply])

theorem gaussianReal_integrable_quartC :
    Integrable (fun z : ℝ => z ^ 8 - 4 * z ^ 6 + 6 * z ^ 4 - 4 * z ^ 2) (gaussianReal 0 1) :=
  gaussianReal_integrable_congr
    (gaussianReal_integrable_quartB.sub (gaussianReal_integrable_const_mul_pow 4 2))
    (fun z => by simp [Pi.sub_apply])

theorem gaussianReal_centeredSquare_sq :
    (∫ z : ℝ, (z ^ 2 - 1) ^ 2 ∂gaussianReal 0 1) = 2 := by
  have hexp : (fun z : ℝ => (z ^ 2 - 1) ^ 2)
      = fun z : ℝ => z ^ 4 - 2 * z ^ 2 + 1 := by
    funext z; ring
  rw [hexp, integral_add gaussianReal_integrable_quad gaussianReal_integrable_one,
    integral_sub (gaussianReal_integrable_pow 4)
      (gaussianReal_integrable_const_mul_pow 2 2)]
  simp only [integral_const_mul]
  rw [gaussianReal_integral_X_pow_four, gaussianReal_integral_X_sq]
  norm_num

theorem gaussianReal_centeredSquare_pow_three :
    (∫ z : ℝ, (z ^ 2 - 1) ^ 3 ∂gaussianReal 0 1) = 8 := by
  have hexp : (fun z : ℝ => (z ^ 2 - 1) ^ 3)
      = fun z : ℝ => z ^ 6 - 3 * z ^ 4 + 3 * z ^ 2 - 1 := by
    funext z; ring
  rw [hexp, integral_sub gaussianReal_integrable_cubB gaussianReal_integrable_one,
    integral_add gaussianReal_integrable_cubA
      (gaussianReal_integrable_const_mul_pow 3 2),
    integral_sub (gaussianReal_integrable_pow 6)
      (gaussianReal_integrable_const_mul_pow 3 4)]
  simp only [integral_const_mul]
  rw [gaussianReal_integral_X_pow_six, gaussianReal_integral_X_pow_four,
    gaussianReal_integral_X_sq]
  norm_num

theorem gaussianReal_centeredSquare_pow_four :
    (∫ z : ℝ, (z ^ 2 - 1) ^ 4 ∂gaussianReal 0 1) = 60 := by
  have hexp : (fun z : ℝ => (z ^ 2 - 1) ^ 4)
      = fun z : ℝ => z ^ 8 - 4 * z ^ 6 + 6 * z ^ 4 - 4 * z ^ 2 + 1 := by
    funext z; ring
  rw [hexp, integral_add gaussianReal_integrable_quartC
      gaussianReal_integrable_one,
    integral_sub gaussianReal_integrable_quartB
      (gaussianReal_integrable_const_mul_pow 4 2),
    integral_add gaussianReal_integrable_quartA
      (gaussianReal_integrable_const_mul_pow 6 4),
    integral_sub (gaussianReal_integrable_pow 8)
      (gaussianReal_integrable_const_mul_pow 4 6)]
  simp only [integral_const_mul]
  rw [gaussianReal_integral_X_pow_eight, gaussianReal_integral_X_pow_six,
    gaussianReal_integral_X_pow_four, gaussianReal_integral_X_sq]
  norm_num

/-! ### Per-coordinate moments on the constructed sequence space -/

theorem measurable_finsetSum_of {β : Type*} [MeasurableSpace β] {s : Finset ℕ}
    (F : ℕ → β → ℝ) (hF : ∀ j ∈ s, Measurable (F j)) :
    Measurable (fun x => ∑ j ∈ s, F j x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using measurable_const
  | insert k s hk ih =>
    have key : Measurable (fun x => F k x + ∑ j ∈ s, F j x) :=
      (hF k (Finset.mem_insert_self k s)).add (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))
    simpa [Finset.sum_insert hk] using key

theorem gaussianSeqVar_pow_integrable (j n : ℕ) :
    Integrable (fun x : ℕ → ℝ => (x j) ^ n) gaussianSeqMeasure := by
  have hI : Integrable (fun z : ℝ => z ^ n) (gaussianReal 0 1) :=
    (standardGaussian_polynomial_integrable (Polynomial.X ^ n)).congr
      (Eventually.of_forall fun u => by simp [Polynomial.eval_pow, Polynomial.eval_X])
  have hL : MemLp (fun z : ℝ => z ^ n) 1 (gaussianReal 0 1) :=
    memLp_one_iff_integrable.2 hI
  have h2 : MemLp (fun z : ℝ => z ^ n) 1 (gaussianSeqMeasure.map (gaussianSeqVar j)) := by
    rw [gaussianSeqMeasure_map_var j]; exact hL
  have h3 := MemLp.comp_of_map (f := gaussianSeqVar j) (g := fun z : ℝ => z ^ n) h2
    (gaussianSeqVar_measurable j).aemeasurable
  exact (memLp_one_iff_integrable.1 h3).congr (Eventually.of_forall fun x => rfl)

/-- The single coordinate term has fourth moment `60 * lambda j ^ 4`. -/
theorem gaussSeq_term_pow_four (lambda : ℕ → ℝ) (j : ℕ) :
    (∫ x : ℕ → ℝ, (lambda j * ((x j) ^ 2 - 1)) ^ 4 ∂gaussianSeqMeasure)
      = 60 * lambda j ^ 4 := by
  have hlaw : HasLaw (gaussianSeqVar j) (gaussianReal 0 1) gaussianSeqMeasure :=
    ⟨(gaussianSeqVar_measurable j).aemeasurable, gaussianSeqMeasure_map_var j⟩
  have hf : AEStronglyMeasurable
      (fun z : ℝ => (lambda j * (z ^ 2 - 1)) ^ 4) (gaussianReal 0 1) :=
    (show Continuous fun z : ℝ => (lambda j * (z ^ 2 - 1)) ^ 4 by fun_prop).aestronglyMeasurable
  have hval : (∫ x : ℕ → ℝ, (lambda j * (gaussianSeqVar j x ^ 2 - 1)) ^ 4 ∂gaussianSeqMeasure)
      = ∫ z : ℝ, (lambda j * (z ^ 2 - 1)) ^ 4 ∂gaussianReal 0 1 := hlaw.integral_comp hf
  rw [show (∫ x : ℕ → ℝ, (lambda j * ((x j) ^ 2 - 1)) ^ 4 ∂gaussianSeqMeasure)
      = ∫ x : ℕ → ℝ, (lambda j * (gaussianSeqVar j x ^ 2 - 1)) ^ 4 ∂gaussianSeqMeasure from rfl,
    hval,
    show (fun z : ℝ => (lambda j * (z ^ 2 - 1)) ^ 4)
      = fun z : ℝ => lambda j ^ 4 * (z ^ 2 - 1) ^ 4 by
      funext z; ring, integral_const_mul, gaussianReal_centeredSquare_pow_four]
  ring

/-- `(a + b)^4 <= 8 * (a^4 + b^4)`. -/
theorem pow4_add_le (a b : ℝ) : (a + b) ^ 4 ≤ 8 * (a ^ 4 + b ^ 4) := by
  have h1 : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
    nlinarith [sq_nonneg (a - b)]
  have h2 : (a ^ 2 + b ^ 2) ^ 2 ≤ 2 * (a ^ 4 + b ^ 4) := by
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2)]
  have h3 : ((a + b) ^ 2) ^ 2 ≤ (2 * (a ^ 2 + b ^ 2)) ^ 2 := by
    nlinarith [h1, sq_nonneg (a + b), sq_nonneg (2 * (a ^ 2 + b ^ 2))]
  calc (a + b) ^ 4 = ((a + b) ^ 2) ^ 2 := by ring
    _ ≤ (2 * (a ^ 2 + b ^ 2)) ^ 2 := h3
    _ = 4 * (a ^ 2 + b ^ 2) ^ 2 := by ring
    _ ≤ 8 * (a ^ 4 + b ^ 4) := by nlinarith [h2]

/-- Pointwise bound used for integrability of fourth powers. -/
theorem pow4_le_eight (z : ℝ) : (z ^ 2 - 1) ^ 4 ≤ 8 * (1 + z ^ 8) := by
  have habs : |z ^ 2 - 1| ≤ z ^ 2 + 1 := by
    rcases abs_cases (z ^ 2 - 1) with h | h
    · linarith
    · linarith [sq_nonneg z]
  have h2 : (z ^ 2 - 1) ^ 4 = |z ^ 2 - 1| ^ 4 := by
    rw [← abs_pow, abs_of_nonneg (by positivity)]
  calc (z ^ 2 - 1) ^ 4 = |z ^ 2 - 1| ^ 4 := h2
    _ ≤ (z ^ 2 + 1) ^ 4 := pow_le_pow_left₀ (abs_nonneg (z ^ 2 - 1)) habs 4
    _ ≤ 8 * ((z ^ 2) ^ 4 + 1 ^ 4) := pow4_add_le (z ^ 2) 1
    _ = 8 * (1 + z ^ 8) := by ring

/-- `L2` membership implies integrability on the sequence space. -/
theorem integrable_of_memLp_seq {f : (ℕ → ℝ) → ℝ}
    (hf : MemLp f 2 gaussianSeqMeasure) : Integrable f gaussianSeqMeasure :=
  memLp_one_iff_integrable.1
    ⟨hf.aestronglyMeasurable, lt_of_le_of_lt
      (eLpNorm_le_eLpNorm_of_exponent_le (μ := gaussianSeqMeasure) (p := 1) (q := 2)
        (by norm_num) hf.aestronglyMeasurable) hf.eLpNorm_lt_top⟩

/-! ### E1: nondegeneracy of the L2 limit -/

/-- If the `L2` limit of the Gaussian second-chaos series is almost surely
constant, then every coefficient vanishes. -/
theorem gaussSeriesLimit_ae_const_forces_zero (lambda : ℕ → ℝ)
    (hlambda : Summable fun j => (lambda j) ^ 2) {Q : (ℕ → ℝ) → ℝ}
    (_hmemK : ∀ K : ℕ, MemLp (fun x => Q x - gaussPartial lambda K x) 2 gaussianSeqMeasure)
    (htail : Tendsto (fun K : ℕ =>
        ∫ x, (Q x - gaussPartial lambda K x) ^ 2 ∂gaussianSeqMeasure) atTop (𝓝 0))
    (hconst : ∃ c : ℝ, Q =ᵐ[gaussianSeqMeasure] fun _ => c) :
    ∀ j, lambda j = 0 := by
  classical
  obtain ⟨c, hc⟩ := hconst
  have hcongr : ∀ K : ℕ,
      (∫ x, (Q x - gaussPartial lambda K x) ^ 2 ∂gaussianSeqMeasure)
        = ∫ x, (c - gaussPartial lambda K x) ^ 2 ∂gaussianSeqMeasure := fun K =>
    by
      refine integral_congr_ae ?_
      filter_upwards [hc] with x hx
      rw [hx]
  have hSint : ∀ K : ℕ, Integrable (gaussPartial lambda K) gaussianSeqMeasure := fun K =>
    integrable_of_memLp_seq (gaussPartial_memLp lambda K)
  have hS2 : ∀ K : ℕ,
      (∫ x, (gaussPartial lambda K x) ^ 2 ∂gaussianSeqMeasure)
        = 2 * ∑ j ∈ Finset.range K, (lambda j) ^ 2 := fun K =>
    gaussianSeq_centeredSquare_finset_L2 lambda (Finset.range K)
  have hmeanS : ∀ K : ℕ, (∫ x, gaussPartial lambda K x ∂gaussianSeqMeasure) = 0 := by
    intro K
    have hfin : ∀ j ∈ Finset.range K,
        Integrable (fun x : ℕ → ℝ => lambda j * ((x j) ^ 2 - 1)) gaussianSeqMeasure :=
      fun j _ => integrable_of_memLp_seq
        ((iid_standardGaussian_centeredSquare_memLp gaussianSeqMeasure gaussianSeqVar
          (fun j => (gaussianSeqVar_measurable j).aemeasurable)
          gaussianSeqMeasure_map_var j).const_mul (lambda j))
    rw [show (∫ x, gaussPartial lambda K x ∂gaussianSeqMeasure)
        = ∫ x, ∑ j ∈ Finset.range K, lambda j * ((x j) ^ 2 - 1) ∂gaussianSeqMeasure from rfl,
      integral_finsetSum (Finset.range K) hfin]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [integral_const_mul,
      show (∫ x : ℕ → ℝ, (x j) ^ 2 - 1 ∂gaussianSeqMeasure) = 0
        from gaussianSeq_centeredSquare_mean j]
    ring
  have hexpand : ∀ K : ℕ,
      (∫ x, (c - gaussPartial lambda K x) ^ 2 ∂gaussianSeqMeasure)
        = c ^ 2 + 2 * ∑ j ∈ Finset.range K, (lambda j) ^ 2 := by
    intro K
    have hexp : (fun x : ℕ → ℝ => (c - gaussPartial lambda K x) ^ 2)
        = fun x => c ^ 2 - 2 * c * gaussPartial lambda K x + (gaussPartial lambda K x) ^ 2 := by
      funext x; ring
    have hIntA : Integrable (fun x => c ^ 2 - 2 * c * gaussPartial lambda K x)
        gaussianSeqMeasure :=
      (integrable_const (c ^ 2)).sub ((hSint K).const_mul (2 * c))
    rw [hexp, integral_add hIntA
      ((memLp_two_iff_integrable_sq
        (gaussPartial_memLp lambda K).aestronglyMeasurable).mp
        (gaussPartial_memLp lambda K)),
      integral_sub (integrable_const (c ^ 2)) ((hSint K).const_mul (2 * c))]
    simp only [integral_const, integral_const_mul, probReal_univ]
    rw [hmeanS K, hS2 K]
    ring
  have h1 : Tendsto (fun K : ℕ =>
      ∫ x, (c - gaussPartial lambda K x) ^ 2 ∂gaussianSeqMeasure) atTop (𝓝 0) := by
    convert htail using 1
    exact funext fun K => (hcongr K).symm
  have h2 : Tendsto (fun K : ℕ => c ^ 2 + 2 * ∑ j ∈ Finset.range K, (lambda j) ^ 2)
      atTop (𝓝 0) := by
    convert h1 using 1
    exact funext fun K => (hexpand K).symm
  have h3 : Tendsto (fun K : ℕ => (2:ℝ) * ∑ j ∈ Finset.range K, (lambda j) ^ 2)
      atTop (𝓝 ((2:ℝ) * ∑' j, (lambda j) ^ 2)) :=
    hlambda.hasSum.tendsto_sum_nat.const_mul 2
  have h4 : Tendsto (fun K : ℕ => (c:ℝ) ^ 2) atTop
      (𝓝 ((0:ℝ) - (2:ℝ) * ∑' j, (lambda j) ^ 2)) := by
    convert h2.sub h3 using 1
    exact funext fun K => by ring
  have h5 : (0:ℝ) - (2:ℝ) * ∑' j, (lambda j) ^ 2 = c ^ 2 :=
    tendsto_nhds_unique h4 tendsto_const_nhds
  have hA0 : (2:ℝ) * ∑' j, (lambda j) ^ 2 = 0 := by
    have hnn : (0:ℝ) ≤ ∑' j, (lambda j) ^ 2 :=
      tsum_nonneg fun j => sq_nonneg (lambda j)
    linarith [sq_nonneg c]
  have hA' : ∑' j, (lambda j) ^ 2 = 0 := by
    rcases mul_eq_zero.1 hA0 with h' | h'
    · exact absurd h' two_ne_zero
    · exact h'

  intro j
  have hle := hlambda.sum_le_tsum {j} (fun i _ => sq_nonneg _)
  simp only [Finset.sum_singleton] at hle
  have hj : (lambda j) ^ 2 = 0 := by linarith [sq_nonneg (lambda j)]
  exact sq_eq_zero_iff.mp hj

/-- E1 (nondegeneracy): if some coefficient is nonzero, the constructed
`L2` limit is not almost surely constant. -/
theorem gaussSeriesLimit_not_ae_const (lambda : ℕ → ℝ)
    (hlambda : Summable fun j => (lambda j) ^ 2) {Q : (ℕ → ℝ) → ℝ}
    (hmemK : ∀ K : ℕ, MemLp (fun x => Q x - gaussPartial lambda K x) 2 gaussianSeqMeasure)
    (htail : Tendsto (fun K : ℕ =>
        ∫ x, (Q x - gaussPartial lambda K x) ^ 2 ∂gaussianSeqMeasure) atTop (𝓝 0))
    (hne : ∃ j, lambda j ≠ 0) :
    ¬ ∃ c : ℝ, Q =ᵐ[gaussianSeqMeasure] fun _ => c := by
  rintro ⟨c, hc⟩
  exact absurd
    (gaussSeriesLimit_ae_const_forces_zero lambda hlambda hmemK htail ⟨c, hc⟩ hne.choose)
    hne.choose_spec

/-! ### E3: characteristic function of the finite partial sums -/

/-- Scaling law for the characteristic function of one centered square on
the constructed space. -/
theorem charFun_centeredSquare_scaled (lambda : ℕ → ℝ) (j : ℕ) (t : ℝ) :
    charFun (gaussianSeqMeasure.map (fun x => lambda j * ((x j) ^ 2 - 1))) t
      = charFun ((gaussianReal 0 1).map (fun z : ℝ => z ^ 2 - 1)) (lambda j * t) := by
  have hmeas : AEMeasurable (fun x : ℕ → ℝ => (x j) ^ 2 - 1) gaussianSeqMeasure :=
    (((measurable_pi_apply j).pow_const 2).sub measurable_const).aemeasurable
  have hcomp : gaussianSeqMeasure.map (fun x : ℕ → ℝ => (x j) ^ 2 - 1)
      = (gaussianReal 0 1).map (fun z : ℝ => z ^ 2 - 1) := by
    rw [show gaussianSeqMeasure.map (fun x : ℕ → ℝ => (x j) ^ 2 - 1)
        = gaussianSeqMeasure.map ((fun z : ℝ => z ^ 2 - 1) ∘ fun x : ℕ → ℝ => x j) from rfl,
      ← Measure.map_map (g := fun z : ℝ => z ^ 2 - 1) (f := fun x : ℕ → ℝ => x j)
        (by fun_prop) (measurable_pi_apply j),
      show gaussianSeqMeasure.map (fun x : ℕ → ℝ => x j) = gaussianReal 0 1 from
        gaussianSeqMeasure_map_var j]
  rw [charFun_map_mul_comp hmeas, hcomp]

/-- E3: the characteristic function of a finite partial sum of the Gaussian
second-chaos series is the product over coordinates of the scaled
characteristic functions of the centered square. -/
theorem charFun_gaussPartial (lambda : ℕ → ℝ) (K : ℕ) (t : ℝ) :
    charFun (gaussianSeqMeasure.map (fun x =>
        ∑ j ∈ Finset.range K, lambda j * ((x j) ^ 2 - 1))) t
      = ∏ j ∈ Finset.range K,
          charFun ((gaussianReal 0 1).map (fun z : ℝ => z ^ 2 - 1)) (lambda j * t) := by
  have hmeasM : ∀ j : ℕ, Measurable (fun x : ℕ → ℝ => lambda j * ((x j) ^ 2 - 1)) :=
    fun j => measurable_const.mul ((measurable_pi_apply j).pow_const 2 |>.sub measurable_const)
  have hind : iIndepFun (fun (j : ℕ) (x : ℕ → ℝ) => lambda j * ((x j) ^ 2 - 1))
      gaussianSeqMeasure :=
    gaussianSeq_iIndepFun.comp (fun j z => lambda j * (z ^ 2 - 1)) (fun j => by fun_prop)
  have hmeasFam : ∀ j : ℕ,
      AEMeasurable (fun x : ℕ → ℝ => lambda j * ((x j) ^ 2 - 1)) gaussianSeqMeasure :=
    fun j => (hmeasM j).aemeasurable
  rw [iIndepFun.charFun_map_fun_finsetSum_eq_prod
    (fun j _ => hmeasFam j) (iIndepFun.restrict hind (Finset.range K)),
    Finset.prod_apply]
  exact Finset.prod_congr rfl fun j _ => charFun_centeredSquare_scaled lambda j t

end Hurst
