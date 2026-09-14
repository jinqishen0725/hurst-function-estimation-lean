import Hurst.P6LawIdentification

/-!
# Fourth moment of the Gaussian second-chaos partial sums

The exact fourth-moment identity for the finite partial sums of the Gaussian
second-chaos series on the constructed space `gaussianSeqMeasure` of
`Hurst.P4GaussianSeriesLaw`:

`E[(∑_{j<K} λ_j (Z_j² − 1))⁴] = 12 · (∑_{j<K} λ_j²)² + 48 · ∑_{j<K} λ_j⁴`

with the exact classical coefficients (the variance `E[S_K²] = 2 ∑ λ²` gives
`3·(2∑λ²)² = 12(∑λ²)²`; the single-coordinate fourth moment `60λ⁴` splits as
`48λ⁴ + 12λ⁴`).

* `gaussSeq_finset_pow_four`: the identity for an arbitrary finite index set.
* `fourthMoment_partialSum`: the `K`-prefix form.
* `fourthMoment_partialSum_le`: the `(∑λ²)`-scale bound
  `E[S_K⁴] ≤ 60 · (∑_{j<K} λ_j²)²` used for uniform integrability downstream.

Method: `Finset.induction_on` with the insert step `S ↦ S + λ_k(Z_k² − 1)`,
the binomial expansion `(x+y)⁴ = x⁴ + 4x³y + 6x²y² + 4xy³ + y⁴`, and the
independence of the partial sum over `s` from the `k`-th term
(`iIndepFun.indepFun_finsetSum_of_notMem`), which kills the odd cross terms
(the partial sum has mean zero and the centered square has mean zero) and
factorizes the even ones (`IndepFun.comp` +
`IndepFun.integral_fun_mul_eq_mul_integral`).
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Hurst

/-! ### Per-coordinate term moments on the constructed sequence space -/

/-- The single coordinate term has mean zero. -/
theorem gaussSeq_term_mean (lambda : ℕ → ℝ) (j : ℕ) :
    (∫ x : ℕ → ℝ, lambda j * ((x j) ^ 2 - 1) ∂gaussianSeqMeasure) = 0 := by
  rw [integral_const_mul,
    show (∫ x : ℕ → ℝ, (x j) ^ 2 - 1 ∂gaussianSeqMeasure) = 0
      from gaussianSeq_centeredSquare_mean j]
  ring

/-- The single coordinate term has second moment `2 * lambda j ^ 2`. -/
theorem gaussSeq_term_pow_two (lambda : ℕ → ℝ) (j : ℕ) :
    (∫ x : ℕ → ℝ, (lambda j * ((x j) ^ 2 - 1)) ^ 2 ∂gaussianSeqMeasure)
      = 2 * lambda j ^ 2 := by
  have hlaw : HasLaw (gaussianSeqVar j) (gaussianReal 0 1) gaussianSeqMeasure :=
    ⟨(gaussianSeqVar_measurable j).aemeasurable, gaussianSeqMeasure_map_var j⟩
  have hf : AEStronglyMeasurable (fun z : ℝ => (lambda j * (z ^ 2 - 1)) ^ 2)
      (gaussianReal 0 1) :=
    (show Continuous fun z : ℝ => (lambda j * (z ^ 2 - 1)) ^ 2 by fun_prop).aestronglyMeasurable
  have hval : (∫ x : ℕ → ℝ, (lambda j * (gaussianSeqVar j x ^ 2 - 1)) ^ 2
        ∂gaussianSeqMeasure)
      = ∫ z : ℝ, (lambda j * (z ^ 2 - 1)) ^ 2 ∂gaussianReal 0 1 := hlaw.integral_comp hf
  rw [show (∫ x : ℕ → ℝ, (lambda j * ((x j) ^ 2 - 1)) ^ 2 ∂gaussianSeqMeasure)
      = ∫ x : ℕ → ℝ, (lambda j * (gaussianSeqVar j x ^ 2 - 1)) ^ 2 ∂gaussianSeqMeasure from rfl,
    hval,
    show (fun z : ℝ => (lambda j * (z ^ 2 - 1)) ^ 2)
      = fun z : ℝ => lambda j ^ 2 * (z ^ 2 - 1) ^ 2 by
      funext z; ring, integral_const_mul, gaussianReal_centeredSquare_sq]
  ring

/-- The single coordinate term has third moment `8 * lambda j ^ 3`. -/
theorem gaussSeq_term_pow_three (lambda : ℕ → ℝ) (j : ℕ) :
    (∫ x : ℕ → ℝ, (lambda j * ((x j) ^ 2 - 1)) ^ 3 ∂gaussianSeqMeasure)
      = 8 * lambda j ^ 3 := by
  have hlaw : HasLaw (gaussianSeqVar j) (gaussianReal 0 1) gaussianSeqMeasure :=
    ⟨(gaussianSeqVar_measurable j).aemeasurable, gaussianSeqMeasure_map_var j⟩
  have hf : AEStronglyMeasurable (fun z : ℝ => (lambda j * (z ^ 2 - 1)) ^ 3)
      (gaussianReal 0 1) :=
    (show Continuous fun z : ℝ => (lambda j * (z ^ 2 - 1)) ^ 3 by fun_prop).aestronglyMeasurable
  have hval : (∫ x : ℕ → ℝ, (lambda j * (gaussianSeqVar j x ^ 2 - 1)) ^ 3
        ∂gaussianSeqMeasure)
      = ∫ z : ℝ, (lambda j * (z ^ 2 - 1)) ^ 3 ∂gaussianReal 0 1 := hlaw.integral_comp hf
  rw [show (∫ x : ℕ → ℝ, (lambda j * ((x j) ^ 2 - 1)) ^ 3 ∂gaussianSeqMeasure)
      = ∫ x : ℕ → ℝ, (lambda j * (gaussianSeqVar j x ^ 2 - 1)) ^ 3 ∂gaussianSeqMeasure from rfl,
    hval,
    show (fun z : ℝ => (lambda j * (z ^ 2 - 1)) ^ 3)
      = fun z : ℝ => lambda j ^ 3 * (z ^ 2 - 1) ^ 3 by
      funext z; ring, integral_const_mul, gaussianReal_centeredSquare_pow_three]
  ring

/-- All powers of a single coordinate term are integrable. -/
theorem gaussSeq_term_pow_integrable (c : ℝ) (j n : ℕ) :
    Integrable (fun x : ℕ → ℝ => (c * ((x j) ^ 2 - 1)) ^ n) gaussianSeqMeasure := by
  have hL : MemLp (fun z : ℝ => (c * (z ^ 2 - 1)) ^ n) 1 (gaussianReal 0 1) := by
    refine memLp_one_iff_integrable.2 ?_
    have h := standardGaussian_polynomial_integrable
      ((Polynomial.C c * (Polynomial.X ^ 2 - Polynomial.C 1)) ^ n)
    refine h.congr (Eventually.of_forall fun z => ?_)
    simp [Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_C, Polynomial.eval_X]
  have h2 : MemLp (fun z : ℝ => (c * (z ^ 2 - 1)) ^ n) 1
      (gaussianSeqMeasure.map (gaussianSeqVar j)) := by
    rw [gaussianSeqMeasure_map_var j]; exact hL
  have h3 := MemLp.comp_of_map (f := gaussianSeqVar j)
    (g := fun z : ℝ => (c * (z ^ 2 - 1)) ^ n) h2 (gaussianSeqVar_measurable j).aemeasurable
  exact (memLp_one_iff_integrable.1 h3).congr (Eventually.of_forall fun x => rfl)

/-- A finite sum of the coordinate terms has mean zero. -/
theorem gaussSeq_finsetSum_mean (lambda : ℕ → ℝ) (s : Finset ℕ) :
    (∫ x : ℕ → ℝ, ∑ j ∈ s, lambda j * ((x j) ^ 2 - 1) ∂gaussianSeqMeasure) = 0 := by
  have hfin : ∀ j ∈ s, Integrable (fun x : ℕ → ℝ => lambda j * ((x j) ^ 2 - 1))
      gaussianSeqMeasure :=
    fun j _ => integrable_of_memLp_two ((gaussianSeqVar_sq_memLp j).const_mul (lambda j))
  rw [integral_finsetSum s hfin]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [integral_const_mul,
    show (∫ x : ℕ → ℝ, (x j) ^ 2 - 1 ∂gaussianSeqMeasure) = 0
      from gaussianSeq_centeredSquare_mean j]
  ring

set_option maxHeartbeats 2000000 in
/-- A finite sum of the coordinate terms is measurable. -/
theorem gaussSeq_finsetSum_measurable (lambda : ℕ → ℝ) (s : Finset ℕ) :
    Measurable (fun x : ℕ → ℝ => ∑ j ∈ s, lambda j * ((x j) ^ 2 - 1)) :=
  measurable_finsetSum_of (fun (j : ℕ) (x : ℕ → ℝ) => lambda j * ((x j) ^ 2 - 1))
    (fun j _ => measurable_const.mul
      (((measurable_pi_apply j).pow_const 2).sub measurable_const))

/-! ### Independence of the partial sum and a fresh term -/

/-- The partial sum over a finite set `s` of coordinates is independent of the
term carried by any coordinate outside `s`. -/
theorem gaussSeq_finsetSum_indepFun_term (lambda : ℕ → ℝ) (s : Finset ℕ) (k : ℕ)
    (hk : k ∉ s) :
    IndepFun (fun x : ℕ → ℝ => ∑ j ∈ s, lambda j * ((x j) ^ 2 - 1))
      (fun x : ℕ → ℝ => lambda k * ((x k) ^ 2 - 1)) gaussianSeqMeasure := by
  have h := (gaussianSeq_iIndepFun.comp (fun j z => lambda j * (z ^ 2 - 1))
      (fun j => by fun_prop)).indepFun_finsetSum_of_notMem
    (fun i => measurable_const.mul
      (((measurable_pi_apply i).pow_const 2).sub measurable_const)) hk
  have heq : (∑ j ∈ s, (fun z => lambda j * (z ^ 2 - 1)) ∘ (fun x : ℕ → ℝ => x j))
      = fun x : ℕ → ℝ => ∑ j ∈ s, lambda j * ((x j) ^ 2 - 1) := by
    funext x
    simp [Function.comp_def, Finset.sum_apply]
  rw [heq] at h
  exact h

/-! ### Independence factorization of cross-term integrals -/

/-- For independent random variables, the integral of a product of powers
factorizes. -/
private theorem integral_pow_mul_eq_mul (X Y : (ℕ → ℝ) → ℝ)
    (hind : IndepFun X Y gaussianSeqMeasure) (mX : Measurable X) (mY : Measurable Y)
    (a b : ℕ) :
    (∫ x : ℕ → ℝ, X x ^ a * Y x ^ b ∂gaussianSeqMeasure)
      = (∫ x : ℕ → ℝ, X x ^ a ∂gaussianSeqMeasure)
          * (∫ x : ℕ → ℝ, Y x ^ b ∂gaussianSeqMeasure) := by
  have hindep : IndepFun ((fun z : ℝ => z ^ a) ∘ X) ((fun z : ℝ => z ^ b) ∘ Y)
      gaussianSeqMeasure :=
    hind.comp (measurable_id.pow_const a) (measurable_id.pow_const b)
  have h := hindep.integral_fun_mul_eq_mul_integral ((mX.pow_const a).aestronglyMeasurable)
    (mY.pow_const b).aestronglyMeasurable
  simpa only [Function.comp_apply, id_eq] using h

private theorem integral_cube_mul_eq (X Y : (ℕ → ℝ) → ℝ)
    (hind : IndepFun X Y gaussianSeqMeasure) (mX : Measurable X) (mY : Measurable Y) :
    (∫ x : ℕ → ℝ, X x ^ 3 * Y x ∂gaussianSeqMeasure)
      = (∫ x : ℕ → ℝ, X x ^ 3 ∂gaussianSeqMeasure)
          * (∫ x : ℕ → ℝ, Y x ∂gaussianSeqMeasure) := by
  simpa only [pow_one] using integral_pow_mul_eq_mul X Y hind mX mY 3 1

private theorem integral_sq_mul_sq_eq (X Y : (ℕ → ℝ) → ℝ)
    (hind : IndepFun X Y gaussianSeqMeasure) (mX : Measurable X) (mY : Measurable Y) :
    (∫ x : ℕ → ℝ, X x ^ 2 * Y x ^ 2 ∂gaussianSeqMeasure)
      = (∫ x : ℕ → ℝ, X x ^ 2 ∂gaussianSeqMeasure)
          * (∫ x : ℕ → ℝ, Y x ^ 2 ∂gaussianSeqMeasure) :=
  integral_pow_mul_eq_mul X Y hind mX mY 2 2

private theorem integral_mul_cube_eq (X Y : (ℕ → ℝ) → ℝ)
    (hind : IndepFun X Y gaussianSeqMeasure) (mX : Measurable X) (mY : Measurable Y) :
    (∫ x : ℕ → ℝ, Y x ^ 3 * X x ∂gaussianSeqMeasure)
      = (∫ x : ℕ → ℝ, Y x ^ 3 ∂gaussianSeqMeasure)
          * (∫ x : ℕ → ℝ, X x ∂gaussianSeqMeasure) := by
  simpa only [pow_one] using integral_pow_mul_eq_mul Y X hind.symm mY mX 3 1

/-! ### Integrability of the binomial cross terms -/

/-- Young-type inequality `4|u|³|v| ≤ 3u⁴ + v⁴`. -/
private theorem young43 (u v : ℝ) : 4 * |u| ^ 3 * |v| ≤ 3 * u ^ 4 + v ^ 4 := by
  have h4u : u ^ 4 = |u| ^ 4 := by
    rw [← abs_pow]; exact (abs_of_nonneg (show (0:ℝ) ≤ u ^ 4 by positivity)).symm
  have h4v : v ^ 4 = |v| ^ 4 := by
    rw [← abs_pow]; exact (abs_of_nonneg (show (0:ℝ) ≤ v ^ 4 by positivity)).symm
  rw [h4u, h4v]
  nlinarith [sq_nonneg (|u| - |v|),
    show (0:ℝ) ≤ 3 * |u| ^ 2 + 2 * |u| * |v| + |v| ^ 2 by positivity]

/-- Young-type inequality `6u²v² ≤ 3u⁴ + 3v⁴`. -/
private theorem young22 (u v : ℝ) : 6 * u ^ 2 * v ^ 2 ≤ 3 * u ^ 4 + 3 * v ^ 4 := by
  nlinarith [sq_nonneg (u ^ 2 - v ^ 2)]

private theorem integrable_cube_mul {f g : (ℕ → ℝ) → ℝ}
    (mf : Measurable f) (mg : Measurable g)
    (hf4 : Integrable (fun x => f x ^ 4) gaussianSeqMeasure)
    (hg4 : Integrable (fun x => g x ^ 4) gaussianSeqMeasure) :
    Integrable (fun x => f x ^ 3 * g x) gaussianSeqMeasure := by
  have hbound : Integrable (fun x => 3 * f x ^ 4 + g x ^ 4) gaussianSeqMeasure :=
    (hf4.const_mul 3).add hg4
  refine Integrable.mono' hbound ((mf.pow_const 3).mul mg).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  have hy := young43 (f x) (g x)
  have hpos : (0:ℝ) ≤ 3 * f x ^ 4 + g x ^ 4 := by positivity
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  nlinarith [hy, hpos, sq_nonneg (f x ^ 2), sq_nonneg (g x ^ 2)]

private theorem integrable_sq_mul_sq {f g : (ℕ → ℝ) → ℝ}
    (mf : Measurable f) (mg : Measurable g)
    (hf4 : Integrable (fun x => f x ^ 4) gaussianSeqMeasure)
    (hg4 : Integrable (fun x => g x ^ 4) gaussianSeqMeasure) :
    Integrable (fun x => f x ^ 2 * g x ^ 2) gaussianSeqMeasure := by
  have hbound : Integrable (fun x => 3 * f x ^ 4 + 3 * g x ^ 4) gaussianSeqMeasure :=
    (hf4.const_mul 3).add (hg4.const_mul 3)
  refine Integrable.mono' hbound ((mf.pow_const 2).mul (mg.pow_const 2)).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  have hy := young22 (f x) (g x)
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_pow, sq_abs, sq_abs]
  nlinarith [hy, sq_nonneg (f x ^ 2), sq_nonneg (g x ^ 2)]

private theorem integrable_mul_cube {f g : (ℕ → ℝ) → ℝ}
    (mf : Measurable f) (mg : Measurable g)
    (hf4 : Integrable (fun x => f x ^ 4) gaussianSeqMeasure)
    (hg4 : Integrable (fun x => g x ^ 4) gaussianSeqMeasure) :
    Integrable (fun x => g x ^ 3 * f x) gaussianSeqMeasure :=
  integrable_cube_mul mg mf hg4 hf4

/-- Binomial expansion of the fourth power of a sum. -/
private theorem pow_four_add (u v : ℝ) : (u + v) ^ 4
    = u ^ 4 + ((4 * (u ^ 3 * v) + 6 * (u ^ 2 * v ^ 2))
        + (4 * (v ^ 3 * u) + v ^ 4)) := by
  ring

/-! ### Integrability of the fourth power of a finite partial sum -/

/-- The fourth power of a finite partial sum is integrable (induction on the
index set via `pow4_add_le`). -/
theorem gaussSeq_finsetSum_pow_four_integrable (lambda : ℕ → ℝ) (s : Finset ℕ) :
    Integrable (fun x : ℕ → ℝ => (∑ j ∈ s, lambda j * ((x j) ^ 2 - 1)) ^ 4)
      gaussianSeqMeasure := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    have hmeasY : Measurable (fun x : ℕ → ℝ => lambda k * ((x k) ^ 2 - 1)) :=
      measurable_const.mul (((measurable_pi_apply k).pow_const 2).sub measurable_const)
    have hmeasS : Measurable (fun x : ℕ → ℝ => ∑ j ∈ s, lambda j * ((x j) ^ 2 - 1)) :=
      gaussSeq_finsetSum_measurable lambda s
    have hA : Integrable (fun x : ℕ → ℝ => (lambda k * ((x k) ^ 2 - 1)) ^ 4)
        gaussianSeqMeasure := gaussSeq_term_pow_integrable (lambda k) k 4
    have hbound : Integrable (fun x : ℕ → ℝ =>
        8 * (lambda k * ((x k) ^ 2 - 1)) ^ 4
          + 8 * (∑ j ∈ s, lambda j * ((x j) ^ 2 - 1)) ^ 4) gaussianSeqMeasure :=
      (hA.const_mul 8).add (ih.const_mul 8)
    refine Integrable.mono' hbound ((hmeasY.add hmeasS).pow_const 4).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    have hp := pow4_add_le (lambda k * ((x k) ^ 2 - 1))
      (∑ j ∈ s, lambda j * ((x j) ^ 2 - 1))
    rw [Real.norm_eq_abs, abs_of_nonneg (show (0:ℝ) ≤
      (lambda k * ((x k) ^ 2 - 1) + ∑ j ∈ s, lambda j * ((x j) ^ 2 - 1)) ^ 4 by
      positivity)]
    linarith

/-! ### The fourth-moment identity -/

set_option maxHeartbeats 1000000 in
/-- The exact fourth moment of a finite partial sum of the Gaussian
second-chaos series: `12 * (∑ λ²)² + 48 * ∑ λ⁴`. -/
theorem gaussSeq_finset_pow_four (lambda : ℕ → ℝ) (s : Finset ℕ) :
    (∫ x : ℕ → ℝ, (∑ j ∈ s, lambda j * ((x j) ^ 2 - 1)) ^ 4 ∂gaussianSeqMeasure)
      = 12 * (∑ j ∈ s, (lambda j) ^ 2) ^ 2 + 48 * ∑ j ∈ s, (lambda j) ^ 4 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    -- the previous partial sum and the fresh term, as explicit functions
    have hind : IndepFun (fun x : ℕ → ℝ => ∑ j ∈ s, lambda j * ((x j) ^ 2 - 1))
        (fun x : ℕ → ℝ => lambda k * ((x k) ^ 2 - 1)) gaussianSeqMeasure :=
      gaussSeq_finsetSum_indepFun_term lambda s k hk
    have hmeasX : Measurable (fun x : ℕ → ℝ => ∑ j ∈ s, lambda j * ((x j) ^ 2 - 1)) :=
      gaussSeq_finsetSum_measurable lambda s
    have hmeasY : Measurable (fun x : ℕ → ℝ => lambda k * ((x k) ^ 2 - 1)) :=
      measurable_const.mul (((measurable_pi_apply k).pow_const 2).sub measurable_const)
    have hIf4 : Integrable (fun x : ℕ → ℝ => (∑ j ∈ s, lambda j * ((x j) ^ 2 - 1)) ^ 4)
        gaussianSeqMeasure := gaussSeq_finsetSum_pow_four_integrable lambda s
    have hIg4 : Integrable (fun x : ℕ → ℝ => (lambda k * ((x k) ^ 2 - 1)) ^ 4)
        gaussianSeqMeasure := gaussSeq_term_pow_integrable (lambda k) k 4
    have hI1 : Integrable (fun x : ℕ → ℝ => (∑ j ∈ s, lambda j * ((x j) ^ 2 - 1)) ^ 4)
        gaussianSeqMeasure := hIf4
    have hI2 : Integrable (fun x : ℕ → ℝ =>
        4 * ((∑ j ∈ s, lambda j * ((x j) ^ 2 - 1)) ^ 3
          * (lambda k * ((x k) ^ 2 - 1)))) gaussianSeqMeasure :=
      (integrable_cube_mul hmeasX hmeasY hIf4 hIg4).const_mul 4
    have hI3 : Integrable (fun x : ℕ → ℝ =>
        6 * ((∑ j ∈ s, lambda j * ((x j) ^ 2 - 1)) ^ 2
          * (lambda k * ((x k) ^ 2 - 1)) ^ 2)) gaussianSeqMeasure :=
      (integrable_sq_mul_sq hmeasX hmeasY hIf4 hIg4).const_mul 6
    have hI4 : Integrable (fun x : ℕ → ℝ =>
        4 * ((lambda k * ((x k) ^ 2 - 1)) ^ 3
          * (∑ j ∈ s, lambda j * ((x j) ^ 2 - 1)))) gaussianSeqMeasure :=
      (integrable_mul_cube hmeasX hmeasY hIf4 hIg4).const_mul 4
    have hI5 : Integrable (fun x : ℕ → ℝ => (lambda k * ((x k) ^ 2 - 1)) ^ 4)
        gaussianSeqMeasure := hIg4
    have hI23 : Integrable (fun x : ℕ → ℝ =>
        4 * ((∑ j ∈ s, lambda j * ((x j) ^ 2 - 1)) ^ 3
          * (lambda k * ((x k) ^ 2 - 1)))
        + 6 * ((∑ j ∈ s, lambda j * ((x j) ^ 2 - 1)) ^ 2
          * (lambda k * ((x k) ^ 2 - 1)) ^ 2)) gaussianSeqMeasure := hI2.add hI3
    have hI45 : Integrable (fun x : ℕ → ℝ =>
        4 * ((lambda k * ((x k) ^ 2 - 1)) ^ 3
          * (∑ j ∈ s, lambda j * ((x j) ^ 2 - 1)))
        + (lambda k * ((x k) ^ 2 - 1)) ^ 4) gaussianSeqMeasure := hI4.add hI5
    have hIrest : Integrable (fun x : ℕ → ℝ =>
        4 * ((∑ j ∈ s, lambda j * ((x j) ^ 2 - 1)) ^ 3
          * (lambda k * ((x k) ^ 2 - 1)))
        + 6 * ((∑ j ∈ s, lambda j * ((x j) ^ 2 - 1)) ^ 2
          * (lambda k * ((x k) ^ 2 - 1)) ^ 2)
        + (4 * ((lambda k * ((x k) ^ 2 - 1)) ^ 3
          * (∑ j ∈ s, lambda j * ((x j) ^ 2 - 1)))
        + (lambda k * ((x k) ^ 2 - 1)) ^ 4)) gaussianSeqMeasure := hI23.add hI45
    -- binomial expansion pointwise (association matches hIrest via integral_add)
    have hpoint : ∀ x : ℕ → ℝ,
        (lambda k * ((x k) ^ 2 - 1) + ∑ j ∈ s, lambda j * ((x j) ^ 2 - 1)) ^ 4
          = (∑ j ∈ s, lambda j * ((x j) ^ 2 - 1)) ^ 4
            + ((4 * ((∑ j ∈ s, lambda j * ((x j) ^ 2 - 1)) ^ 3
                  * (lambda k * ((x k) ^ 2 - 1)))
                + 6 * ((∑ j ∈ s, lambda j * ((x j) ^ 2 - 1)) ^ 2
                  * (lambda k * ((x k) ^ 2 - 1)) ^ 2))
              + (4 * ((lambda k * ((x k) ^ 2 - 1)) ^ 3
                  * (∑ j ∈ s, lambda j * ((x j) ^ 2 - 1)))
                + (lambda k * ((x k) ^ 2 - 1)) ^ 4)) := by
      intro x
      rw [add_comm (lambda k * ((x k) ^ 2 - 1))
        (∑ j ∈ s, lambda j * ((x j) ^ 2 - 1))]
      exact pow_four_add _ _
    rw [integral_congr_ae (Eventually.of_forall hpoint),
      integral_add hI1 hIrest, integral_add hI23 hI45, integral_add hI2 hI3,
      integral_add hI4 hI5]
    simp only [integral_const_mul]
    rw [ih,
      integral_cube_mul_eq (fun x : ℕ → ℝ => ∑ j ∈ s, lambda j * ((x j) ^ 2 - 1))
        (fun x : ℕ → ℝ => lambda k * ((x k) ^ 2 - 1)) hind hmeasX hmeasY,
      gaussSeq_term_mean lambda k, mul_zero,
      integral_sq_mul_sq_eq (fun x : ℕ → ℝ => ∑ j ∈ s, lambda j * ((x j) ^ 2 - 1))
        (fun x : ℕ → ℝ => lambda k * ((x k) ^ 2 - 1)) hind hmeasX hmeasY,
      gaussianSeq_centeredSquare_finset_L2 lambda s, gaussSeq_term_pow_two lambda k,
      integral_mul_cube_eq (fun x : ℕ → ℝ => ∑ j ∈ s, lambda j * ((x j) ^ 2 - 1))
        (fun x : ℕ → ℝ => lambda k * ((x k) ^ 2 - 1)) hind hmeasX hmeasY,
      gaussSeq_finsetSum_mean lambda s, mul_zero,
      gaussSeq_term_pow_four lambda k]
    ring

/-- The fourth-moment identity for the `K`-prefix partial sums:
`E[S_K⁴] = 12 * (∑_{j<K} λ_j²)² + 48 * ∑_{j<K} λ_j⁴`. -/
theorem fourthMoment_partialSum (lambda : ℕ → ℝ) (K : ℕ) :
    (∫ x : ℕ → ℝ, (∑ j ∈ Finset.range K, lambda j * ((x j) ^ 2 - 1)) ^ 4
        ∂gaussianSeqMeasure)
      = 12 * (∑ j ∈ Finset.range K, (lambda j) ^ 2) ^ 2
        + 48 * ∑ j ∈ Finset.range K, (lambda j) ^ 4 :=
  gaussSeq_finset_pow_four lambda (Finset.range K)

/-! ### The `(∑λ²)`-scale bound for uniform integrability -/

/-- For any real sequence, `∑ u⁴ ≤ (∑ u²)²`. -/
private theorem sum_pow_four_le_sq_sum_sq {s : Finset ℕ} (u : ℕ → ℝ) :
    ∑ j ∈ s, u j ^ 4 ≤ (∑ j ∈ s, u j ^ 2) ^ 2 := by
  have hexp : (∑ j ∈ s, u j ^ 2) ^ 2 = ∑ i ∈ s, ∑ j ∈ s, u i ^ 2 * u j ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
  have hdiag : ∑ j ∈ s, u j ^ 4 = ∑ i ∈ s, ∑ j ∈ s, (if i = j then u j ^ 4 else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp [hj]
  calc ∑ j ∈ s, u j ^ 4
      = ∑ i ∈ s, ∑ j ∈ s, (if i = j then u j ^ 4 else 0) := hdiag
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, u i ^ 2 * u j ^ 2 := by
        refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
        rcases eq_or_ne i j with rfl | hij
        · have h4 : u i ^ 4 = u i ^ 2 * u i ^ 2 := by ring
          rw [if_pos rfl, h4]
        · simp only [if_neg hij]
          exact mul_nonneg (pow_two_nonneg _) (pow_two_nonneg _)
    _ = (∑ j ∈ s, u j ^ 2) ^ 2 := hexp.symm

set_option maxHeartbeats 1000000 in
/-- `(∑λ²)`-scale fourth-moment bound: `E[S_K⁴] ≤ 60 * (∑_{j<K} λ_j²)²`,
uniform in `K` for bounded `∑ λ²`. -/
theorem fourthMoment_partialSum_le (lambda : ℕ → ℝ) (K : ℕ) :
    (∫ x : ℕ → ℝ, (∑ j ∈ Finset.range K, lambda j * ((x j) ^ 2 - 1)) ^ 4
        ∂gaussianSeqMeasure)
      ≤ 60 * (∑ j ∈ Finset.range K, (lambda j) ^ 2) ^ 2 := by
  rw [fourthMoment_partialSum]
  have hB : ∑ j ∈ Finset.range K, (lambda j) ^ 4
      ≤ (∑ j ∈ Finset.range K, (lambda j) ^ 2) ^ 2 :=
    sum_pow_four_le_sq_sum_sq lambda
  linarith

end Hurst
