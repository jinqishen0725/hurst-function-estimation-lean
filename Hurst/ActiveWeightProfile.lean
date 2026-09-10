import Hurst.ActiveWindowCoordinates
import Hurst.GaussianHermite

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Hurst

/-- The full-row equivalent-kernel limit, transported to increasing active
ranks and the B&S profile coordinate `(j+1)/card`. -/
theorem localPolynomialWeights_active_rank_uniform_tendsto
    (r q : ℕ) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      ∀ j : Fin (localWeightActiveSet n q (δ n) t).card,
        |((n : ℝ) * δ n) * localPolynomialWeights r n q (δ n) t
            (localWeightActiveIndex n q (δ n) t j) -
          equivalentKernel r
            (2 * (((j.val + 1 : ℕ) : ℝ) /
              ((localWeightActiveSet n q (δ n) t).card : ℝ)) - 1)| ≤ ε := by
  have hUC : UniformContinuous (equivalentKernel r) :=
    (equivalentKernel_compactSupport r).uniformContinuous_of_continuous
      (equivalentKernel_continuous r)
  intro ε hε
  obtain ⟨η, hη, hUCη⟩ :=
    Metric.uniformContinuous_iff.mp hUC (ε / 2) (half_pos hε)
  have hweight := localPolynomialWeights_scaled_uniform_tendsto
    r q t ht δ hδpos hδ0 hN (ε / 2) (half_pos hε)
  have hcoord := localWeightActiveIndex_rank_coordinate_uniform_tendsto
    q t ht δ hδpos hδ0 hN (η / 2) (half_pos hη)
  filter_upwards [hweight, hcoord] with n hnweight hncoord
  intro j
  let x := (grid n (localWeightActiveIndex n q (δ n) t j).val - t) / δ n
  let y := 2 * (((j.val + 1 : ℕ) : ℝ) /
    ((localWeightActiveSet n q (δ n) t).card : ℝ)) - 1
  have hxy : |x - y| ≤ η / 2 := by simpa only [x, y] using hncoord j
  have hk : |equivalentKernel r x - equivalentKernel r y| < ε / 2 := by
    have hdist : dist x y < η := by
      rw [Real.dist_eq]
      exact hxy.trans_lt (half_lt_self hη)
    have := hUCη hdist
    simpa only [Real.dist_eq] using this
  calc
    |((n : ℝ) * δ n) * localPolynomialWeights r n q (δ n) t
          (localWeightActiveIndex n q (δ n) t j) - equivalentKernel r y| ≤
        |((n : ℝ) * δ n) * localPolynomialWeights r n q (δ n) t
          (localWeightActiveIndex n q (δ n) t j) - equivalentKernel r x| +
          |equivalentKernel r x - equivalentKernel r y| := by
            simpa only [sub_add_sub_cancel] using
              abs_add_le
                (((n : ℝ) * δ n) * localPolynomialWeights r n q (δ n) t
                  (localWeightActiveIndex n q (δ n) t j) - equivalentKernel r x)
                (equivalentKernel r x - equivalentKernel r y)
    _ ≤ ε / 2 + ε / 2 := add_le_add (hnweight _) hk.le
    _ = ε := by ring

theorem equivalentKernel_bounded (r : ℕ) :
    ∃ D ≥ 0, ∀ x : ℝ, |equivalentKernel r x| ≤ D := by
  obtain ⟨B, hB, hlocal⟩ := kernelMomentFunction_bounded 0
  let A : ℝ := ∑ j : Fin (r + 1),
    |(continuousKernelGram r (-1) 1)⁻¹ 0 j|
  refine ⟨B * A, mul_nonneg hB (Finset.sum_nonneg fun _ _ => abs_nonneg _), ?_⟩
  intro x
  by_cases hx : |x| ≤ 1
  · rw [equivalentKernel, abs_mul]
    have hkernel : |localKernel x| ≤ B := by
      simpa only [kernelMomentFunction, pow_zero, mul_one] using hlocal x
    have hpoly :
        |∑ j : Fin (r + 1),
          (continuousKernelGram r (-1) 1)⁻¹ 0 j * x ^ j.val| ≤ A := by
      calc
        _ ≤ ∑ j : Fin (r + 1),
            |(continuousKernelGram r (-1) 1)⁻¹ 0 j * x ^ j.val| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j : Fin (r + 1),
            |(continuousKernelGram r (-1) 1)⁻¹ 0 j| := by
          apply Finset.sum_le_sum
          intro j _
          rw [abs_mul, abs_pow]
          exact mul_le_of_le_one_right (abs_nonneg _)
            (pow_le_one₀ (abs_nonneg _) hx)
        _ = A := rfl
    calc
      |localKernel x| *
          |∑ j : Fin (r + 1), (continuousKernelGram r (-1) 1)⁻¹ 0 j * x ^ j.val| ≤
          B * |∑ j : Fin (r + 1),
            (continuousKernelGram r (-1) 1)⁻¹ 0 j * x ^ j.val| :=
        mul_le_mul_of_nonneg_right hkernel (abs_nonneg _)
      _ ≤ B * A := mul_le_mul_of_nonneg_left hpoly hB
  · rw [equivalentKernel, localKernel_zero x (le_of_not_ge hx), zero_mul, abs_zero]
    exact mul_nonneg hB (Finset.sum_nonneg fun _ _ => abs_nonneg _)

/-- Coefficients in the active-row B&S normalization converge uniformly to
`sqrt 2` times the equivalent-kernel profile.  Multiplication by a fixed
centered Hermite polynomial then gives the polynomial profile used by the
external theorem. -/
theorem localPolynomialWeights_active_bsCoefficient_uniform_tendsto
    (r q : ℕ) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      ∀ j : Fin (localWeightActiveSet n q (δ n) t).card,
        |Real.sqrt (((localWeightActiveSet n q (δ n) t).card : ℝ) /
              ((n : ℝ) * δ n)) *
            (((n : ℝ) * δ n) * localPolynomialWeights r n q (δ n) t
              (localWeightActiveIndex n q (δ n) t j)) -
          Real.sqrt 2 * equivalentKernel r
            (2 * (((j.val + 1 : ℕ) : ℝ) /
              ((localWeightActiveSet n q (δ n) t).card : ℝ)) - 1)| ≤ ε := by
  obtain ⟨D, hD, hkernel⟩ := equivalentKernel_bounded r
  have hratio :=
    (localWeightActiveSet_card_ratio_tendsto_two q t ht δ hδpos hδ0 hN).2
  have hsqrt : Tendsto (fun n : ℕ =>
      Real.sqrt (((localWeightActiveSet n q (δ n) t).card : ℝ) /
        ((n : ℝ) * δ n))) atTop (𝓝 (Real.sqrt 2)) := hratio.sqrt
  have hdiff : Tendsto (fun n : ℕ =>
      |Real.sqrt (((localWeightActiveSet n q (δ n) t).card : ℝ) /
          ((n : ℝ) * δ n)) - Real.sqrt 2|) atTop (𝓝 0) := by
    convert (hsqrt.sub tendsto_const_nhds).abs using 1 <;> simp
  intro ε hε
  have hs2p : 0 < Real.sqrt 2 + 1 := by positivity
  have hDp : 0 < D + 1 := by linarith
  have hbase := localPolynomialWeights_active_rank_uniform_tendsto
    r q t ht δ hδpos hδ0 hN (ε / (2 * (Real.sqrt 2 + 1)))
      (div_pos hε (mul_pos (by norm_num) hs2p))
  have hAclose : ∀ᶠ n : ℕ in atTop,
      |Real.sqrt (((localWeightActiveSet n q (δ n) t).card : ℝ) /
          ((n : ℝ) * δ n)) - Real.sqrt 2| < ε / (2 * (D + 1)) :=
    hdiff.eventually
      (Iio_mem_nhds (div_pos hε (mul_pos (by norm_num) hDp)))
  have hAbound : ∀ᶠ n : ℕ in atTop,
      Real.sqrt (((localWeightActiveSet n q (δ n) t).card : ℝ) /
          ((n : ℝ) * δ n)) < Real.sqrt 2 + 1 :=
    hsqrt.eventually (Iio_mem_nhds (by linarith))
  filter_upwards [hbase, hAclose, hAbound] with n hnbase hnAclose hnAbound
  intro j
  let A := Real.sqrt (((localWeightActiveSet n q (δ n) t).card : ℝ) /
    ((n : ℝ) * δ n))
  let B := ((n : ℝ) * δ n) * localPolynomialWeights r n q (δ n) t
    (localWeightActiveIndex n q (δ n) t j)
  let K := equivalentKernel r
    (2 * (((j.val + 1 : ℕ) : ℝ) /
      ((localWeightActiveSet n q (δ n) t).card : ℝ)) - 1)
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hBK : |B - K| ≤ ε / (2 * (Real.sqrt 2 + 1)) := by
    simpa only [B, K] using hnbase j
  have hK : |K| ≤ D := hkernel _
  have halg : A * B - Real.sqrt 2 * K = A * (B - K) + (A - Real.sqrt 2) * K := by ring
  rw [halg]
  calc
    |A * (B - K) + (A - Real.sqrt 2) * K| ≤
        |A * (B - K)| + |(A - Real.sqrt 2) * K| := abs_add_le _ _
    _ = A * |B - K| + |A - Real.sqrt 2| * |K| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hA0]
    _ ≤ (Real.sqrt 2 + 1) * (ε / (2 * (Real.sqrt 2 + 1))) +
        (ε / (2 * (D + 1))) * D := by
      gcongr
    _ ≤ ε / 2 + ε / 2 := by
      have hfirst : (Real.sqrt 2 + 1) * (ε / (2 * (Real.sqrt 2 + 1))) = ε / 2 := by
        field_simp [hs2p.ne']
      rw [hfirst]
      have hsecond : ε / (2 * (D + 1)) * D ≤ ε / 2 := by
        apply le_of_lt
        rw [div_mul_eq_mul_div, div_lt_iff₀ (mul_pos (by norm_num) hDp)]
        nlinarith
      linarith
    _ = ε := by ring

def activeBSProfile (r : ℕ) (P : Polynomial ℝ) (τ z : ℝ) : ℝ :=
  Real.sqrt 2 * equivalentKernel r (2 * τ - 1) * P.eval z

theorem activeBSProfile_memLp (r : ℕ) (P : Polynomial ℝ) (τ : ℝ) :
    MemLp (activeBSProfile r P τ) 2 (gaussianReal 0 1) := by
  change MemLp (fun z : ℝ =>
    (Real.sqrt 2 * equivalentKernel r (2 * τ - 1)) * P.eval z)
    2 (gaussianReal 0 1)
  simpa only [mul_assoc] using
    (standardGaussian_polynomial_memLp_two P).const_mul
      (Real.sqrt 2 * equivalentKernel r (2 * τ - 1))

theorem activeBSProfile_L2_uniformContinuous
    (r : ℕ) (P : Polynomial ℝ) :
    ∀ ε > 0, ∃ η > 0, ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |s - t| < η →
        (∫ z : ℝ, (activeBSProfile r P s z - activeBSProfile r P t z) ^ 2
          ∂gaussianReal 0 1) ≤ ε := by
  let J : ℝ := ∫ z : ℝ, (P.eval z) ^ 2 ∂gaussianReal 0 1
  have hJ : 0 ≤ J := integral_nonneg (fun _ => sq_nonneg _)
  have hJp : 0 < J + 1 := by linarith
  have hUC : UniformContinuous (equivalentKernel r) :=
    (equivalentKernel_compactSupport r).uniformContinuous_of_continuous
      (equivalentKernel_continuous r)
  intro ε hε
  let κ := Real.sqrt (ε / (J + 1)) / (Real.sqrt 2 + 1)
  have hs2p : 0 < Real.sqrt 2 + 1 := by positivity
  have hκ : 0 < κ := div_pos (Real.sqrt_pos.mpr (div_pos hε hJp)) hs2p
  obtain ⟨η, hη, hUCη⟩ := Metric.uniformContinuous_iff.mp hUC κ hκ
  refine ⟨η / 2, half_pos hη, ?_⟩
  intro s _ t _ hst
  have harg : dist (2 * s - 1) (2 * t - 1) < η := by
    rw [Real.dist_eq]
    have habs : |(2 * s - 1) - (2 * t - 1)| = 2 * |s - t| := by
      rw [show (2 * s - 1) - (2 * t - 1) = 2 * (s - t) by ring,
        abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [habs]
    linarith
  have hkdist := hUCη harg
  have hk : |equivalentKernel r (2 * s - 1) -
      equivalentKernel r (2 * t - 1)| < κ := by
    simpa only [Real.dist_eq] using hkdist
  let A := Real.sqrt 2 * equivalentKernel r (2 * s - 1)
  let B := Real.sqrt 2 * equivalentKernel r (2 * t - 1)
  have hd : |A - B| ≤ Real.sqrt (ε / (J + 1)) := by
    have hs2 : Real.sqrt 2 ≤ Real.sqrt 2 + 1 := by linarith
    calc
      |A - B| = Real.sqrt 2 *
          |equivalentKernel r (2 * s - 1) - equivalentKernel r (2 * t - 1)| := by
        dsimp only [A, B]
        rw [← mul_sub, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      _ ≤ (Real.sqrt 2 + 1) * κ :=
        mul_le_mul hs2 hk.le (abs_nonneg _) hs2p.le
      _ = Real.sqrt (ε / (J + 1)) := by
        dsimp only [κ]
        field_simp [hs2p.ne']
  have hsq : (A - B) ^ 2 ≤ ε / (J + 1) := by
    calc
      (A - B) ^ 2 = |A - B| ^ 2 := by rw [sq_abs]
      _ ≤ (Real.sqrt (ε / (J + 1))) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hd 2
      _ = ε / (J + 1) := Real.sq_sqrt (div_nonneg hε.le hJp.le)
  have hint :
      (∫ z : ℝ, (activeBSProfile r P s z - activeBSProfile r P t z) ^ 2
        ∂gaussianReal 0 1) = (A - B) ^ 2 * J := by
    have hfun : (fun z : ℝ =>
        (activeBSProfile r P s z - activeBSProfile r P t z) ^ 2) =
        (fun z : ℝ => (A - B) ^ 2 * (P.eval z) ^ 2) := by
      funext z
      simp only [activeBSProfile, A, B]
      ring
    rw [hfun, integral_const_mul]
  rw [hint]
  calc
    (A - B) ^ 2 * J ≤ (ε / (J + 1)) * J :=
      mul_le_mul_of_nonneg_right hsq hJ
    _ ≤ ε := by
      apply le_of_lt
      rw [div_mul_eq_mul_div, div_lt_iff₀ hJp]
      nlinarith

def activeBSPolynomial (r n q : ℕ) (δ t : ℝ) (P : Polynomial ℝ)
    (j : Fin (localWeightActiveSet n q δ t).card) : Polynomial ℝ :=
  Polynomial.C
      (Real.sqrt (((localWeightActiveSet n q δ t).card : ℝ) /
          ((n : ℝ) * δ)) *
        (((n : ℝ) * δ) * localPolynomialWeights r n q δ t
          (localWeightActiveIndex n q δ t j))) * P

/-- Uniform Gaussian-L2 profile convergence for the active-row polynomials in
the exact normalization required by B&S. -/
theorem localPolynomialWeights_active_polynomial_L2_uniform_tendsto
    (r q : ℕ) (P : Polynomial ℝ)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      ∀ j : Fin (localWeightActiveSet n q (δ n) t).card,
        (∫ z : ℝ,
          ((activeBSPolynomial r n q (δ n) t P j).eval z -
            activeBSProfile r P
              (((j.val : ℝ) + 1) /
                ((localWeightActiveSet n q (δ n) t).card : ℝ)) z) ^ 2
            ∂gaussianReal 0 1) ≤ ε := by
  let J : ℝ := ∫ z : ℝ, (P.eval z) ^ 2 ∂gaussianReal 0 1
  have hP2 : Integrable (fun z : ℝ => (P.eval z) ^ 2) (gaussianReal 0 1) := by
    have hmul := (standardGaussian_polynomial_memLp_two P).integrable_mul
      (standardGaussian_polynomial_memLp_two P)
    change Integrable (fun z : ℝ => P.eval z * P.eval z) (gaussianReal 0 1) at hmul
    simpa only [pow_two] using hmul
  have hJ : 0 ≤ J := integral_nonneg (fun _ => sq_nonneg _)
  have hJp : 0 < J + 1 := by linarith
  intro ε hε
  let η := Real.sqrt (ε / (J + 1))
  have hη : 0 < η := Real.sqrt_pos.mpr (div_pos hε hJp)
  have hcoeff := localPolynomialWeights_active_bsCoefficient_uniform_tendsto
    r q t ht δ hδpos hδ0 hN η hη
  filter_upwards [hcoeff] with n hn
  intro j
  let A := Real.sqrt (((localWeightActiveSet n q (δ n) t).card : ℝ) /
      ((n : ℝ) * δ n)) *
    (((n : ℝ) * δ n) * localPolynomialWeights r n q (δ n) t
      (localWeightActiveIndex n q (δ n) t j))
  let B := Real.sqrt 2 * equivalentKernel r
    (2 * (((j.val : ℝ) + 1) /
      ((localWeightActiveSet n q (δ n) t).card : ℝ)) - 1)
  have hd : |A - B| ≤ η := by
    simpa only [A, B, Nat.cast_add, Nat.cast_one] using hn j
  have hsq : (A - B) ^ 2 ≤ ε / (J + 1) := by
    calc
      (A - B) ^ 2 = |A - B| ^ 2 := by rw [sq_abs]
      _ ≤ η ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hd 2
      _ = ε / (J + 1) := Real.sq_sqrt (div_nonneg hε.le hJp.le)
  have hint :
      (∫ z : ℝ,
        ((Polynomial.C A * P).eval z - activeBSProfile r P
          (((j.val : ℝ) + 1) /
            ((localWeightActiveSet n q (δ n) t).card : ℝ)) z) ^ 2
          ∂gaussianReal 0 1) = (A - B) ^ 2 * J := by
    have hfun : (fun z : ℝ =>
        ((Polynomial.C A * P).eval z - activeBSProfile r P
          (((j.val : ℝ) + 1) /
            ((localWeightActiveSet n q (δ n) t).card : ℝ)) z) ^ 2) =
        (fun z : ℝ => (A - B) ^ 2 * (P.eval z) ^ 2) := by
      funext z
      simp only [Polynomial.eval_mul, Polynomial.eval_C, activeBSProfile, B]
      ring
    rw [hfun, integral_const_mul]
  change (∫ z : ℝ,
      ((Polynomial.C A * P).eval z - activeBSProfile r P
        (((j.val : ℝ) + 1) /
          ((localWeightActiveSet n q (δ n) t).card : ℝ)) z) ^ 2
        ∂gaussianReal 0 1) ≤ ε
  rw [hint]
  calc
    (A - B) ^ 2 * J ≤ (ε / (J + 1)) * J :=
      mul_le_mul_of_nonneg_right hsq hJ
    _ ≤ ε := by
      apply le_of_lt
      rw [div_mul_eq_mul_div, div_lt_iff₀ hJp]
      nlinarith

end Hurst
