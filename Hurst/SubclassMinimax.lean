import Hurst.MinimaxLower

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal Topology
namespace Hurst

def subclassHurstExperiment (p M σ : ℝ) (n : ℕ) (F : Set (HurstParameter p M)) :
    Kernel F (EuclideanSpace ℝ (Fin n)) := (hurstExperiment p M σ n).comap Subtype.val measurable_subtype_coe

instance subclassHurstExperiment_isMarkov (p M σ : ℝ) (n : ℕ) (F : Set (HurstParameter p M)) :
    IsMarkovKernel (subclassHurstExperiment p M σ n F) := by unfold subclassHurstExperiment; infer_instance

def subclassHurstTarget (s : {s : ℝ // 1 ≤ s}) {p M : ℝ} (hp : 1 ≤ p) (F : Set (HurstParameter p M)) :
    F → HurstDecision s := fun H => hurstTarget s hp H.val

def subclassHurstTailRisk (s : {s : ℝ // 1 ≤ s}) (p M σ : ℝ) (hp : 1 ≤ p) (n : ℕ)
    (F : Set (HurstParameter p M)) (r : ℝ≥0∞) : ℝ≥0∞ :=
  minimaxRiskDist (tailLoss r) (subclassHurstTarget s hp F) (subclassHurstExperiment p M σ n F)

/-- Finite-sample lower bound for the actual Hurst experiment, with the constructed code and no abstract model premise. -/
theorem hurst_minimax_subclass_finite_code (s : {s : ℝ // 1 ≤ s}) (p M : ℝ) (hp : 1 ≤ p) (F : Set (HurstParameter p M)) :
    ∃ A > 0, ∃ D > 0, ∃ c₀ > 0, ∃ b₀ > 0, ∃ C > 0,
      ∀ n : ℕ, 0 < n → ∀ m : ℕ, 0 < m → ∀ ε : ℝ, 0 ≤ ε →
      ∀ S : Finset (Fin m → Bool), 2 ≤ S.card →
      (∀ θ ∈ S, bumpAlternative m p ε (booleanBumpWeights θ) ∈ hurstHolderClass p M) →
      (∀ θ ∈ S, ∀ hθ : bumpAlternative m p ε (booleanBumpWeights θ) ∈ hurstHolderClass p M,
        bumpHurstParameter p M ε m θ hθ ∈ F) →
      (∀ θ ∈ S, ∀ η ∈ S, θ ≠ η → (m : ℝ) / 8 ≤ (hammingDist θ η : ℝ)) →
      ∀ σ : ℝ, σ ≠ 0 →
      A * ε * (m : ℝ) ^ (-p) * Real.log (2 * (n : ℝ)) ≤ c₀ →
      D * ε * (m : ℝ) ^ (1 - p) ≤ b₀ →
      ∀ (Φ : ℝ≥0∞ → ℝ≥0∞), Monotone Φ → ∀ δ : ℝ≥0∞,
      2 * δ ≤ ENNReal.ofReal (((∫ x : ℝ, |correctedBump x| ^ s.val) / 8) ^ s.val⁻¹ * ε * (m : ℝ) ^ (-p)) →
      Φ δ * (1 - (ENNReal.ofReal (C * ε ^ 2 * ((n : ℝ) * (m : ℝ) ^ (-2 * p) + (m : ℝ) ^ (2 - 2 * p)) *
          Real.log (2 * (n : ℝ)) ^ 2) + ENNReal.ofReal (Real.log 2)) / ENNReal.ofReal (Real.log (S.card : ℝ))) ≤
        minimaxRiskDist Φ (subclassHurstTarget s hp F) (subclassHurstExperiment p M σ n F) := by
  classical
  obtain ⟨A, hA, D, hD, c₀, hc₀, b₀, hb₀, C, hC, hk⟩ := bumpAlternative_klDiv_rate
  refine ⟨A, hA, D, hD, c₀, hc₀, b₀, hb₀, C, hC, ?_⟩
  intro n hn m hm ε hε S hS hclass hbelongs hsep σ hσ hsmall hB Φ hΦ δ hδ
  letI : NeZero S.card := ⟨by omega⟩
  let e : Fin S.card ≃ S := (Fintype.equivFinOfCardEq (by simp : Fintype.card S = S.card)).symm
  let θfam : Fin S.card → F := fun j =>
    ⟨bumpHurstParameter p M ε m (e j).val (hclass _ (e j).property), hbelongs _ (e j).property _⟩
  have hθ : Measurable θfam := measurable_of_countable _
  let R := scaledHarmonizableGaussian σ (fun _ : Fin n => brownianHurst) (fun i => grid n i.val)
  haveI : IsProbabilityMeasure R := by unfold R scaledHarmonizableGaussian; infer_instance
  refine minimax_subfamily_reference (subclassHurstExperiment p M σ n F) θfam hθ R _ ?_ hS Φ hΦ (subclassHurstTarget s hp F) δ ?_
  · intro j
    exact hk n hn m hm p ε hε (booleanBumpWeights (e j).val) (booleanBumpWeights_bound _)
      (hclass _ (e j).property).1 σ hσ hsmall hB
  · intro j k hjk
    have he : (e j).val ≠ (e k).val := fun h => hjk (e.injective (Subtype.ext h))
    exact hδ.trans (bumpAlternative_distance_separation s m hm p ε hε _ _
      (hsep _ (e j).property _ (e k).property he))

/-- The actual minimax probability lower bound, uniformly in a nonzero common scale, including p=1. -/
theorem hurst_minimax_subclass_lower_eventually (s : {s : ℝ // 1 ≤ s}) (p M γ : ℝ)
    (hp : 1 ≤ p) (hM : 0 < M) (hγ : 0 < γ) (hγ1 : γ < 1)
    (F : Set (HurstParameter p M))
    (hF : ∃ εF > 0, ∀ ε : ℝ, 0 ≤ ε → ε ≤ εF → ∀ m : ℕ, 0 < m → ∀ θ : Fin m → Bool,
      ∀ hθ : bumpAlternative m p ε (booleanBumpWeights θ) ∈ hurstHolderClass p M,
        bumpHurstParameter p M ε m θ hθ ∈ F) :
    ∃ δ > 0, ∀ᶠ n : ℕ in atTop, ∀ σ : ℝ, σ ≠ 0 →
      ENNReal.ofReal ((1 + γ) / 2) ≤
        subclassHurstTailRisk s p M σ hp n F (ENNReal.ofReal (δ * lowerBoundRate p n)) := by
  classical
  obtain ⟨A, hA, D, hD, c₀, hc₀, b₀, hb₀, C, hC, hk⟩ := hurst_minimax_subclass_finite_code s p M hp F
  obtain ⟨ε₀, hε₀, hclass⟩ := bumpAlternative_mem_hurstHolderClass p M hp hM
  obtain ⟨c, hc, hcode⟩ := binary_code_packing
  obtain ⟨εF, hεF, hclassF⟩ := hF
  let τ := (1 - γ) / 4
  have hτ : 0 < τ := by dsimp [τ]; linarith
  obtain ⟨ε, hε, hεboth, hεD, hεC⟩ := minimax_amplitude_choice (min ε₀ εF) D b₀ C c τ (lt_min hε₀ hεF) hD hb₀ hC hc hτ
  have hεclass : ε ≤ ε₀ := hεboth.trans (min_le_left _ _)
  have hεsubclass : ε ≤ εF := hεboth.trans (min_le_right _ _)
  let d := ((∫ x : ℝ, |correctedBump x| ^ s.val) / 8) ^ s.val⁻¹
  have hs : 0 < s.val := lt_of_lt_of_le zero_lt_one s.property
  have hI := correctedBump_power_integral_pos s.val hs
  have hd : 0 < d := by dsimp [d]; positivity
  let δ := d * ε * (2 : ℝ) ^ (-p) / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, ?_⟩
  have hamp : ∀ᶠ n : ℕ in atTop,
      A * ε * (packingResolution p n : ℝ) ^ (-p) * Real.log (2 * (n : ℝ)) ≤ c₀ := by
    have ht := (packingResolution_amplitude_log_tendsto p hp).const_mul (A * ε)
    simp only [mul_zero] at ht
    simpa only [mul_assoc] using ht.eventually_le_const hc₀
  have hderiv : ∀ᶠ n : ℕ in atTop,
      (packingResolution p n : ℝ) ^ (1 - 2 * p) * Real.log (2 * (n : ℝ)) ^ 2 ≤ 1 :=
    (packingResolution_derivative_entropy_tendsto p hp).eventually_le_const zero_lt_one
  have hlog : ∀ᶠ n : ℕ in atTop, Real.log 2 ≤ c * τ * (packingResolution p n : ℝ) := by
    filter_upwards [(packingResolution_tendsto p hp).eventually_ge_atTop (Real.log 2 / (c * τ))] with n hn
    exact (div_le_iff₀ (mul_pos hc hτ)).mp hn |>.trans_eq (by ring)
  filter_upwards [packingResolution_bounds p hp, hamp, hderiv, hlog, eventually_ge_atTop 2] with n hn ha hb hl hn2
  intro σ hσ
  let m := packingResolution p n
  have hm : 0 < m := hn.2.1
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨S, hSnonempty, hScard, hSsep⟩ := hcode m hm
  have hlogS : 0 < Real.log (S.card : ℝ) := (mul_pos hc hmR).trans_le hScard
  have hS : 2 ≤ S.card := by
    have h := (Real.log_pos_iff (by positivity : (0 : ℝ) ≤ S.card)).mp hlogS
    exact_mod_cast (show 1 < S.card from by exact_mod_cast h)
  have hclassS : ∀ θ ∈ S, bumpAlternative m p ε (booleanBumpWeights θ) ∈ hurstHolderClass p M :=
    fun θ _ => hclass ε hε.le hεclass m hm _ (booleanBumpWeights_bound θ)
  have hB : D * ε * (m : ℝ) ^ (1 - p) ≤ b₀ := by
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hb1 := Real.rpow_le_one_of_one_le_of_nonpos hm1 (by linarith : 1 - p ≤ 0)
    exact (mul_le_mul_of_nonneg_left hb1 (by positivity : 0 ≤ D * ε)).trans (by simpa using hεD)
  have hr : 0 < lowerBoundRate p n := by
    unfold lowerBoundRate
    have hnR : (1 : ℝ) < n := by exact_mod_cast hn2
    have hnlog := Real.log_pos hnR
    positivity
  have hsep : 2 * ENNReal.ofReal (2 * (δ * lowerBoundRate p n)) ≤
      ENNReal.ofReal (d * ε * (m : ℝ) ^ (-p)) := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    apply ENNReal.ofReal_le_ofReal
    have he := mul_le_mul_of_nonneg_left hn.2.2.2.2.2 (by positivity : 0 ≤ d * ε)
    dsimp [δ]
    nlinarith
  have hbound := hk n hn.1 m hm ε hε.le S hS hclassS
    (fun θ _ hθ => hclassF ε hε.le hεsubclass m hm θ hθ)
    (fun θ hθ η hη hneq => (hSsep θ hθ η hη hneq).le) σ hσ ha hB
    (tailLoss (ENNReal.ofReal (δ * lowerBoundRate p n))) (tailLoss_monotone _)
    (ENNReal.ofReal (2 * (δ * lowerBoundRate p n))) hsep
  rw [positive_tailLoss _ (mul_pos hδ hr), one_mul] at hbound
  apply le_trans _ hbound
  apply real_fano_fraction_bound _ _ _ (by positivity) hlogS (by linarith) (by linarith)
  have hfactor := packing_kl_factor_bound m hm n p hn.2.2.2.2.1 hb
  have hK : C * ε ^ 2 * ((n : ℝ) * (m : ℝ) ^ (-2 * p) + (m : ℝ) ^ (2 - 2 * p)) *
      Real.log (2 * (n : ℝ)) ^ 2 ≤ c * τ * m := by
    calc
      _ = C * ε ^ 2 * (((n : ℝ) * (m : ℝ) ^ (-2 * p) + (m : ℝ) ^ (2 - 2 * p)) *
        Real.log (2 * (n : ℝ)) ^ 2) := by ring
      _ ≤ C * ε ^ 2 * (5 * m) := mul_le_mul_of_nonneg_left hfactor (by positivity)
      _ ≤ c * τ * m := by nlinarith [mul_le_mul_of_nonneg_right hεC hmR.le]
  have hcard := mul_le_mul_of_nonneg_left hScard (show 0 ≤ 1 - (1 + γ) / 2 by linarith)
  dsimp [τ] at hK hl
  nlinarith


/-- The fixed value-range class used in the matching upper-bound proofs. -/
def fixedRangeHurstClass (p M η hstar : ℝ) : Set (HurstParameter p M) :=
  {H | ∀ x ∈ Ioo (0 : ℝ) 1, η ≤ H.value x ∧ H.value x ≤ hstar}

theorem fixedRange_bump_inclusion (p M η hstar : ℝ) (hp : 1 ≤ p)
    (hη : η < 1 / 2) (hupper : 1 / 2 < hstar) :
    ∃ εF > 0, ∀ ε : ℝ, 0 ≤ ε → ε ≤ εF → ∀ m : ℕ, 0 < m → ∀ θ : Fin m → Bool,
      ∀ hθ : bumpAlternative m p ε (booleanBumpWeights θ) ∈ hurstHolderClass p M,
        bumpHurstParameter p M ε m θ hθ ∈ fixedRangeHurstClass p M η hstar := by
  obtain ⟨A, hA, ha⟩ := bumpAlternative_amplitude_bound
  let εF := min ((1 / 2 - η) / (A + 1)) ((hstar - 1 / 2) / (A + 1))
  have heF : 0 < εF := by dsimp [εF]; positivity
  refine ⟨εF, heF, ?_⟩
  intro ε hε he m hm θ hθ x hx
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpow := Real.rpow_le_one_of_one_le_of_nonpos hmR (show -p ≤ 0 by linarith)
  have he1 : ε * (A + 1) ≤ 1 / 2 - η :=
    (le_div_iff₀ (by positivity : 0 < A + 1)).mp (he.trans (min_le_left _ _))
  have he2 : ε * (A + 1) ≤ hstar - 1 / 2 :=
    (le_div_iff₀ (by positivity : 0 < A + 1)).mp (he.trans (min_le_right _ _))
  have hab := (ha m p ε hε (booleanBumpWeights θ) (booleanBumpWeights_bound θ) x).trans
    (mul_le_mul_of_nonneg_left hpow (mul_nonneg hA hε))
  rw [mul_one] at hab
  have hlow := (abs_le.mp hab).1
  have hhigh := (abs_le.mp hab).2
  change η ≤ bumpAlternative m p ε (booleanBumpWeights θ) x ∧
    bumpAlternative m p ε (booleanBumpWeights θ) x ≤ hstar
  constructor <;> nlinarith

/-- The lower bound on the same fixed value-range class as files 18 and 20, including p=1. -/
theorem fixedRange_minimax_lower_liminf (s : {s : ℝ // 1 ≤ s}) (p M η hstar γ : ℝ)
    (hp : 1 ≤ p) (hM : 0 < M) (hη : η < 1 / 2) (hupper : 1 / 2 < hstar)
    (hγ : 0 < γ) (hγ1 : γ < 1) :
    ∃ δ > 0, ∀ σ : ℝ, σ ≠ 0 → ENNReal.ofReal γ <
      liminf (fun n => subclassHurstTailRisk s p M σ hp n (fixedRangeHurstClass p M η hstar)
        (ENNReal.ofReal (δ * lowerBoundRate p n))) atTop := by
  obtain ⟨δ, hδ, h⟩ := hurst_minimax_subclass_lower_eventually s p M γ hp hM hγ hγ1
    (fixedRangeHurstClass p M η hstar) (fixedRange_bump_inclusion p M η hstar hp hη hupper)
  refine ⟨δ, hδ, ?_⟩
  intro σ hσ
  have he : ENNReal.ofReal ((1 + γ) / 2) ≤
      liminf (fun n => subclassHurstTailRisk s p M σ hp n (fixedRangeHurstClass p M η hstar)
        (ENNReal.ofReal (δ * lowerBoundRate p n))) atTop :=
    le_liminf_of_le (by isBoundedDefault) (h.mono fun n hn => hn σ hσ)
  apply lt_of_lt_of_le _ he
  exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)

end Hurst
