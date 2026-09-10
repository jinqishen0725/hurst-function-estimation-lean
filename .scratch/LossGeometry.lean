import Hurst.HurstPacking
import Hurst.GaussianFano
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

noncomputable section
open Set MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
namespace Hurst

/-- All almost everywhere strongly measurable decisions, allowing infinite Ls error. -/
structure HurstDecision (s : {s : ℝ // 1 ≤ s}) where
  value : ℝ → ℝ
  measurable : AEStronglyMeasurable value (volume.restrict (Ioo (0 : ℝ) 1))

instance (s : {s : ℝ // 1 ≤ s}) : PseudoEMetricSpace (HurstDecision s) :=
  PseudoEMetricSpace.ofEDist
    (fun f g => eLpNorm (f.value - g.value) (ENNReal.ofReal s.val) (volume.restrict (Ioo (0 : ℝ) 1)))
    (fun f => by simp)
    (fun f g => eLpNorm_sub_comm _ _ _ _)
    (fun f g h => by
      have he : f.value - h.value = (f.value - g.value) + (g.value - h.value) := by ext x; simp
      rw [he]
      exact eLpNorm_add_le (f.measurable.sub g.measurable) (g.measurable.sub h.measurable)
        (by exact_mod_cast (ENNReal.ofReal_le_ofReal s.property)))

instance (s : {s : ℝ // 1 ≤ s}) : MeasurableSpace (HurstDecision s) := borel _
instance (s : {s : ℝ // 1 ≤ s}) : BorelSpace (HurstDecision s) := ⟨rfl⟩

def continuousHurstDecision (s : {s : ℝ // 1 ≤ s}) (f : ℝ → ℝ) (hf : Continuous f) : HurstDecision s :=
  ⟨f, hf.aestronglyMeasurable⟩

theorem hurstDecision_edist (s : {s : ℝ // 1 ≤ s}) (f g : HurstDecision s) :
    edist f g = eLpNorm (f.value - g.value) (ENNReal.ofReal s.val)
      (volume.restrict (Ioo (0 : ℝ) 1)) := rfl

/-- An actual reference-law Fano bound for a subfamily of an arbitrary experiment. -/
theorem minimax_subfamily_reference {Θ Ω X : Type*}
    [MeasurableSpace Θ] [MeasurableSpace Ω] [MeasurableSpace X]
    [PseudoEMetricSpace Ω] [OpensMeasurableSpace Ω] {M : ℕ} [NeZero M]
    (P : Kernel Θ X) [IsMarkovKernel P] (θfam : Fin M → Θ) (hθ : Measurable θfam)
    (R : Measure X) [IsProbabilityMeasure R] (K : ℝ≥0∞)
    (hK : ∀ j, klDiv (P (θfam j)) R ≤ K) (hM : 2 ≤ M)
    (Φ : ℝ≥0∞ → ℝ≥0∞) (hΦ : Monotone Φ) (g : Θ → Ω) (δ : ℝ≥0∞)
    (hsep : IsSeparatedFamily g θfam δ) :
    Φ δ * (1 - (K + ENNReal.ofReal (Real.log 2)) / ENNReal.ofReal (Real.log (M : ℝ))) ≤
      minimaxRiskDist Φ g P := by
  have hi : mutualInformation (P.comap θfam hθ) ≤ K :=
    mutualInformation_le_of_reference_bound _ R K hK
  have ht := fano_inequality (P.comap θfam hθ) hM
  have hg := minimax_ge_testing_error Φ g P θfam hθ δ hΦ hsep
  apply le_trans _ hg
  apply mul_le_mul_right _ (Φ δ)
  apply le_trans _ ht
  gcongr

/-- Continuous functions on the unit interval have finite Ls norm for each finite exponent. -/
theorem continuous_memLp_unit (f : ℝ → ℝ) (hf : Continuous f) (q : ℝ≥0∞) :
    MemLp f q (volume.restrict (Ioo (0 : ℝ) 1)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact hC x ⟨hx.1.le, hx.2.le⟩

theorem continuousHurstDecision_distance_integral (s : {s : ℝ // 1 ≤ s})
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    edist (continuousHurstDecision s f hf) (continuousHurstDecision s g hg) =
      ENNReal.ofReal ((∫ x in Ioo (0 : ℝ) 1, |f x - g x| ^ s.val) ^ s.val⁻¹) := by
  have hs : 0 < s.val := lt_of_lt_of_le zero_lt_one s.property
  have h := (continuous_memLp_unit (f - g) (hf.sub hg) (ENNReal.ofReal s.val)).eLpNorm_eq_integral_rpow_norm
    (by positivity) (by simp)
  simpa only [hurstDecision_edist, continuousHurstDecision, ENNReal.toReal_ofReal hs.le,
    Real.norm_eq_abs, Pi.sub_apply] using h

theorem bumpAlternative_distance_separation (s : {s : ℝ // 1 ≤ s})
    (m : ℕ) (hm : 0 < m) (p ε : ℝ) (hε : 0 ≤ ε) (θ η : Fin m → Bool)
    (hsep : (m : ℝ) / 8 ≤ (hammingDist θ η : ℝ)) :
    ENNReal.ofReal (((∫ x : ℝ, |correctedBump x| ^ s.val) / 8) ^ s.val⁻¹ * ε * (m : ℝ) ^ (-p)) ≤
      edist (continuousHurstDecision s (bumpAlternative m p ε (booleanBumpWeights θ))
        (bumpAlternative_smooth m p ε _).continuous)
        (continuousHurstDecision s (bumpAlternative m p ε (booleanBumpWeights η))
        (bumpAlternative_smooth m p ε _).continuous) := by
  have hs : 0 < s.val := lt_of_lt_of_le zero_lt_one s.property
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hI := correctedBump_power_integral_pos s.val hs
  rw [continuousHurstDecision_distance_integral]
  apply ENNReal.ofReal_le_ofReal
  have he := Real.rpow_le_rpow (by positivity)
    (bumpAlternative_boolean_loss_separation m hm p ε s.val hε hs θ η hsep)
    (inv_nonneg.mpr hs.le)
  have hp : ((m : ℝ) ^ (-p * s.val)) ^ s.val⁻¹ = (m : ℝ) ^ (-p) := by
    rw [← Real.rpow_mul hmR.le]
    congr 1
    field_simp
  simpa only [Real.mul_rpow (by positivity : 0 ≤ (∫ x : ℝ, |correctedBump x| ^ s.val) / 8 * ε ^ s.val)
    (Real.rpow_nonneg hmR.le _), Real.mul_rpow (by positivity : 0 ≤ (∫ x : ℝ, |correctedBump x| ^ s.val) / 8)
    (Real.rpow_nonneg hε _), Real.rpow_rpow_inv hε hs.ne', hp] using he

end Hurst
