import Hurst.MomentPartitions
import Hurst.GaussianFiniteMoments

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Hurst

theorem integrable_finite_product_of_memLp {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ι → Ω → ℝ)
    (hY : ∀ i,MemLp (Y i) (Fintype.card ι) P) :
    Integrable (fun ω => ∏ i,Y i ω) P := by
  classical
  have hm : MemLp (fun ω => ∑ i,‖Y i ω‖) (Fintype.card ι) P :=
    memLp_finsetSum _ (fun i _ => (hY i).norm)
  have hi := hm.integrable_norm_pow'
  apply hi.mono'
  · exact Finset.aestronglyMeasurable_fun_prod Finset.univ (fun i _ => (hY i).1)
  filter_upwards [] with ω
  rw [Real.norm_eq_abs,Finset.abs_prod]
  have hs : 0≤∑ i,‖Y i ω‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  rw [Real.norm_eq_abs,abs_of_nonneg hs]
  calc
    (∏ i,|Y i ω|) ≤ ∏ _i : ι,(∑ j,‖Y j ω‖) := by
      apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
      intro i _
      simpa only [Real.norm_eq_abs] using Finset.single_le_sum (fun j _ => norm_nonneg (Y j ω)) (Finset.mem_univ i)
    _ = _ := by simp

theorem moment_sum_le_distinct_patterns {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ι → Ω → ℝ) (m : ℕ)
    (hY : ∀ i,MemLp (Y i) m P) :
    (∫ ω,(∑ i,Y i ω)^m ∂P) ≤
      ∑ q : MomentPattern m,∑ g : Fin q.1.val ↪ ι,
        |∫ ω,∏ j : Fin q.1.val,(Y (g j) ω)^momentMultiplicity q j ∂P| := by
  classical
  have hi : ∀ t : Fin m → ι,Integrable (fun ω => ∏ j : Fin m,Y (t j) ω) P := by
    intro t
    apply integrable_finite_product_of_memLp
    intro j
    simpa only [Fintype.card_fin] using hY (t j)
  simp_rw [Fintype.sum_pow]
  rw [integral_finsetSum Finset.univ (fun t _ => hi t)]
  calc
    _ ≤ ∑ t : Fin m → ι,|∫ ω,∏ j : Fin m,Y (t j) ω ∂P| :=
      Finset.sum_le_sum (fun t _ => le_abs_self _)
    _ ≤ ∑ z : MomentRealization m ι,|∫ ω,∏ j : Fin m,Y (momentRealizationTuple z j) ω ∂P| :=
      moment_tuple_sum_le_realizations _ (fun _ => abs_nonneg _)
    _ = _ := by
      change (∑ z : Σ q : MomentPattern m, Fin q.1.val ↪ ι,
          |∫ ω, ∏ j : Fin m, Y (momentRealizationTuple z j) ω ∂P|) = _
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro g _
      congr 1
      apply integral_congr_ae
      filter_upwards [] with ω
      exact @momentRealization_product m ι ℝ _ ⟨q, g⟩ (fun i => Y i ω)

theorem moment_sum_bound_of_distinct_pattern_bounds {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ι → Ω → ℝ) (m : ℕ)
    (hY : ∀ i,MemLp (Y i) m P) (C : MomentPattern m → ℝ) (B : ℝ)
    (hC : ∀ q : MomentPattern m,
      (∑ g : Fin q.1.val ↪ ι,|∫ ω,∏ j : Fin q.1.val,(Y (g j) ω)^momentMultiplicity q j ∂P|)≤C q*B) :
    (∫ ω,(∑ i,Y i ω)^m ∂P)≤(∑ q : MomentPattern m,C q)*B := by
  calc
    _ ≤ _ := moment_sum_le_distinct_patterns P Y m hY
    _ ≤ ∑ q : MomentPattern m,C q*B := Finset.sum_le_sum (fun q _ => hC q)
    _ = _ := (Finset.sum_mul _ _ _).symm

theorem momentMultiplicity_exponent_le {k : ℕ} (q : MomentPattern (2*k)) :
    (q.1.val:ℝ)-(Finset.univ.filter (fun j => momentMultiplicity q j=1)).card/2≤k := by
  have hh := momentMultiplicity_singletons_bound q
  have hh' : (2:ℝ)*q.1.val ≤ 2*k + (Finset.univ.filter (fun j => momentMultiplicity q j=1)).card := by
    exact_mod_cast hh
  linarith

end Hurst
