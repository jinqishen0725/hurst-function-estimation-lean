import Hurst.GaussianFiniteMoments

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Hurst

theorem centered_linear_combination_evenMoment_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (a b : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hX : Integrable X P) (hY : Integrable Y P)
    (hXp : Integrable (fun x => |X x - ∫ y, X y ∂P| ^ (2 * k)) P)
    (hYp : Integrable (fun x => |Y x - ∫ y, Y y ∂P| ^ (2 * k)) P) :
    (∫ x, |(a * X x + b * Y x) -
        (∫ y, a * X y + b * Y y ∂P)| ^ (2 * k) ∂P) ≤
      2 ^ (2 * k - 1) *
        (|a| ^ (2 * k) * (∫ x, |X x - ∫ y, X y ∂P| ^ (2 * k) ∂P) +
         |b| ^ (2 * k) * (∫ x, |Y x - ∫ y, Y y ∂P| ^ (2 * k) ∂P)) := by
  have hcenter : (∫ y, a * X y + b * Y y ∂P) =
      a * (∫ y, X y ∂P) + b * (∫ y, Y y ∂P) := by
    rw [integral_add (hX.const_mul a) (hY.const_mul b),
      integral_const_mul, integral_const_mul]
  rw [hcenter]
  let F : Ω → ℝ := fun x =>
    |(a * X x + b * Y x) -
      (a * (∫ y, X y ∂P) + b * (∫ y, Y y ∂P))| ^ (2 * k)
  let G : Ω → ℝ := fun x => 2 ^ (2 * k - 1) *
    (|a| ^ (2 * k) * |X x - ∫ y, X y ∂P| ^ (2 * k) +
     |b| ^ (2 * k) * |Y x - ∫ y, Y y ∂P| ^ (2 * k))
  have hG : Integrable G P := by
    dsimp only [G]
    exact ((hXp.const_mul (|a| ^ (2 * k))).add
      (hYp.const_mul (|b| ^ (2 * k)))).const_mul (2 ^ (2 * k - 1))
  have hpoint : ∀ x, F x ≤ G x := by
    intro x
    let U := a * (X x - ∫ y, X y ∂P)
    let V := b * (Y x - ∫ y, Y y ∂P)
    have huv : |U + V| ≤ |U| + |V| := abs_add_le U V
    calc
      F x = |U + V| ^ (2 * k) := by dsimp only [F, U, V]; congr 1 <;> ring
      _ ≤ (|U| + |V|) ^ (2 * k) := pow_le_pow_left₀ (abs_nonneg _) huv _
      _ ≤ 2 ^ (2 * k - 1) * (|U| ^ (2 * k) + |V| ^ (2 * k)) :=
        add_pow_le (abs_nonneg U) (abs_nonneg V) _
      _ = G x := by dsimp only [G, U, V]; simp only [abs_mul, mul_pow]
  have hF : Integrable F P := hG.mono'
    (by dsimp only [F]; fun_prop)
    (Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
      exact hpoint x))
  exact (integral_mono hF hG hpoint).trans_eq (by
    dsimp only [G]
    rw [integral_const_mul, integral_add
      (hXp.const_mul (|a| ^ (2 * k))) (hYp.const_mul (|b| ^ (2 * k))),
      integral_const_mul, integral_const_mul])

theorem evenMoment_le_centered_add_bias
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (θ : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hX : Integrable X P)
    (hXp : Integrable (fun x => |X x - ∫ y, X y ∂P| ^ (2 * k)) P) :
    (∫ x, |X x - θ| ^ (2 * k) ∂P) ≤
      2 ^ (2 * k - 1) *
        ((∫ x, |X x - ∫ y, X y ∂P| ^ (2 * k) ∂P) +
          |(∫ y, X y ∂P) - θ| ^ (2 * k)) := by
  let F : Ω → ℝ := fun x => |X x - θ| ^ (2 * k)
  let G : Ω → ℝ := fun x => 2 ^ (2 * k - 1) *
    (|X x - ∫ y, X y ∂P| ^ (2 * k) + |(∫ y, X y ∂P) - θ| ^ (2 * k))
  have hpoint : ∀ x, F x ≤ G x := by
    intro x
    let U := X x - ∫ y, X y ∂P
    let V := (∫ y, X y ∂P) - θ
    have huv : |U + V| ≤ |U| + |V| := abs_add_le U V
    calc
      F x = |U + V| ^ (2 * k) := by dsimp only [F, U, V]; congr 1 <;> ring
      _ ≤ (|U| + |V|) ^ (2 * k) := pow_le_pow_left₀ (abs_nonneg _) huv _
      _ ≤ 2 ^ (2 * k - 1) * (|U| ^ (2 * k) + |V| ^ (2 * k)) :=
        add_pow_le (abs_nonneg U) (abs_nonneg V) _
      _ = G x := rfl
  have hG : Integrable G P := by
    dsimp only [G]
    exact (hXp.add (integrable_const _)).const_mul _
  have hF : Integrable F P := hG.mono'
    (by
      dsimp only [F]
      exact (hX.sub (integrable_const _)).aestronglyMeasurable.norm.pow (2 * k))
    (Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
      exact hpoint x))
  exact (integral_mono hF hG hpoint).trans_eq (by
    dsimp only [G]
    rw [integral_const_mul, integral_add hXp (integrable_const _), integral_const]
    simp)

theorem evenPower_about_integrable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (X : Ω → ℝ) (θ : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hX : Integrable X P)
    (hXp : Integrable (fun x => |X x - ∫ y, X y ∂P| ^ (2 * k)) P) :
    Integrable (fun x => |X x - θ| ^ (2 * k)) P := by
  let G : Ω → ℝ := fun x => 2 ^ (2 * k - 1) *
    (|X x - ∫ y, X y ∂P| ^ (2 * k) + |(∫ y, X y ∂P) - θ| ^ (2 * k))
  have hG : Integrable G P := by
    dsimp only [G]
    exact (hXp.add (integrable_const _)).const_mul _
  apply hG.mono'
  · exact (hX.sub (integrable_const _)).aestronglyMeasurable.norm.pow (2 * k)
  · filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
    let U := X x - ∫ y, X y ∂P
    let V := (∫ y, X y ∂P) - θ
    have huv : |U + V| ≤ |U| + |V| := abs_add_le U V
    calc
      |X x - θ| ^ (2 * k) = |U + V| ^ (2 * k) := by
        dsimp only [U, V]
        congr 1 <;> ring
      _ ≤ (|U| + |V|) ^ (2 * k) := pow_le_pow_left₀ (abs_nonneg _) huv _
      _ ≤ 2 ^ (2 * k - 1) * (|U| ^ (2 * k) + |V| ^ (2 * k)) :=
        add_pow_le (abs_nonneg U) (abs_nonneg V) _
      _ = G x := rfl

theorem evenMoment_add_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X Y : Ω → ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hXm : AEStronglyMeasurable X P) (hYm : AEStronglyMeasurable Y P)
    (hXi : Integrable (fun x => |X x| ^ (2 * k)) P)
    (hYi : Integrable (fun x => |Y x| ^ (2 * k)) P) :
    (∫ x, |X x + Y x| ^ (2 * k) ∂P) ≤
      2 ^ (2 * k - 1) *
        ((∫ x, |X x| ^ (2 * k) ∂P) + (∫ x, |Y x| ^ (2 * k) ∂P)) := by
  let G : Ω → ℝ := fun x => 2 ^ (2 * k - 1) *
    (|X x| ^ (2 * k) + |Y x| ^ (2 * k))
  have hG : Integrable G P := by
    dsimp only [G]
    exact (hXi.add hYi).const_mul _
  have hpoint : ∀ x, |X x + Y x| ^ (2 * k) ≤ G x := by
    intro x
    calc
      |X x + Y x| ^ (2 * k) ≤ (|X x| + |Y x|) ^ (2 * k) :=
        pow_le_pow_left₀ (abs_nonneg _) (abs_add_le _ _) _
      _ ≤ 2 ^ (2 * k - 1) * (|X x| ^ (2 * k) + |Y x| ^ (2 * k)) :=
        add_pow_le (abs_nonneg _) (abs_nonneg _) _
      _ = G x := rfl
  have hleft : Integrable (fun x => |X x + Y x| ^ (2 * k)) P := by
    apply hG.mono'
    · exact (hXm.add hYm).norm.pow (2 * k)
    · filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
      exact hpoint x
  exact (integral_mono hleft hG hpoint).trans_eq (by
      dsimp only [G]
      rw [integral_const_mul, integral_add hXi hYi])

theorem finite_average_abs_even_pow_le (m : ℕ) (hm : 0 < m)
    (x : Fin m → ℝ) (k : ℕ) (hk : 1 ≤ k) :
    |(∑ i, x i) / (m : ℝ)| ^ (2 * k) ≤
      (∑ i, |x i| ^ (2 * k)) / (m : ℝ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have habs := Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := x)
  have hp := pow_le_pow_left₀ (abs_nonneg _) habs (2 * k)
  have hsum := pow_sum_le_card_mul_sum_pow
    (s := Finset.univ) (f := fun i : Fin m => |x i|)
    (fun _ _ => abs_nonneg _) (2 * k - 1)
  have h2k : 2 * k - 1 + 1 = 2 * k := by omega
  simp only [h2k, Finset.card_univ, Fintype.card_fin] at hsum
  rw [abs_div, abs_of_pos hmR, div_pow]
  apply (div_le_iff₀ (pow_pos hmR _)).mpr
  calc
    |∑ i, x i| ^ (2 * k) ≤ (∑ i, |x i|) ^ (2 * k) := hp
    _ ≤ (m : ℝ) ^ (2 * k - 1) * ∑ i, |x i| ^ (2 * k) := hsum
    _ = ((∑ i, |x i| ^ (2 * k)) / (m : ℝ)) * (m : ℝ) ^ (2 * k) := by
      have hpow : (m : ℝ) ^ (2 * k) = (m : ℝ) ^ (2 * k - 1) * (m : ℝ) := by
        rw [← pow_succ, h2k]
      rw [hpow]
      field_simp

theorem finite_average_evenPower_integrable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (m : ℕ) (hm : 0 < m) (X : Fin m → Ω → ℝ)
    (k : ℕ) (hk : 1 ≤ k)
    (hXm : ∀ i, AEStronglyMeasurable (X i) P)
    (hXi : ∀ i, Integrable (fun x => |X i x| ^ (2 * k)) P) :
    Integrable (fun x => |(∑ i, X i x) / (m : ℝ)| ^ (2 * k)) P := by
  let G : Ω → ℝ := fun x => (∑ i, |X i x| ^ (2 * k)) / (m : ℝ)
  have hG : Integrable G P := by
    dsimp only [G]
    exact (integrable_finsetSum _ (fun i _ => hXi i)).div_const _
  apply hG.mono'
  · change AEStronglyMeasurable
      ((fun x => |(∑ i, X i x) / (m : ℝ)|) ^ (2 * k)) P
    have hs := Finset.aestronglyMeasurable_sum Finset.univ (fun i _ => hXm i)
    have hd := hs.const_mul ((m : ℝ)⁻¹)
    simpa only [div_eq_mul_inv, mul_comm, Real.norm_eq_abs, Finset.sum_apply,
      Pi.pow_apply] using hd.norm.pow (2 * k)
  · filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
    exact finite_average_abs_even_pow_le m hm (fun i => X i x) k hk

theorem finite_average_evenMoment_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (m : ℕ) (hm : 0 < m) (X : Fin m → Ω → ℝ)
    (k : ℕ) (hk : 1 ≤ k) (R : ℝ)
    (hXm : ∀ i, AEStronglyMeasurable (X i) P)
    (hXi : ∀ i, Integrable (fun x => |X i x| ^ (2 * k)) P)
    (hR : ∀ i, (∫ x, |X i x| ^ (2 * k) ∂P) ≤ R) :
    (∫ x, |(∑ i, X i x) / (m : ℝ)| ^ (2 * k) ∂P) ≤ R := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  let G : Ω → ℝ := fun x => (∑ i, |X i x| ^ (2 * k)) / (m : ℝ)
  have hG : Integrable G P := by
    dsimp only [G]
    exact (integrable_finsetSum _ (fun i _ => hXi i)).div_const _
  have hleftm : AEStronglyMeasurable
      (fun x => |(∑ i, X i x) / (m : ℝ)| ^ (2 * k)) P := by
    change AEStronglyMeasurable
      ((fun x => |(∑ i, X i x) / (m : ℝ)|) ^ (2 * k)) P
    have hs := Finset.aestronglyMeasurable_sum Finset.univ (fun i _ => hXm i)
    have hd := hs.const_mul ((m : ℝ)⁻¹)
    simpa only [div_eq_mul_inv, mul_comm, Real.norm_eq_abs, Finset.sum_apply,
      Pi.pow_apply] using hd.norm.pow (2 * k)
  have hleft : Integrable (fun x => |(∑ i, X i x) / (m : ℝ)| ^ (2 * k)) P :=
    hG.mono' hleftm (Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
      exact finite_average_abs_even_pow_le m hm (fun i => X i x) k hk))
  have hi := integral_mono hleft hG
    (fun x => finite_average_abs_even_pow_le m hm (fun i => X i x) k hk)
  apply hi.trans
  dsimp only [G]
  rw [integral_div, integral_finsetSum _ (fun i _ => hXi i)]
  apply (div_le_iff₀ hmR).mpr
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hR i)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_comm] using hs

end Hurst
