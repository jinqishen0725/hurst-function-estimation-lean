import Hurst.PeelingInduction
import Hurst.LevelCakeTransfer
import Hurst.P3SignedMatching
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Continuous tests of the square-weighted signed spectrum

The B1--B4 steps of `direct_proofs/23_spectral_probability_support.md`.
All powers starting at two are used; no assumption on vanishing negative mass
is made. Continuous tests give high powers of each sign separately. Squaring
then reuses nonnegative peeling, while the existing quantile re-sort and
layer-cake transfer construct the target profiles with multiplicity. Finally
the total square mass supplies the uniform tails and the interleaved-row
second-chaos endpoint. Transfer to the original finite row is a separate
permutation/zero-padding identity.
-/

set_option maxHeartbeats 2000000

noncomputable section
namespace Hurst
open Filter Topology

/-- A bounded test preserves summability after square weighting. -/
theorem summable_sq_mul_of_bounded {lam : ℕ → ℝ} {f : ℝ → ℝ}
    (hs : Summable (fun j => lam j ^ 2)) {C : ℝ}
    (hb : ∀ j, |f (lam j)| ≤ C) :
    Summable (fun j => lam j ^ 2 * f (lam j)) := by
  apply Summable.of_norm_bounded (hs.mul_right C)
  intro j
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
  exact mul_le_mul_of_nonneg_left (hb j) (sq_nonneg _)

/-- Compact support gives summability for every continuous test. -/
theorem summable_sq_mul_of_continuousOn {lam : ℕ → ℝ} {f : ℝ → ℝ} {D : ℝ}
    (hs : Summable (fun j => lam j ^ 2))
    (hl : ∀ j, lam j ∈ Set.Icc (-D) D)
    (hf : ContinuousOn f (Set.Icc (-D) D)) :
    Summable (fun j => lam j ^ 2 * f (lam j)) := by
  let F : C(Set.Icc (-D) D, ℝ) :=
    ⟨fun x => f x, continuousOn_iff_continuous_restrict.mp hf⟩
  apply summable_sq_mul_of_bounded hs (C := ‖F‖)
  intro j
  exact F.norm_coe_le_norm ⟨lam j, hl j⟩

/-- Power-sum convergence gives convergence for polynomial tests, with the
square weighting converting a monomial of degree q into moment q+2. -/
theorem tendsto_sq_weighted_polynomial {m : ℕ → ℕ}
    {a : ∀ n, Fin (m n) → ℝ} {lam : ℕ → ℝ} {D : ℝ}
    (hs : Summable (fun j => lam j ^ 2))
    (hl : ∀ j, lam j ∈ Set.Icc (-D) D)
    (hp : ∀ k : ℕ, 2 ≤ k → Tendsto
      (fun n => ∑ i, a n i ^ k) atTop (𝓝 (∑' j, lam j ^ k)))
    (p : Polynomial ℝ) :
    Tendsto (fun n => ∑ i, a n i ^ 2 * p.eval (a n i)) atTop
      (𝓝 (∑' j, lam j ^ 2 * p.eval (lam j))) := by
  induction p using Polynomial.induction_on' with
  | add p q ihp ihq =>
      have hsp := summable_sq_mul_of_continuousOn hs hl p.continuous.continuousOn
      have hsq := summable_sq_mul_of_continuousOn hs hl q.continuous.continuousOn
      simpa only [Polynomial.eval_add, mul_add, Finset.sum_add_distrib,
        hsp.tsum_add hsq] using ihp.add ihq
  | monomial k c =>
      convert (hp (k + 2) (by omega)).mul_const c using 1
      · ext n
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        simp only [Polynomial.eval_monomial, pow_add, pow_two]
        ring
      · congr 1
        rw [← tsum_mul_right]
        apply tsum_congr
        intro j
        simp only [Polynomial.eval_monomial, pow_add, pow_two]
        ring

/-- Uniform test approximation error for a finite spectral row. -/
theorem abs_sum_sq_mul_sub_le {m : ℕ} (a : Fin m → ℝ)
    {f g : ℝ → ℝ} {eps : ℝ} (h : ∀ i, |f (a i) - g (a i)| ≤ eps) :
    |(∑ i, a i ^ 2 * f (a i)) - ∑ i, a i ^ 2 * g (a i)|
      ≤ (∑ i, a i ^ 2) * eps := by
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  calc
    _ ≤ ∑ i, |a i ^ 2 * f (a i) - a i ^ 2 * g (a i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := Finset.sum_le_sum fun i _ => by
      rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul_of_nonneg_left (h i) (sq_nonneg _)

/-- The analogous approximation error for the limiting square-summable spectrum. -/
theorem abs_tsum_sq_mul_sub_le {lam : ℕ → ℝ} {f g : ℝ → ℝ} {eps : ℝ}
    (hs : Summable (fun j => lam j ^ 2))
    (hf : Summable (fun j => lam j ^ 2 * f (lam j)))
    (hg : Summable (fun j => lam j ^ 2 * g (lam j)))
    (h : ∀ j, |f (lam j) - g (lam j)| ≤ eps) :
    |(∑' j, lam j ^ 2 * f (lam j)) - ∑' j, lam j ^ 2 * g (lam j)|
      ≤ (∑' j, lam j ^ 2) * eps := by
  rw [← hf.tsum_sub hg, ← tsum_mul_right]
  apply le_trans (show |(∑' j, (lam j ^ 2 * f (lam j) - lam j ^ 2 * g (lam j)))| ≤
      ∑' j, ‖lam j ^ 2 * f (lam j) - lam j ^ 2 * g (lam j)‖ from
    norm_tsum_le_tsum_norm (hf.sub hg).norm)
  apply (hf.sub hg).norm.tsum_le_tsum _ (hs.mul_right eps)
  intro j
  rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg _)]
  exact mul_le_mul_of_nonneg_left (h j) (sq_nonneg _)

/-- **B1: every continuous test of the square-weighted signed spectrum
converges.** The support and mass bounds need hold only eventually. Positive
and negative spectra are both allowed to have nonzero limiting square mass. -/
theorem tendsto_sq_weighted_continuousTest {m : ℕ → ℕ}
    {a : ∀ n, Fin (m n) → ℝ} {lam : ℕ → ℝ} {D M : ℝ}
    (hs : Summable (fun j => lam j ^ 2))
    (hl : ∀ j, lam j ∈ Set.Icc (-D) D)
    (ha : ∀ᶠ n in atTop, ∀ i, a n i ∈ Set.Icc (-D) D)
    (hM : 0 < M)
    (hMass : ∀ᶠ n in atTop, (∑ i, a n i ^ 2) ≤ M)
    (hlMass : (∑' j, lam j ^ 2) ≤ M)
    (hp : ∀ k : ℕ, 2 ≤ k → Tendsto
      (fun n => ∑ i, a n i ^ k) atTop (𝓝 (∑' j, lam j ^ k)))
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (-D) D)) :
    Tendsto (fun n => ∑ i, a n i ^ 2 * f (a n i)) atTop
      (𝓝 (∑' j, lam j ^ 2 * f (lam j))) := by
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  let eta := eps / (4 * M)
  have heta : 0 < eta := div_pos heps (by positivity)
  obtain ⟨p, hpclose⟩ := exists_polynomial_near_of_continuousOn (-D) D f hf eta heta
  have hplim := tendsto_sq_weighted_polynomial hs hl hp p
  have hpevent := Metric.tendsto_nhds.mp hplim (eps / 2) (by positivity)
  filter_upwards [ha, hMass, hpevent] with n hn hmn hpn
  have hsf := summable_sq_mul_of_continuousOn hs hl hf
  have hsp := summable_sq_mul_of_continuousOn hs hl p.continuous.continuousOn
  have hfin : |(∑ i, a n i ^ 2 * f (a n i)) -
      ∑ i, a n i ^ 2 * p.eval (a n i)| ≤ M * eta := by
    apply (abs_sum_sq_mul_sub_le (a n) (f := f) (g := fun x => p.eval x) (fun i => ?_)).trans
      (mul_le_mul_of_nonneg_right hmn heta.le)
    rw [abs_sub_comm]
    exact (hpclose _ (hn i)).le
  have hinf : |(∑' j, lam j ^ 2 * p.eval (lam j)) -
      ∑' j, lam j ^ 2 * f (lam j)| ≤ M * eta :=
    (abs_tsum_sq_mul_sub_le (f := fun x => p.eval x) (g := f) hs hsp hsf (fun j => (hpclose _ (hl j)).le)).trans
      (mul_le_mul_of_nonneg_right hlMass heta.le)
  rw [Real.dist_eq] at hpn ⊢
  have htri := abs_add_three
    ((∑ i, a n i ^ 2 * f (a n i)) - ∑ i, a n i ^ 2 * p.eval (a n i))
    ((∑ i, a n i ^ 2 * p.eval (a n i)) - ∑' j, lam j ^ 2 * p.eval (lam j))
    ((∑' j, lam j ^ 2 * p.eval (lam j)) - ∑' j, lam j ^ 2 * f (lam j))
  have heq : M * eta = eps / 4 := by dsimp [eta]; field_simp [ne_of_gt hM]
  rw [heq] at hfin hinf
  have hcancel : ((∑ i, a n i ^ 2 * f (a n i)) - ∑ i, a n i ^ 2 * p.eval (a n i)) +
      ((∑ i, a n i ^ 2 * p.eval (a n i)) - ∑' j, lam j ^ 2 * p.eval (lam j)) +
      ((∑' j, lam j ^ 2 * p.eval (lam j)) - ∑' j, lam j ^ 2 * f (lam j)) =
      (∑ i, a n i ^ 2 * f (a n i)) - ∑' j, lam j ^ 2 * f (lam j) := by ring
  rw [hcancel] at htri
  linarith

/-- The compact support and uniform mass needed above follow from the second
power sum alone. These are outputs, not extra spectral assumptions. -/
theorem exists_eventual_sq_spectral_bounds {m : ℕ → ℕ}
    {a : ∀ n, Fin (m n) → ℝ} {lam : ℕ → ℝ}
    (hs : Summable (fun j => lam j ^ 2))
    (hp2 : Tendsto (fun n => ∑ i, a n i ^ 2) atTop
      (𝓝 (∑' j, lam j ^ 2))) :
    ∃ D : ℝ, 0 < D ∧ (∀ j, lam j ∈ Set.Icc (-D) D) ∧
      (∑' j, lam j ^ 2) ≤ D ∧
      ∀ᶠ n in atTop, (∀ i, a n i ∈ Set.Icc (-D) D) ∧ (∑ i, a n i ^ 2) ≤ D := by
  let L := ∑' j, lam j ^ 2
  have hL : 0 ≤ L := tsum_nonneg fun j => sq_nonneg _
  let D := L + 2
  have hD : 1 ≤ D := by dsimp [D]; linarith
  have hbound : ∀ x : ℝ, x ^ 2 ≤ D → x ∈ Set.Icc (-D) D := by
    intro x hx
    constructor <;> nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1)]
  refine ⟨D, by linarith, ?_, by dsimp [D, L]; linarith, ?_⟩
  · intro j
    apply hbound
    have hj := hs.le_tsum j (fun k _ => sq_nonneg (lam k))
    dsimp [D, L]
    linarith
  · have hmass : ∀ᶠ n in atTop, (∑ i, a n i ^ 2) < D :=
      (tendsto_order.mp hp2).2 D (by dsimp [D, L]; linarith)
    filter_upwards [hmass] with n hn
    refine ⟨fun i => hbound _ ?_, hn.le⟩
    exact (Finset.single_le_sum (fun j _ => sq_nonneg (a n j))
      (Finset.mem_univ i)).trans hn.le

/-- A version of B1 with exactly the square summability and power-sum
convergence inputs; support and total-mass bounds are derived internally. -/
theorem tendsto_sq_weighted_continuous_of_powerSums {m : ℕ → ℕ}
    {a : ∀ n, Fin (m n) → ℝ} {lam : ℕ → ℝ}
    (hs : Summable (fun j => lam j ^ 2))
    (hp : ∀ k : ℕ, 2 ≤ k → Tendsto
      (fun n => ∑ i, a n i ^ k) atTop (𝓝 (∑' j, lam j ^ k)))
    {f : ℝ → ℝ} (hf : Continuous f) :
    Tendsto (fun n => ∑ i, a n i ^ 2 * f (a n i)) atTop
      (𝓝 (∑' j, lam j ^ 2 * f (lam j))) := by
  obtain ⟨D, hD, hl, hlMass, hevent⟩ := exists_eventual_sq_spectral_bounds hs (hp 2 le_rfl)
  exact tendsto_sq_weighted_continuousTest hs hl (hevent.mono fun _ h => h.1)
    hD (hevent.mono fun _ h => h.2) hlMass hp hf.continuousOn

private theorem sq_mul_pos_pow (x : ℝ) {k : ℕ} (hk : 3 ≤ k) :
    x ^ 2 * max x 0 ^ (k - 2) = max x 0 ^ k := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx, ← pow_add, Nat.add_sub_of_le (by omega : 2 ≤ k)]
  · rw [max_eq_right (le_of_not_ge hx), zero_pow (by omega : k - 2 ≠ 0),
      zero_pow (by omega : k ≠ 0), mul_zero]

private theorem sq_mul_neg_pow (x : ℝ) {k : ℕ} (hk : 3 ≤ k) :
    x ^ 2 * max (-x) 0 ^ (k - 2) = max (-x) 0 ^ k := by
  simpa only [neg_sq] using sq_mul_pos_pow (-x) hk

/-- All positive-part powers of order at least three converge, without a
negative-mass hypothesis. Squaring the positive parts therefore supplies all
moments required by the existing nonnegative peeling theorem. -/
theorem tendsto_posPart_powerSums_of_signed_powerSums {m : ℕ → ℕ}
    {a : ∀ n, Fin (m n) → ℝ} {lam : ℕ → ℝ}
    (hs : Summable (fun j => lam j ^ 2))
    (hp : ∀ k : ℕ, 2 ≤ k → Tendsto
      (fun n => ∑ i, a n i ^ k) atTop (𝓝 (∑' j, lam j ^ k)))
    {k : ℕ} (hk : 3 ≤ k) :
    Tendsto (fun n => ∑ i, max (a n i) 0 ^ k) atTop
      (𝓝 (∑' j, max (lam j) 0 ^ k)) := by
  have h := tendsto_sq_weighted_continuous_of_powerSums hs hp
    (f := fun x : ℝ => max x 0 ^ (k - 2))
    ((continuous_id.max continuous_const).pow (k - 2))
  simpa only [sq_mul_pos_pow _ hk] using h

/-- The same conclusion for the magnitudes of negative eigenvalues. -/
theorem tendsto_negPart_powerSums_of_signed_powerSums {m : ℕ → ℕ}
    {a : ∀ n, Fin (m n) → ℝ} {lam : ℕ → ℝ}
    (hs : Summable (fun j => lam j ^ 2))
    (hp : ∀ k : ℕ, 2 ≤ k → Tendsto
      (fun n => ∑ i, a n i ^ k) atTop (𝓝 (∑' j, lam j ^ k)))
    {k : ℕ} (hk : 3 ≤ k) :
    Tendsto (fun n => ∑ i, max (-a n i) 0 ^ k) atTop
      (𝓝 (∑' j, max (-lam j) 0 ^ k)) := by
  have h := tendsto_sq_weighted_continuous_of_powerSums hs hp
    (f := fun x : ℝ => max (-x) 0 ^ (k - 2))
    ((continuous_id.neg.max continuous_const).pow (k - 2))
  simpa only [sq_mul_neg_pow _ hk] using h

/-- Sorting a nonnegative finite row commutes with squaring. -/
theorem padRearranged_sq_of_nonneg {m : ℕ} (x : Fin m → ℝ)
    (hx : ∀ i, 0 ≤ x i) (j : ℕ) :
    padRearranged (fun i => x i ^ 2) j = padRearranged x j ^ 2 := by
  have hsort : Antitone (fun i => x (decreasingSpectralPerm x i) ^ 2) := by
    intro i j hij
    exact pow_le_pow_left₀ (hx _) (decreasingSpectralPerm_antitone x hij) 2
  have heq := eq_decreasingSpectralPerm_of_antitone_rearrangement
    (f := fun i => x i ^ 2) hsort
    (decreasingSpectralPerm x) (fun i => rfl)
  unfold padRearranged
  split_ifs with hj
  · exact (heq ⟨j, hj⟩).symm
  · simp

/-- Nonnegative coefficient matching only needs the even powers of order at
least four. Squaring reduces this to the existing peeling theorem. This
lemma alone does not assert convergence of the total square mass. -/
theorem paddedRearranged_tendsto_of_evenPowersAboveTwo
    (m : ℕ → ℕ) (x : ∀ n, Fin (m n) → ℝ) (p : ℕ → ℝ)
    (hm : ∀ n, 0 < m n) (hmtop : Tendsto m atTop atTop)
    (hx : ∀ n i, 0 ≤ x n i) (hpanti : Antitone p)
    (hpnonneg : ∀ j, 0 ≤ p j) (hpsum : Summable (fun j => p j ^ 2))
    (hMom : ∀ k : ℕ, 2 ≤ k → Tendsto
      (fun n => ∑ i, x n i ^ (2 * k)) atTop (𝓝 (∑' j, p j ^ (2 * k)))) :
    ∀ j, Tendsto (fun n => padRearranged (x n) j) atTop (𝓝 (p j)) := by
  have hpanti2 : Antitone (fun j => p j ^ 2) := by
    intro i j hij
    exact pow_le_pow_left₀ (hpnonneg _) (hpanti hij) 2
  have hpsq : Summable (fun j => (p j ^ 2) ^ 2) := by
    simpa only [← pow_mul] using
      summable_pow_of_square hpanti hpnonneg (by norm_num : 2 ≤ 4) hpsum
  have hconv := paddedRearranged_tendsto m (fun n i => x n i ^ 2)
    (fun j => p j ^ 2) hm hmtop (fun n i => sq_nonneg _)
    ⟨hpanti2, fun j => ⟨sq_nonneg _, hpsq⟩⟩
    (fun k hk => by simpa only [← pow_mul] using hMom k hk)
  intro j
  have hsq : Tendsto (fun n => padRearranged (x n) j ^ 2) atTop (𝓝 (p j ^ 2)) := by
    convert hconv j using 1
    ext n
    exact (padRearranged_sq_of_nonneg (x n) (hx n) j).symm
  have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  have hpad : ∀ n, 0 ≤ padRearranged (x n) j := by
    intro n
    unfold padRearranged
    split_ifs
    · exact hx n _
    · exact le_rfl
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_nonneg (hpnonneg j),
    abs_of_nonneg (hpad _)] using hroot

/-- Consume an already ordered positive spectrum. `hTarget` is only the
power-sum preservation of its enumeration, not a coefficient-convergence
assumption. The quantile construction below supplies this ordered enumeration. -/
theorem padded_posPart_tendsto_of_signed_powerSums
    (m : ℕ → ℕ) (a : ∀ n, Fin (m n) → ℝ) (lam p : ℕ → ℝ)
    (hm : ∀ n, 0 < m n) (hmtop : Tendsto m atTop atTop)
    (hs : Summable (fun j => lam j ^ 2))
    (hpanti : Antitone p) (hpnonneg : ∀ j, 0 ≤ p j)
    (hpsum : Summable (fun j => p j ^ 2))
    (hTarget : ∀ k : ℕ, 3 ≤ k → (∑' j, max (lam j) 0 ^ k) = ∑' j, p j ^ k)
    (hp : ∀ k : ℕ, 2 ≤ k → Tendsto
      (fun n => ∑ i, a n i ^ k) atTop (𝓝 (∑' j, lam j ^ k))) :
    ∀ j, Tendsto (fun n => padRearranged (fun i => max (a n i) 0) j) atTop (𝓝 (p j)) := by
  apply paddedRearranged_tendsto_of_evenPowersAboveTwo m
    (fun n i => max (a n i) 0) p hm hmtop (fun n i => le_max_right _ _)
    hpanti hpnonneg hpsum
  intro k hk
  have h2k : 3 ≤ 2 * k := by omega
  rw [← hTarget (2 * k) h2k]
  exact tendsto_posPart_powerSums_of_signed_powerSums hs hp h2k

/-- The negative-magnitude counterpart; no negative mass is assumed to vanish. -/
theorem padded_negPart_tendsto_of_signed_powerSums
    (m : ℕ → ℕ) (a : ∀ n, Fin (m n) → ℝ) (lam q : ℕ → ℝ)
    (hm : ∀ n, 0 < m n) (hmtop : Tendsto m atTop atTop)
    (hs : Summable (fun j => lam j ^ 2))
    (hqanti : Antitone q) (hqnonneg : ∀ j, 0 ≤ q j)
    (hqsum : Summable (fun j => q j ^ 2))
    (hTarget : ∀ k : ℕ, 3 ≤ k → (∑' j, max (-lam j) 0 ^ k) = ∑' j, q j ^ k)
    (hp : ∀ k : ℕ, 2 ≤ k → Tendsto
      (fun n => ∑ i, a n i ^ k) atTop (𝓝 (∑' j, lam j ^ k))) :
    ∀ j, Tendsto (fun n => padRearranged (fun i => max (-a n i) 0) j) atTop (𝓝 (q j)) := by
  apply paddedRearranged_tendsto_of_evenPowersAboveTwo m
    (fun n i => max (-a n i) 0) q hm hmtop (fun n i => le_max_right _ _)
    hqanti hqnonneg hqsum
  intro k hk
  have h2k : 3 ≤ 2 * k := by omega
  rw [← hTarget (2 * k) h2k]
  exact tendsto_negPart_powerSums_of_signed_powerSums hs hp h2k

/-- Nonnegative square-summable sequences have all higher powers summable;
no ordering hypothesis is needed. -/
theorem summable_nonneg_pow_of_sq {v : ℕ → ℝ} (hv : ∀ j, 0 ≤ v j)
    (hs : Summable (fun j => v j ^ 2)) {k : ℕ} (hk : 2 ≤ k) :
    Summable (fun j => v j ^ k) := by
  obtain ⟨M, hM⟩ := bounded_of_squareSummable hv (by simpa only [pow_two] using hs)
  apply Summable.of_nonneg_of_le (fun j => pow_nonneg (hv j) _) _
    (hs.mul_left (M ^ (k - 2)))
  intro j
  calc
    v j ^ k = v j ^ (k - 2) * v j ^ 2 := by rw [← pow_add, Nat.sub_add_cancel hk]
    _ ≤ M ^ (k - 2) * v j ^ 2 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hv j) (hM j) _) (sq_nonneg _)

/-- The already implemented quantile re-sort supplies the full ordered
profile, including all power HasSums; finite spectra and zero padding are
handled by the quantile construction. -/
theorem antitoneResort_sq_profile {v : ℕ → ℝ} (hv : ∀ j, 0 ≤ v j)
    (hs : Summable (fun j => v j ^ 2)) :
    Antitone (antitoneResort v) ∧ (∀ j, 0 ≤ antitoneResort v j) ∧
      Summable (fun j => antitoneResort v j ^ 2) ∧
      ∀ k : ℕ, 2 ≤ k → HasSum (fun j => antitoneResort v j ^ k) (∑' j, v j ^ k) := by
  have hs' : Summable (fun j => v j * v j) := by simpa only [pow_two] using hs
  have hpow : ∀ k : ℕ, 2 ≤ k →
      HasSum (fun j => antitoneResort v j ^ k) (∑' j, v j ^ k) := by
    intro k hk
    exact hasSum_pow_of_resort_lvlCount v hv hs' k (by omega)
      (summable_nonneg_pow_of_sq hv hs hk)
  exact ⟨antitoneResort_antitone hv hs', antitoneResort_nonneg hv hs',
    (hpow 2 le_rfl).summable, hpow⟩

theorem summable_posPart_sq {lam : ℕ → ℝ} (hs : Summable (fun j => lam j ^ 2)) :
    Summable (fun j => max (lam j) 0 ^ 2) := by
  apply Summable.of_nonneg_of_le (fun j => sq_nonneg _) _ hs
  intro j
  by_cases hj : 0 ≤ lam j
  · simp only [max_eq_left hj, le_refl]
  · simp only [max_eq_right (le_of_not_ge hj), zero_pow (by norm_num : 2 ≠ 0)]
    exact sq_nonneg _

theorem summable_negPart_sq {lam : ℕ → ℝ} (hs : Summable (fun j => lam j ^ 2)) :
    Summable (fun j => max (-lam j) 0 ^ 2) := by
  apply summable_posPart_sq (lam := fun j => -lam j)
  simpa only [neg_sq] using hs

/-- **General signed coefficient matching.** Both sorted profiles are
constructed internally from an arbitrary square-summable real spectrum.
The hypotheses are genuine power-sum convergence, not coefficient matching
or vanishing negative mass. -/
theorem signed_sorted_coefficients_tendsto_of_powerSums
    (m : ℕ → ℕ) (a : ∀ n, Fin (m n) → ℝ) (lam : ℕ → ℝ)
    (hm : ∀ n, 0 < m n) (hmtop : Tendsto m atTop atTop)
    (hs : Summable (fun j => lam j ^ 2))
    (hp : ∀ k : ℕ, 2 ≤ k → Tendsto
      (fun n => ∑ i, a n i ^ k) atTop (𝓝 (∑' j, lam j ^ k))) :
    (∀ j, Tendsto (fun n => padRearranged (fun i => max (a n i) 0) j) atTop
      (𝓝 (antitoneResort (fun i => max (lam i) 0) j))) ∧
    (∀ j, Tendsto (fun n => padRearranged (fun i => max (-a n i) 0) j) atTop
      (𝓝 (antitoneResort (fun i => max (-lam i) 0) j))) := by
  obtain ⟨hpa, hpn, hps, hpowers⟩ := antitoneResort_sq_profile
    (fun j => le_max_right (lam j) 0) (summable_posPart_sq hs)
  obtain ⟨hqa, hqn, hqs, hqowers⟩ := antitoneResort_sq_profile
    (fun j => le_max_right (-lam j) 0) (summable_negPart_sq hs)
  constructor
  · exact padded_posPart_tendsto_of_signed_powerSums m a lam _ hm hmtop hs
      hpa hpn hps (fun k hk => (hpowers k (by omega)).tsum_eq.symm) hp
  · exact padded_negPart_tendsto_of_signed_powerSums m a lam _ hm hmtop hs
      hqa hqn hqs (fun k hk => (hqowers k (by omega)).tsum_eq.symm) hp

/-- The all-row nonemptiness precondition of the old peeling implementation
is removed by shifting past finitely many bad rows. This is the final
coefficient-matching interface for arbitrary varying row sizes. -/
theorem signed_sorted_coefficients_tendsto
    (m : ℕ → ℕ) (a : ∀ n, Fin (m n) → ℝ) (lam : ℕ → ℝ)
    (hmtop : Tendsto m atTop atTop)
    (hs : Summable (fun j => lam j ^ 2))
    (hp : ∀ k : ℕ, 2 ≤ k → Tendsto
      (fun n => ∑ i, a n i ^ k) atTop (𝓝 (∑' j, lam j ^ k))) :
    (∀ j, Tendsto (fun n => padRearranged (fun i => max (a n i) 0) j) atTop
      (𝓝 (antitoneResort (fun i => max (lam i) 0) j))) ∧
    (∀ j, Tendsto (fun n => padRearranged (fun i => max (-a n i) 0) j) atTop
      (𝓝 (antitoneResort (fun i => max (-lam i) 0) j))) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hmtop.eventually_ge_atTop 1)
  have hshift := tendsto_add_atTop_nat N
  have hnonempty : ∀ n, 0 < m (n + N) := by
    intro n
    exact lt_of_lt_of_le Nat.zero_lt_one (hN (n + N) (by omega))
  obtain ⟨hpos, hneg⟩ := signed_sorted_coefficients_tendsto_of_powerSums
    (fun n => m (n + N)) (fun n => a (n + N)) lam hnonempty (hmtop.comp hshift) hs
    (fun k hk => (hp k hk).comp hshift)
  exact ⟨fun j => (tendsto_add_atTop_iff_nat N).mp (hpos j),
    fun j => (tendsto_add_atTop_iff_nat N).mp (hneg j)⟩

/-- Canonical signed target: positive and negative spectra are separately
sorted and interleaved, retaining every nonzero eigenvalue with multiplicity. -/
def signedSortedSpectrum (lam : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j % 2 = 0 then antitoneResort (fun i => max (lam i) 0) (j / 2)
  else -antitoneResort (fun i => max (-lam i) 0) (j / 2)

@[simp] theorem signedSortedSpectrum_even (lam : ℕ → ℝ) (j : ℕ) :
    signedSortedSpectrum lam (2 * j) = antitoneResort (fun i => max (lam i) 0) j := by
  simp [signedSortedSpectrum, show (2 * j) % 2 = 0 by omega,
    show (2 * j) / 2 = j by omega]

@[simp] theorem signedSortedSpectrum_odd (lam : ℕ → ℝ) (j : ℕ) :
    signedSortedSpectrum lam (2 * j + 1) = -antitoneResort (fun i => max (-lam i) 0) j := by
  simp [signedSortedSpectrum, show (2 * j + 1) % 2 ≠ 0 by omega,
    show (2 * j + 1) / 2 = j by omega]

/-- Pointwise bridge from the odd slots; `rw` avoids the `simp` self-loop of
`neg_pow` (whose RHS contains `(-1)^k`, matching its own LHS pattern). -/
private theorem signedSortedSpectrum_odd_pow_eq (lam : ℕ → ℝ) (j k : ℕ) :
    signedSortedSpectrum lam (2 * j + 1) ^ k
      = (-1 : ℝ) ^ k * antitoneResort (fun i => max (-lam i) 0) j ^ k := by
  rw [signedSortedSpectrum_odd, neg_pow]

/-- All signed powers are preserved, including odd powers. This permits the
constructed order to replace the original spectrum in Riesz moment identities. -/
theorem signedSortedSpectrum_hasSum_pow {lam : ℕ → ℝ}
    (hs : Summable (fun j => lam j ^ 2)) {k : ℕ} (hk : 2 ≤ k) :
    HasSum (fun j => signedSortedSpectrum lam j ^ k) (∑' j, lam j ^ k) := by
  have hp := (antitoneResort_sq_profile (fun j => le_max_right (lam j) 0)
    (summable_posPart_sq hs)).2.2.2 k hk
  have hq := (antitoneResort_sq_profile (fun j => le_max_right (-lam j) 0)
    (summable_negPart_sq hs)).2.2.2 k hk
  have he : HasSum (fun j => signedSortedSpectrum lam (2 * j) ^ k)
      (∑' j, max (lam j) 0 ^ k) := by simpa only [signedSortedSpectrum_even] using hp
  have ho : HasSum (fun j => signedSortedSpectrum lam (2 * j + 1) ^ k)
      ((-1 : ℝ) ^ k * ∑' j, max (-lam j) 0 ^ k) := by
    rw [funext fun j => signedSortedSpectrum_odd_pow_eq lam j k]
    exact hq.mul_left ((-1 : ℝ) ^ k)
  have hsum : HasSum (fun j => signedSortedSpectrum lam j ^ k)
      ((∑' j, max (lam j) 0 ^ k) + (-1 : ℝ) ^ k * ∑' j, max (-lam j) 0 ^ k) :=
    HasSum.even_add_odd (f := fun j => signedSortedSpectrum lam j ^ k) he ho
  have hsp := summable_nonneg_pow_of_sq (fun j => le_max_right (lam j) 0)
    (summable_posPart_sq hs) hk
  have hsq := summable_nonneg_pow_of_sq (fun j => le_max_right (-lam j) 0)
    (summable_negPart_sq hs) hk
  have hpt : ∀ j, max (lam j) 0 ^ k + (-1 : ℝ) ^ k * max (-lam j) 0 ^ k
      = lam j ^ k := by
    intro j
    have h := signed_pow_decompose (fun _ : Fin 1 => lam j) 0 (by omega : 0 < k)
    simpa only [signedPosPart, signedAbsNegPart] using h.symm
  have hid : (∑' j, max (lam j) 0 ^ k) + (-1 : ℝ) ^ k * (∑' j, max (-lam j) 0 ^ k) =
      ∑' j, lam j ^ k := by
    rw [← tsum_mul_left, ← hsp.tsum_add (hsq.mul_left ((-1 : ℝ) ^ k))]
    exact tsum_congr (f := fun j => max (lam j) 0 ^ k + (-1 : ℝ) ^ k * max (-lam j) 0 ^ k)
      (g := fun j => lam j ^ k) hpt
  rwa [hid] at hsum

/-- Exact preservation of square mass under the canonical signed ordering. -/
theorem signedSortedSpectrum_hasSum_sq {lam : ℕ → ℝ}
    (hs : Summable (fun j => lam j ^ 2)) :
    HasSum (fun j => signedSortedSpectrum lam j ^ 2) (∑' j, lam j ^ 2) := by
  have hp := (antitoneResort_sq_profile (fun j => le_max_right (lam j) 0)
    (summable_posPart_sq hs)).2.2.2 2 le_rfl
  have hq := (antitoneResort_sq_profile (fun j => le_max_right (-lam j) 0)
    (summable_negPart_sq hs)).2.2.2 2 le_rfl
  have he : HasSum (fun j => signedSortedSpectrum lam (2 * j) ^ 2)
      (∑' j, max (lam j) 0 ^ 2) := by simpa only [signedSortedSpectrum_even] using hp
  have ho : HasSum (fun j => signedSortedSpectrum lam (2 * j + 1) ^ 2)
      (∑' j, max (-lam j) 0 ^ 2) := by
    have hpt : ∀ j, signedSortedSpectrum lam (2 * j + 1) ^ 2
        = antitoneResort (fun i => max (-lam i) 0) j ^ 2 := by
      intro j
      rw [signedSortedSpectrum_odd, neg_sq]
    rw [funext hpt]
    exact hq
  have hsum : HasSum (fun j => signedSortedSpectrum lam j ^ 2)
      ((∑' j, max (lam j) 0 ^ 2) + ∑' j, max (-lam j) 0 ^ 2) :=
    HasSum.even_add_odd (f := fun j => signedSortedSpectrum lam j ^ 2) he ho
  have hpt : ∀ j, max (lam j) 0 ^ 2 + max (-lam j) 0 ^ 2 = lam j ^ 2 := by
    intro j
    by_cases hj : 0 ≤ lam j
    · rw [max_eq_left hj, max_eq_right (by linarith : -lam j ≤ 0)]
      simp
    · rw [max_eq_right (le_of_not_ge hj), max_eq_left (by linarith : 0 ≤ -lam j)]
      simp
  have hid : (∑' j, max (lam j) 0 ^ 2) + (∑' j, max (-lam j) 0 ^ 2) =
      ∑' j, lam j ^ 2 := by
    rw [← (summable_posPart_sq hs).tsum_add (summable_negPart_sq hs)]
    exact tsum_congr (f := fun j => max (lam j) 0 ^ 2 + max (-lam j) 0 ^ 2)
      (g := fun j => lam j ^ 2) hpt
  rwa [hid] at hsum

/-- Slot access into the interleaved row, stated so that later steps close by
`rfl` through the definitional unfolding of `signedPosPart`/`signedAbsNegPart`. -/
theorem signedInterleavedRow_of_even {m : ℕ} (c : Fin m → ℝ) {j : ℕ}
    (hj : j % 2 = 0) (hlt : j < 2 * m) :
    signedInterleavedRow c ⟨j, hlt⟩ = padRearranged (signedPosPart c) (j / 2) :=
  dif_pos hj

theorem signedInterleavedRow_of_odd {m : ℕ} (c : Fin m → ℝ) {j : ℕ}
    (hj : ¬ j % 2 = 0) (hlt : j < 2 * m) :
    signedInterleavedRow c ⟨j, hlt⟩ = -padRearranged (signedAbsNegPart c) (j / 2) :=
  dif_neg hj

/-- The actual interleaved finite rows converge at every padded coordinate. -/
theorem signedInterleavedRow_coefficients_tendsto
    (m : ℕ → ℕ) (a : ∀ n, Fin (m n) → ℝ) (lam : ℕ → ℝ)
    (hmtop : Tendsto m atTop atTop)
    (hs : Summable (fun j => lam j ^ 2))
    (hp : ∀ k : ℕ, 2 ≤ k → Tendsto
      (fun n => ∑ i, a n i ^ k) atTop (𝓝 (∑' j, lam j ^ k))) :
    ∀ j, Tendsto (fun n => if hj : j < 2 * m n then
      signedInterleavedRow (a n) ⟨j, hj⟩ else 0) atTop (𝓝 (signedSortedSpectrum lam j)) := by
  obtain ⟨hpos, hneg⟩ := signed_sorted_coefficients_tendsto m a lam hmtop hs hp
  intro j
  have hevent : ∀ᶠ n in atTop, j < 2 * m n :=
    (hmtop.eventually_ge_atTop (j + 1)).mono fun n hn => by omega
  by_cases hj : j % 2 = 0
  · rw [signedSortedSpectrum, if_pos hj]
    refine (hpos (j / 2)).congr' ?_
    filter_upwards [hevent] with n hn
    rw [dif_pos hn, signedInterleavedRow_of_even _ hj hn]
    rfl
  · rw [signedSortedSpectrum, if_neg hj]
    refine ((hneg (j / 2)).neg).congr' ?_
    filter_upwards [hevent] with n hn
    rw [dif_pos hn, signedInterleavedRow_of_odd _ hj hn]
    rfl

/-- **B3+B4 delivery:** full signed, padded coefficient convergence together
with the eventual square-tail bounds required by the existing chaos bridge.
All matching data are derived from the original signed power sums. -/
theorem signedInterleavedRow_matching_data
    (m : ℕ → ℕ) (a : ∀ n, Fin (m n) → ℝ) (lam : ℕ → ℝ)
    (hmtop : Tendsto m atTop atTop)
    (hs : Summable (fun j => lam j ^ 2))
    (hp : ∀ k : ℕ, 2 ≤ k → Tendsto
      (fun n => ∑ i, a n i ^ k) atTop (𝓝 (∑' j, lam j ^ k))) :
    ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧
      ∀ K : ℕ, ∀ᶠ n in atTop,
        2 * (∑ i : Fin (2 * m n), if K ≤ i.val then
          signedInterleavedRow (a n) i ^ 2 else 0) ≤ e K := by
  have hsize : Tendsto (fun n => 2 * m n) atTop atTop :=
    tendsto_atTop_mono (fun n => by omega : ∀ n, m n ≤ 2 * m n) hmtop
  have hmass : Tendsto (fun n => ∑ i, signedInterleavedRow (a n) i ^ 2) atTop
      (𝓝 (∑' j, signedSortedSpectrum lam j ^ 2)) := by
    simpa only [signedInterleavedRow_sum_sq, (signedSortedSpectrum_hasSum_sq hs).tsum_eq]
      using hp 2 le_rfl
  exact spectralTailBound_of_padded_coefficient_convergence (fun n => 2 * m n)
    (fun n => signedInterleavedRow (a n)) (signedSortedSpectrum lam)
    (signedSortedSpectrum_hasSum_sq hs).summable hsize
    (signedInterleavedRow_coefficients_tendsto m a lam hmtop hs hp) hmass

/-- The constructed matching data feed the existing second-chaos theorem.
This is the interleaved-row endpoint; transfer back to the original row uses
its separate, finite-dimensional permutation/zero-padding identity. -/
theorem signedInterleavedRow_tendsto_secondChaos_of_powerSums
    (m : ℕ → ℕ) (a : ∀ n, Fin (m n) → ℝ) (lam : ℕ → ℝ)
    (hmtop : Tendsto m atTop atTop)
    (hs : Summable (fun j => lam j ^ 2))
    (hp : ∀ k : ℕ, 2 ≤ k → Tendsto
      (fun n => ∑ i, a n i ^ k) atTop (𝓝 (∑' j, lam j ^ k)))
    {Theta : Type*} [MeasurableSpace Theta]
    (P' : MeasureTheory.Measure Theta) [MeasureTheory.IsProbabilityMeasure P']
    (Q : Theta → ℝ) (hQ : IsSecondChaosSeriesLaw P' Q (signedSortedSpectrum lam)) :
    MeasureTheory.TendstoInDistribution
      (fun n => centeredSpectralSquares (signedInterleavedRow (a n))) atTop Q
      (fun n => ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin (2 * m n)))) P' := by
  obtain ⟨e, he, htail⟩ := signedInterleavedRow_matching_data m a lam hmtop hs hp
  exact centeredSpectralSquares_tendsto_secondChaos_of_padded_l2
    (fun n => 2 * m n) (fun n => signedInterleavedRow (a n)) P' Q (signedSortedSpectrum lam)
    hQ (tendsto_atTop_mono (fun n => by omega : ∀ n, m n ≤ 2 * m n) hmtop)
    (signedInterleavedRow_coefficients_tendsto m a lam hmtop hs hp) e he htail

end Hurst
