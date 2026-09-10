import Hurst.WeightEnergyLimit
import Hurst.CorrelationLimit
import Mathlib.Analysis.Real.Sqrt

noncomputable section
open Set Filter
open scoped Topology
namespace Hurst

/-- Shift a finite row by `k`, extending it by zero past the right endpoint.
This is the indexing convention obtained after collecting a covariance double
sum by a fixed nonnegative lag. -/
def finZeroExtendedShift {m : ℕ} (k : ℕ) (w : Fin m → ℝ) (i : Fin m) : ℝ :=
  if h : i.val + k < m then w ⟨i.val + k, h⟩ else 0

@[simp]
theorem finZeroExtendedShift_zero {m : ℕ} (w : Fin m → ℝ) :
    finZeroExtendedShift 0 w = w := by
  funext i
  simp only [finZeroExtendedShift, add_zero, i.isLt, dite_true]

/-- Every kernel moment profile is globally Lipschitz.  Compact support is
essential here: its continuous derivative has a finite global bound. -/
theorem kernelMomentFunction_lipschitz (j : ℕ) :
    ∃ L : NNReal, LipschitzWith L (kernelMomentFunction j) := by
  obtain ⟨C, hC⟩ :=
    (kernelMomentFunction_compactSupport j).deriv.exists_bound_of_continuousOn
      ((kernelMomentFunction_smooth j).continuous_deriv (by simp)).continuousOn
  let B : ℝ := max C 0
  have hB : 0 ≤ B := le_max_right _ _
  refine ⟨⟨B, hB⟩, ?_⟩
  rw [← lipschitzOnWith_univ]
  apply convex_univ.lipschitzOnWith_of_nnnorm_deriv_le
  · intro x _
    exact (kernelMomentFunction_smooth j).differentiable (by simp) x
  · intro x _
    rw [← NNReal.coe_le_coe]
    change ‖deriv (kernelMomentFunction j) x‖ ≤ B
    by_cases hz : deriv (kernelMomentFunction j) x = 0
    · simp only [hz, norm_zero]
      exact hB
    · exact (hC x (subset_closure hz)).trans (le_max_left _ _)

/-- Rewrite an actual local-polynomial weight as a finite linear combination
of the globally Lipschitz kernel moment profiles. -/
theorem localPolynomialWeights_formula_kernelMoments
    (r n q : ℕ) (δ t : ℝ) (i : Fin (n - q)) :
    localPolynomialWeights r n q δ t i =
      ((n : ℝ) * δ)⁻¹ * ∑ j : Fin (r + 1),
        (localDesignGram r n q δ t)⁻¹ 0 j *
          kernelMomentFunction j.val ((grid n i.val - t) / δ) := by
  rw [localPolynomialWeights_formula]
  simp only [kernelMomentFunction, Finset.mul_sum]
  ring

/-- Moving `k` midpoint-grid indices changes the rescaled kernel argument by
exactly `k / (n δ)`. -/
theorem normalized_grid_fixedShift
    (n i k : ℕ) (δ t : ℝ) (hn : 0 < n) (hδ : 0 < δ) :
    (grid n (i + k) - t) / δ =
      (grid n i - t) / δ + (k : ℝ) / ((n : ℝ) * δ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold grid
  field_simp
  push_cast
  ring

/-- Pointwise fixed-lag translation bound for the actual local-polynomial
weights.  The bound is of order `k / (n δ)^2` when the inverse design entries
are uniformly bounded. -/
theorem localPolynomialWeights_fixedShift_pointwise
    (r n q k : ℕ) (δ t D : ℝ) (hn : 0 < n) (hδ : 0 < δ) (hD : 0 ≤ D)
    (L : Fin (r + 1) → NNReal)
    (hL : ∀ j, LipschitzWith (L j) (kernelMomentFunction j.val))
    (hinv : ∀ j : Fin (r + 1), |(localDesignGram r n q δ t)⁻¹ 0 j| ≤ D)
    (i : Fin (n - q)) (hik : i.val + k < n - q) :
    |localPolynomialWeights r n q δ t ⟨i.val + k, hik⟩ -
        localPolynomialWeights r n q δ t i| ≤
      ((n : ℝ) * δ)⁻¹ * ∑ j : Fin (r + 1),
        D * (L j : ℝ) * ((k : ℝ) / ((n : ℝ) * δ)) := by
  let N : ℝ := (n : ℝ) * δ
  have hN : 0 < N := by
    dsimp [N]
    positivity
  let x : ℝ := (grid n i.val - t) / δ
  have hxshift : (grid n (i.val + k) - t) / δ =
      x + (k : ℝ) / N := by
    dsimp [x, N]
    exact normalized_grid_fixedShift n i.val k δ t hn hδ
  rw [localPolynomialWeights_formula_kernelMoments,
    localPolynomialWeights_formula_kernelMoments, hxshift]
  rw [← mul_sub, abs_mul, abs_of_nonneg (inv_nonneg.mpr hN.le)]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hN.le)
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [← mul_sub, abs_mul]
  have hLip := (hL j).norm_sub_le (x + (k : ℝ) / N) x
  have hstep : |kernelMomentFunction j.val (x + (k : ℝ) / N) -
      kernelMomentFunction j.val x| ≤ (L j : ℝ) * ((k : ℝ) / N) := by
    simpa only [Real.norm_eq_abs, add_sub_cancel_left,
      abs_of_nonneg (by positivity : 0 ≤ (k : ℝ) / N)] using hLip
  dsimp [x, N] at hstep ⊢
  exact (mul_le_mul (hinv j) hstep (abs_nonneg _) hD).trans_eq (by ring)

theorem finZeroExtendedShift_boundary_card {m : ℕ} (k : ℕ) :
    (Finset.univ.filter (fun i : Fin m => ¬ i.val + k < m)).card ≤ k := by
  classical
  by_cases hk : k = 0
  · subst k
    simp
  let f : Fin m → Fin k := fun i =>
    if h : ¬ i.val + k < m then
      ⟨i.val + k - m, by omega⟩
    else ⟨0, Nat.pos_of_ne_zero hk⟩
  have hc : (Finset.univ.filter (fun i : Fin m => ¬ i.val + k < m)).card ≤
      (Finset.univ : Finset (Fin k)).card := by
    apply Finset.card_le_card_of_injOn f
    · intro i hi
      exact Finset.mem_univ _
    · intro i hi j hj hij
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
      apply Fin.ext
      dsimp [f] at hij
      rw [dif_pos hi, dif_pos hj] at hij
      simp only [Fin.mk.injEq] at hij
      omega
  simpa using hc

theorem finZeroExtendedShift_sq_sum_bound
    {m : ℕ} (k : ℕ) (w : Fin m → ℝ) (active : Fin m → Prop)
    [DecidablePred active] (a b M : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hvalid : ∀ (i : Fin m) (hi : i.val + k < m),
      |w ⟨i.val + k, hi⟩ - w i| ≤ a)
    (hzero : ∀ (i : Fin m) (hi : i.val + k < m),
      ¬ active i → ¬ active ⟨i.val + k, hi⟩ →
        w ⟨i.val + k, hi⟩ - w i = 0)
    (hweight : ∀ i, |w i| ≤ b)
    (hactive : ((Finset.univ.filter active).card : ℝ) ≤ M) :
    (∑ i, (finZeroExtendedShift k w i - w i) ^ 2) ≤
      2 * M * a ^ 2 + (k : ℝ) * b ^ 2 := by
  classical
  let V := Finset.univ.filter (fun i : Fin m => i.val + k < m)
  let B := Finset.univ.filter (fun i : Fin m => ¬ i.val + k < m)
  let A := Finset.univ.filter active
  let T := Finset.univ.filter (fun i : Fin m =>
    ∃ h : i.val + k < m, active ⟨i.val + k, h⟩)
  let S := V.filter (fun i : Fin m => active i ∨
    ∃ h : i.val + k < m, active ⟨i.val + k, h⟩)
  have hsplit :
      (∑ i, (finZeroExtendedShift k w i - w i) ^ 2) =
        (∑ i ∈ V, (finZeroExtendedShift k w i - w i) ^ 2) +
        ∑ i ∈ B, (finZeroExtendedShift k w i - w i) ^ 2 := by
    simpa only [V, B] using
      (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun i : Fin m => i.val + k < m)
        (fun i => (finZeroExtendedShift k w i - w i) ^ 2)).symm
  have hVeq :
      (∑ i ∈ V, (finZeroExtendedShift k w i - w i) ^ 2) =
        ∑ i ∈ S, (finZeroExtendedShift k w i - w i) ^ 2 := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hiV hiS
    simp only [Finset.mem_filter] at hiS
    have hv : i.val + k < m := by
      simpa only [V, Finset.mem_filter, Finset.mem_univ, true_and] using hiV
    have hna : ¬ active i := fun h => hiS ⟨hiV, Or.inl h⟩
    have hnas : ¬ active ⟨i.val + k, hv⟩ := fun h => hiS ⟨hiV, Or.inr ⟨hv, h⟩⟩
    rw [finZeroExtendedShift, dif_pos hv, hzero i hv hna hnas]
    norm_num
  have hTcard : T.card ≤ A.card := by
    let f : Fin m → Fin m := fun i =>
      if h : i.val + k < m then ⟨i.val + k, h⟩ else i
    apply Finset.card_le_card_of_injOn f
    · intro i hi
      simp only [Finset.mem_coe, T, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      obtain ⟨h, ha'⟩ := hi
      change f i ∈ A
      simp only [f, dif_pos h, A, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ha'
    · intro i hi j hj hij
      simp only [Finset.mem_coe, T, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
      obtain ⟨hi', _⟩ := hi
      obtain ⟨hj', _⟩ := hj
      apply Fin.ext
      dsimp [f] at hij
      rw [dif_pos hi', dif_pos hj'] at hij
      simp only [Fin.mk.injEq] at hij
      omega
  have hScard : S.card ≤ A.card + T.card := by
    calc
      S.card ≤ (A ∪ T).card := by
        apply Finset.card_le_card
        intro i hi
        simp only [S, Finset.mem_filter] at hi
        rcases hi.2 with hai | hti
        · exact Finset.mem_union_left T (by
            simpa only [A, Finset.mem_filter, Finset.mem_univ, true_and] using hai)
        · exact Finset.mem_union_right A (by
            simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and] using hti)
      _ ≤ A.card + T.card := Finset.card_union_le _ _
  have hScardR : (S.card : ℝ) ≤ 2 * M := by
    have hs : S.card ≤ 2 * A.card := by omega
    have hsR : (S.card : ℝ) ≤ 2 * (A.card : ℝ) := by exact_mod_cast hs
    have hAR : (A.card : ℝ) ≤ M := by simpa only [A] using hactive
    linarith
  have hV :
      (∑ i ∈ V, (finZeroExtendedShift k w i - w i) ^ 2) ≤
        2 * M * a ^ 2 := by
    rw [hVeq]
    calc
      _ ≤ S.card • a ^ 2 := Finset.sum_le_card_nsmul S _ _ (by
        intro i hi
        simp only [S, Finset.mem_filter, V, Finset.mem_univ, true_and] at hi
        have hv := hi.1
        rw [finZeroExtendedShift, dif_pos hv, sq_le_sq]
        simpa only [abs_of_nonneg ha] using hvalid i hv)
      _ = (S.card : ℝ) * a ^ 2 := by simp
      _ ≤ (2 * M) * a ^ 2 := mul_le_mul_of_nonneg_right hScardR (sq_nonneg _)
      _ = 2 * M * a ^ 2 := by ring
  have hBcard : (B.card : ℝ) ≤ k := by
    exact_mod_cast (show B.card ≤ k from by
      simpa only [B] using finZeroExtendedShift_boundary_card (m := m) k)
  have hB :
      (∑ i ∈ B, (finZeroExtendedShift k w i - w i) ^ 2) ≤
        (k : ℝ) * b ^ 2 := by
    calc
      _ ≤ B.card • b ^ 2 := Finset.sum_le_card_nsmul B _ _ (by
        intro i hi
        have hnv : ¬ i.val + k < m := by
          simpa only [B, Finset.mem_filter, Finset.mem_univ, true_and] using hi
        rw [finZeroExtendedShift, dif_neg hnv, zero_sub, neg_sq, sq_le_sq]
        simpa only [abs_of_nonneg hb] using hweight i)
      _ = (B.card : ℝ) * b ^ 2 := by simp
      _ ≤ (k : ℝ) * b ^ 2 := mul_le_mul_of_nonneg_right hBcard (sq_nonneg _)
  rw [hsplit]
  exact add_le_add hV hB



theorem abs_finset_sum_mul_le_sqrt_mul_sqrt
    {ι : Type*} [Fintype ι] (f g : ι → ℝ) :
    |∑ i, f i * g i| ≤ Real.sqrt (∑ i, f i ^ 2) * Real.sqrt (∑ i, g i ^ 2) := by
  rw [abs_le]
  constructor
  · have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (-f) g
    have h' := neg_le_neg h
    simpa only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_neg,
      neg_sq] using h'
  · exact Real.sum_mul_le_sqrt_mul_sqrt Finset.univ f g

/-- A fixed-shift cross energy has the same limit as the unshifted energy once
the shifted row is asymptotically equal in the scaled discrete L2 norm. -/
theorem weighted_cross_energy_tendsto_of_scaled_l2
    (κ : ℕ → Type*) [∀ n, Fintype (κ n)]
    (N : ℕ → ℝ) (w u : ∀ n, κ n → ℝ) (E : ℝ)
    (hN : ∀ᶠ n in atTop, 0 ≤ N n)
    (henergy : Tendsto (fun n => N n * ∑ i, w n i ^ 2) atTop (𝓝 E))
    (hshift : Tendsto (fun n => N n * ∑ i, (u n i - w n i) ^ 2)
      atTop (𝓝 0)) :
    Tendsto (fun n => N n * ∑ i, w n i * u n i) atTop (𝓝 E) := by
  let A := fun n => N n * ∑ i, w n i ^ 2
  let D := fun n => N n * ∑ i, (u n i - w n i) ^ 2
  let R := fun n => N n * ∑ i, w n i * (u n i - w n i)
  have hA0 : ∀ᶠ n in atTop, 0 ≤ A n := by
    filter_upwards [hN] with n hn
    exact mul_nonneg hn (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hD0 : ∀ᶠ n in atTop, 0 ≤ D n := by
    filter_upwards [hN] with n hn
    exact mul_nonneg hn (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hbound : ∀ᶠ n in atTop, |R n| ≤ Real.sqrt (A n) * Real.sqrt (D n) := by
    filter_upwards [hN] with n hn
    have hs := abs_finset_sum_mul_le_sqrt_mul_sqrt
      (fun i => Real.sqrt (N n) * w n i)
      (fun i => Real.sqrt (N n) * (u n i - w n i))
    have hsqrt : Real.sqrt (N n) ^ 2 = N n := Real.sq_sqrt hn
    have hleft : R n = ∑ i,
        (Real.sqrt (N n) * w n i) *
          (Real.sqrt (N n) * (u n i - w n i)) := by
      dsimp [R]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      have hroot : Real.sqrt (N n) * Real.sqrt (N n) = N n := by
        simpa only [pow_two] using hsqrt
      calc
        N n * (w n i * (u n i - w n i)) =
            (Real.sqrt (N n) * Real.sqrt (N n)) *
              (w n i * (u n i - w n i)) := by rw [hroot]
        _ = _ := by ring
    have hrightA : (∑ i, (Real.sqrt (N n) * w n i) ^ 2) = A n := by
      dsimp [A]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_pow, hsqrt]
    have hrightD : (∑ i, (Real.sqrt (N n) * (u n i - w n i)) ^ 2) = D n := by
      dsimp [D]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_pow, hsqrt]
    rw [hleft, ← hrightA, ← hrightD]
    exact hs
  have hR : Tendsto R atTop (𝓝 0) := by
    have hsA : Tendsto (fun n => Real.sqrt (A n)) atTop (𝓝 (Real.sqrt E)) :=
      Real.continuous_sqrt.continuousAt.tendsto.comp (by simpa only [A] using henergy)
    have hsD : Tendsto (fun n => Real.sqrt (D n)) atTop (𝓝 0) := by
      have hDt : Tendsto D atTop (𝓝 0) := by simpa only [D] using hshift
      change Tendsto ((fun x : ℝ => Real.sqrt x) ∘ D) atTop (𝓝 0)
      simpa only [Real.sqrt_zero] using
        Real.continuous_sqrt.continuousAt.tendsto.comp hDt
    have hprod : Tendsto (fun n => Real.sqrt (A n) * Real.sqrt (D n))
        atTop (𝓝 0) := by
      simpa only [mul_zero] using hsA.mul hsD
    apply tendsto_of_abs_sub_le_zero R (fun _ => 0)
      (fun n => Real.sqrt (A n) * Real.sqrt (D n)) 0 tendsto_const_nhds
      hprod
    · filter_upwards [hA0, hD0] with n hAn hDn
      exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    · filter_upwards [hbound] with n hn
      simpa only [sub_zero] using hn
  have hid : (fun n => N n * ∑ i, w n i * u n i) = fun n => A n + R n := by
    funext n
    dsimp [A, R]
    rw [← mul_add, ← Finset.sum_add_distrib]
    apply congrArg (fun z => N n * z)
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hid]
  simpa only [A, add_zero] using henergy.add hR

/-- Fixed-lag form of `weighted_cross_energy_tendsto_of_scaled_l2`, with the
terminal entries of the shifted row set to zero.  Thus the only model-specific
input is the scaled discrete L2 translation estimate. -/
theorem weighted_fixedShift_energy_tendsto_of_scaled_l2
    (m : ℕ → ℕ) (N : ℕ → ℝ) (w : ∀ n, Fin (m n) → ℝ) (k : ℕ) (E : ℝ)
    (hN : ∀ᶠ n in atTop, 0 ≤ N n)
    (henergy : Tendsto (fun n => N n * ∑ i, w n i ^ 2) atTop (𝓝 E))
    (hshift : Tendsto (fun n => N n * ∑ i,
      (finZeroExtendedShift k (w n) i - w n i) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => N n * ∑ i,
      w n i * finZeroExtendedShift k (w n) i) atTop (𝓝 E) := by
  exact weighted_cross_energy_tendsto_of_scaled_l2
    (fun n => Fin (m n)) N w (fun n => finZeroExtendedShift k (w n)) E
    hN henergy hshift

theorem localPolynomialWeights_fixedShift_scaledL2_tendsto
    (r q k : ℕ) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop) :
    Tendsto (fun n : ℕ => (n : ℝ) * δ n *
      ∑ i, (finZeroExtendedShift k
          (localPolynomialWeights r n q (δ n) t) i -
        localPolynomialWeights r n q (δ n) t i) ^ 2) atTop (𝓝 0) := by
  classical
  choose L hL using fun j : Fin (r + 1) => kernelMomentFunction_lipschitz j.val
  obtain ⟨Ni, hNi, D, hD, hinv⟩ := localDesignGram_uniform_inverse r q
  obtain ⟨Nw, hNw, Cw, hCw, hw⟩ := localPolynomialWeights_uniform_stability r q
  let C : ℝ := ∑ j : Fin (r + 1), D * (L j : ℝ)
  let N : ℕ → ℝ := fun n => (n : ℝ) * δ n
  let a : ℕ → ℝ := fun n => (N n)⁻¹ * C * ((k : ℝ) / N n)
  let b : ℕ → ℝ := fun n => Cw / N n
  have hC : 0 ≤ C := Finset.sum_nonneg (fun j _ => mul_nonneg hD (L j).coe_nonneg)
  have hInv : Tendsto (fun n => (N n)⁻¹) atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp (by simpa only [N] using hN)
  let U : ℕ → ℝ := fun n =>
    6 * (C * (k : ℝ)) ^ 2 * (N n)⁻¹ ^ 2 +
      (k : ℝ) * Cw ^ 2 * (N n)⁻¹
  have hU : Tendsto U atTop (𝓝 0) := by
    have h1 := (hInv.pow 2).const_mul (6 * (C * (k : ℝ)) ^ 2)
    have h2 := hInv.const_mul ((k : ℝ) * Cw ^ 2)
    simpa [U] using h1.add h2
  apply squeeze_zero'
  · filter_upwards [hδpos, eventually_ge_atTop 1] with n hnδ hn
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hnδ.le)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  · filter_upwards [hδpos,
      hδ.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
      hN.eventually_ge_atTop (max Ni (max Nw 1)),
      eventually_ge_atTop (q + 1)] with n hnδ hnδhalf hnN hnq
    have hn0 : 0 < n := by omega
    have hqn : q ≤ n := by omega
    have hNpos : 0 < N n := by
      dsimp [N]
      positivity
    have hNiN : Ni ≤ N n := le_trans (le_max_left _ _) hnN
    have hNwN : Nw ≤ N n := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hnN)
    have hOneN : 1 ≤ N n :=
      le_trans (le_max_right Nw 1) (le_trans (le_max_right Ni _) hnN)
    obtain ⟨_, hinvN⟩ :=
      hinv n hn0 hqn (δ n) t hnδ hnδhalf.le ⟨ht.1.le, ht.2.le⟩ hNiN
    obtain ⟨_, hweight, _, _⟩ :=
      hw n hn0 hqn (δ n) t hnδ hnδhalf.le ⟨ht.1.le, ht.2.le⟩ hNwN
    let active : Fin (n - q) → Prop := fun i =>
      |(grid n i.val - t) / δ n| < 1
    have hactive : (((Finset.univ.filter active).card : ℝ) ≤ 3 * N n) := by
      have hc := midpoint_active_card_bound n (n - q) hn0 (δ n) t hnδ
        (Finset.univ.filter active) (fun i hi => by
          simpa only [active, Finset.mem_filter, Finset.mem_univ, true_and] using hi)
      dsimp [N]
      linarith
    have ha0 : 0 ≤ a n := by
      dsimp [a]
      positivity
    have hb0 : 0 ≤ b n := by
      dsimp [b]
      positivity
    have hsum := finZeroExtendedShift_sq_sum_bound k
      (localPolynomialWeights r n q (δ n) t) active
      (a n) (b n) (3 * N n) ha0 hb0
      (fun i hi => by
        have hp := localPolynomialWeights_fixedShift_pointwise r n q k
          (δ n) t D hn0 hnδ hD L hL (fun j => hinvN 0 j) i hi
        convert hp using 1
        dsimp [a, C, N]
        simp only [← Finset.sum_mul]
        ring)
      (fun i hi hia his => by
        have hz1 := localPolynomialWeights_zero r n q (δ n) t i (le_of_not_gt hia)
        have hz2 := localPolynomialWeights_zero r n q (δ n) t
          ⟨i.val + k, hi⟩ (le_of_not_gt his)
        rw [hz1, hz2, sub_self])
      (fun i => by
        simpa only [b, N] using hweight i)
      hactive
    have hmul := mul_le_mul_of_nonneg_left hsum hNpos.le
    calc
      N n * ∑ i, (finZeroExtendedShift k
          (localPolynomialWeights r n q (δ n) t) i -
        localPolynomialWeights r n q (δ n) t i) ^ 2
          ≤ N n * (2 * (3 * N n) * (a n) ^ 2 + (k : ℝ) * (b n) ^ 2) := hmul
      _ = U n := by
        dsimp [a, b, U]
        field_simp
        ring
  · exact hU



/-- Every fixed-lag product of actual interior local-polynomial weights has
the same equivalent-kernel energy limit as the unshifted product. -/
theorem localPolynomialWeights_fixedShift_energy_tendsto
    (r q k : ℕ) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop) :
    Tendsto (fun n : ℕ => (n : ℝ) * δ n * ∑ i,
      localPolynomialWeights r n q (δ n) t i *
        finZeroExtendedShift k
          (localPolynomialWeights r n q (δ n) t) i) atTop
      (𝓝 (∫ x in (-1 : ℝ)..1, equivalentKernel r x ^ 2)) := by
  apply weighted_fixedShift_energy_tendsto_of_scaled_l2
    (fun n => n - q) (fun n => (n : ℝ) * δ n)
    (fun n => localPolynomialWeights r n q (δ n) t) k
    (∫ x in (-1 : ℝ)..1, equivalentKernel r x ^ 2)
  · filter_upwards [hδpos] with n hn
    exact mul_nonneg (Nat.cast_nonneg n) hn.le
  · exact localPolynomialWeights_energy_tendsto_integral
      r q t ht δ hδpos hδ hN
  · exact localPolynomialWeights_fixedShift_scaledL2_tendsto
      r q k t ht δ hδpos hδ hN

end Hurst
