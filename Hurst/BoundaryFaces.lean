import Hurst.TruncatedRieszCycleBridge
import Hurst.LatticeReindex

/-!
# Boundary faces of the fixed-cutoff unit-cube lattice sum

This file supplies the deterministic bounds needed to compare the
right-endpoint lattice sum `offsetLatticeSum` (the reindexed matrix trace) with
the full lattice sum `unitCubeTruncatedRieszLatticeSum`, and the uniform bound
on the capped unit-cube integrand itself.

Main results:

* `affine_unit_cube_mem_Icc`: the affine coordinate `2 * y i - 1` of a unit-cube
  point lands in `[-1, 1]`.
* `unitCubeWeightedTruncatedRieszIntegrand_abs_le`: uniform bound
  `|integrand y| ≤ (|c| * (R+1)^psi * B_omega)^k` on the whole unit cube
  (each capped edge factor is at most `|c| * (R+1)^psi` because the cap floor
  dominates the distance, times `B_omega` for the weight).
* `offsetLatticeSum_abs_le`: the right-endpoint lattice sum (over `m^k` tuples)
  is at most `m^k` times that uniform bound.
* `lattice_point_count`: the full scaled lattice inside the unit cube has at
  most `(m+1)^k` points, via the coordinate injection into `Fin k → Fin (m+1)`.
* `unitCubeTruncatedRieszLatticeSum_abs_le`: the normalized lattice sum is at
  most `((m+1)/m)^k` times the uniform bound.
* `tendsto_mesh_factor_atTop`: `((m+1)/m)^k → 1`, the vanishing mesh-factor
  used when re-normalizing.
-/

noncomputable section

open scoped Pointwise
open Filter
open scoped Topology

namespace Hurst

/-! ### Affine coordinates of the unit cube -/

theorem mem_rieszUnitCube_iff {k : ℕ} {y : Fin k → ℝ} :
    y ∈ rieszUnitCube k ↔ ∀ i : Fin k, y i ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · intro hy i
    exact ⟨hy.1 i, hy.2 i⟩
  · intro hy
    exact ⟨fun i => (hy i).1, fun i => (hy i).2⟩

/-- The affine coordinate `2 * y i - 1` of a point of the unit cube lies in
`[-1, 1]`. -/
theorem affine_unit_cube_mem_Icc {k : ℕ} {y : Fin k → ℝ}
    (hy : y ∈ rieszUnitCube k) (i : Fin k) :
    2 * y i - 1 ∈ Set.Icc (-1 : ℝ) 1 := by
  rw [mem_rieszUnitCube_iff] at hy
  have h := hy i
  have h1 := h.1
  have h2 := h.2
  constructor <;> linarith

/-! ### The uniform integrand bound -/

/-- The cutoff to the power `-psi` equals `(R+1)^psi`. -/
theorem rieszCycleCutoff_rpow_neg (R : ℕ) (psi : ℝ) :
    rieszCycleCutoff R ^ (-psi) = ((R + 1 : ℝ)) ^ psi := by
  unfold rieszCycleCutoff
  rw [Real.inv_rpow (by positivity), Real.rpow_neg (by positivity) psi,
    inv_inv, Nat.cast_add, Nat.cast_one]

/-- The capped kernel is uniformly bounded: the cap floor dominates the
distance, so `(max cutoff |x-y|)^(-psi) ≤ cutoff^(-psi) = (R+1)^psi` for
`0 ≤ psi`. -/
theorem truncatedRieszKernel_abs_le (R : ℕ) (psi c x y : ℝ) (hpsi : 0 ≤ psi) :
    |truncatedRieszKernel R psi c x y| ≤ |c| * ((R + 1 : ℝ)) ^ psi := by
  have hd : 0 < max (rieszCycleCutoff R) |x - y| :=
    (rieszCycleCutoff_pos R).trans_le (le_max_left _ _)
  have hcap : (max (rieszCycleCutoff R) |x - y|) ^ (-psi)
      ≤ ((R + 1 : ℝ)) ^ psi := by
    have h' : (max (rieszCycleCutoff R) |x - y|) ^ (-psi)
        ≤ rieszCycleCutoff R ^ (-psi) :=
      Real.rpow_le_rpow_of_nonpos (rieszCycleCutoff_pos R) (le_max_left _ _)
        (by linarith)
    rw [rieszCycleCutoff_rpow_neg] at h'
    exact h'
  unfold truncatedRieszKernel
  rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hd (-psi))]
  exact mul_le_mul_of_nonneg_left hcap (abs_nonneg c)

/-- **Uniform integrand bound on the unit cube.**  For `y ∈ [0,1]^k` the
capped, weighted, cyclic integrand satisfies
`|integrand y| ≤ (|c| * (R+1)^psi * B_omega)^k`, given `0 ≤ psi` and a uniform
bound `|omega| ≤ B_omega` on `[-1,1]` (where the integrand evaluates its
weight). -/
theorem unitCubeWeightedTruncatedRieszIntegrand_abs_le
    (k R : ℕ) (psi c : ℝ) (omega : ℝ → ℝ) (B_omega : ℝ)
    (hpsi : 0 ≤ psi)
    (homegaB : ∀ z ∈ Set.Icc (-1 : ℝ) 1, |omega z| ≤ B_omega)
    (y : Fin k → ℝ) (hy : y ∈ rieszUnitCube k) :
    |unitCubeWeightedTruncatedRieszIntegrand k R psi c omega y|
      ≤ (|c| * ((R + 1 : ℝ)) ^ psi * B_omega) ^ k := by
  have hzy : ∀ i : Fin k, rieszUnitToSymmetricCube y i ∈ Set.Icc (-1 : ℝ) 1 :=
    fun i => affine_unit_cube_mem_Icc hy i
  have hfactor : ∀ i : Fin k,
      |omega (rieszUnitToSymmetricCube y i) *
          truncatedRieszKernel R psi c (rieszUnitToSymmetricCube y i)
            (rieszUnitToSymmetricCube y (finCyclicSucc i))|
        ≤ |c| * ((R + 1 : ℝ)) ^ psi * B_omega := by
    intro i
    have hw := homegaB (rieszUnitToSymmetricCube y i) (hzy i)
    have hk := truncatedRieszKernel_abs_le R psi c
      (rieszUnitToSymmetricCube y i)
      (rieszUnitToSymmetricCube y (finCyclicSucc i)) hpsi
    rw [abs_mul]
    have hBomega' : (0 : ℝ) ≤ B_omega :=
      le_trans (abs_nonneg (omega (rieszUnitToSymmetricCube y i)))
        (homegaB _ (hzy i))
    have hsplit : |omega (rieszUnitToSymmetricCube y i)| *
          |truncatedRieszKernel R psi c (rieszUnitToSymmetricCube y i)
            (rieszUnitToSymmetricCube y (finCyclicSucc i))|
        ≤ B_omega * (|c| * ((R + 1 : ℝ)) ^ psi) :=
      mul_le_mul hw hk (abs_nonneg _) hBomega'
    calc |omega (rieszUnitToSymmetricCube y i)| *
          |truncatedRieszKernel R psi c (rieszUnitToSymmetricCube y i)
            (rieszUnitToSymmetricCube y (finCyclicSucc i))|
        ≤ B_omega * (|c| * ((R + 1 : ℝ)) ^ psi) := hsplit
      _ = |c| * ((R + 1 : ℝ)) ^ psi * B_omega := by ring
  rw [unitCubeWeightedTruncatedRieszIntegrand,
    weightedTruncatedRieszCycleIntegrand, Finset.abs_prod]
  calc ∏ i : Fin k,
        |omega (rieszUnitToSymmetricCube y i) *
            truncatedRieszKernel R psi c (rieszUnitToSymmetricCube y i)
              (rieszUnitToSymmetricCube y (finCyclicSucc i))|
      ≤ ∏ _i : Fin k, (|c| * ((R + 1 : ℝ)) ^ psi * B_omega) :=
      Finset.prod_le_prod (fun _i _ => abs_nonneg _) (fun i _ => hfactor i)
    _ = (|c| * ((R + 1 : ℝ)) ^ psi * B_omega) ^ k := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ### The right-endpoint lattice sum -/

/-- The right-endpoint grid points lie in the unit cube. -/
theorem offsetLatticePoint_mem_cube (m k : ℕ) (w : Fin k → Fin m) :
    offsetLatticePoint w ∈ rieszUnitCube k := by
  rw [mem_rieszUnitCube_iff]
  intro i
  have hm : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast lt_of_le_of_lt (Nat.zero_le (w i).val) (w i).isLt
  constructor
  · exact div_nonneg (by positivity) (by positivity)
  · show ((((w i : ℕ) + 1 : ℕ) : ℝ)) / ((m : ℝ)) ≤ 1
    rw [div_le_one hm]
    have hle : ((w i : ℕ) + 1 : ℕ) ≤ m := by omega
    exact_mod_cast hle

/-- **The right-endpoint lattice sum is uniformly bounded** by its number
`m^k` of tuples times the uniform integrand bound. -/
theorem offsetLatticeSum_abs_le (m k R : ℕ) (psi c : ℝ) (omega : ℝ → ℝ)
    (B_omega : ℝ) (hpsi : 0 ≤ psi)
    (homegaB : ∀ z ∈ Set.Icc (-1 : ℝ) 1, |omega z| ≤ B_omega) :
    |offsetLatticeSum m k R psi c omega|
      ≤ ((m : ℝ)) ^ k * (|c| * ((R + 1 : ℝ)) ^ psi * B_omega) ^ k := by
  unfold offsetLatticeSum
  have hbound := unitCubeWeightedTruncatedRieszIntegrand_abs_le k R psi c omega
    B_omega hpsi homegaB
  have hmem : ∀ w : Fin k → Fin m, offsetLatticePoint w ∈ rieszUnitCube k :=
    fun w => offsetLatticePoint_mem_cube m k w
  calc |∑ w : Fin k → Fin m,
        unitCubeWeightedTruncatedRieszIntegrand k R psi c omega
          (offsetLatticePoint w)|
      ≤ ∑ w : Fin k → Fin m,
        |unitCubeWeightedTruncatedRieszIntegrand k R psi c omega
          (offsetLatticePoint w)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _w : Fin k → Fin m, (|c| * ((R + 1 : ℝ)) ^ psi * B_omega) ^ k :=
      Finset.sum_le_sum (fun w _ => hbound _ (hmem w))
    _ = ((m : ℝ)) ^ k * (|c| * ((R + 1 : ℝ)) ^ psi * B_omega) ^ k := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        show Fintype.card (Fin k → Fin m) = m ^ k from by
          rw [← Nat.card_eq_fintype_card, Nat.card_pi, Finset.prod_const,
            Finset.card_univ, Fintype.card_fin, Nat.card_fin]]
      push_cast
      ring

/-! ### Coordinates of scaled lattice points -/

/-- Membership in the integer lattice forces each coordinate to be integral. -/
theorem rieszIntegerLattice_coord (k : ℕ) (n : Fin k → ℝ) (i : Fin k)
    (hn : n ∈ rieszIntegerLattice k) : ∃ a : ℤ, n i = (a : ℝ) := by
  have hsub : rieszIntegerLattice k ≤
      (Submodule.span ℤ ({(1 : ℝ)} : Set ℝ)).comap
        (LinearMap.proj i : (Fin k → ℝ) →ₗ[ℤ] ℝ) := by
    unfold rieszIntegerLattice
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, Submodule.mem_span_singleton]
    by_cases hji : j = i
    · refine ⟨1, ?_⟩
      simp [Pi.basisFun_apply, hji]
    · exact ⟨0, by simp [Pi.basisFun_apply, hji]⟩
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp
    (Submodule.mem_comap.mp (hsub hn))
  refine ⟨a, ?_⟩
  simpa using ha.symm

/-- A point of the scaled integer lattice inside the unit cube has all
coordinates of the form `a / m` with a natural number `a ≤ m`. -/
theorem exists_lattice_cube_coord (m k : ℕ) (y : Fin k → ℝ)
    (hy : y ∈ rieszUnitCube k ∩ ((m : ℝ)⁻¹ • rieszIntegerLattice k)) :
    ∃ a : Fin k → ℕ, (∀ i, a i ≤ m) ∧ ∀ i, y i = ((a i : ℝ)) / (m : ℝ) := by
  obtain ⟨hy1, hy2⟩ := hy
  rw [mem_rieszUnitCube_iff] at hy1
  obtain ⟨n, hnmem, hyn⟩ := Set.mem_smul_set.mp hy2
  have hyi : ∀ i, ((m : ℝ)⁻¹ * n i) = y i := by
    intro i
    have h := congrFun hyn i
    simpa using h
  choose f hf using fun i => rieszIntegerLattice_coord k n i hnmem
  by_cases hm : m = 0
  · subst hm
    refine ⟨fun _ => 0, fun _ => le_refl _, fun i => ?_⟩
    have hy0 : y i = 0 := by
      rw [← hyi i]
      norm_num
    rw [hy0]
    norm_num
  · have hmy : ∀ i, (m : ℝ) * y i = f i := by
      intro i
      rw [← hyi i, hf i]
      field_simp
    refine ⟨fun i => (f i).toNat, fun i => ?_, fun i => ?_⟩
    · have hfipos : (0 : ℤ) ≤ f i := by
        have h0 : ((0 : ℤ) : ℝ) ≤ ((f i : ℤ) : ℝ) := by
          rw [← hmy i, Int.cast_zero]
          exact mul_nonneg (Nat.cast_nonneg m) ((hy1 i).1)
        exact Int.cast_le.1 h0
      have hfiz : (f i : ℤ) ≤ (m : ℤ) := by
        have h1 : ((f i : ℤ) : ℝ) ≤ (m : ℝ) := by
          rw [← hmy i]
          have h2' : (m : ℝ) * y i ≤ (m : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left (hy1 i).2 (Nat.cast_nonneg m)
          rw [mul_one] at h2'
          exact h2'
        exact Int.cast_le.mp h1
      have h1 : (f i).toNat ≤ m := by
        have h2 : ((f i).toNat : ℤ) ≤ (m : ℤ) := by
          rw [Int.toNat_of_nonneg hfipos]; exact hfiz
        exact_mod_cast h2
      exact h1
    · have hfipos : (0 : ℤ) ≤ f i := by
        have h0 : ((0 : ℤ) : ℝ) ≤ ((f i : ℤ) : ℝ) := by
          rw [← hmy i, Int.cast_zero]
          exact mul_nonneg (Nat.cast_nonneg m) ((hy1 i).1)
        exact Int.cast_le.1 h0
      have hcast : (((f i).toNat : ℕ) : ℝ) = ((f i : ℤ) : ℝ) := by
        have hz := Int.toNat_of_nonneg hfipos
        exact_mod_cast hz
      rw [hcast, ← hmy i]
      field_simp

/-- **Lattice point count.**  The scaled integer lattice meets the unit cube in
at most `(m+1)^k` points: the coordinate tuple `a i ≤ m` is an injection into
`Fin k → Fin (m+1)`. -/
theorem lattice_point_count (m k : ℕ) :
    Nat.card ↥(rieszUnitCube k ∩ ((m : ℝ)⁻¹ • rieszIntegerLattice k))
      ≤ (m + 1) ^ k := by
  classical
  set S := rieszUnitCube k ∩ ((m : ℝ)⁻¹ • rieszIntegerLattice k) with hS
  have hex : ∀ y : ↥S, ∃ a : Fin k → ℕ, (∀ i, a i ≤ m) ∧
      ∀ i, (y : Fin k → ℝ) i = ((a i : ℝ)) / (m : ℝ) :=
    fun y => exists_lattice_cube_coord m k y y.2
  choose g hg1 hg2 using hex
  set f : ↥S → (Fin k → Fin (m + 1)) :=
    fun y i => ⟨g y i, Nat.lt_succ_of_le (hg1 y i)⟩ with hf
  have hinj : Function.Injective f := by
    intro y z h
    have hgi : ∀ i, g y i = g z i := fun i =>
      congrArg Fin.val (congrFun h i)
    have hval : ∀ i, (y : Fin k → ℝ) i = (z : Fin k → ℝ) i := by
      intro i
      rw [hg2 y i, hg2 z i, hgi i]
    exact Subtype.ext (funext hval)
  haveI : Finite ↥S := Finite.of_injective f hinj
  haveI : Fintype ↥S := Fintype.ofFinite (α := ↥S)
  calc Nat.card ↥S = Fintype.card ↥S := Nat.card_eq_fintype_card
    _ ≤ Fintype.card (Fin k → Fin (m + 1)) := Fintype.card_le_of_injective f hinj
    _ = (m + 1) ^ k := by
        rw [← Nat.card_eq_fintype_card, Nat.card_pi, Finset.prod_const,
          Finset.card_univ, Fintype.card_fin, Nat.card_fin]

/-! ### The full lattice sum -/

/-- **The full unit-cube lattice sum is uniformly bounded** by `((m+1)/m)^k`
times the uniform integrand bound: the tsum has at most `(m+1)^k` terms of size
at most the uniform bound, and the whole sum is divided by `m^k`. -/
theorem unitCubeTruncatedRieszLatticeSum_abs_le (m k R : ℕ) (psi c : ℝ)
    (omega : ℝ → ℝ) (B_omega : ℝ) (hpsi : 0 ≤ psi)
    (homegaB : ∀ z ∈ Set.Icc (-1 : ℝ) 1, |omega z| ≤ B_omega) :
    |unitCubeTruncatedRieszLatticeSum m k R psi c omega|
      ≤ (((m : ℝ) + 1) / (m : ℝ)) ^ k
        * (|c| * ((R + 1 : ℝ)) ^ psi * B_omega) ^ k := by
  classical
  unfold unitCubeTruncatedRieszLatticeSum
  set S := rieszUnitCube k ∩ ((m : ℝ)⁻¹ • rieszIntegerLattice k) with hS
  set B := (|c| * ((R + 1 : ℝ)) ^ psi * B_omega) ^ k with hB
  have hBomega : (0 : ℝ) ≤ B_omega :=
    le_trans (abs_nonneg (omega 0)) (homegaB 0 ⟨by norm_num, by norm_num⟩)
  have hB0 : (0 : ℝ) ≤ B := by
    rw [hB]
    exact pow_nonneg (mul_nonneg (mul_nonneg (abs_nonneg c)
      (Real.rpow_nonneg (x := (R : ℝ) + 1) (by positivity) psi)) hBomega) k
  have hpt := unitCubeWeightedTruncatedRieszIntegrand_abs_le k R psi c omega
    B_omega hpsi homegaB
  have hex : ∀ y : ↥S, ∃ a : Fin k → ℕ, (∀ i, a i ≤ m) ∧
      ∀ i, (y : Fin k → ℝ) i = ((a i : ℝ)) / (m : ℝ) :=
    fun y => exists_lattice_cube_coord m k y y.2
  choose g hg1 hg2 using hex
  set f : ↥S → (Fin k → Fin (m + 1)) :=
    fun y i => ⟨g y i, Nat.lt_succ_of_le (hg1 y i)⟩ with hf
  have hinj : Function.Injective f := by
    intro y z h
    have hgi : ∀ i, g y i = g z i := fun i =>
      congrArg Fin.val (congrFun h i)
    have hval : ∀ i, (y : Fin k → ℝ) i = (z : Fin k → ℝ) i := by
      intro i
      rw [hg2 y i, hg2 z i, hgi i]
    exact Subtype.ext (funext hval)
  haveI : Finite ↥S := Finite.of_injective f hinj
  haveI : Fintype ↥S := Fintype.ofFinite (α := ↥S)
  have hcardNat := lattice_point_count m k
  rw [Nat.card_eq_fintype_card] at hcardNat
  have hsum : |∑' y : ↥S,
      unitCubeWeightedTruncatedRieszIntegrand k R psi c omega
        (y : Fin k → ℝ)| ≤ ((m : ℕ) + 1 : ℕ) ^ k * B := by
    have hcard : ((Fintype.card ↥S : ℕ) : ℝ) ≤ (((m : ℕ) + 1 : ℕ) : ℝ) ^ k := by
      exact_mod_cast hcardNat
    rw [tsum_fintype]
    calc |∑ y : ↥S,
          unitCubeWeightedTruncatedRieszIntegrand k R psi c omega
            (y : Fin k → ℝ)|
        ≤ ∑ y : ↥S,
          |unitCubeWeightedTruncatedRieszIntegrand k R psi c omega
            (y : Fin k → ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _y : ↥S, B := Finset.sum_le_sum (fun y _ => by
          exact hpt _ ((Set.mem_inter_iff _ _ _).mp y.2).1)
      _ = ((Fintype.card ↥S : ℕ) : ℝ) * B := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ((m : ℕ) + 1 : ℕ) ^ k * B := mul_le_mul_of_nonneg_right hcard hB0
  simp only [Fintype.card_fin]
  rcases eq_or_ne ((m : ℝ) ^ k) 0 with hz | hz
  · have hzero :
        |(∑' y : ↥S,
          unitCubeWeightedTruncatedRieszIntegrand k R psi c omega
            (y : Fin k → ℝ)) / (m : ℝ) ^ k| = 0 := by
      rw [hz, div_zero, abs_zero]
    rw [hzero]
    exact mul_nonneg
      (pow_nonneg (div_nonneg (by positivity) (Nat.cast_nonneg m)) k) hB0
  · rw [abs_div, div_le_iff₀ (abs_pos.mpr hz)]
    have hmabs : |(m : ℝ) ^ k| = (m : ℝ) ^ k :=
      abs_of_nonneg (pow_nonneg (Nat.cast_nonneg m) k)
    have hcancel : (((m : ℝ) + 1) / (m : ℝ)) ^ k * ((m : ℝ) ^ k)
        = ((m : ℕ) + 1 : ℕ) ^ k := by
      rw [div_pow]
      field_simp
      push_cast
      ring
    rw [mul_right_comm, hmabs, hcancel]
    exact hsum

/-! ### The vanishing mesh factor -/

/-- `((m+1)/m)^k → 1`: the power of the mesh factor that appears when
comparing the `(m+1)^k` lattice points against the `m^k` normalization. -/
theorem tendsto_mesh_factor_atTop {k : ℕ} :
    Tendsto (fun m : ℕ => (((m : ℝ) + 1) / (m : ℝ)) ^ k) atTop (𝓝 1) := by
  have h1 : Tendsto (fun m : ℕ => ((m : ℝ))⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun m : ℕ => 1 + ((m : ℝ))⁻¹) atTop (𝓝 (1 : ℝ)) :=
    by simpa using h1.const_add (1 : ℝ)
  have h3 : Tendsto (fun m : ℕ => (1 + ((m : ℝ))⁻¹) ^ k)
      atTop (𝓝 ((1 : ℝ) ^ k)) := h2.pow k
  rw [one_pow] at h3
  refine Tendsto.congr' ?_ h3
  have hmem : ∀ᶠ m : ℕ in atTop, 1 ≤ m := eventually_atTop.2 ⟨1, fun m hm => hm⟩
  filter_upwards [hmem] with m hm
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  rw [show (((m : ℝ) + 1) / (m : ℝ)) = 1 + ((m : ℝ))⁻¹ by
    rw [add_div, div_self hm0, inv_eq_one_div]]

end Hurst
