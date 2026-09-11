import Hurst.LatticeReindex
import Hurst.BoundaryFaces
import Hurst.MeshFactorizationLimit

/-!
# Assembly of the fixed-cutoff matrix lattice reindex

This file assembles the predicate `HasFixedCutoffMatrixLatticeReindex` from
the proved pieces:

* `Hurst.LatticeReindex`: the exact identity
  `weightedTruncatedRieszDiscreteCycleValue m k R S psi c omega
    = ((2 : ℝ) / m) ^ k * (((m : ℝ) / (2 * S)) ^ k * offsetLatticeSum ...)`
  (mesh-normalized form, `weightedTruncatedRieszDiscreteCycleValue_eq_meshScaled`).
* `Hurst.BoundaryFaces`: the uniform integrand bound and the embedding of the
  right-endpoint grid into the scaled integer lattice.
* `Hurst.MeshFactorizationLimit`: the mesh factor limits.

The single new piece of bookkeeping is the boundary-face difference bound
`abs_offsetLatticeSum_sub_latticeTsum_le`: the right-endpoint lattice sum
agrees with the full unit-cube lattice tsum up to the contribution of the
lattice points *outside* its image (the lower faces, of which there are at
most `(m+1)^k - m^k`), each bounded by the uniform integrand bound.
-/

noncomputable section

open Set Filter
open scoped Topology Pointwise

namespace Hurst

/-! ### Integer vectors lie in the scaled lattice -/

/-- A vector with natural coordinates lies in the canonical integer lattice. -/
theorem natVector_mem_rieszIntegerLattice {k : ℕ} (a : Fin k → ℕ) :
    (fun i => ((a i : ℝ))) ∈ rieszIntegerLattice k := by
  rw [rieszIntegerLattice, Submodule.mem_span_range_iff_exists_fun]
  refine ⟨fun i => ((a i : ℤ)), ?_⟩
  funext i
  simp [Pi.basisFun_apply, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq']

/-- The right-endpoint grid point of a vertex tuple lies on the scaled integer
lattice inside the unit cube: each coordinate is `(w i + 1)/m`. -/
theorem offsetLatticePoint_mem_lattice (m k : ℕ) (w : Fin k → Fin m) :
    offsetLatticePoint w ∈ rieszUnitCube k ∩ ((m : ℝ)⁻¹ • rieszIntegerLattice k) := by
  refine ⟨offsetLatticePoint_mem_cube m k w, ?_⟩
  rw [Set.mem_smul_set]
  exact ⟨fun i => (((w i : ℕ) + 1 : ℕ) : ℝ),
    natVector_mem_rieszIntegerLattice (fun i => ((w i : ℕ) + 1 : ℕ)), by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, offsetLatticePoint, div_eq_inv_mul]⟩

/-! ### The boundary-face difference bound -/

/-- **Boundary-face difference bound.**  The right-endpoint lattice sum
`offsetLatticeSum` differs from the full unit-cube lattice tsum by at most the
number of lattice points outside its image (at most `(m+1)^k - m^k`, the lower
faces) times the uniform integrand bound. -/
theorem abs_offsetLatticeSum_sub_latticeTsum_le
    (m k R : ℕ) (psi c : ℝ) (omega : ℝ → ℝ) (B_omega : ℝ)
    (hpsi : 0 ≤ psi)
    (homegaB : ∀ z ∈ Set.Icc (-1 : ℝ) 1, |omega z| ≤ B_omega) :
    |offsetLatticeSum m k R psi c omega -
        (∑' y : ↥(rieszUnitCube k ∩ ((m : ℝ)⁻¹ • rieszIntegerLattice k)),
          unitCubeWeightedTruncatedRieszIntegrand k R psi c omega
            (y : Fin k → ℝ))|
      ≤ (((m : ℝ) + 1) ^ k - (m : ℝ) ^ k) *
        (|c| * ((R + 1 : ℝ)) ^ psi * B_omega) ^ k := by
  classical
  set Sset := rieszUnitCube k ∩ ((m : ℝ)⁻¹ • rieszIntegerLattice k) with hSset
  set B := (|c| * ((R + 1 : ℝ)) ^ psi * B_omega) ^ k with hBdef
  have hBomega : (0 : ℝ) ≤ B_omega :=
    le_trans (abs_nonneg (omega 0)) (homegaB 0 ⟨by norm_num, by norm_num⟩)
  have hB0 : (0 : ℝ) ≤ B := by
    rw [hBdef]
    exact pow_nonneg
      (mul_nonneg
        (mul_nonneg (abs_nonneg c)
          (Real.rpow_nonneg (x := (R : ℝ) + 1) (by positivity) psi))
        hBomega) k
  -- Finiteness of the set of lattice points in the cube, via the coordinate
  -- injection into `Fin k → Fin (m+1)` (as in `Hurst.BoundaryFaces`).
  have hex : ∀ y : ↥Sset, ∃ a : Fin k → ℕ, (∀ i, a i ≤ m) ∧
      ∀ i, (y : Fin k → ℝ) i = ((a i : ℝ)) / (m : ℝ) :=
    fun y => exists_lattice_cube_coord m k y y.2
  choose g hg1 hg2 using hex
  have hinjcoord : Function.Injective
      (fun (y : ↥Sset) (i : Fin k) => (⟨g y i, Nat.lt_succ_of_le (hg1 y i)⟩ :
        Fin (m + 1))) := by
    intro y z h
    have hgi : ∀ i, g y i = g z i := fun i =>
      congrArg Fin.val (congrFun h i)
    have hval : ∀ i, (y : Fin k → ℝ) i = (z : Fin k → ℝ) i := fun i => by
      rw [hg2 y i, hg2 z i, hgi i]
    exact Subtype.ext (funext hval)
  haveI : Finite ↥Sset :=
    Finite.of_injective
      (fun (y : ↥Sset) (i : Fin k) => (⟨g y i, Nat.lt_succ_of_le (hg1 y i)⟩ :
        Fin (m + 1))) hinjcoord
  haveI : Fintype ↥Sset := Fintype.ofFinite (α := ↥Sset)
  -- The right-endpoint embedding into the lattice points.
  set emb : (Fin k → Fin m) → ↥Sset :=
    fun w => ⟨offsetLatticePoint w, offsetLatticePoint_mem_lattice m k w⟩ with hemb
  have hinjemb : Function.Injective emb := by
    intro w w' h
    have hval : offsetLatticePoint w = offsetLatticePoint w' :=
      congrArg Subtype.val h
    by_cases hm : m = 0
    · funext i
      exact absurd (w i).isLt (by omega)
    · have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
      have hcoord : ∀ i : Fin k,
          ((((w i : ℕ) + 1 : ℕ) : ℝ)) = ((((w' i : ℕ) + 1 : ℕ) : ℝ)) := by
        intro i
        have hi := congrFun hval i
        simp only [offsetLatticePoint] at hi
        have h2 := congrArg (fun x : ℝ => x * (m : ℝ)) hi
        rw [div_mul_cancel₀ _ hmR, div_mul_cancel₀ _ hmR] at h2
        exact h2
      funext i
      have h2 := Nat.cast_injective (R := ℝ) (hcoord i)
      exact Fin.ext (by omega)
  set img : Finset ↥Sset := Finset.univ.image emb with himg
  have hcardimg : img.card = m ^ k := by
    have h1 : img.card = Fintype.card (Fin k → Fin m) := by
      rw [himg]
      exact (Finset.card_image_of_injective Finset.univ hinjemb).trans
        Finset.card_univ
    rw [h1, Fintype.card_pi]
    simp
  have hfpt : ∀ y : ↥Sset,
      |unitCubeWeightedTruncatedRieszIntegrand k R psi c omega (y : Fin k → ℝ)| ≤ B :=
    fun y => unitCubeWeightedTruncatedRieszIntegrand_abs_le k R psi c omega B_omega
      hpsi homegaB _ ((Set.mem_inter_iff _ _ _).mp y.2).1
  have hcompcard : imgᶜ.card ≤ (m + 1) ^ k - m ^ k := by
    have h1 : imgᶜ.card = Fintype.card ↥Sset - img.card := Finset.card_compl img
    have h2' : Fintype.card ↥Sset ≤ (m + 1) ^ k := by
      have h2 := lattice_point_count m k
      rw [← hSset] at h2
      rwa [← Nat.card_eq_fintype_card]
    rw [h1, hcardimg]
    omega
  -- Split of the tsum into the image part and the lower-face part.
  have hsplitsum : (∑' y : ↥Sset,
      unitCubeWeightedTruncatedRieszIntegrand k R psi c omega (y : Fin k → ℝ))
      = (∑ y ∈ img,
          unitCubeWeightedTruncatedRieszIntegrand k R psi c omega
            (y : Fin k → ℝ)) +
        (∑ y ∈ imgᶜ,
          unitCubeWeightedTruncatedRieszIntegrand k R psi c omega
            (y : Fin k → ℝ)) := by
    rw [tsum_fintype, ← Finset.sum_sdiff (Finset.subset_univ img),
      Finset.compl_eq_univ_sdiff]
    exact add_comm _ _
  have himgsum : (∑ y ∈ img,
      unitCubeWeightedTruncatedRieszIntegrand k R psi c omega (y : Fin k → ℝ))
      = offsetLatticeSum m k R psi c omega := by
    rw [himg, Finset.sum_image (fun x _ y _ h => hinjemb h)]
    simp only [hemb]
    exact Finset.sum_congr rfl fun w _ => rfl
  calc |offsetLatticeSum m k R psi c omega -
        (∑' y : ↥Sset, unitCubeWeightedTruncatedRieszIntegrand k R psi c omega
          (y : Fin k → ℝ))|
      = |∑ y ∈ imgᶜ, unitCubeWeightedTruncatedRieszIntegrand k R psi c omega
          (y : Fin k → ℝ)| := by
        rw [hsplitsum, himgsum]
        have hneg : offsetLatticeSum m k R psi c omega -
            (offsetLatticeSum m k R psi c omega +
              (∑ y ∈ imgᶜ, unitCubeWeightedTruncatedRieszIntegrand k R psi c omega
                (y : Fin k → ℝ)))
            = -(∑ y ∈ imgᶜ, unitCubeWeightedTruncatedRieszIntegrand k R psi c omega
              (y : Fin k → ℝ)) := by ring
        rw [hneg, abs_neg]
    _ ≤ ((imgᶜ.card : ℝ)) * B := by
        calc |∑ y ∈ imgᶜ, unitCubeWeightedTruncatedRieszIntegrand k R psi c omega
              (y : Fin k → ℝ)|
            ≤ ∑ y ∈ imgᶜ, |unitCubeWeightedTruncatedRieszIntegrand k R psi c omega
              (y : Fin k → ℝ)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _y ∈ imgᶜ, B := Finset.sum_le_sum fun y _ => hfpt y
          _ = ((imgᶜ.card : ℝ)) * B := by
              rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (((m : ℕ) + 1) ^ k - m ^ k : ℕ) * B := by
        exact mul_le_mul_of_nonneg_right (Nat.cast_le.2 hcompcard) hB0
    _ = (((m : ℝ) + 1) ^ k - (m : ℝ) ^ k) * B := by
        have hle : m ^ k ≤ (m + 1) ^ k := Nat.pow_le_pow_left (Nat.le_succ m) k
        rw [Nat.cast_sub hle, Nat.cast_pow, Nat.cast_pow, Nat.cast_add, Nat.cast_one]

/-! ### The assembly -/

/-- **Predicate 1, assembled.**  In the mesh regime `m n → ∞`, `m n / S n → 2`
with eventually positive `S n`, `m n`, the fixed-cutoff discrete cyclic value
minus `2^k` times the unit-cube lattice sum tends to `0` for every `k ≥ 2` and
every cutoff `R`. -/
theorem fixedCutoffMatrixLatticeReindex
    (m : ℕ → ℕ) (S : ℕ → ℝ) (psi c : ℝ) (omega : ℝ → ℝ) (B_omega : ℝ)
    (hmtop : Tendsto (fun n => m n) atTop atTop)
    (hMS : Tendsto (fun n => (m n : ℝ) / S n) atTop (𝓝 2))
    (hpos : ∀ᶠ n in atTop, 0 < S n ∧ 0 < m n)
    (hpsi : 0 ≤ psi)
    (homegaB : ∀ z ∈ Set.Icc (-1 : ℝ) 1, |omega z| ≤ B_omega) :
    HasFixedCutoffMatrixLatticeReindex m S psi c omega := by
  intro k hk R
  set B : ℝ := (|c| * ((R + 1 : ℝ)) ^ psi * B_omega) ^ k with hBdef
  have hBge0 : (0 : ℝ) ≤ B := by
    rw [hBdef]
    exact pow_nonneg
      (mul_nonneg
        (mul_nonneg (abs_nonneg c)
          (Real.rpow_nonneg (x := (R : ℝ) + 1) (by positivity) psi))
        (le_trans (abs_nonneg (omega 0)) (homegaB 0 ⟨by norm_num, by norm_num⟩))) k
  have hne : ∀ᶠ n in atTop, (S n : ℝ) ≠ 0 ∧ 0 < (m n : ℝ) :=
    hpos.mono fun n h => ⟨ne_of_gt h.1, by exact_mod_cast h.2⟩
  -- Term A scalar: `m n / (2 * S n) → 1`, hence its `k`-th power tends to `1`.
  have hMS1 : Tendsto (fun n => (m n : ℝ) / (2 * S n)) atTop (𝓝 1) := by
    have h : Tendsto (fun n => (1:ℝ)/2 * ((m n : ℝ) / S n))
        atTop (𝓝 ((1:ℝ)/2 * 2)) := hMS.const_mul _
    rw [show ((1:ℝ)/2 * 2) = 1 by ring] at h
    refine Tendsto.congr' ?_ h
    filter_upwards [hne] with n hn
    have hconv : ((1:ℝ)/2) * ((m n : ℝ) / S n) = (m n : ℝ) / (2 * S n) := by
      field_simp [hn.1]
    rw [hconv]
  have hA : Tendsto (fun n => ((m n : ℝ) / (2 * S n)) ^ k) atTop (𝓝 1) := by
    simpa [one_pow] using hMS1.pow k
  have hAabs : Tendsto (fun n => |((m n : ℝ) / (2 * S n)) ^ k - 1|) atTop (𝓝 0) := by
    have hsub := hA.sub (tendsto_const_nhds (x := (1:ℝ)))
    rw [sub_self] at hsub
    simpa using hsub.abs
  have hmesh : Tendsto (fun n => (((m n : ℝ) + 1) / (m n : ℝ)) ^ k) atTop (𝓝 1) :=
    tendsto_mesh_factor_atTop.comp hmtop
  -- The vanishing envelope.
  have hE : Tendsto (fun n => (2:ℝ) ^ k * B *
      (|((m n : ℝ) / (2 * S n)) ^ k - 1| +
        ((((m n : ℝ) + 1) / (m n : ℝ)) ^ k - 1))) atTop (𝓝 0) := by
    have h2 : Tendsto (fun n => (((m n : ℝ) + 1) / (m n : ℝ)) ^ k - 1)
        atTop (𝓝 0) := by
      have hsub := hmesh.sub (tendsto_const_nhds (x := (1:ℝ)))
      rw [sub_self] at hsub
      simpa using hsub
    simpa using (hAabs.add h2).const_mul ((2:ℝ) ^ k * B)
  -- The eventual triangle bound.
  have hbound : ∀ᶠ n in atTop,
      |weightedTruncatedRieszDiscreteCycleValue (m n) k R (S n) psi c omega -
        (2:ℝ) ^ k * unitCubeTruncatedRieszLatticeSum (m n) k R psi c omega|
      ≤ (2:ℝ) ^ k * B *
        (|((m n : ℝ) / (2 * S n)) ^ k - 1| +
          ((((m n : ℝ) + 1) / (m n : ℝ)) ^ k - 1)) := by
    filter_upwards [hne, hpos] with n hn hn0
    obtain ⟨hSn0, hmnpos⟩ := hn
    have hmn0 : (m n : ℝ) ≠ 0 := ne_of_gt hmnpos
    set U : ℝ := ((2:ℝ) / (m n : ℝ)) ^ k with hU
    set A : ℝ := ((m n : ℝ) / (2 * S n)) ^ k - 1 with hA'
    set off : ℝ := offsetLatticeSum (m n) k R psi c omega with hoff
    set Tn : ℝ := (∑' y : ↥(rieszUnitCube k ∩ ((m n : ℝ)⁻¹ • rieszIntegerLattice k)),
      unitCubeWeightedTruncatedRieszIntegrand k R psi c omega
        (y : Fin k → ℝ)) with hTn
    set mf : ℝ := (((m n : ℝ) + 1) / (m n : ℝ)) ^ k with hmf
    have hu : (0 : ℝ) ≤ U := by
      rw [hU]
      exact pow_nonneg (div_nonneg (by norm_num) (by positivity)) k
    have hL : unitCubeTruncatedRieszLatticeSum (m n) k R psi c omega
        = Tn / ((m n : ℝ) ^ k) := by
      rw [hTn]
      unfold unitCubeTruncatedRieszLatticeSum
      rw [Fintype.card_fin]
    have huT : U * Tn = (2:ℝ) ^ k * (Tn / ((m n : ℝ) ^ k)) := by
      rw [hU, div_pow (2:ℝ) (m n : ℝ) k]
      field_simp [hmn0, pow_ne_zero k hmn0]
    have hident : weightedTruncatedRieszDiscreteCycleValue (m n) k R (S n) psi c omega -
        (2:ℝ) ^ k * unitCubeTruncatedRieszLatticeSum (m n) k R psi c omega
        = U * (A * off + (off - Tn)) := by
      rw [weightedTruncatedRieszDiscreteCycleValue_eq_meshScaled (m n) k R (S n)
        psi c omega hSn0 hn0.2 (by omega), hL, ← huT, hU, hA', hoff]
      ring
    have hoffb : |off| ≤ ((m n : ℝ)) ^ k * B := by
      rw [hoff]
      exact offsetLatticeSum_abs_le (m n) k R psi c omega B_omega hpsi homegaB
    have hfaceb : |off - Tn| ≤ ((((m n : ℝ) + 1) ^ k - ((m n : ℝ)) ^ k)) * B := by
      rw [hoff, hTn]
      exact abs_offsetLatticeSum_sub_latticeTsum_le (m n) k R psi c omega B_omega
        hpsi homegaB
    have hpowmul : U * ((m n : ℝ)) ^ k = (2:ℝ) ^ k := by
      rw [hU, div_pow (2:ℝ) (m n : ℝ) k]
      field_simp [hmn0, pow_ne_zero k hmn0]
    have hscale : U * ((((m n : ℝ) + 1) ^ k - ((m n : ℝ)) ^ k) * B)
        = (2:ℝ) ^ k * B * (mf - 1) := by
      rw [hU, hmf, div_pow (2:ℝ) (m n : ℝ) k,
        div_pow (((m n : ℝ) + 1)) ((m n : ℝ)) k]
      field_simp [hmn0, pow_ne_zero k hmn0]
    calc |weightedTruncatedRieszDiscreteCycleValue (m n) k R (S n) psi c omega -
          (2:ℝ) ^ k * unitCubeTruncatedRieszLatticeSum (m n) k R psi c omega|
        = |U * (A * off + (off - Tn))| := by rw [hident]
      _ ≤ U * (|A * off| + |off - Tn|) := by
          have hab := abs_mul U (A * off + (off - Tn))
          rw [hab, abs_of_nonneg hu]
          exact mul_le_mul_of_nonneg_left (abs_add_le _ _) hu
      _ ≤ U * (|A| * |off|) + U * |off - Tn| := by
          rw [abs_mul, mul_add]
      _ ≤ (2:ℝ) ^ k * B * |A| + (2:ℝ) ^ k * B * (mf - 1) := by
          have e1 : U * (|A| * |off|) ≤ (2:ℝ) ^ k * B * |A| := by
            calc U * (|A| * |off|)
                ≤ U * (|A| * (((m n : ℝ)) ^ k * B)) :=
                  mul_le_mul_of_nonneg_left
                    (mul_le_mul_of_nonneg_left hoffb (abs_nonneg A)) hu
              _ = U * ((m n : ℝ)) ^ k * (|A| * B) := by ring
              _ = (2:ℝ) ^ k * (|A| * B) := by rw [hpowmul]
              _ = (2:ℝ) ^ k * B * |A| := by ring
          have e2 : U * |off - Tn| ≤ (2:ℝ) ^ k * B * (mf - 1) := by
            calc U * |off - Tn|
                ≤ U * ((((m n : ℝ) + 1) ^ k - ((m n : ℝ)) ^ k) * B) :=
                  mul_le_mul_of_nonneg_left hfaceb hu
              _ = (2:ℝ) ^ k * B * (mf - 1) := hscale
          exact add_le_add e1 e2
      _ = (2:ℝ) ^ k * B * (|A| + (mf - 1)) := (mul_add _ _ _).symm
  -- Squeeze and remove the absolute value.
  have habs0 : Tendsto (fun n => |weightedTruncatedRieszDiscreteCycleValue (m n) k R
      (S n) psi c omega -
      (2:ℝ) ^ k * unitCubeTruncatedRieszLatticeSum (m n) k R psi c omega|)
      atTop (𝓝 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun _ => abs_nonneg _) hbound hE
  have hneg0 : Tendsto (fun n => -|weightedTruncatedRieszDiscreteCycleValue (m n) k R
      (S n) psi c omega -
      (2:ℝ) ^ k * unitCubeTruncatedRieszLatticeSum (m n) k R psi c omega|)
      atTop (𝓝 0) := by
    simpa using habs0.neg
  exact Filter.Tendsto.squeeze' hneg0 habs0
    (Filter.Eventually.of_forall fun _ => neg_abs_le _)
    (Filter.Eventually.of_forall fun _ => le_abs_self _)

end Hurst
