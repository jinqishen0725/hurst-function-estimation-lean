import Hurst.HermiteTotal
import Mathlib.Analysis.InnerProductSpace.l2Space

noncomputable section
open Set MeasureTheory ProbabilityTheory Polynomial
open scoped RealInnerProductSpace
namespace Hurst

abbrev GaussianL2 := Lp ℝ 2 (gaussianReal 0 1)

def gaussianHermiteLp (n : ℕ) : GaussianL2 :=
  (standardGaussian_polynomial_memLp_two (gaussianHermite n)).toLp (fun x => (gaussianHermite n).eval x)

def gaussianHermiteUnit (n : ℕ) : GaussianL2 :=
  (Real.sqrt (n.factorial:ℝ))⁻¹ • gaussianHermiteLp n

theorem gaussianHermiteLp_ae (n : ℕ) :
    gaussianHermiteLp n =ᵐ[gaussianReal 0 1] fun x => (gaussianHermite n).eval x :=
  MemLp.coeFn_toLp _

theorem gaussianHermiteLp_inner (n m : ℕ) :
    ⟪gaussianHermiteLp n,gaussianHermiteLp m⟫ = if n=m then (n.factorial:ℝ) else 0 := by
  rw [L2.inner_def,← standardGaussian_hermite_orthogonality]
  apply integral_congr_ae
  filter_upwards [gaussianHermiteLp_ae n,gaussianHermiteLp_ae m] with x hn hm
  simp only [hn,hm,Real.inner_apply]

theorem gaussianHermiteLp_inner_function (n : ℕ) (f : GaussianL2) :
    ⟪gaussianHermiteLp n,f⟫ = ∫ x,f x*(gaussianHermite n).eval x ∂gaussianReal 0 1 := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [gaussianHermiteLp_ae n] with x hn
  simp only [hn,Real.inner_apply,mul_comm]

theorem gaussianHermiteUnit_orthonormal : Orthonormal ℝ gaussianHermiteUnit := by
  rw [orthonormal_iff_ite]
  intro n m
  simp only [gaussianHermiteUnit,inner_smul_left,inner_smul_right,conj_trivial,
    gaussianHermiteLp_inner]
  split_ifs with h
  · subst m
    have hpos : 0 < (n.factorial:ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
    have hs : Real.sqrt (n.factorial:ℝ) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
    have he := Real.sq_sqrt hpos.le
    field_simp
    nlinarith
  · ring

theorem gaussianHermiteUnit_orthogonal_eq_bot :
    (Submodule.span ℝ (Set.range gaussianHermiteUnit))ᗮ = ⊥ := by
  apply bot_unique
  intro f hf
  change f=0
  apply Lp.ext
  have ht : (f : ℝ → ℝ) =ᵐ[gaussianReal 0 1] 0 := by
    apply standardGaussian_L2_hermite_total (Lp.memLp f)
    intro n
    have he := (Submodule.mem_orthogonal _ _).mp hf (gaussianHermiteUnit n)
      (Submodule.subset_span (Set.mem_range_self n))
    rw [gaussianHermiteUnit,inner_smul_left,conj_trivial,gaussianHermiteLp_inner_function] at he
    have hs : (Real.sqrt (n.factorial:ℝ))⁻¹ ≠ 0 :=
      inv_ne_zero (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.factorial_pos n))).ne'
    exact (mul_eq_zero.mp he).resolve_left hs
  exact ht.trans (Lp.coeFn_zero ℝ 2 (gaussianReal 0 1)).symm

def gaussianHermiteBasis : HilbertBasis ℕ ℝ GaussianL2 :=
  HilbertBasis.mkOfOrthogonalEqBot gaussianHermiteUnit_orthonormal gaussianHermiteUnit_orthogonal_eq_bot

theorem gaussianHermiteBasis_apply (n : ℕ) : gaussianHermiteBasis n=gaussianHermiteUnit n := by
  simp [gaussianHermiteBasis]

theorem gaussianHermite_expansion (f : GaussianL2) :
    HasSum (fun n => ⟪gaussianHermiteUnit n,f⟫ • gaussianHermiteUnit n) f := by
  simpa only [HilbertBasis.repr_apply_apply,gaussianHermiteBasis_apply] using
    gaussianHermiteBasis.hasSum_repr f

theorem gaussianHermite_parseval (f : GaussianL2) :
    HasSum (fun n => ⟪gaussianHermiteUnit n,f⟫^2) (‖f‖^2) := by
  simpa only [gaussianHermiteBasis_apply,real_inner_comm,pow_two,real_inner_self_eq_norm_sq] using
    gaussianHermiteBasis.hasSum_inner_mul_inner f f

end Hurst
