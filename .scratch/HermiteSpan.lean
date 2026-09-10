import Hurst.HermiteAlgebra
import Mathlib.LinearAlgebra.Span.Basic

noncomputable section
open Set Polynomial
namespace Hurst

theorem gaussianHermite_span_X_mul {p : Polynomial ℝ}
    (hp : p ∈ Submodule.span ℝ (Set.range gaussianHermite)) :
    X*p ∈ Submodule.span ℝ (Set.range gaussianHermite) := by
  let S := Submodule.span ℝ (Set.range gaussianHermite)
  have hH (n : ℕ) : gaussianHermite n ∈ S := Submodule.subset_span (Set.mem_range_self n)
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨n,rfl⟩ := hp
    cases n with
    | zero => simpa [gaussianHermite_zero,gaussianHermite_one] using hH 1
    | succ n =>
      have he : X*gaussianHermite (n+1) =
          gaussianHermite (n+2)+(n+1:ℝ) • gaussianHermite n := by
        rw [show n+2=(n+1)+1 by omega,gaussianHermite_succ (n+1),
          gaussianHermite_derivative_succ,Polynomial.smul_eq_C_mul]
        ring
      rw [he]
      exact S.add_mem (hH _) (S.smul_mem _ (hH _))
  | zero => simp
  | add p q hp hq ihp ihq => simpa [mul_add] using S.add_mem ihp ihq
  | smul a p hp ih => simpa [mul_smul_comm] using S.smul_mem a ih

theorem gaussianHermite_span_eq_top :
    Submodule.span ℝ (Set.range gaussianHermite) = ⊤ := by
  let S := Submodule.span ℝ (Set.range gaussianHermite)
  have hpow (n : ℕ) : (X:Polynomial ℝ)^n ∈ S := by
    induction n with
    | zero => simpa [gaussianHermite_zero] using
        (Submodule.subset_span (Set.mem_range_self 0) : gaussianHermite 0 ∈ S)
    | succ n ih => simpa [pow_succ,mul_comm] using gaussianHermite_span_X_mul ih
  apply top_unique
  intro p hp
  clear hp
  induction p using Polynomial.induction_on' with
  | add p q hp hq => exact S.add_mem hp hq
  | monomial n c =>
    simpa [Polynomial.smul_eq_C_mul,Polynomial.C_mul_X_pow_eq_monomial] using
      S.smul_mem c (hpow n)

end Hurst
