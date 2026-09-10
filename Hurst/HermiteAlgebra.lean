import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
import Mathlib.Tactic

noncomputable section
open Polynomial
namespace Hurst

theorem hermite_derivative_succ (n : ℕ) :
    (Polynomial.hermite (n+1)).derivative = Polynomial.C (n+1:ℤ)*Polynomial.hermite n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [hermite_succ (n+1),derivative_sub,derivative_mul,derivative_X,one_mul,ih,
      derivative_mul,derivative_C,zero_mul,zero_add]
    have he := hermite_succ n
    push_cast
    rw [he]
    simp only [map_add,map_one]
    ring

def gaussianHermite (n : ℕ) : Polynomial ℝ := (Polynomial.hermite n).map (Int.castRingHom ℝ)

theorem gaussianHermite_zero : gaussianHermite 0 = 1 := by simp [gaussianHermite]

theorem gaussianHermite_one : gaussianHermite 1 = Polynomial.X := by simp [gaussianHermite]

theorem gaussianHermite_succ (n : ℕ) :
    gaussianHermite (n+1) = Polynomial.X*gaussianHermite n-(gaussianHermite n).derivative := by
  simp [gaussianHermite,hermite_succ,Polynomial.derivative_map]

theorem gaussianHermite_derivative_succ (n : ℕ) :
    (gaussianHermite (n+1)).derivative = Polynomial.C (n+1:ℝ)*gaussianHermite n := by
  unfold gaussianHermite
  rw [Polynomial.derivative_map,hermite_derivative_succ,Polynomial.map_mul,Polynomial.map_C]
  simp

end Hurst
