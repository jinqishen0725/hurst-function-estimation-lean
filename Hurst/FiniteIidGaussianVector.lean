import Hurst.FiniteGaussianSpectralTruncation
import Mathlib.Probability.HasLaw

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Hurst

/-- The first `K` variables of a real sequence, bundled as a Euclidean
vector. -/
def iidGaussianFinVector {Omega : Type*} (Z : ℕ → Omega → ℝ) (K : ℕ)
    (x : Omega) : EuclideanSpace ℝ (Fin K) :=
  WithLp.toLp 2 (fun j : Fin K ↦ Z j.val x)

@[simp]
theorem iidGaussianFinVector_apply {Omega : Type*}
    (Z : ℕ → Omega → ℝ) (K : ℕ) (x : Omega) (j : Fin K) :
    iidGaussianFinVector Z K x j = Z j.val x := rfl

/-- Any finite prefix of an iid standard Gaussian sequence has the canonical
finite-dimensional standard Gaussian law. -/
theorem iidGaussianFinVector_hasLaw
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    [IsProbabilityMeasure P] (Z : ℕ → Omega → ℝ)
    (hZmeas : ∀ j, AEMeasurable (Z j) P) (hZi : iIndepFun Z P)
    (hZlaw : ∀ j, P.map (Z j) = gaussianReal 0 1) (K : ℕ) :
    HasLaw (iidGaussianFinVector Z K)
      (stdGaussian (EuclideanSpace ℝ (Fin K))) P := by
  have hcoord : ∀ j : Fin K,
      HasLaw (Z j.val) (gaussianReal 0 1) P := fun j ↦
    ⟨hZmeas j.val, hZlaw j.val⟩
  have hind : iIndepFun (fun j : Fin K ↦ Z j.val) P :=
    hZi.precomp Fin.val_injective
  have hpi := hind.hasLaw_pi hcoord
  have htoLp : HasLaw (WithLp.toLp 2)
      (stdGaussian (EuclideanSpace ℝ (Fin K)))
      (Measure.pi fun _ : Fin K ↦ gaussianReal 0 1) :=
    ⟨by fun_prop, map_pi_eq_stdGaussian⟩
  change HasLaw (fun x ↦ WithLp.toLp 2 (fun j : Fin K ↦ Z j.val x))
    (stdGaussian (EuclideanSpace ℝ (Fin K))) P
  simpa only [Function.comp_def] using htoLp.comp hpi

/-- A finite centered spectral sum evaluated on an iid standard Gaussian
sequence has the same law as the corresponding canonical Euclidean sum. -/
theorem centeredSpectralSquares_iid_identDistrib
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    [IsProbabilityMeasure P] (Z : ℕ → Omega → ℝ)
    (hZmeas : ∀ j, AEMeasurable (Z j) P) (hZi : iIndepFun Z P)
    (hZlaw : ∀ j, P.map (Z j) = gaussianReal 0 1)
    (lambda : Fin K → ℝ) :
    IdentDistrib (centeredSpectralSquares lambda)
      (fun x ↦ ∑ j : Fin K, lambda j * (Z j.val x ^ 2 - 1))
      (stdGaussian (EuclideanSpace ℝ (Fin K))) P := by
  have hvec := iidGaussianFinVector_hasLaw P Z hZmeas hZi hZlaw K
  have hid : HasLaw id (stdGaussian (EuclideanSpace ℝ (Fin K)))
      (stdGaussian (EuclideanSpace ℝ (Fin K))) := HasLaw.id
  have hident : IdentDistrib id (iidGaussianFinVector Z K)
      (stdGaussian (EuclideanSpace ℝ (Fin K))) P :=
    hid.identDistrib hvec
  have hF : Measurable (centeredSpectralSquares lambda) := by
    unfold centeredSpectralSquares
    exact Finset.measurable_sum _ fun j _ => by fun_prop
  have hcomp := hident.comp hF
  convert hcomp using 1
  · funext x
    rfl
  · funext x
    unfold centeredSpectralSquares iidGaussianFinVector
    rfl

end Hurst
