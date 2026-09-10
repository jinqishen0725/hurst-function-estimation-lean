import Hurst.SpectralMatchingSort
import Hurst.FiniteGaussianSpectral
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.Monoid

/-!
# Uniform spectral tails from coefficient convergence and trace-square data

For a triangular array of real eigenvalue sequences, the uniform `ℓ²` spectral
tail hypothesis consumed by
`centeredMatrixQuadratic_tendsto_secondChaos_of_permuted_spectral_data` is not
an independent deterministic input: it follows from padded coefficient
convergence together with convergence of the total eigenvalue-square sum
(that is, of the trace of the square).  This file proves that reduction.
-/

noncomputable section
open Finset Filter Metric
open scoped Topology
namespace Hurst

variable {m : ℕ}

/-- The eigenvalue entries of the initial segment `{i | i.val < K}` can be
reindexed through `Fin.castLE`. -/
theorem sum_univ_filter_val_lt_castLE {K : ℕ} (hKm : K ≤ m) (f : Fin m → ℝ) :
    (∑ i : Fin m, if i.val < K then f i else 0) = ∑ j : Fin K, f (Fin.castLE hKm j) := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun (i : Fin m) (hi : i ∈ Finset.univ.filter
      fun j : Fin m => j.val < K) => (⟨i.val, (Finset.mem_filter.mp hi).2⟩ : Fin K)) ?_ ?_ ?_ ?_
  · intro i _
    exact Finset.mem_univ _
  · intro a _ b _ hEq
    have hval := congrArg Fin.val hEq
    exact Fin.ext hval
  · intro b _
    refine ⟨Fin.castLE hKm b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    have hval : (Fin.castLE hKm b).val = b.val := rfl
    omega
  · intro a _
    rfl

/-- For a finite centered Gaussian spectral array the uniform `ℓ²` tail of the
permuted eigenvalues follows from padded coefficient convergence and
convergence of the total eigenvalue-square sum.  Concretely, one may take
`e K = 4 * ∑' i, lambda (i + K)² + 2/(K+1)`. -/
theorem spectralTailBound_of_padded_coefficient_convergence
    (m : ℕ → ℕ) (lamN : ∀ n, Fin (m n) → ℝ)
    (lambda : ℕ → ℝ) (hsum : Summable (fun j : ℕ => lambda j ^ 2))
    (hm : Tendsto m atTop atTop)
    (hcoeff : ∀ j : ℕ, Tendsto (fun n ↦ if hj : j < m n then lamN n ⟨j, hj⟩ else 0)
      atTop (𝓝 (lambda j)))
    (htr2 : Tendsto (fun n ↦ ∑ i : Fin (m n), lamN n i ^ 2)
      atTop (𝓝 (∑' j : ℕ, lambda j ^ 2))) :
    ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧
      ∀ K : ℕ, ∀ᶠ n in atTop,
        2 * (∑ i : Fin (m n), if K ≤ i.val then lamN n i ^ 2 else 0) ≤ e K := by
  obtain ⟨t, htsub, htadd, htnonneg⟩ :
      ∃ t : ℕ → ℝ,
        (∀ K : ℕ, t K = (∑' j : ℕ, lambda j ^ 2) -
          ∑ j ∈ Finset.range K, lambda j ^ 2) ∧
        (∀ K : ℕ, (∑ j ∈ Finset.range K, lambda j ^ 2) + t K = ∑' j : ℕ, lambda j ^ 2) ∧
        (∀ K : ℕ, 0 ≤ t K) :=
    ⟨fun K => ∑' i : ℕ, lambda (i + K) ^ 2,
      fun K => by
        have := hsum.sum_add_tsum_nat_add K
        linarith,
      fun K => by
        have := hsum.sum_add_tsum_nat_add K
        linarith,
      fun _ => tsum_nonneg fun _ => sq_nonneg _⟩
  have hpart : Tendsto (fun K : ℕ => ∑ j ∈ Finset.range K, lambda j ^ 2) atTop
      (𝓝 (∑' j : ℕ, lambda j ^ 2)) := hsum.hasSum.tendsto_sum_nat
  have ht0 : Tendsto t atTop (𝓝 0) := by
    have h1 : Tendsto (fun K : ℕ => (∑' j : ℕ, lambda j ^ 2) -
        (∑ j ∈ Finset.range K, lambda j ^ 2)) atTop (𝓝 (0 : ℝ)) := by
      have h2 := hpart.const_sub (∑' j : ℕ, lambda j ^ 2)
      simpa using h2
    refine Tendsto.congr' (Eventually.of_forall fun K => (htsub K).symm) h1
  have hshift : Tendsto (fun K : ℕ => ((K : ℝ) + 1)) atTop atTop :=
    tendsto_atTop_atTop_of_monotone
      (fun x y h => by
        have h2 : (x : ℝ) ≤ (y : ℝ) := Nat.cast_le.mpr h
        linarith)
      (fun a => ⟨Nat.ceil a + 1, by
        have hle : (a : ℝ) ≤ (Nat.ceil a : ℕ) := Nat.le_ceil a
        have h2 : ((Nat.ceil a + 1 : ℕ) : ℝ) ≥ (a : ℝ) + 1 := by
          have : ((Nat.ceil a : ℕ) : ℝ) ≥ (a : ℝ) := hle
          have hcast : ((Nat.ceil a + 1 : ℕ) : ℝ) = ((Nat.ceil a : ℕ) : ℝ) + 1 := by
            push_cast
            ring
          linarith
        linarith⟩)
  have hinv : Tendsto (fun K : ℕ => (((K : ℝ) + 1 : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hshift
  have hE : Tendsto (fun K : ℕ => 4 * t K + 2 * (((K : ℝ) + 1 : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa using (ht0.const_mul (4 : ℝ)).add (hinv.const_mul (2 : ℝ))
  refine ⟨fun K => 4 * t K + 2 * (((K : ℝ) + 1 : ℝ))⁻¹, hE, fun K => ?_⟩
  have hKm : ∀ᶠ n in atTop, K ≤ m n := hm.eventually_ge_atTop K
  -- the head sum converges to the finite partial sum
  have hhead : Tendsto (fun n => ∑ i : Fin (m n), if i.val < K then lamN n i ^ 2 else 0)
      atTop (𝓝 (∑ j ∈ Finset.range K, lambda j ^ 2)) := by
    have hlim : Tendsto (fun n => ∑ j : Fin K,
        (if hj : (j : ℕ) < m n then lamN n ⟨(j : ℕ), hj⟩ else 0) ^ 2)
        atTop (𝓝 (∑ j ∈ Finset.range K, lambda j ^ 2)) := by
      rw [show (∑ j ∈ Finset.range K, lambda j ^ 2)
          = ∑ j : Fin K, lambda (j : ℕ) ^ 2 from
          (Fin.sum_univ_eq_sum_range (fun j : ℕ => lambda j ^ 2) K).symm]
      refine tendsto_finsetSum _ fun j _ => ?_
      exact (hcoeff (j : ℕ)).pow 2
    refine Tendsto.congr' ?_ hlim
    filter_upwards [hKm] with n hn
    rw [sum_univ_filter_val_lt_castLE (f := fun i => lamN n i ^ 2) hn]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dif_pos (show (j : ℕ) < m n from Nat.lt_of_lt_of_le j.isLt hn),
      show Fin.castLE hn j = ⟨(j : ℕ), Nat.lt_of_lt_of_le j.isLt hn⟩ from rfl]
  -- tail + head = total, so the tail converges to the remaining series
  have hsplit : ∀ n : ℕ, (∑ i : Fin (m n), if K ≤ i.val then lamN n i ^ 2 else 0)
      + (∑ i : Fin (m n), if i.val < K then lamN n i ^ 2 else 0)
      = ∑ i : Fin (m n), lamN n i ^ 2 := by
    intro n
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : K ≤ i.val
    · rw [if_pos h, if_neg (by omega)]
      ring
    · rw [if_neg h, if_pos (by omega)]
      ring
  have htail : Tendsto (fun n => ∑ i : Fin (m n), if K ≤ i.val then lamN n i ^ 2 else 0)
      atTop (𝓝 (t K)) := by
    have h1 : Tendsto (fun n => (∑ i : Fin (m n), lamN n i ^ 2)
        - (∑ i : Fin (m n), if i.val < K then lamN n i ^ 2 else 0)) atTop
        (𝓝 (t K)) := by
      have h2 := htr2.sub hhead
      rw [← htsub K] at h2
      exact h2
    refine Tendsto.congr' ?_ h1
    filter_upwards [] with n
    have hk := hsplit n
    linarith
  have hpos : (0 : ℝ) < ((K : ℝ) + 1)⁻¹ := by positivity
  have htarget : (0 : ℝ) < t K + ((K : ℝ) + 1)⁻¹ :=
    lt_add_of_le_of_pos (htnonneg K) hpos
  filter_upwards [(Metric.tendsto_nhds.mp htail (t K + ((K : ℝ) + 1)⁻¹)
      htarget)] with n hclose
  have habs : (∑ i : Fin (m n), if K ≤ i.val then lamN n i ^ 2 else 0)
      ≤ |(∑ i : Fin (m n), if K ≤ i.val then lamN n i ^ 2 else 0) - t K| + t K := by
    have h1 : ((∑ i : Fin (m n), if K ≤ i.val then lamN n i ^ 2 else 0) - t K)
        ≤ |(∑ i : Fin (m n), if K ≤ i.val then lamN n i ^ 2 else 0) - t K| :=
      le_abs_self _
    linarith
  rw [Real.dist_eq] at hclose
  calc 2 * (∑ i : Fin (m n), if K ≤ i.val then lamN n i ^ 2 else 0)
      ≤ 2 * (t K + (t K + ((K : ℝ) + 1)⁻¹)) := by
        have := habs
        linarith
    _ = 4 * t K + 2 * ((K : ℝ) + 1)⁻¹ := by ring

end Hurst
