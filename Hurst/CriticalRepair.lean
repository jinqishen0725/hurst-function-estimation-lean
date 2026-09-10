import Hurst.Corrections
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-! A structural counterexample to the center-value kernel dependence in
Lemma S.3.2. Stationary quadratic sums are translation invariant, whereas
f(0)^2 is not. This does not assume or prove a central limit theorem. -/
noncomputable section
open Filter
open scoped Topology
namespace Hurst

def stationaryQuadratic (w r : ℤ → ℝ) : ℝ :=
  ∑' i : ℤ, ∑' j : ℤ, w i*w j*r (i-j)

theorem stationaryQuadratic_translation (w r : ℤ → ℝ) (k : ℤ) :
    stationaryQuadratic (fun i => w (i-k)) r = stationaryQuadratic w r := by
  unfold stationaryQuadratic
  rw [← (Equiv.addRight k).tsum_eq (fun i : ℤ => ∑' j : ℤ, w (i-k)*w (j-k)*r (i-j))]
  apply tsum_congr
  intro i
  change (∑' j : ℤ, w ((i+k)-k)*w (j-k)*r ((i+k)-j)) = ∑' j : ℤ, w i*w j*r (i-j)
  rw [← (Equiv.addRight k).tsum_eq (fun j : ℤ => w ((i+k)-k)*w (j-k)*r ((i+k)-j))]
  simp

/-- The infinite-sum notation is exactly a finite quadratic form whenever
the weights are zero outside a finite index set. -/
theorem stationaryQuadratic_finite (w r : ℤ → ℝ) (s : Finset ℤ)
    (hs : ∀ i ∉ s, w i = 0) :
    stationaryQuadratic w r = ∑ i ∈ s, ∑ j ∈ s, w i*w j*r (i-j) := by
  unfold stationaryQuadratic
  rw [tsum_eq_sum (s := s) (fun i hi => by simp [hs i hi])]
  apply Finset.sum_congr rfl
  intro i hi
  exact tsum_eq_sum (fun j hj => by simp [hs j hj])

/-- Two smooth kernels supported strictly inside (-1,1). -/
def centralKernel (x : ℝ) : ℝ := correctedBump (2*x)
def shiftedKernel (x : ℝ) : ℝ := centralKernel (x-1/2)

theorem centralKernel_smooth : ContDiff ℝ (⊤ : ℕ∞) centralKernel :=
  correctedBump_smooth.comp (contDiff_const.mul contDiff_id)

theorem shiftedKernel_smooth : ContDiff ℝ (⊤ : ℕ∞) shiftedKernel :=
  centralKernel_smooth.comp (contDiff_id.sub contDiff_const)

theorem centralKernel_at_zero : 0 < centralKernel 0 := by
  exact correctedBump_positive _ ⟨by norm_num, by norm_num⟩

theorem shiftedKernel_at_zero : shiftedKernel 0 = 0 := by
  apply correctedBump_zero
  left; norm_num

theorem centralKernel_outside (x : ℝ) (hx : x ≤ -1 ∨ 1 ≤ x) : centralKernel x = 0 := by
  apply correctedBump_zero
  rcases hx with hx | hx
  · left; linarith
  · right; linarith

theorem shiftedKernel_outside (x : ℝ) (hx : x ≤ -1 ∨ 1 ≤ x) : shiftedKernel x = 0 := by
  apply correctedBump_zero
  rcases hx with hx | hx
  · left; linarith
  · right; linarith

def evenWindow (n : ℕ) : ℝ := 2*((n:ℝ)+1)
def sampledKernel (f : ℝ → ℝ) (n : ℕ) (i : ℤ) : ℝ := f ((i:ℝ)/evenWindow n)

theorem sampled_shift_identity (n : ℕ) (i : ℤ) :
    sampledKernel shiftedKernel n i = sampledKernel centralKernel n (i-((n:ℤ)+1)) := by
  unfold sampledKernel shiftedKernel evenWindow
  congr 1
  push_cast
  have hn : (n:ℝ)+1 ≠ 0 := by positivity
  field_simp

theorem sampled_stationary_translation (n : ℕ) (r : ℤ → ℝ) :
    stationaryQuadratic (sampledKernel shiftedKernel n) r =
      stationaryQuadratic (sampledKernel centralKernel n) r := by
  simp_rw [funext (sampled_shift_identity n)]
  exact stationaryQuadratic_translation _ r ((n:ℤ)+1)

/-- No positive coefficient times f(0)^2 can be the universal limit of
stationary weighted quadratic sums, even restricted to this smooth pair.
The normalizer and the lag kernels are arbitrary, so this includes the
normalizer and stationary fBm correlations in S.3.2. -/
theorem no_universal_center_value_limit (a : ℕ → ℝ) (r : ℕ → ℤ → ℝ)
    (C : ℝ) (hC : 0 < C) :
    ¬ (Tendsto (fun n => a n*stationaryQuadratic (sampledKernel centralKernel n) (r n))
         atTop (𝓝 (C*(centralKernel 0)^2)) ∧
       Tendsto (fun n => a n*stationaryQuadratic (sampledKernel shiftedKernel n) (r n))
         atTop (𝓝 (C*(shiftedKernel 0)^2))) := by
  rintro ⟨hbase, hshift⟩
  simp only [sampled_stationary_translation, shiftedKernel_at_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at hshift
  have he := tendsto_nhds_unique hbase hshift
  have hp : 0 < C*(centralKernel 0)^2 := mul_pos hC (sq_pos_of_pos centralKernel_at_zero)
  linarith

end Hurst
