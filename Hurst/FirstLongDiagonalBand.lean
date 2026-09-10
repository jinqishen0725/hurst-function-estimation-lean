import Hurst.FirstLongCrossKernel
import Hurst.LatticeCount
import Hurst.GridCorrelationRows

noncomputable section
open Set Filter
open scoped Topology RealInnerProductSpace
namespace Hurst

/-- Squared mesh `L²` mass of a matrix kernel inside a diagonal band.  A
matrix entry `rᵢⱼ` represents the step-kernel value `N^ψ rᵢⱼ` on a cell of
area `N⁻²`. -/
def meshDiagonalBandEnergy {m : ℕ} (N R : ℕ) (ψ : ℝ)
    (r : Fin m → Fin m → ℝ) : ℝ :=
  (N : ℝ) ^ (2 * ψ - 2) *
    ∑ i : Fin m, ∑ j ∈ Finset.univ.filter
      (fun j : Fin m => Nat.dist j.val i.val ≤ R), r i j ^ 2

private theorem diagonal_band_card {m : ℕ} (R : ℕ) (i : Fin m) :
    (Finset.univ.filter
      (fun j : Fin m => Nat.dist j.val i.val ≤ R)).card ≤ 2 * R + 1 := by
  let S : Finset (Fin m) := Finset.univ.filter
    (fun j => Nat.dist j.val i.val ≤ R)
  have hc := finite_lattice_interval_card S
    ((i.val : ℝ) - R) ((i.val : ℝ) + R) (by linarith) (by
      intro j hj
      have hd : Nat.dist j.val i.val ≤ R := (Finset.mem_filter.mp hj).2
      have hleft : j.val ≤ i.val + R := by
        rcases le_total i.val j.val with hij | hji
        · rw [Nat.dist_eq_sub_of_le_right hij] at hd
          omega
        · omega
      have hright : i.val ≤ j.val + R := by
        rcases le_total j.val i.val with hji | hij
        · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le_right hji] at hd
          omega
        · omega
      have hleftR : (j.val : ℝ) ≤ i.val + R := by exact_mod_cast hleft
      have hrightR : (i.val : ℝ) ≤ j.val + R := by exact_mod_cast hright
      constructor <;> linarith
    )
  have hcR : (S.card : ℝ) ≤ (2 * R + 1 : ℕ) := by
    convert hc using 1 <;> push_cast <;> ring
  exact_mod_cast hcR

/-- A correlation matrix contributes at most
`N^(2ψ-1) (2R+1)` to the squared step-kernel norm in a band of `R` cells.
This treats the diagonal using its true finite value rather than evaluating
the singular limiting kernel there. -/
theorem meshDiagonalBandEnergy_le {m N R : ℕ} (ψ : ℝ)
    (hn : 0 < N) (hmN : m ≤ N) (r : Fin m → Fin m → ℝ)
    (hr : ∀ i j, |r i j| ≤ 1) :
    meshDiagonalBandEnergy N R ψ r ≤
      (N : ℝ) ^ (2 * ψ - 1) * (2 * (R : ℝ) + 1) := by
  have hinner : ∀ i : Fin m,
      (∑ j ∈ Finset.univ.filter
        (fun j : Fin m => Nat.dist j.val i.val ≤ R), r i j ^ 2) ≤
        2 * (R : ℝ) + 1 := by
    intro i
    calc
      _ ≤ ∑ _j ∈ Finset.univ.filter
          (fun j : Fin m => Nat.dist j.val i.val ≤ R), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        have hs := pow_le_pow_left₀ (abs_nonneg (r i j)) (hr i j) 2
        simpa only [sq_abs, one_pow] using hs
      _ = ((Finset.univ.filter
          (fun j : Fin m => Nat.dist j.val i.val ≤ R)).card : ℝ) := by simp
      _ ≤ (2 * R + 1 : ℕ) := by exact_mod_cast diagonal_band_card R i
      _ = _ := by push_cast; ring
  have hdouble :
      (∑ i : Fin m, ∑ j ∈ Finset.univ.filter
        (fun j : Fin m => Nat.dist j.val i.val ≤ R), r i j ^ 2) ≤
        (N : ℝ) * (2 * (R : ℝ) + 1) := by
    calc
      _ ≤ ∑ _i : Fin m, (2 * (R : ℝ) + 1) :=
        Finset.sum_le_sum fun i _ => hinner i
      _ = (m : ℝ) * (2 * (R : ℝ) + 1) := by simp; ring
      _ ≤ (N : ℝ) * (2 * (R : ℝ) + 1) := by
        gcongr
  unfold meshDiagonalBandEnergy
  have hscale : 0 ≤ (N : ℝ) ^ (2 * ψ - 2) :=
    Real.rpow_nonneg (by positivity) _
  calc
    _ ≤ (N : ℝ) ^ (2 * ψ - 2) *
        ((N : ℝ) * (2 * (R : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hdouble hscale
    _ = (N : ℝ) ^ (2 * ψ - 1) * (2 * (R : ℝ) + 1) := by
      have hnR : (0 : ℝ) < N := by exact_mod_cast hn
      have hpow : (N : ℝ) ^ (2 * ψ - 2) * N =
          (N : ℝ) ^ (2 * ψ - 1) := by
        calc
          _ = (N : ℝ) ^ (2 * ψ - 2) * (N : ℝ) ^ (1 : ℝ) := by simp
          _ = (N : ℝ) ^ ((2 * ψ - 2) + 1) := by rw [Real.rpow_add hnR]
          _ = _ := by congr 1; ring
      rw [← mul_assoc, hpow]

/-- Abstract shrinking-band consequence of `meshDiagonalBandEnergy_le`.
The final scalar premise is deterministic and is discharged by any cutoff
`Rₙ=o(Nₙ^(1-2ψ))`. -/
theorem meshDiagonalBandEnergy_tendsto_zero
    (m N R : ℕ → ℕ) (ψ : ℝ)
    (r : ∀ n, Fin (m n) → Fin (m n) → ℝ)
    (hN : ∀ᶠ n in atTop, 0 < N n)
    (hmN : ∀ᶠ n in atTop, m n ≤ N n)
    (hr : ∀ᶠ n in atTop, ∀ i j, |r n i j| ≤ 1)
    (hcut : Tendsto (fun n =>
      (N n : ℝ) ^ (2 * ψ - 1) * (2 * (R n : ℝ) + 1))
      atTop (𝓝 0)) :
    Tendsto (fun n => meshDiagonalBandEnergy (N n) (R n) ψ (r n))
      atTop (𝓝 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall fun n => mul_nonneg
      (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ N n) (2 * ψ - 2))
      (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
  · filter_upwards [hN, hmN, hr] with n hn hm hrn
    exact meshDiagonalBandEnergy_le ψ hn hm (r n) hrn
  · exact hcut

/-- Every Hilbert-space correlation matrix satisfies the unit entry bound
needed by the diagonal-band estimate. -/
theorem vectorCorrelation_abs_le_one {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (u v : E) :
    |vectorCorrelation u v| ≤ 1 := by
  exact abs_real_inner_div_norm_mul_norm_le_one u v

end Hurst
