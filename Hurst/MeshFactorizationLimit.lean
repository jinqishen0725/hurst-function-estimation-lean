import Mathlib

/-!
# Mesh factorization limit for truncated Riesz cycle edge entries

A far-from-diagonal edge entry of the discrete truncated Riesz cycle kernel at
mesh scale `S` with `m` grid points has the shape `c * S ^ psi * d ^ (-psi)`
for a grid distance `d` (cf. `Hurst.TruncatedRieszCycleBridge`, where the
kernel is `c * (max ((R + 1 : ℕ) : ℝ)⁻¹ |x - y|) ^ (-psi)`).  Normalizing the
mesh distance by the half mesh `m / 2`, such an entry factors as the continuum
model constant `c` times a single mesh correction factor:

`c * S ^ psi * (m / 2) ^ (-psi) = c * (2 * S / m) ^ psi`.

In the mesh regime `m n → ∞` and `m n / S n → 2` (i.e. `S n` tracks `m n / 2`),
the correction factor `(2 * S n / m n) ^ psi` tends to `1`, so the normalized
edge entries converge to the model value `c` (in particular to `|c|` when the
entry carries `|c|`).
-/

open Filter Real
open scoped Topology

namespace Hurst

/-! ### The edge factorization identity -/

/-- **Edge factorization identity**: for positive mesh scale `S` and grid size
`m`, a far-from-diagonal edge entry of shape `c * S ^ psi * (m / 2) ^ (-psi)`
factors as the model constant `c` times the mesh correction factor
`(2 * S / m) ^ psi`. -/
theorem riesz_edge_factorization {c psi S m : ℝ} (hS : 0 < S) (hm : 0 < m) :
    c * S ^ psi * (m / 2) ^ (-psi) = c * (2 * S / m) ^ psi := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have hhalf : (0 : ℝ) ≤ m / 2 := div_nonneg hm.le h2
  rw [Real.rpow_neg hhalf psi, Real.div_rpow hm.le h2 psi, inv_div,
    Real.div_rpow (mul_nonneg h2 hS.le) hm.le psi, Real.mul_rpow h2 hS.le]
  ring

/-! ### The mesh correction limit -/

/-- **Mesh correction limit**: in the mesh regime `m n → ∞` and
`m n / S n → 2` with eventually positive `S n`, `m n`, the mesh correction
factor `(2 * S n / m n) ^ psi` tends to `1`. -/
theorem tendsto_mesh_correction_rpow {psi : ℝ} (_hpsi : 0 < psi) {m S : ℕ → ℝ}
    (_hm : Tendsto m atTop atTop) (hMS : Tendsto (fun n => m n / S n) atTop (𝓝 2))
    (hpos : ∀ᶠ n in atTop, 0 < S n ∧ 0 < m n) :
    Tendsto (fun n => (2 * S n / m n) ^ psi) atTop (𝓝 1) := by
  have h1 : Tendsto (fun n => ((2 : ℝ) / (m n / S n)) ^ psi) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2)).div hMS
      (show (2 : ℝ) ≠ 0 by norm_num)
    rw [div_self (show (2 : ℝ) ≠ 0 by norm_num)] at h
    simpa using h.rpow_const (Or.inl (show (1 : ℝ) ≠ 0 by norm_num))
  refine Tendsto.congr' ?_ h1
  filter_upwards [hpos] with n hn
  obtain ⟨hSn, hmn⟩ := hn
  have hSn0 : S n ≠ 0 := ne_of_gt hSn
  have hmn0 : m n ≠ 0 := ne_of_gt hmn
  exact congrArg (fun x : ℝ => x ^ psi)
    (show (2 : ℝ) / (m n / S n) = 2 * S n / m n by field_simp)

/-- **Paired edge limit**: in the mesh regime `m n → ∞`, `m n / S n → 2`, the
normalized edge entries `c * S n ^ psi * (m n / 2) ^ (-psi)` converge to the
model constant `c`; applied with `c := |c|` this gives the `|c|`-normalized
version `|c| * S n ^ psi * (m n / 2) ^ (-psi) → |c|`.  No assumption
`c ≠ 0` is needed. -/
theorem tendsto_riesz_edge_entry {psi : ℝ} (hpsi : 0 < psi) {m S : ℕ → ℝ}
    (hm : Tendsto m atTop atTop) (hMS : Tendsto (fun n => m n / S n) atTop (𝓝 2))
    (hpos : ∀ᶠ n in atTop, 0 < S n ∧ 0 < m n) (c : ℝ) :
    Tendsto (fun n => c * S n ^ psi * (m n / 2) ^ (-psi)) atTop (𝓝 c) := by
  have h1 := tendsto_mesh_correction_rpow hpsi hm hMS hpos
  have h2 : Tendsto (fun n => c * (2 * S n / m n) ^ psi) atTop (𝓝 c) := by
    simpa [mul_one] using h1.const_mul c
  refine Tendsto.congr' ?_ h2
  filter_upwards [hpos] with n hn
  obtain ⟨hSn, hmn⟩ := hn
  exact (riesz_edge_factorization hSn hmn).symm

end Hurst
