import Hurst.SpectralMatchingSort
import Hurst.TailExtraction
import Hurst.PeelingSubtraction

/-!
# The supremum of the residual array is the `J`-th descending entry

Fix an array `xv : Fin m → ℝ` of nonnegative values and a peeling level `J ≤ m`.
The residual array `spectralResidual J xv` keeps exactly the entries whose
descending spectral rank is `≥ J`.  Since the decreasing rearrangement is
antitone, every kept entry is at most the entry at descending position `J`,
and that entry itself is kept, so

* `spectralResidual_le_padRearranged`: pointwise companion
  `spectralResidual J xv i ≤ padRearranged xv J`;
* `iSup_spectralResidual_eq_padRearranged`: the supremum of the residual array
  equals `padRearranged xv J`.

The two ingredients consumed downstream are exactly the pointwise bound above
and the witness identity `padRearranged_eq_spectralResidual`
(`padRearranged xv J` is the residual at the index of descending rank `J`).
-/

namespace Hurst

/-- Unfolding of `padRearranged` below the array length. -/
theorem padRearranged_of_lt {m : ℕ} (xv : Fin m → ℝ) {c : ℕ} (hc : c < m) :
    padRearranged xv c = xv (decreasingSpectralPerm xv ⟨c, hc⟩) := by
  simp only [padRearranged, dif_pos hc]

/-- Unfolding of `padRearranged` at or beyond the array length. -/
theorem padRearranged_of_ge {m : ℕ} (xv : Fin m → ℝ) {c : ℕ} (hc : m ≤ c) :
    padRearranged xv c = 0 := by
  simp only [padRearranged, dif_neg (by omega : ¬ c < m)]

/-- The index of descending rank `J` seen from inside the array:
`decreasingSpectralPerm` maps the position `J` to the entry with rank `J`. -/
theorem decreasingSpectralPerm_apply_rank (xv : Fin m → ℝ) (i : Fin m) :
    decreasingSpectralPerm xv
      ⟨specDescendingRank xv i, specDescendingRank_lt xv i⟩ = i :=
  specDescendingRank_injective xv (by
    rw [specDescendingRank_decreasingSpectralPerm, Fin.val_mk])

/-- **Pointwise companion, nonzero case.**  If the residual at `i` is nonzero
(i.e. `J ≤ specDescendingRank xv i`), then it is at most the `J`-th descending
entry, by antitone-ness of the decreasing rearrangement.  No sign hypotheses. -/
theorem spectralResidual_le_padRearranged_of_le (J : ℕ) {m : ℕ} (xv : Fin m → ℝ)
    {i : Fin m} (hr : J ≤ specDescendingRank xv i) :
    spectralResidual J xv i ≤ padRearranged xv J := by
  by_cases hJm : J < m
  · have hFinle : (⟨J, hJm⟩ : Fin m) ≤
        ⟨specDescendingRank xv i, specDescendingRank_lt xv i⟩ :=
      (Fin.le_iff_val_le_val).2 hr
    have hanti := decreasingSpectralPerm_antitone xv hFinle
    rw [spectralResidual_apply, if_pos hr, padRearranged_of_lt xv hJm]
    simp only [decreasingSpectralPerm_apply_rank] at hanti
    exact hanti
  · have hlt := specDescendingRank_lt xv i
    rw [spectralResidual_apply, if_neg (by omega), padRearranged_of_ge xv (by omega)]

/-- **Pointwise companion.**  For a nonnegative array, every entry of the
residual is at most the `J`-th (padded) descending entry. -/
theorem spectralResidual_le_padRearranged (J : ℕ) {m : ℕ} (xv : Fin m → ℝ)
    (hnn : ∀ i, 0 ≤ xv i) (i : Fin m) :
    spectralResidual J xv i ≤ padRearranged xv J := by
  by_cases hr : J ≤ specDescendingRank xv i
  · exact spectralResidual_le_padRearranged_of_le J xv hr
  · by_cases hJm : J < m
    · rw [spectralResidual_apply, if_neg hr, padRearranged_of_lt xv hJm]
      exact hnn _
    · have hlt := specDescendingRank_lt xv i
      rw [spectralResidual_apply, if_neg (by omega), padRearranged_of_ge xv (by omega)]

/-- **Witness identity.**  The `J`-th padded descending entry *is* a residual
entry: the residual at the index of descending rank exactly `J` (which exists
for `J < m`). -/
theorem padRearranged_eq_spectralResidual (J : ℕ) {m : ℕ} (xv : Fin m → ℝ)
    (hJ : J < m) :
    padRearranged xv J =
      spectralResidual J xv (decreasingSpectralPerm xv ⟨J, hJ⟩) := by
  have hrJ : J ≤ specDescendingRank xv (decreasingSpectralPerm xv ⟨J, hJ⟩) := by
    rw [specDescendingRank_decreasingSpectralPerm, Fin.val_mk]
  rw [padRearranged_of_lt xv hJ, spectralResidual_apply, if_pos hrJ]

/-- **Residual max identification.**  For a nonnegative array and `J ≤ m`,
the supremum of the residual array equals the `J`-th padded descending entry.
When `J = m` the residual is identically `0` and the padded side is `0` too. -/
theorem iSup_spectralResidual_eq_padRearranged (J : ℕ) {m : ℕ} (xv : Fin m → ℝ)
    (hnn : ∀ i, 0 ≤ xv i) (hJ : J ≤ m) :
    ⨆ i : Fin m, spectralResidual J xv i = padRearranged xv J := by
  by_cases hJm : J < m
  · have hm1 : 0 < m := lt_of_le_of_lt (Nat.zero_le J) hJm
    have hpoint : ∀ i : Fin m, spectralResidual J xv i ≤ padRearranged xv J :=
      fun i => spectralResidual_le_padRearranged J xv hnn i
    have h2 : padRearranged xv J ≤ ⨆ i : Fin m, spectralResidual J xv i := by
      rw [padRearranged_eq_spectralResidual J xv hJm]
      exact Finite.le_ciSup _ (decreasingSpectralPerm xv ⟨J, hJm⟩)
    have hne : Nonempty (Fin m) := ⟨⟨0, hm1⟩⟩
    obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin m,
        spectralResidual J xv i₀ = ⨆ i : Fin m, spectralResidual J xv i :=
      exists_eq_ciSup_of_finite
    refine le_antisymm ?_ h2
    calc ⨆ i : Fin m, spectralResidual J xv i = spectralResidual J xv i₀ := hi₀.symm
      _ ≤ padRearranged xv J := hpoint i₀
  · rw [padRearranged_of_ge xv (by omega)]
    have hzero : ∀ i : Fin m, spectralResidual J xv i = 0 := by
      intro i
      rw [spectralResidual_apply, if_neg]
      have hlt := specDescendingRank_lt xv i
      exact not_le.mpr (by omega)
    simp only [hzero]
    rcases isEmpty_or_nonempty (Fin m) with h0 | h1
    · rw [iSup_of_empty', Real.sSup_empty]
    · rw [ciSup_const]

end Hurst
