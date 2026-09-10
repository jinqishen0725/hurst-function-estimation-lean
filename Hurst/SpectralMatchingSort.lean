import Hurst.FiniteGaussianSpectral
import Mathlib.Data.Fintype.Perm

/-!
# Deterministic decreasing spectral permutations

Mathlib's `Matrix.IsHermitian.eigenvalues` enumeration carries no ordering
guarantee, so every ordered use of the eigenvalues of a finite Hermitian
matrix must be mediated by an explicitly constructed permutation.  This file
provides that construction, together with the uniqueness statement that makes
it canonical.

Main contents:

* `specDescendingRank`: the descending rank of a value with a deterministic
  index tie-break;
* `decreasingSpectralPerm`: the unique permutation arranging the values of a
  finite real-valued function in weakly decreasing order;
* `decreasingSpectralPerm_antitone`: the permuted function is antitone;
* `antitone_perm_eq_pointwise`: two antitone rearrangements of one function
  are equal, so any ordering theorem stated through an arbitrary permutation
  can be transported to the canonical one.
-/

noncomputable section
open Finset Function
open scoped Classical
namespace Hurst

variable {m : ℕ}

/-- The cardinality of `{j : Fin m | j.val < k}` is `k` whenever `k ≤ m`. -/
theorem card_univ_filter_val_lt {k : ℕ} (hkm : k ≤ m) :
    (Finset.univ.filter (fun j : Fin m => j.val < k)).card = k := by
  have h : (Finset.univ.filter (fun j : Fin m => j.val < k)).card =
      (Finset.range k).card := by
    refine Finset.card_bij (fun j _ => (j : ℕ)) ?_ ?_ ?_
    · intro j hj
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
    · intro a _ b _ hEq
      exact Fin.ext hEq
    · intro b hb
      have hbval := Finset.mem_range.mp hb
      exact ⟨⟨b, Nat.lt_of_lt_of_le hbval hkm⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbval⟩, rfl⟩
  rw [h, Finset.card_range]

/-- The cardinality of `{j : Fin m | j.val ≤ k}` is `k + 1` whenever `k + 1 ≤ m`. -/
theorem card_univ_filter_val_le {k : ℕ} (hkm : k + 1 ≤ m) :
    (Finset.univ.filter (fun j : Fin m => j.val ≤ k)).card = k + 1 := by
  have hEq : Finset.univ.filter (fun j : Fin m => j.val ≤ k) =
      Finset.univ.filter (fun j : Fin m => j.val < k + 1) := by
    refine Finset.filter_congr fun j _ => ?_
    omega
  rw [hEq]
  exact card_univ_filter_val_lt hkm

/-- The descending rank of the value `f j` among the values of `f : Fin m → ℝ`,
using the index order as a deterministic tie-break among equal values. -/
def specDescendingRank (f : Fin m → ℝ) (j : Fin m) : ℕ :=
  (Finset.univ.filter (fun k : Fin m => f k > f j)).card +
    (Finset.univ.filter (fun k : Fin m => f k = f j ∧ k.val < j.val)).card

/-- The descending rank is bounded by the total number of indices. -/
theorem specDescendingRank_lt (f : Fin m → ℝ) (j : Fin m) :
    specDescendingRank f j < m := by
  have hjA : j ∉ Finset.univ.filter (fun k : Fin m => f k > f j) := by
    intro hk
    have hk' := (Finset.mem_filter.mp hk).2
    exact lt_irrefl (f j) hk'
  have hjB : j ∉ Finset.univ.filter (fun k : Fin m => f k = f j ∧ k.val < j.val) := by
    intro hk
    have hk' := (Finset.mem_filter.mp hk).2.2
    omega
  have hdisj : Disjoint (Finset.univ.filter (fun k : Fin m => f k > f j))
      (Finset.univ.filter (fun k : Fin m => f k = f j ∧ k.val < j.val)) := by
    refine Finset.disjoint_left.mpr fun k h1 h2 => ?_
    have h1' := (Finset.mem_filter.mp h1).2
    have h2' := (Finset.mem_filter.mp h2).2.1
    exact lt_irrefl (f j) (h2' ▸ h1')
  have hsub : Finset.univ.filter (fun k : Fin m => f k > f j)
        ∪ Finset.univ.filter (fun k : Fin m => f k = f j ∧ k.val < j.val) ⊆
      Finset.univ.erase j := by
    intro k hk
    rcases Finset.mem_union.mp hk with h | h
    · refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ k⟩
      intro hkj
      subst hkj
      exact hjA h
    · refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ k⟩
      intro hkj
      subst hkj
      exact hjB h
  have hmem : j ∉ (Finset.univ.filter (fun k : Fin m => f k > f j)
      ∪ Finset.univ.filter (fun k : Fin m => f k = f j ∧ k.val < j.val)) := by
    intro hm
    rcases Finset.mem_union.mp hm with h' | h'
    · exact hjA h'
    · exact hjB h'
  have hcard : specDescendingRank f j + 1 ≤ (Finset.univ : Finset (Fin m)).card := by
    have hc : (insert j (Finset.univ.filter (fun k : Fin m => f k > f j)
          ∪ Finset.univ.filter (fun k : Fin m => f k = f j ∧ k.val < j.val))).card ≤
        (Finset.univ : Finset (Fin m)).card :=
      Finset.card_le_card (by
        intro k _
        exact Finset.mem_univ k)
    rw [Finset.card_insert_of_notMem hmem, Finset.card_union_of_disjoint hdisj] at hc
    show (Finset.univ.filter (fun k : Fin m => f k > f j)).card +
      (Finset.univ.filter (fun k : Fin m => f k = f j ∧ k.val < j.val)).card + 1 ≤ _
    omega
  calc specDescendingRank f j < specDescendingRank f j + 1 := by omega
    _ ≤ (Finset.univ : Finset (Fin m)).card := hcard
    _ = m := by simp

/-- A strictly larger value has a strictly smaller descending rank. -/
theorem specDescendingRank_lt_of_value_lt {f : Fin m → ℝ} {a b : Fin m} (h : f a < f b) :
    specDescendingRank f b < specDescendingRank f a := by
  have hbAa : b ∈ Finset.univ.filter (fun k : Fin m => f k > f a) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ b, h⟩
  have hbAb : b ∉ Finset.univ.filter (fun k : Fin m => f k > f b) := by
    intro hk
    exact lt_irrefl (f b) (Finset.mem_filter.mp hk).2
  have hbBb : b ∉ Finset.univ.filter (fun k : Fin m => f k = f b ∧ k.val < b.val) := by
    intro hk
    have hk2 := (Finset.mem_filter.mp hk).2.2
    omega
  have hdisj : Disjoint (Finset.univ.filter (fun k : Fin m => f k > f b))
      (Finset.univ.filter (fun k : Fin m => f k = f b ∧ k.val < b.val)) := by
    refine Finset.disjoint_left.mpr fun k h1 h2 => ?_
    exact absurd (Finset.mem_filter.mp h2).2.1 (ne_of_gt (Finset.mem_filter.mp h1).2)
  have hsubS : insert b
        (Finset.univ.filter (fun k : Fin m => f k > f b)
          ∪ Finset.univ.filter (fun k : Fin m => f k = f b ∧ k.val < b.val)) ⊆
      Finset.univ.filter (fun k : Fin m => f k > f a) := by
    intro k hk
    rcases Finset.mem_insert.mp hk with h' | h'
    · rw [h']
      exact hbAa
    · rcases Finset.mem_union.mp h' with h'' | h''
      · refine Finset.mem_filter.mpr ⟨Finset.mem_univ k, ?_⟩
        exact lt_trans h (Finset.mem_filter.mp h'').2
      · refine Finset.mem_filter.mpr ⟨Finset.mem_univ k, ?_⟩
        have hk2 := (Finset.mem_filter.mp h'').2.1
        rw [hk2]
        exact h
  have hcardS : (insert b
        (Finset.univ.filter (fun k : Fin m => f k > f b)
          ∪ Finset.univ.filter (fun k : Fin m => f k = f b ∧ k.val < b.val))).card =
      (Finset.univ.filter (fun k : Fin m => f k > f b)).card +
        (Finset.univ.filter (fun k : Fin m => f k = f b ∧ k.val < b.val)).card + 1 := by
    rw [Finset.card_insert_of_notMem
        (by
          intro hmem
          rcases Finset.mem_union.mp hmem with h' | h'
          · exact hbAb h'
          · exact hbBb h'),
      Finset.card_union_of_disjoint hdisj]
  have hle := Finset.card_le_card hsubS
  rw [hcardS] at hle
  show (Finset.univ.filter (fun k : Fin m => f k > f b)).card +
    (Finset.univ.filter (fun k : Fin m => f k = f b ∧ k.val < b.val)).card <
    (Finset.univ.filter (fun k : Fin m => f k > f a)).card +
    (Finset.univ.filter (fun k : Fin m => f k = f a ∧ k.val < a.val)).card
  omega

private theorem specDescendingRank_lt_of_tie {f : Fin m → ℝ} {a b : Fin m}
    (hlt : a.val < b.val) (hv : f a = f b) :
    specDescendingRank f a < specDescendingRank f b := by
  have hAeq : Finset.univ.filter (fun k : Fin m => f k > f a) =
      Finset.univ.filter (fun k : Fin m => f k > f b) :=
    Finset.filter_congr fun k _ => by rw [hv]
  have hBsub : Finset.univ.filter (fun k : Fin m => f k = f a ∧ k.val < a.val) ⊆
      Finset.univ.filter (fun k : Fin m => f k = f b ∧ k.val < b.val) := by
    intro k hk
    have hk1 := (Finset.mem_filter.mp hk).2.1
    have hk2 := (Finset.mem_filter.mp hk).2.2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ k, by rw [← hv]; exact hk1, by omega⟩
  have hainBb : a ∈ Finset.univ.filter (fun k : Fin m => f k = f b ∧ k.val < b.val) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ a, hv, hlt⟩
  have hainBa : a ∉ Finset.univ.filter (fun k : Fin m => f k = f a ∧ k.val < a.val) := by
    intro hk
    have hk2 := (Finset.mem_filter.mp hk).2.2
    omega
  have hssub : Finset.univ.filter (fun k : Fin m => f k = f a ∧ k.val < a.val) ⊂
      Finset.univ.filter (fun k : Fin m => f k = f b ∧ k.val < b.val) :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hBsub, fun heq => hainBa (by rw [heq]; exact hainBb)⟩
  have hBcard := Finset.card_lt_card hssub
  show (Finset.univ.filter (fun k : Fin m => f k > f a)).card +
    (Finset.univ.filter (fun k : Fin m => f k = f a ∧ k.val < a.val)).card <
    (Finset.univ.filter (fun k : Fin m => f k > f b)).card +
    (Finset.univ.filter (fun k : Fin m => f k = f b ∧ k.val < b.val)).card
  rw [hAeq]
  omega

/-- The descending rank function is injective. -/
theorem specDescendingRank_injective (f : Fin m → ℝ) :
    Function.Injective (specDescendingRank f) := by
  intro a b hab
  rcases Nat.lt_trichotomy a.val b.val with hlt | heq | hgt
  · by_cases hv : f a = f b
    · exact absurd (specDescendingRank_lt_of_tie hlt hv) (by omega)
    · rcases lt_trichotomy (f a) (f b) with h2 | h2 | h2
      · exact absurd hab.symm (by
          have h3 := specDescendingRank_lt_of_value_lt h2
          omega)
      · exact absurd h2 hv
      · exact absurd hab (by
          have h3 := specDescendingRank_lt_of_value_lt h2
          omega)
  · exact Fin.ext heq
  · by_cases hv : f a = f b
    · exact absurd hab.symm (by
        have h3 := specDescendingRank_lt_of_tie hgt hv.symm
        omega)
    · rcases lt_trichotomy (f a) (f b) with h2 | h2 | h2
      · exact absurd hab (by
          have h3 := specDescendingRank_lt_of_value_lt h2
          omega)
      · exact absurd h2 hv
      · exact absurd hab.symm (by
          have h3 := specDescendingRank_lt_of_value_lt h2
          omega)

/-- The descending rank viewed as an endomap of `Fin m`, via the uniform bound
`specDescendingRank_lt`. -/
def specDescendingRankFin (f : Fin m → ℝ) (j : Fin m) : Fin m :=
  ⟨specDescendingRank f j, specDescendingRank_lt f j⟩

/-- The induced endomap of `Fin m` is injective and hence bijective. -/
theorem specDescendingRankFin_injective (f : Fin m → ℝ) :
    Function.Injective (specDescendingRankFin f) := by
  intro a b hab
  have hval : (specDescendingRankFin f a : ℕ) = (specDescendingRankFin f b : ℕ) :=
    congrArg Fin.val hab
  exact specDescendingRank_injective f hval

/-- The unique permutation of `Fin m` that arranges the values of `f` in weakly
decreasing order, with deterministic index tie-breaks for equal values.  This
is the canonical ordering used to feed mathlib's unordered eigenvalue
enumeration into ordered spectral-convergence statements. -/
def decreasingSpectralPerm (f : Fin m → ℝ) : Equiv.Perm (Fin m) :=
  (Equiv.ofBijective (specDescendingRankFin f)
    (Finite.injective_iff_bijective.mp (specDescendingRankFin_injective f))).symm

/-- Applying the rank function to a permuted index recovers the rank value. -/
theorem specDescendingRank_decreasingSpectralPerm (f : Fin m → ℝ) (i : Fin m) :
    specDescendingRank f (decreasingSpectralPerm f i) = i := by
  have h : specDescendingRankFin f (decreasingSpectralPerm f i) = i :=
    Equiv.apply_symm_apply (Equiv.ofBijective (specDescendingRankFin f)
      (Finite.injective_iff_bijective.mp (specDescendingRankFin_injective f))) i
  exact congrArg Fin.val h

/-- The decreasingly permuted values are weakly decreasing. -/
theorem decreasingSpectralPerm_antitone (f : Fin m → ℝ) :
    Antitone (fun i : Fin m => f (decreasingSpectralPerm f i)) := by
  intro i j hij
  by_contra hcon
  have hlt : f (decreasingSpectralPerm f i) < f (decreasingSpectralPerm f j) :=
    lt_of_not_ge hcon
  have hrank := specDescendingRank_lt_of_value_lt hlt
  rw [specDescendingRank_decreasingSpectralPerm,
    specDescendingRank_decreasingSpectralPerm] at hrank
  exact absurd hrank (not_lt.mpr hij)

/-- Threshold counts are permutation invariant. -/
theorem card_filter_perm_mono_le (g : Fin m → ℝ) (tau : Equiv.Perm (Fin m)) (t : ℝ) :
    (Finset.univ.filter (fun j => t ≤ g (tau j))).card =
      (Finset.univ.filter (fun j => t ≤ g j)).card := by
  refine Finset.card_bij (fun j _ => tau j) ?_ (fun a _ b _ hEq => tau.injective hEq) ?_
  · intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
  · intro b hb
    refine ⟨tau.symm b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, by simp⟩
    rw [Equiv.apply_symm_apply]
    exact (Finset.mem_filter.mp hb).2

/-- For an antitone sequence the superlevel set at level `t` is exactly the
initial segment of length equal to its cardinality. -/
theorem antitone_mem_threshold_iff {g : Fin m → ℝ} (hg : Antitone g) (t : ℝ) (i : Fin m) :
    t ≤ g i ↔ i.val < (Finset.univ.filter (fun j => t ≤ g j)).card := by
  constructor
  · intro hti
    have hsub : Finset.univ.filter (fun j : Fin m => j.val ≤ i.val) ⊆
        Finset.univ.filter (fun j => t ≤ g j) := by
      intro j hj
      have hjle : j.val ≤ i.val := (Finset.mem_filter.mp hj).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ j,
        le_trans hti (hg (Fin.le_def.mpr hjle))⟩
    have hcard := Finset.card_le_card hsub
    rw [card_univ_filter_val_le (show i.val + 1 ≤ m from i.isLt)] at hcard
    omega
  · intro hcard
    by_contra hcon
    have hgt : g i < t := lt_of_not_ge hcon
    have hsub : Finset.univ.filter (fun j => t ≤ g j) ⊆
        Finset.univ.filter (fun j : Fin m => j.val < i.val) := by
      intro j hj
      have hjt : t ≤ g j := (Finset.mem_filter.mp hj).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ j, ?_⟩
      by_contra hjge
      have hle : i ≤ j := Fin.le_def.mpr (by omega)
      exact lt_irrefl (g i)
        (lt_of_lt_of_le hgt (le_trans hjt (hg hle)))
    have hcard' := Finset.card_le_card hsub
    rw [card_univ_filter_val_lt (le_of_lt i.isLt)] at hcard'
    omega

private theorem antitone_rearrange_le {g g' : Fin m → ℝ}
    (hg : Antitone g) (hg' : Antitone g') (tau : Equiv.Perm (Fin m))
    (h : ∀ i, g' i = g (tau i)) (i : Fin m) : g i ≤ g' i := by
  have h1 := card_filter_perm_mono_le g' tau.symm (g i)
  have h2 : (Finset.univ.filter (fun j : Fin m => g i ≤ g' (Equiv.symm tau j))) =
      (Finset.univ.filter (fun j : Fin m => g i ≤ g j)) := by
    refine Finset.filter_congr fun j _ => ?_
    rw [h, Equiv.apply_symm_apply]
  have hN : (Finset.univ.filter (fun j => g i ≤ g j)).card =
      (Finset.univ.filter (fun j => g i ≤ g' j)).card := by
    rw [← h2]
    exact h1
  have hmem := (antitone_mem_threshold_iff hg (g i) i).1 (le_refl (g i))
  rw [hN] at hmem
  exact (antitone_mem_threshold_iff hg' (g i) i).mpr hmem

/-- Two antitone rearrangements of one function agree pointwise.  This is the
uniqueness of the decreasing rearrangement; it shows the canonical
`decreasingSpectralPerm` is compatible with any other ordering construction. -/
theorem antitone_perm_eq_pointwise {g g' : Fin m → ℝ}
    (hg : Antitone g) (hg' : Antitone g') (tau : Equiv.Perm (Fin m))
    (h : ∀ i, g' i = g (tau i)) (i : Fin m) : g i = g' i := by
  have hswap : ∀ k, g k = g' (Equiv.symm tau k) := by
    intro k
    rw [h, Equiv.apply_symm_apply]
  exact le_antisymm (antitone_rearrange_le hg hg' tau h i)
    (antitone_rearrange_le hg' hg (Equiv.symm tau) hswap i)

/-- If `g` is an antitone rearrangement of `f` through an arbitrary
permutation, then `g` agrees with the canonical decreasing permutation.  This
lets an ordering theorem be stated through any permutation of its choice. -/
theorem eq_decreasingSpectralPerm_of_antitone_rearrangement {f g : Fin m → ℝ}
    (hg : Antitone g) (tau : Equiv.Perm (Fin m)) (h : ∀ i, g i = f (tau i)) (i : Fin m) :
    g i = f (decreasingSpectralPerm f i) := by
  have hG : Antitone (fun k : Fin m => f (decreasingSpectralPerm f k)) :=
    decreasingSpectralPerm_antitone f
  let w : Equiv.Perm (Fin m) := tau.trans (Equiv.symm (decreasingSpectralPerm f))
  have hcomp : ∀ k : Fin m, g k = f (decreasingSpectralPerm f (w k)) := by
    intro k
    rw [Equiv.trans_apply, Equiv.apply_symm_apply]
    exact h k
  exact (antitone_perm_eq_pointwise hG hg w hcomp i).symm

end Hurst
