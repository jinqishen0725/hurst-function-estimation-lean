import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Noncommutative word/binomial expansion of matrix powers

For matrices `A B : Matrix n n ℝ` and scalars `c₁ c₂ : ℝ`, the power
`(c₁ • A + c₂ • B) ^ k` expands as a sum over the `2^k` words
`w : Fin k → Bool`:

`(c₁ • A + c₂ • B) ^ k = ∑ w : Fin k → Bool, (c₁ ^ countTrue w * c₂ ^ countFalse w) • matWord A B w`

where `matWord A B w` is the ordered matrix product of the word's letters
(`w i = true` contributes `A`, `w i = false` contributes `B`), taken in the
standard order `i = 0, …, k-1` (`List.prod (List.ofFn …)`).

Also provided:

* the per-word Frobenius bounds `frobenius_matWord_le` (`≤ (max ‖A‖ ‖B‖)^k`)
  and `frobenius_matWord_le'` (`≤ ‖A‖ ^ countTrue w * ‖B‖ ^ countFalse w`),
* cardinality bookkeeping `card_matrix_words` (`Fintype.card (Fin k → Bool) = 2^k`)
  and the subset bounds `card_word_subset_le`, `card_words_with_true_le`,
* the trace corollary `abs_trace_matrix_pow_binomial_le`:
  `|tr((c₁•A + c₂•B)^k)| ≤ 2^k * √d * (max (|c₁|*‖A‖_F) (|c₂|*‖B‖_F))^k`.
-/

noncomputable section

open scoped Matrix.Norms.Frobenius

namespace Hurst

/-! ### A card-vs-indicator-sum bridge -/

private theorem card_filter_bool_eq_sum {α : Type*} [DecidableEq α] (p : α → Bool) (v : Bool)
    (s : Finset α) :
    (s.filter fun a => p a = v).card = ∑ a ∈ s, (if p a = v then 1 else 0) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.filter_insert, Finset.sum_insert ha]
    by_cases h : p a = v
    · rw [if_pos h, if_pos h, Finset.card_insert_of_notMem (by
        intro hmem
        exact ha ((Finset.mem_filter.mp hmem).1)), ih]
      omega
    · rw [if_neg h, if_neg h, ih]
      omega

/-! ### Matrix words -/

/-- The matrix word indexed by `w : Fin k → Bool`: the product of the letters
`if w i then A else B` in the standard order `i = 0, …, k-1`
(`List.prod (List.ofFn …)` over the noncommutative matrix monoid). -/
def matWord {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n ℝ) {k : ℕ}
    (w : Fin k → Bool) : Matrix n n ℝ :=
  List.prod (List.ofFn fun i : Fin k => if w i then A else B)

/-- Adjoining a last bit `b` appends the letter `if b then A else B` to the word. -/
theorem matWord_snoc {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n ℝ) {k : ℕ}
    (w : Fin k → Bool) (b : Bool) :
    matWord A B (@Fin.snoc k (fun _ => Bool) w b) =
      matWord A B w * (if b then A else B) := by
  unfold matWord
  rw [List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_cons,
    List.prod_nil, mul_one]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

theorem matWord_snoc_true {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n ℝ)
    {k : ℕ} (w : Fin k → Bool) :
    matWord A B (@Fin.snoc k (fun _ => Bool) w true) = matWord A B w * A := by
  rw [matWord_snoc, if_pos rfl]

theorem matWord_snoc_false {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n ℝ)
    {k : ℕ} (w : Fin k → Bool) :
    matWord A B (@Fin.snoc k (fun _ => Bool) w false) = matWord A B w * B := by
  rw [matWord_snoc, if_neg (by decide : (false : Bool) ≠ true)]

/-! ### Bit counts in words -/

/-- Number of `true` bits of a word, i.e. the number of `A`-factors. -/
def countTrue {k : ℕ} (w : Fin k → Bool) : ℕ :=
  (Finset.univ.filter fun i => w i = true).card

/-- Number of `false` bits of a word, i.e. the number of `B`-factors. -/
def countFalse {k : ℕ} (w : Fin k → Bool) : ℕ :=
  (Finset.univ.filter fun i => w i = false).card

theorem countTrue_snoc {k : ℕ} (w : Fin k → Bool) (b : Bool) :
    countTrue (Fin.snoc w b) = countTrue w + (if b = true then 1 else 0) := by
  have h := card_filter_bool_eq_sum (p := Fin.snoc w b) true Finset.univ
  rw [Fin.sum_univ_castSucc] at h
  simp only [Fin.snoc_castSucc, Fin.snoc_last] at h
  rw [← card_filter_bool_eq_sum (p := w) true Finset.univ] at h
  unfold countTrue
  omega

theorem countFalse_snoc {k : ℕ} (w : Fin k → Bool) (b : Bool) :
    countFalse (Fin.snoc w b) = countFalse w + (if b = false then 1 else 0) := by
  have h := card_filter_bool_eq_sum (p := Fin.snoc w b) false Finset.univ
  rw [Fin.sum_univ_castSucc] at h
  simp only [Fin.snoc_castSucc, Fin.snoc_last] at h
  rw [← card_filter_bool_eq_sum (p := w) false Finset.univ] at h
  unfold countFalse
  omega

theorem countTrue_snoc_true {k : ℕ} (w : Fin k → Bool) :
    countTrue (Fin.snoc w true) = countTrue w + 1 := by
  rw [countTrue_snoc, if_pos rfl]

theorem countTrue_snoc_false {k : ℕ} (w : Fin k → Bool) :
    countTrue (Fin.snoc w false) = countTrue w := by
  rw [countTrue_snoc, if_neg (by decide : (false : Bool) ≠ true), Nat.add_zero]

theorem countFalse_snoc_true {k : ℕ} (w : Fin k → Bool) :
    countFalse (Fin.snoc w true) = countFalse w := by
  rw [countFalse_snoc, if_neg (by decide : ¬(true = false)), Nat.add_zero]

theorem countFalse_snoc_false {k : ℕ} (w : Fin k → Bool) :
    countFalse (Fin.snoc w false) = countFalse w + 1 := by
  rw [countFalse_snoc, if_pos rfl]

theorem countTrue_add_countFalse {k : ℕ} (w : Fin k → Bool) :
    countTrue w + countFalse w = k := by
  have h1 : (Finset.univ.filter fun i : Fin k => w i = false) =
      (Finset.univ.filter fun i : Fin k => ¬(w i = true)) := by
    refine Finset.filter_congr fun i _ => ?_
    cases w i <;> simp
  have h2 : (Finset.univ.filter (fun i : Fin k => w i = true)).card +
      (Finset.univ.filter fun i : Fin k => ¬(w i = true)).card = Finset.univ.card :=
    Finset.card_filter_add_card_filter_not (fun i : Fin k => w i = true)
  rw [← h1] at h2
  rw [Finset.card_univ, Fintype.card_fin] at h2
  unfold countTrue countFalse
  omega

/-! ### The bijection between extended words and last-bit/word pairs -/

/-- `Fin.snoc` identifies pairs (last bit `b`, word `w : Fin k → Bool`) with
words on `Fin (k + 1)`. -/
theorem bijective_word_snoc {k : ℕ} :
    Function.Bijective (fun p : Bool × (Fin k → Bool) =>
      @Fin.snoc k (fun _ => Bool) p.2 p.1) :=
  (Fin.snocEquiv (fun _ => Bool) (n := k)).bijective

/-- Sum over `Bool` unfolds to the two values (order: `false`, then `true`). -/
private theorem sum_bool {M : Type*} [AddCommMonoid M] (f : Bool → M) :
    ∑ b : Bool, f b = f false + f true := by
  have huniv : (Finset.univ : Finset Bool) = {false, true} := by
    ext b
    cases b <;> simp
  rw [huniv, Finset.sum_insert (by simp), Finset.sum_singleton]

/-! ### The word/binomial expansion -/

/-- The noncommutative binomial expansion: the `k`-th power of `c₁ • A + c₂ • B`
is the sum over all `2^k` words of the scalar-weighted matrix words. -/
theorem matrix_pow_binomial {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) (c₁ c₂ : ℝ) (k : ℕ) :
    (c₁ • A + c₂ • B) ^ k
      = ∑ w : Fin k → Bool,
          ((c₁ ^ countTrue w * c₂ ^ countFalse w) • matWord A B w) := by
  induction k with
  | zero =>
    rw [pow_zero]
    have h2 : ∀ w : Fin 0 → Bool,
        ((c₁ ^ countTrue w * c₂ ^ countFalse w) • matWord A B w : Matrix n n ℝ) = 1 := by
      intro w
      simp [matWord, countTrue, countFalse, List.ofFn_zero, List.prod_nil]
    have h0 : ∀ b ∈ (Finset.univ : Finset (Fin 0 → Bool)), b ≠ (default : Fin 0 → Bool) →
        ((c₁ ^ countTrue b * c₂ ^ countFalse b) • matWord A B b) = 0 := by
      intro b _ hb
      exact absurd (funext fun i => i.elim0 : b = default) hb
    rw [Finset.sum_eq_single_of_mem (default : Fin 0 → Bool) (Finset.mem_univ _) h0]
    exact (h2 default).symm
  | succ k ih =>
    rw [pow_succ, ih, Finset.sum_mul]
    have hexpair : (∑ w : Fin k → Bool,
        (c₁ ^ countTrue w * c₂ ^ countFalse w) • matWord A B w * (c₁ • A + c₂ • B))
        = ∑ p : Bool × (Fin k → Bool),
          (c₁ ^ countTrue p.2 * c₂ ^ countFalse p.2) • matWord A B p.2
            * (if p.1 then c₁ • A else c₂ • B) := by
      rw [Fintype.sum_prod_type, sum_bool, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun w _ => ?_
      show (c₁ ^ countTrue w * c₂ ^ countFalse w) • matWord A B w * (c₁ • A + c₂ • B)
        = (c₁ ^ countTrue w * c₂ ^ countFalse w) • matWord A B w * (c₂ • B)
          + (c₁ ^ countTrue w * c₂ ^ countFalse w) • matWord A B w * (c₁ • A)
      rw [mul_add]
      exact add_comm
        ((c₁ ^ countTrue w * c₂ ^ countFalse w) • matWord A B w * (c₁ • A))
        ((c₁ ^ countTrue w * c₂ ^ countFalse w) • matWord A B w * (c₂ • B))
    have stepF : ∀ w : Fin k → Bool,
        (c₁ ^ countTrue w * c₂ ^ countFalse w) • matWord A B w * (c₂ • B)
          = (c₁ ^ countTrue (Fin.snoc w false) * c₂ ^ countFalse (Fin.snoc w false))
              • matWord A B (Fin.snoc w false) := by
      intro w
      rw [matWord_snoc_false, countTrue_snoc_false, countFalse_snoc_false, pow_succ,
        Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      congr 1
      ring
    have stepT : ∀ w : Fin k → Bool,
        (c₁ ^ countTrue w * c₂ ^ countFalse w) • matWord A B w * (c₁ • A)
          = (c₁ ^ countTrue (Fin.snoc w true) * c₂ ^ countFalse (Fin.snoc w true))
              • matWord A B (Fin.snoc w true) := by
      intro w
      rw [matWord_snoc_true, countTrue_snoc_true, countFalse_snoc_true, pow_succ',
        Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      congr 1
      ring
    rw [hexpair]
    refine Fintype.sum_bijective _ bijective_word_snoc _ _ (fun p => ?_)
    cases p with
    | mk b w =>
      cases b with
      | false =>
        show (c₁ ^ countTrue w * c₂ ^ countFalse w) • matWord A B w * (c₂ • B)
          = (c₁ ^ countTrue (Fin.snoc w false) * c₂ ^ countFalse (Fin.snoc w false))
              • matWord A B (Fin.snoc w false)
        exact stepF w
      | true =>
        show (c₁ ^ countTrue w * c₂ ^ countFalse w) • matWord A B w * (c₁ • A)
          = (c₁ ^ countTrue (Fin.snoc w true) * c₂ ^ countFalse (Fin.snoc w true))
              • matWord A B (Fin.snoc w true)
        exact stepT w

/-! ### Frobenius bounds per word -/

/-- Sharper per-word Frobenius bound for nonempty words: the norm of a word of
length `t + 1` is at most `‖A‖^(number of trues) * ‖B‖^(number of falses)`, by
induction on the word length peeling the last letter
(`Matrix.frobenius_norm_mul`).  (The empty word is excluded: it is the
identity, of Frobenius norm `√n` rather than `1`.) -/
theorem frobenius_matWord_le' {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) :
    ∀ (t : ℕ) (w : Fin (t + 1) → Bool),
      ‖matWord A B w‖ ≤ ‖A‖ ^ countTrue w * ‖B‖ ^ countFalse w := by
  intro t
  induction t with
  | zero =>
    intro w
    obtain ⟨b, w', rfl⟩ : ∃ (b : Bool) (w' : Fin 0 → Bool),
        w = @Fin.snoc 0 (fun _ => Bool) w' b := by
      obtain ⟨⟨b, w'⟩, hs⟩ := bijective_word_snoc.surjective w
      exact ⟨b, w', hs.symm⟩
    have hw0 : matWord A B w' = 1 := by
      simp [matWord, List.ofFn_zero, List.prod_nil]
    have hc0 : countTrue w' = 0 := by simp [countTrue]
    have hf0 : countFalse w' = 0 := by simp [countFalse]
    cases b with
    | true =>
      rw [matWord_snoc_true, countTrue_snoc_true, countFalse_snoc_true, hw0, hc0, hf0,
        one_mul, zero_add, pow_one, pow_zero, mul_one]
    | false =>
      rw [matWord_snoc_false, countTrue_snoc_false, countFalse_snoc_false, hw0, hc0, hf0,
        one_mul, pow_zero, zero_add, pow_one, one_mul]
  | succ t ih =>
    intro w
    obtain ⟨b, w', rfl⟩ : ∃ (b : Bool) (w' : Fin (t + 1) → Bool),
        w = @Fin.snoc (t + 1) (fun _ => Bool) w' b := by
      obtain ⟨⟨b, w'⟩, hs⟩ := bijective_word_snoc.surjective w
      exact ⟨b, w', hs.symm⟩
    cases b with
    | true =>
      rw [matWord_snoc_true, countTrue_snoc_true, countFalse_snoc_true]
      calc ‖matWord A B w' * A‖
          ≤ ‖matWord A B w'‖ * ‖A‖ := Matrix.frobenius_norm_mul _ _
        _ ≤ (‖A‖ ^ countTrue w' * ‖B‖ ^ countFalse w') * ‖A‖ :=
            mul_le_mul (ih w') le_rfl (norm_nonneg _)
              (mul_nonneg (pow_nonneg (norm_nonneg A) _) (pow_nonneg (norm_nonneg B) _))
        _ = ‖A‖ ^ (countTrue w' + 1) * ‖B‖ ^ countFalse w' := by
              rw [pow_succ]; ring
    | false =>
      rw [matWord_snoc_false, countTrue_snoc_false, countFalse_snoc_false]
      calc ‖matWord A B w' * B‖
          ≤ ‖matWord A B w'‖ * ‖B‖ := Matrix.frobenius_norm_mul _ _
        _ ≤ (‖A‖ ^ countTrue w' * ‖B‖ ^ countFalse w') * ‖B‖ :=
            mul_le_mul (ih w') le_rfl (norm_nonneg _)
              (mul_nonneg (pow_nonneg (norm_nonneg A) _) (pow_nonneg (norm_nonneg B) _))
        _ = ‖A‖ ^ countTrue w' * ‖B‖ ^ (countFalse w' + 1) := by
              rw [pow_succ]; ring

/-- Each nonempty matrix word has Frobenius norm at most `(max ‖A‖ ‖B‖)^k`. -/
theorem frobenius_matWord_le {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) {k : ℕ} (w : Fin k → Bool) (hk : 1 ≤ k) :
    ‖matWord A B w‖ ≤ (max ‖A‖ ‖B‖) ^ k := by
  obtain ⟨t, rfl⟩ : ∃ t, k = t + 1 := ⟨k - 1, by omega⟩
  have h1 : ‖A‖ ^ countTrue w ≤ (max ‖A‖ ‖B‖) ^ countTrue w :=
    pow_le_pow_left₀ (norm_nonneg A) (le_max_left ‖A‖ ‖B‖) _
  have h2 : ‖B‖ ^ countFalse w ≤ (max ‖A‖ ‖B‖) ^ countFalse w :=
    pow_le_pow_left₀ (norm_nonneg B) (le_max_right ‖A‖ ‖B‖) _
  refine le_trans (frobenius_matWord_le' A B t w) ?_
  calc ‖A‖ ^ countTrue w * ‖B‖ ^ countFalse w
      ≤ (max ‖A‖ ‖B‖) ^ countTrue w * (max ‖A‖ ‖B‖) ^ countFalse w :=
        mul_le_mul h1 h2 (pow_nonneg (norm_nonneg B) _)
          (pow_nonneg (by positivity : 0 ≤ max ‖A‖ ‖B‖) _)
    _ = (max ‖A‖ ‖B‖) ^ (countTrue w + countFalse w) := (pow_add _ _ _).symm
    _ = (max ‖A‖ ‖B‖) ^ (t + 1) := by rw [countTrue_add_countFalse]

/-- Weighted per-word Frobenius bound for nonempty words:
`|(c₁^t c₂^f) • matWord A B w|_F ≤ (max (|c₁|·‖A‖_F) (|c₂|·‖B‖_F))^k`. -/
theorem frobenius_smul_matWord_le {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) (c₁ c₂ : ℝ) {k : ℕ} (w : Fin k → Bool) (hk : 1 ≤ k) :
    ‖(c₁ ^ countTrue w * c₂ ^ countFalse w) • matWord A B w‖
      ≤ (max (|c₁| * ‖A‖) (|c₂| * ‖B‖)) ^ k := by
  obtain ⟨t, rfl⟩ : ∃ t, k = t + 1 := ⟨k - 1, by omega⟩
  have hword := frobenius_matWord_le' A B t w
  have hscal : |c₁ ^ countTrue w * c₂ ^ countFalse w|
      = |c₁| ^ countTrue w * |c₂| ^ countFalse w := by
    rw [abs_mul, abs_pow, abs_pow]
  have hpowA : |c₁| ^ countTrue w * ‖A‖ ^ countTrue w = (|c₁| * ‖A‖) ^ countTrue w :=
    (mul_pow _ _ _).symm
  have hpowB : |c₂| ^ countFalse w * ‖B‖ ^ countFalse w = (|c₂| * ‖B‖) ^ countFalse w :=
    (mul_pow _ _ _).symm
  have h1 : (|c₁| * ‖A‖) ^ countTrue w ≤
      (max (|c₁| * ‖A‖) (|c₂| * ‖B‖)) ^ countTrue w :=
    pow_le_pow_left₀ (mul_nonneg (abs_nonneg c₁) (norm_nonneg A)) (le_max_left _ _) _
  have h2 : (|c₂| * ‖B‖) ^ countFalse w ≤
      (max (|c₁| * ‖A‖) (|c₂| * ‖B‖)) ^ countFalse w :=
    pow_le_pow_left₀ (mul_nonneg (abs_nonneg c₂) (norm_nonneg B)) (le_max_right _ _) _
  calc ‖(c₁ ^ countTrue w * c₂ ^ countFalse w) • matWord A B w‖
      = |c₁ ^ countTrue w * c₂ ^ countFalse w| * ‖matWord A B w‖ := norm_smul _ _
    _ ≤ (|c₁| * ‖A‖) ^ countTrue w * (|c₂| * ‖B‖) ^ countFalse w := by
        rw [hscal]
        calc |c₁| ^ countTrue w * |c₂| ^ countFalse w * ‖matWord A B w‖
            ≤ (|c₁| ^ countTrue w * |c₂| ^ countFalse w) *
                (‖A‖ ^ countTrue w * ‖B‖ ^ countFalse w) :=
              mul_le_mul_of_nonneg_left hword
                (mul_nonneg (pow_nonneg (abs_nonneg c₁) _) (pow_nonneg (abs_nonneg c₂) _))
          _ = (|c₁| * ‖A‖) ^ countTrue w * (|c₂| * ‖B‖) ^ countFalse w := by
              rw [mul_mul_mul_comm, hpowA, hpowB]
    _ ≤ (max (|c₁| * ‖A‖) (|c₂| * ‖B‖)) ^ countTrue w
        * (max (|c₁| * ‖A‖) (|c₂| * ‖B‖)) ^ countFalse w :=
        mul_le_mul h1 h2 (pow_nonneg (mul_nonneg (abs_nonneg c₂) (norm_nonneg B)) _)
          (pow_nonneg (by positivity : 0 ≤ max (|c₁| * ‖A‖) (|c₂| * ‖B‖)) _)
    _ = (max (|c₁| * ‖A‖) (|c₂| * ‖B‖)) ^ (countTrue w + countFalse w) :=
        (pow_add _ _ _).symm
    _ = (max (|c₁| * ‖A‖) (|c₂| * ‖B‖)) ^ (t + 1) := by rw [countTrue_add_countFalse]

/-! ### Cardinality of word sets -/

/-- There are exactly `2^k` words of length `k`. -/
theorem card_matrix_words (k : ℕ) : Fintype.card (Fin k → Bool) = 2 ^ k := by
  rw [Fintype.card_pi, Finset.prod_const, Fintype.card_bool, Finset.card_univ,
    Fintype.card_fin]

/-- Any set of words has cardinality at most `2^k`. -/
theorem card_word_subset_le (k : ℕ) (S : Finset (Fin k → Bool)) : S.card ≤ 2 ^ k := by
  refine le_trans (Finset.card_le_card (Finset.subset_univ S)) ?_
  rw [Finset.card_univ, card_matrix_words]

/-- A set of words each containing at least one `true` has cardinality at most
`2^k - 1` (it misses the all-`false` word), so in particular `≤ 2^k`. -/
theorem card_words_with_true_le (k : ℕ) (S : Finset (Fin k → Bool))
    (hS : ∀ w ∈ S, ∃ i : Fin k, w i = true) : S.card ≤ 2 ^ k - 1 := by
  have hsub : S ⊆ Finset.univ.erase (fun _ => false) := by
    intro w hw
    obtain ⟨i, hi⟩ := hS w hw
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ w⟩
    intro hwe
    rw [hwe] at hi
    simp at hi
  refine le_trans (Finset.card_le_card hsub) ?_
  rw [Finset.card_erase_of_mem (Finset.mem_univ (fun _ => false)), Finset.card_univ,
    card_matrix_words]

/-! ### Trace corollary -/

/-- The absolute trace is bounded by `√(card n)` times the Frobenius norm. -/
theorem abs_trace_le_sqrt_card_mul_frobenius_of_fintype {n : Type*} [Fintype n] [DecidableEq n]
    (Z : Matrix n n ℝ) :
    |Matrix.trace Z| ≤ Real.sqrt (Fintype.card n) * ‖Z‖ := by
  have hnorm : ‖Z‖ = Real.sqrt (∑ i : n, ∑ j : n, |Z i j| ^ 2) := by
    rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
    congr 1
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by simp [Real.norm_eq_abs]
  have h3 : Real.sqrt (∑ i : n, |Z i i| ^ 2)
      ≤ Real.sqrt (∑ i : n, ∑ j : n, |Z i j| ^ 2) :=
    Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ =>
      Finset.single_le_sum (f := fun j => |Z i j| ^ 2) (fun j _ => by positivity)
        (Finset.mem_univ i))
  calc |Matrix.trace Z| = |∑ i : n, Z i i| := by simp [Matrix.trace, Matrix.diag]
    _ ≤ ∑ i : n, |Z i i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : n, (1 * |Z i i|) := by simp
    _ ≤ Real.sqrt (∑ _i : n, (1 : ℝ) ^ 2) * Real.sqrt (∑ i : n, |Z i i| ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _ => 1) (fun i => |Z i i|)
    _ ≤ Real.sqrt (Fintype.card n) * Real.sqrt (∑ i : n, ∑ j : n, |Z i j| ^ 2) :=
        mul_le_mul (by simp) h3 (by simp) (Real.sqrt_nonneg _)
    _ = Real.sqrt (Fintype.card n) * ‖Z‖ := by rw [hnorm]

/-- Consumer-shaped corollary: for `k ≥ 1`, the trace of the matrix power of
the affine combination satisfies
`|tr((c₁•A + c₂•B)^k)| ≤ 2^k · √d · (max (|c₁|·‖A‖_F) (|c₂|·‖B‖_F))^k`
for `A B : Matrix (Fin d) (Fin d) ℝ`.  (At `k = 0` the trace is `d`, so the
`√d` factor must be replaced by `d`.) -/
theorem abs_trace_matrix_pow_binomial_le {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ)
    (c₁ c₂ : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    |Matrix.trace ((c₁ • A + c₂ • B) ^ k)|
      ≤ (2 ^ k : ℝ) * Real.sqrt d * (max (|c₁| * ‖A‖) (|c₂| * ‖B‖)) ^ k := by
  have hbound : ‖(c₁ • A + c₂ • B) ^ k‖
      ≤ (2 ^ k : ℝ) * (max (|c₁| * ‖A‖) (|c₂| * ‖B‖)) ^ k := by
    rw [matrix_pow_binomial]
    calc ‖∑ w : Fin k → Bool, ((c₁ ^ countTrue w * c₂ ^ countFalse w) • matWord A B w)‖
        ≤ ∑ w : Fin k → Bool,
            ‖(c₁ ^ countTrue w * c₂ ^ countFalse w) • matWord A B w‖ := norm_sum_le _ _
      _ ≤ ∑ w : Fin k → Bool, (max (|c₁| * ‖A‖) (|c₂| * ‖B‖)) ^ k :=
          Finset.sum_le_sum fun w _ => frobenius_smul_matWord_le A B c₁ c₂ w hk
      _ = (Fintype.card (Fin k → Bool) : ℝ) * (max (|c₁| * ‖A‖) (|c₂| * ‖B‖)) ^ k := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, card_matrix_words,
            Nat.cast_pow]
      _ = (2 ^ k : ℝ) * (max (|c₁| * ‖A‖) (|c₂| * ‖B‖)) ^ k := by
          rw [card_matrix_words, Nat.cast_pow, Nat.cast_ofNat]
  calc |Matrix.trace ((c₁ • A + c₂ • B) ^ k)|
      ≤ Real.sqrt (Fintype.card (Fin d)) * ‖(c₁ • A + c₂ • B) ^ k‖ :=
        abs_trace_le_sqrt_card_mul_frobenius_of_fintype _
    _ = Real.sqrt d * ‖(c₁ • A + c₂ • B) ^ k‖ := by rw [Fintype.card_fin]
    _ ≤ Real.sqrt d * ((2 ^ k : ℝ) * (max (|c₁| * ‖A‖) (|c₂| * ‖B‖)) ^ k) :=
        mul_le_mul_of_nonneg_left hbound (Real.sqrt_nonneg _)
    _ = (2 ^ k : ℝ) * Real.sqrt d * (max (|c₁| * ‖A‖) (|c₂| * ‖B‖)) ^ k := by ring

end Hurst
