import Hurst.BandRemovalFinal

/-!
# Sharp (cyclic) word trace bounds: removing the `sqrt m` loss

The first assembly (`Hurst.BandRemovalFinal`) reduced Predicate 2 to the
norm-only input `hsmall` because its trace estimate paid a `sqrt m` loss
(`|tr W| <= sqrt(m) * ||W||_F` per word, via
`abs_trace_le_sqrt_card_mul_frobenius`).  The loss is unnecessary because the
trace is *cyclic*: for a word carrying at least one `A`-factor, rotate an `A`
to the front and use `|tr(A * M)| <= ||A||_F * ||M||_F` together with
Frobenius submultiplicativity for the remaining factors.

Landed here:

* `trace_mul_comm'` (L1): `tr(X * Y) = tr(Y * X)`, the seed of cyclic
  invariance (self-contained, instance-robust).
* `frobenius_norm_bool_prod_le`, `list_prod_norm_bool`: for the letter list of
  a word (booleans mapped to `A`/`B`), the norm of a nonempty product is at
  most the product of the letter norms, which is exactly
  `||A||_F^(#true) * ||B||_F^(#false)`.
* `abs_trace_bool_prod_le` (L2): the rotation bound — if a word splits as
  `bs₁ ++ true :: bs₂` with `bs₂ ++ bs₁` nonempty (word length `>= 2`), then
  `|tr(word)| <= ||A||_F^(#true) * ||B||_F^(#false)`; the proof rotates the
  `true` to the front using `trace_mul_comm'` and associativity.
* `trace_matWord_bound` (L3, the engine): for `k >= 2` and any word
  `w : Fin k → Bool` carrying at least one `true`,
  `|tr(matWord A B w)| <= ||A||_F^(countTrue w) * ||B||_F^(countFalse w)` —
  **no `sqrt m`, no `m`-factor**.
* `sum_abs_trace_matWord_le_true`, `sum_abs_trace_matWord_le_bernoulli`:
  summed over the words carrying at least one `true`,
  `sum |tr(matWord)| <= (||A||+||B||)^k - ||B||^k <= k * ||A|| * (||A||+||B||)^(k-1)`
  (transport by the landed `sum_word_scalars_erase_eq` + `bernoulli_pow_split'`).
* `abs_trace_rieszMeshDiff_split_cyclic`: the core split estimate of
  `Hurst.BandRemovalFinal` with the `sqrt m` factor **removed**:
  `|tr(U^k) - rho^k tr(T^k)| <= (||Dg||_F + rho*||T||_F)^k - (rho*||T||_F)^k`.
* `abs_trace_rieszMeshDiff_split_cyclic_bernoulli`: its Bernoulli corollary
  `<= k * ||Dg||_F * (||Dg||_F + rho*||T||_F)^(k-1)`.
* `abs_cycleValue_diff_le_cyclic`: the full cycle-value difference bound with
  the sharp first term:
  `|cycle(U) - cycle(T)| <= k*||Dg||_F*(||Dg||_F + rho*||T||_F)^(k-1)
  + |rho^k - 1| * (((m/S) * |c| * B_omega * cutoff^(-psi)))^k`.

Remaining glue for the final assembly (documented honestly, see the bottom of
this file): sharp cutoff-dependent Frobenius bounds for the mesh-difference and
truncated matrices,
`||Dg||_F <= C_psi * B_omega * |c| * ((m/S)^(1-psi) * cutoff^((1-2psi)/2)
+ (sqrt m / S) * rho * cutoff^(-psi))` (band power-sum route, band part small
in `R` uniformly in `n`, diagonal part vanishing in `n`) and
`||T||_F <= C'_psi * B_omega * |c| * ((m/S) * cutoff^(1/2-psi) + (sqrt m/S) *
(cutoff^(-psi) + 1))` (bounded in `n`, first piece small in `R`), plus the
three-epsilon filter assembly combining these with `tendsto_mesh_correction_rpow`.
-/

noncomputable section

open Set Filter Matrix
open scoped Matrix.Norms.Frobenius Topology

namespace Hurst

/-! ### L1: cyclic invariance of the trace of a two-factor product -/

/-- Cyclic invariance for two factors (self-contained). -/
private theorem trace_mul_comm' {n : Type*} [Fintype n] [DecidableEq n]
    (X Y : Matrix n n ℝ) :
    Matrix.trace (X * Y) = Matrix.trace (Y * X) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-! ### Boolean word lists and their letter matrices -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The letter matrix of a word bit: `true` plays `A`, `false` plays `B`. -/
private def wordLetter (A B : Matrix n n ℝ) : Bool → Matrix n n ℝ :=
  fun b => if b then A else B

/-- Occurrence count of a bit pattern in a boolean list (private, to stay
independent of `List.count` API drift). -/
private def bcnt (p : Bool) : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b = p then 1 else 0) + bcnt p bs

@[simp] private theorem bcnt_nil (p : Bool) : bcnt p [] = 0 := rfl

private theorem bcnt_cons (p b : Bool) (bs : List Bool) :
    bcnt p (b :: bs) = (if b = p then 1 else 0) + bcnt p bs := rfl

private theorem bcnt_cons_self (p : Bool) (bs : List Bool) :
    bcnt p (p :: bs) = 1 + bcnt p bs := by
  show (if p = p then 1 else 0) + bcnt p bs = 1 + bcnt p bs
  rw [if_pos rfl]

private theorem bcnt_cons_of_ne {p b : Bool} (h : b ≠ p) (bs : List Bool) :
    bcnt p (b :: bs) = bcnt p bs := by
  show (if b = p then 1 else 0) + bcnt p bs = bcnt p bs
  rw [if_neg h, zero_add]

private theorem bcnt_append (p : Bool) : ∀ bs₁ bs₂ : List Bool,
    bcnt p (bs₁ ++ bs₂) = bcnt p bs₁ + bcnt p bs₂
  | [], bs₂ => by simp
  | b :: bs₁, bs₂ => by
      show (if b = p then 1 else 0) + bcnt p (bs₁ ++ bs₂)
        = (if b = p then 1 else 0) + bcnt p bs₁ + bcnt p bs₂
      rw [bcnt_append p bs₁ bs₂]
      ring

/-- Splitting a list at a member: `a ∈ l` gives a decomposition `l = l₁ ++ a :: l₂`. -/
private theorem exists_split_of_mem {α : Type*} {a : α} : ∀ l : List α, a ∈ l →
    ∃ l₁ l₂, l = l₁ ++ a :: l₂
  | [], h => absurd h (by simp)
  | x :: l, h => by
      rcases List.mem_cons.mp h with rfl | hm
      · exact ⟨[], l, rfl⟩
      · obtain ⟨l₁, l₂, hss⟩ := exists_split_of_mem l hm
        exact ⟨x :: l₁, l₂, by simp [hss]⟩

/-! ### L2 ingredients: norm of a nonempty letter product -/

/-- Frobenius norm of a nonempty letter product is at most the product of the
letter norms. -/
private theorem frobenius_norm_bool_prod_le (A B : Matrix n n ℝ) :
    ∀ bs : List Bool, bs ≠ [] →
    ‖((bs.map (wordLetter A B)).prod : Matrix n n ℝ)‖
      ≤ (((bs.map (wordLetter A B)).map norm : List ℝ).prod)
  | [], h => absurd rfl h
  | [b], _ => by
      cases b with
      | true => simp [wordLetter]
      | false => simp [wordLetter]
  | b :: c :: bs, _ => by
      have hne : (c :: bs) ≠ [] := by simp
      simp only [List.map_cons, List.prod_cons]
      calc ‖wordLetter A B b * ((c :: bs).map (wordLetter A B)).prod‖
          ≤ ‖wordLetter A B b‖ * ‖((c :: bs).map (wordLetter A B)).prod‖ :=
            Matrix.frobenius_norm_mul _ _
        _ ≤ ‖wordLetter A B b‖ * (((c :: bs).map (wordLetter A B)).map norm : List ℝ).prod :=
            mul_le_mul_of_nonneg_left
              (frobenius_norm_bool_prod_le A B (c :: bs) hne) (norm_nonneg _)

/-- The product of the letter norms over a boolean word is exactly
`||A||_F^(#true) * ||B||_F^(#false)`. -/
private theorem list_prod_norm_bool (A B : Matrix n n ℝ) :
    ∀ bs : List Bool,
    (((bs.map (wordLetter A B)).map norm : List ℝ).prod)
      = ‖A‖ ^ bcnt true bs * ‖B‖ ^ bcnt false bs
  | [] => by simp
  | b :: bs => by
      simp only [List.map_cons, List.prod_cons]
      cases b with
      | true =>
          have hA : (wordLetter A B true : Matrix n n ℝ) = A := rfl
          rw [hA, list_prod_norm_bool A B bs, bcnt_cons_self,
            bcnt_cons_of_ne (by decide : true ≠ (false : Bool))]
          rw [pow_add, pow_one]
          ring
      | false =>
          have hB : (wordLetter A B false : Matrix n n ℝ) = B := rfl
          rw [hB, list_prod_norm_bool A B bs, bcnt_cons_of_ne (by decide : false ≠ (true : Bool)),
            bcnt_cons_self]
          rw [pow_add, pow_one]
          ring

/-- Mapping a nonempty boolean list through `wordLetter` stays nonempty. -/
private theorem map_wordLetter_ne_nil (A B : Matrix n n ℝ) :
    ∀ bs : List Bool, bs ≠ [] → (bs.map (wordLetter A B)) ≠ []
  | [], h => absurd rfl h
  | b :: bs, _ => by simp

/-! ### L2: the rotation bound on boolean words -/

/-- **Rotation bound (L2).**  If a boolean word splits as `bs₁ ++ true :: bs₂`
(the `true` being a chosen `A`-position) with `bs₂ ++ bs₁` nonempty (i.e. the
word has length `>= 2`), then
`|tr(word product)| <= ||A||_F^(#true) * ||B||_F^(#false)`.
The proof rotates the `true` to the front: with
`P = prod(bs₁) * (A * prod(bs₂))` one has `tr P = tr(A * (prod(bs₂) * prod(bs₁)))`
by `trace_mul_comm'` and associativity, then `|tr(A * M)| <= ||A||_F ||M||_F`
and Frobenius submultiplicativity finish the estimate. -/
private theorem abs_trace_bool_prod_le (A B : Matrix n n ℝ) :
    ∀ (bs₁ bs₂ : List Bool), (bs₂ ++ bs₁) ≠ [] →
    |Matrix.trace (((bs₁ ++ true :: bs₂).map (wordLetter A B)).prod : Matrix n n ℝ)|
      ≤ ‖A‖ ^ bcnt true (bs₁ ++ true :: bs₂) * ‖B‖ ^ bcnt false (bs₁ ++ true :: bs₂) := by
  intro bs₁ bs₂ hne
  have hmapA : (((bs₁ ++ true :: bs₂ : List Bool).map (wordLetter A B)) : List (Matrix n n ℝ))
      = (bs₁.map (wordLetter A B)) ++ A :: (bs₂.map (wordLetter A B)) := by
    rw [List.map_append, List.map_cons]
    rfl
  have hsplit : (((bs₁ ++ true :: bs₂ : List Bool).map (wordLetter A B)).prod :
      Matrix n n ℝ)
      = (bs₁.map (wordLetter A B)).prod * (A * (bs₂.map (wordLetter A B)).prod) := by
    rw [hmapA, List.prod_append, List.prod_cons]
  have htr : Matrix.trace (((bs₁ ++ true :: bs₂ : List Bool).map (wordLetter A B)).prod :
      Matrix n n ℝ)
      = Matrix.trace (A * ((bs₂.map (wordLetter A B)).prod
          * (bs₁.map (wordLetter A B)).prod)) := by
    rw [hsplit, trace_mul_comm', mul_assoc]
  have hmapT : (((bs₂ ++ bs₁ : List Bool).map (wordLetter A B)) : List (Matrix n n ℝ))
      = (bs₂.map (wordLetter A B)) ++ (bs₁.map (wordLetter A B)) := by
    rw [List.map_append]
  have hprod : (bs₂.map (wordLetter A B)).prod * (bs₁.map (wordLetter A B)).prod
      = (((bs₂ ++ bs₁ : List Bool).map (wordLetter A B)).prod : Matrix n n ℝ) := by
    rw [hmapT, List.prod_append]
  have hne' : ((bs₂ ++ bs₁).map (wordLetter A B)) ≠ [] :=
    map_wordLetter_ne_nil A B _ hne
  have hnorm : ‖(bs₂.map (wordLetter A B)).prod * (bs₁.map (wordLetter A B)).prod‖
      ≤ ‖A‖ ^ bcnt true (bs₂ ++ bs₁) * ‖B‖ ^ bcnt false (bs₂ ++ bs₁) := by
    rw [hprod]
    calc ‖(((bs₂ ++ bs₁ : List Bool).map (wordLetter A B)).prod : Matrix n n ℝ)‖
        ≤ (((bs₂ ++ bs₁ : List Bool).map (wordLetter A B)).map norm : List ℝ).prod :=
          frobenius_norm_bool_prod_le A B _ hne
      _ = ‖A‖ ^ bcnt true (bs₂ ++ bs₁) * ‖B‖ ^ bcnt false (bs₂ ++ bs₁) :=
          list_prod_norm_bool A B _
  have hc1 : bcnt true (bs₁ ++ true :: bs₂) = bcnt true (bs₂ ++ bs₁) + 1 := by
    rw [bcnt_append, bcnt_append, bcnt_cons_self]
    ring
  have hc2 : bcnt false (bs₁ ++ true :: bs₂) = bcnt false (bs₂ ++ bs₁) := by
    rw [bcnt_append, bcnt_append, bcnt_cons_of_ne (by decide : true ≠ (false : Bool))]
    ring
  rw [htr]
  refine le_trans (abs_matrix_trace_mul_le_frobenius _ _) ?_
  calc ‖A‖ * ‖(bs₂.map (wordLetter A B)).prod * (bs₁.map (wordLetter A B)).prod‖
      ≤ ‖A‖ * (‖A‖ ^ bcnt true (bs₂ ++ bs₁) * ‖B‖ ^ bcnt false (bs₂ ++ bs₁)) :=
        mul_le_mul_of_nonneg_left hnorm (norm_nonneg A)
    _ = ‖A‖ ^ (bcnt true (bs₂ ++ bs₁) + 1) * ‖B‖ ^ bcnt false (bs₂ ++ bs₁) := by
        rw [pow_succ]; ring
    _ = ‖A‖ ^ bcnt true (bs₁ ++ true :: bs₂) * ‖B‖ ^ bcnt false (bs₁ ++ true :: bs₂) := by
        rw [hc1, hc2]

/-! ### The word-level bridge: `ofFn`, `matWord`, `countTrue`/`countFalse` -/

/-- `Fin.snoc` words correspond to appending the last bit to the `ofFn` list. -/
private theorem ofFn_bool_snoc {k : ℕ} (w : Fin k → Bool) (b : Bool) :
    List.ofFn (@Fin.snoc k (fun _ => Bool) w b) = List.ofFn w ++ [b] := by
  rw [List.ofFn_succ', List.concat_eq_append]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

/-- Bridge: the boolean count of the `ofFn` list of a word equals the landed
`countTrue`/`countFalse`. -/
private theorem bcnt_true_ofFn_eq_countTrue : ∀ (k : ℕ) (w : Fin k → Bool),
    bcnt true (List.ofFn w) = countTrue w
  | 0, w => by simp [countTrue]
  | t + 1, w => by
      obtain ⟨b, w', rfl⟩ : ∃ (b : Bool) (w' : Fin t → Bool),
          w = @Fin.snoc t (fun _ => Bool) w' b := by
        obtain ⟨⟨b, w'⟩, hs⟩ := bijective_word_snoc.surjective w
        exact ⟨b, w', hs.symm⟩
      rw [ofFn_bool_snoc, bcnt_append, bcnt_true_ofFn_eq_countTrue t w']
      cases b with
      | true =>
          rw [bcnt_cons_self, bcnt_nil, countTrue_snoc_true]
      | false =>
          rw [bcnt_cons_of_ne (by decide : (false : Bool) ≠ true), bcnt_nil,
            countTrue_snoc_false]
          rw [Nat.add_zero]

/-- Bridge: `bcnt false` of the `ofFn` list equals `countFalse`. -/
private theorem bcnt_false_ofFn_eq_countFalse : ∀ (k : ℕ) (w : Fin k → Bool),
    bcnt false (List.ofFn w) = countFalse w
  | 0, w => by simp [countFalse]
  | t + 1, w => by
      obtain ⟨b, w', rfl⟩ : ∃ (b : Bool) (w' : Fin t → Bool),
          w = @Fin.snoc t (fun _ => Bool) w' b := by
        obtain ⟨⟨b, w'⟩, hs⟩ := bijective_word_snoc.surjective w
        exact ⟨b, w', hs.symm⟩
      rw [ofFn_bool_snoc, bcnt_append, bcnt_false_ofFn_eq_countFalse t w']
      cases b with
      | true =>
          rw [bcnt_cons_of_ne (by decide : (true : Bool) ≠ false), bcnt_nil,
            countFalse_snoc_true]
          rw [Nat.add_zero]
      | false =>
          rw [bcnt_cons_self, bcnt_nil, countFalse_snoc_false]

/-- The word matrix is the product of the letter matrices of the `ofFn` list. -/
private theorem matWord_eq_map_prod (A B : Matrix n n ℝ) {k : ℕ} (w : Fin k → Bool) :
    matWord A B w = ((List.ofFn w).map (wordLetter A B)).prod := by
  show List.prod (List.ofFn fun i : Fin k => if w i = true then A else B)
      = List.prod ((List.ofFn w).map (wordLetter A B))
  rw [← List.ofFn_comp' (g := wordLetter A B) (f := w)]
  rfl

/-! ### L3: the engine — word trace bound with no `sqrt m` -/

/-- **The engine (L3).**  For `k ≥ 2` and any word `w : Fin k → Bool` carrying
at least one `true`:

`|tr(matWord A B w)| <= ||A||_F^(countTrue w) * ||B||_F^(countFalse w)`

with **no `sqrt m` and no `m`-factor**: rotate a `true` to the front
(cyclic invariance of the trace), then `|tr(A * M)| <= ||A||_F * ||M||_F` and
Frobenius submultiplicativity for the remaining `k - 1 >= 1` factors. -/
theorem trace_matWord_bound {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) {k : ℕ} (hk : 2 ≤ k) (w : Fin k → Bool)
    (hw : ∃ i, w i = true) :
    |Matrix.trace (matWord A B w)| ≤ ‖A‖ ^ countTrue w * ‖B‖ ^ countFalse w := by
  classical
  obtain ⟨i0, hi0⟩ := hw
  have hmem : true ∈ List.ofFn w := by
    simp only [List.mem_ofFn]
    exact ⟨i0, hi0⟩
  obtain ⟨bs₁, bs₂, hsplit⟩ := exists_split_of_mem (List.ofFn w) hmem
  have hword : matWord A B w = ((List.ofFn w).map (wordLetter A B)).prod :=
    matWord_eq_map_prod A B w
  -- the remaining rotated word is nonempty because k >= 2
  have hne : (bs₂ ++ bs₁) ≠ [] := by
    intro hc
    have hl : List.length bs₂ + List.length bs₁ = 0 := by
      have h0 := congrArg List.length hc
      rw [List.length_append] at h0
      simpa using h0
    have h1 : bs₁ = [] := by
      cases bs₁ with
      | nil => rfl
      | cons b bs => simp at hl
    have h2 : bs₂ = [] := by
      cases bs₂ with
      | nil => rfl
      | cons b bs => simp at hl
    subst h2
    subst h1
    have hct : bcnt true (List.ofFn w) = 1 := by
      rw [hsplit]
      rfl
    rw [bcnt_true_ofFn_eq_countTrue] at hct
    have hcf : bcnt false (List.ofFn w) = 0 := by
      rw [hsplit]
      rfl
    rw [bcnt_false_ofFn_eq_countFalse] at hcf
    have hsum := countTrue_add_countFalse w
    omega
  have h := abs_trace_bool_prod_le A B bs₁ bs₂ hne
  rw [← hsplit] at h
  rw [bcnt_true_ofFn_eq_countTrue, bcnt_false_ofFn_eq_countFalse] at h
  rw [hword]
  exact h

/-! ### Deliverable 2: the summed bound over words with a `true` -/

/-- Words in the erased set carry at least one `true`. -/
private theorem exists_true_of_mem_erase {k : ℕ} {w : Fin k → Bool}
    (hw : w ∈ Finset.univ.erase (fun _ : Fin k => (false : Bool))) :
    ∃ i, w i = true := by
  by_contra hc
  have hne : w ≠ (fun _ : Fin k => (false : Bool)) := (Finset.mem_erase.mp hw).1
  apply hne
  funext i
  cases h : w i with
  | false => rfl
  | true => exact absurd ⟨i, h⟩ hc

/-- **Summed bound.**  Over the words carrying at least one `true`,
`sum |tr(matWord A B w)| <= (||A||_F + ||B||_F)^k - ||B||_F^k`. -/
theorem sum_abs_trace_matWord_le_true {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) {k : ℕ} (hk : 2 ≤ k) :
    (∑ w ∈ Finset.univ.erase (fun _ : Fin k => (false : Bool)),
      |Matrix.trace (matWord A B w)|)
      ≤ (‖A‖ + ‖B‖) ^ k - ‖B‖ ^ k := by
  refine le_trans (Finset.sum_le_sum fun w hw => ?_)
    (le_of_eq (sum_word_scalars_erase_eq ‖A‖ ‖B‖))
  exact trace_matWord_bound A B hk w (exists_true_of_mem_erase hw)

/-- **Summed bound, Bernoulli form.**
`sum |tr(matWord)| <= k * ||A||_F * (||A||_F + ||B||_F)^(k-1)`. -/
theorem sum_abs_trace_matWord_le_bernoulli {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) {k : ℕ} (hk : 2 ≤ k) :
    (∑ w ∈ Finset.univ.erase (fun _ : Fin k => (false : Bool)),
      |Matrix.trace (matWord A B w)|)
      ≤ (k : ℝ) * ‖A‖ * (‖A‖ + ‖B‖) ^ (k - 1) := by
  have hk1 : 1 ≤ k := by omega
  have h1 := sum_abs_trace_matWord_le_true A B hk
  have h2 := bernoulli_pow_split' hk1 (x := ‖A‖) (y := ‖B‖)
    (norm_nonneg _) (norm_nonneg _)
  linarith

/-! ### Deliverable 3 mechanics: the cyclic split estimate (no `sqrt m`) -/

@[simp] private theorem countTrue_const_false' {k : ℕ} :
    countTrue (fun _ : Fin k => (false : Bool)) = 0 := by
  simp [countTrue]

@[simp] private theorem countFalse_const_false' {k : ℕ} :
    countFalse (fun _ : Fin k => (false : Bool)) = k := by
  simp [countFalse]

/-- **Core split estimate, cyclic (sharp) form.**  For `m ≥ 1` and `k ≥ 2`, with
`U` the untruncated weighted Riesz matrix, `T` the truncated one,
`rho = meshRho m S psi` and `Dg = U - rho • T`:

`|tr(U^k) - rho^k * tr(T^k)| <= (||Dg||_F + rho*||T||_F)^k - (rho*||T||_F)^k`

— the `sqrt m` of `Hurst.abs_trace_rieszMeshDiff_split` is **gone**: each word
carrying at least one `Dg`-factor is bounded via the cyclic engine
`trace_matWord_bound` instead of `abs_trace_le_sqrt_card_mul_frobenius`. -/
theorem abs_trace_rieszMeshDiff_split_cyclic (m R : ℕ) (S psi c : ℝ) (omega : ℝ → ℝ)
    (hS : 0 < S) (hm : 0 < m) {k : ℕ} (hk : 2 ≤ k) :
    |Matrix.trace ((weightedRieszDiscreteMatrix m S psi c omega) ^ k)
        - meshRho m S psi ^ k *
          Matrix.trace ((weightedTruncatedRieszDiscreteMatrix m R S psi c omega) ^ k)|
      ≤ (((‖rieszMeshDiffMatrix m R S psi c omega‖
              + meshRho m S psi * ‖weightedTruncatedRieszDiscreteMatrix m R S psi c omega‖) ^ k
            - (meshRho m S psi * ‖weightedTruncatedRieszDiscreteMatrix m R S psi c omega‖) ^ k)) := by
  classical
  have hrho0 : 0 ≤ meshRho m S psi := by
    unfold meshRho
    exact Real.rpow_nonneg (by positivity) psi
  set Dg : Matrix (Fin m) (Fin m) ℝ := rieszMeshDiffMatrix m R S psi c omega with hDgdef
  set T : Matrix (Fin m) (Fin m) ℝ :=
    weightedTruncatedRieszDiscreteMatrix m R S psi c omega with hTdef
  set U : Matrix (Fin m) (Fin m) ℝ := weightedRieszDiscreteMatrix m S psi c omega with hUdef
  set rho : ℝ := meshRho m S psi with hrho
  have hUeq : U = rho • T + Dg := by
    show weightedRieszDiscreteMatrix m S psi c omega
        = meshRho m S psi • weightedTruncatedRieszDiscreteMatrix m R S psi c omega
          + (weightedRieszDiscreteMatrix m S psi c omega
            - meshRho m S psi • weightedTruncatedRieszDiscreteMatrix m R S psi c omega)
    simp
  have hU' : U = (1 : ℝ) • Dg + rho • T := by rw [one_smul, hUeq, add_comm]
  have hexpand : U ^ k
      = ∑ w : Fin k → Bool,
          ((1 : ℝ) ^ countTrue w * rho ^ countFalse w) • matWord Dg T w := by
    rw [hU', matrix_pow_binomial Dg T 1 rho k]
  have hterm0 : ((1 : ℝ) ^ countTrue (fun _ : Fin k => (false : Bool)) *
      rho ^ countFalse (fun _ : Fin k => (false : Bool))) •
      matWord Dg T (fun _ : Fin k => (false : Bool)) = (rho ^ k) • T ^ k := by
    simp only [countTrue_const_false', countFalse_const_false', pow_zero, one_mul,
      matWord_const_false]
  have hsplit : (∑ w ∈ Finset.univ.erase (fun _ : Fin k => (false : Bool)),
          ((1 : ℝ) ^ countTrue w * rho ^ countFalse w) • matWord Dg T w)
        + (rho ^ k) • T ^ k
      = ∑ w : Fin k → Bool,
          ((1 : ℝ) ^ countTrue w * rho ^ countFalse w) • matWord Dg T w := by
    have hbase := Finset.sum_erase_add (Finset.univ : Finset (Fin k → Bool))
      (fun w => ((1 : ℝ) ^ countTrue w * rho ^ countFalse w) • matWord Dg T w)
      (Finset.mem_univ (fun _ : Fin k => (false : Bool)))
    simp only [hterm0] at hbase
    exact hbase
  have h1 : Matrix.trace (U ^ k) - rho ^ k * Matrix.trace (T ^ k)
      = Matrix.trace (∑ w ∈ Finset.univ.erase (fun _ : Fin k => (false : Bool)),
          ((1 : ℝ) ^ countTrue w * rho ^ countFalse w) • matWord Dg T w) := by
    rw [hexpand, ← hsplit, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
    ring
  rw [h1]
  set E : Finset (Fin k → Bool) :=
    Finset.univ.erase (fun _ : Fin k => (false : Bool)) with hE
  set f : (Fin k → Bool) → Matrix (Fin m) (Fin m) ℝ := fun w =>
    ((1 : ℝ) ^ countTrue w * rho ^ countFalse w) • matWord Dg T w with hf
  have htrsum : Matrix.trace (∑ w ∈ E, f w) = ∑ w ∈ E, Matrix.trace (f w) :=
    Matrix.trace_sum E (fun w => f w)
  have hs1 : |Matrix.trace (∑ w ∈ E, f w)| ≤ ∑ w ∈ E, |Matrix.trace (f w)| := by
    rw [htrsum]
    exact Finset.abs_sum_le_sum_abs (fun w => Matrix.trace (f w)) E
  have hs2 : ∑ w ∈ E, |Matrix.trace (f w)|
      ≤ ∑ w ∈ E, ‖Dg‖ ^ countTrue w * (rho * ‖T‖) ^ countFalse w := by
    refine Finset.sum_le_sum fun w hw => ?_
    have hwt : ∃ i, w i = true := exists_true_of_mem_erase hw
    have htr : |Matrix.trace (f w)|
        = (1 : ℝ) ^ countTrue w * rho ^ countFalse w * |Matrix.trace (matWord Dg T w)| := by
      rw [hf]
      simp only [Matrix.trace_smul, smul_eq_mul, abs_mul, abs_pow, abs_one]
      rw [← abs_pow, abs_of_nonneg (pow_nonneg hrho0 _)]
    rw [htr, one_pow, one_mul]
    have hword := trace_matWord_bound Dg T hk w hwt
    calc rho ^ countFalse w * |Matrix.trace (matWord Dg T w)|
        ≤ rho ^ countFalse w * (‖Dg‖ ^ countTrue w * ‖T‖ ^ countFalse w) :=
          mul_le_mul_of_nonneg_left hword (pow_nonneg hrho0 _)
      _ = ‖Dg‖ ^ countTrue w * (rho * ‖T‖) ^ countFalse w := by
          rw [mul_pow]; ring
  have hs3 : ∑ w ∈ E, |Matrix.trace (f w)|
      ≤ (‖Dg‖ + rho * ‖T‖) ^ k - (rho * ‖T‖) ^ k := by
    refine le_trans hs2 ?_
    exact le_of_eq (sum_word_scalars_erase_eq ‖Dg‖ (rho * ‖T‖))
  exact le_trans hs1 hs3

/-- Bernoulli corollary of the cyclic split estimate:
`|tr(U^k) - rho^k tr(T^k)| <= k * ||Dg||_F * (||Dg||_F + rho*||T||_F)^(k-1)`
with **no** `sqrt m`. -/
theorem abs_trace_rieszMeshDiff_split_cyclic_bernoulli (m R : ℕ) (S psi c : ℝ)
    (omega : ℝ → ℝ) (hS : 0 < S) (hm : 0 < m) {k : ℕ} (hk : 2 ≤ k) :
    |Matrix.trace ((weightedRieszDiscreteMatrix m S psi c omega) ^ k)
        - meshRho m S psi ^ k *
          Matrix.trace ((weightedTruncatedRieszDiscreteMatrix m R S psi c omega) ^ k)|
      ≤ ((k : ℝ) * ‖rieszMeshDiffMatrix m R S psi c omega‖ *
        ((‖rieszMeshDiffMatrix m R S psi c omega‖
              + meshRho m S psi * ‖weightedTruncatedRieszDiscreteMatrix m R S psi c omega‖) ^ (k - 1))) := by
  have hrho0 : 0 ≤ meshRho m S psi := by
    unfold meshRho
    exact Real.rpow_nonneg (by positivity) psi
  have hk1 : 1 ≤ k := by omega
  refine le_trans (abs_trace_rieszMeshDiff_split_cyclic m R S psi c omega hS hm hk) ?_
  exact bernoulli_pow_split' hk1
    (x := ‖rieszMeshDiffMatrix m R S psi c omega‖)
    (y := meshRho m S psi * ‖weightedTruncatedRieszDiscreteMatrix m R S psi c omega‖)
    (norm_nonneg _) (mul_nonneg hrho0 (norm_nonneg _))

/-- **Full cycle-value difference bound, cyclic form.**
`|cycle(U) - cycle(T)| <= k*||Dg||_F*(||Dg||_F + rho*||T||_F)^(k-1)
+ |rho^k - 1| * (((m/S) * (|c| * B_omega * cutoff^(-psi)))^k)`. -/
theorem abs_cycleValue_diff_le_cyclic (m k R : ℕ) (S psi c B_omega : ℝ)
    (hS : 0 < S) (hm : 0 < m) (hpsi1 : 0 < psi) (hpsi2 : 2 * psi < 1) (hk : 2 ≤ k)
    (omega : ℝ → ℝ) (homegaB : ∀ z ∈ Icc (-1 : ℝ) 1, |omega z| ≤ B_omega) :
    |weightedRieszDiscreteCycleValue m k S psi c omega -
        weightedTruncatedRieszDiscreteCycleValue m k R S psi c omega|
      ≤ ((k : ℝ) * ‖rieszMeshDiffMatrix m R S psi c omega‖ *
          ((‖rieszMeshDiffMatrix m R S psi c omega‖
              + meshRho m S psi * ‖weightedTruncatedRieszDiscreteMatrix m R S psi c omega‖) ^ (k - 1)))
        + |meshRho m S psi ^ k - 1| *
          (((m : ℝ) / S) * (|c| * B_omega * rieszCycleCutoff R ^ (-psi))) ^ k := by
  classical
  have hTb := truncatedCycleValue_abs_le k hk R psi c B_omega hpsi1 hpsi2 omega
    homegaB m S hS hm
  rw [weightedTruncatedRieszDiscreteCycleValue_eq_trace_pow] at hTb
  rw [weightedRieszDiscreteCycleValue_eq_trace_pow,
    weightedTruncatedRieszDiscreteCycleValue_eq_trace_pow]
  have hsplit := abs_trace_rieszMeshDiff_split_cyclic_bernoulli m R S psi c omega hS hm hk
  have h2nd : |(meshRho m S psi ^ k - 1) *
      Matrix.trace ((weightedTruncatedRieszDiscreteMatrix m R S psi c omega) ^ k)|
      ≤ |meshRho m S psi ^ k - 1| *
        (((m : ℝ) / S) * (|c| * B_omega * rieszCycleCutoff R ^ (-psi))) ^ k := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hTb (abs_nonneg _)
  have htri : |Matrix.trace ((weightedRieszDiscreteMatrix m S psi c omega) ^ k)
      - Matrix.trace ((weightedTruncatedRieszDiscreteMatrix m R S psi c omega) ^ k)|
      ≤ |Matrix.trace ((weightedRieszDiscreteMatrix m S psi c omega) ^ k)
          - meshRho m S psi ^ k *
            Matrix.trace ((weightedTruncatedRieszDiscreteMatrix m R S psi c omega) ^ k)|
        + |(meshRho m S psi ^ k - 1) *
          Matrix.trace ((weightedTruncatedRieszDiscreteMatrix m R S psi c omega) ^ k)| := by
    have hident : Matrix.trace ((weightedRieszDiscreteMatrix m S psi c omega) ^ k)
        - Matrix.trace ((weightedTruncatedRieszDiscreteMatrix m R S psi c omega) ^ k)
        = (Matrix.trace ((weightedRieszDiscreteMatrix m S psi c omega) ^ k)
            - meshRho m S psi ^ k *
              Matrix.trace ((weightedTruncatedRieszDiscreteMatrix m R S psi c omega) ^ k))
          + (meshRho m S psi ^ k - 1) *
            Matrix.trace ((weightedTruncatedRieszDiscreteMatrix m R S psi c omega) ^ k) := by
      ring
    rw [hident]
    exact abs_add_le _ _
  calc |Matrix.trace ((weightedRieszDiscreteMatrix m S psi c omega) ^ k)
        - Matrix.trace ((weightedTruncatedRieszDiscreteMatrix m R S psi c omega) ^ k)|
      ≤ |Matrix.trace ((weightedRieszDiscreteMatrix m S psi c omega) ^ k)
          - meshRho m S psi ^ k *
            Matrix.trace ((weightedTruncatedRieszDiscreteMatrix m R S psi c omega) ^ k)|
          + |(meshRho m S psi ^ k - 1) *
            Matrix.trace ((weightedTruncatedRieszDiscreteMatrix m R S psi c omega) ^ k)| :=
        htri
    _ ≤ ((k : ℝ) * ‖rieszMeshDiffMatrix m R S psi c omega‖ *
          ((‖rieszMeshDiffMatrix m R S psi c omega‖
              + meshRho m S psi * ‖weightedTruncatedRieszDiscreteMatrix m R S psi c omega‖) ^ (k - 1)))
        + |meshRho m S psi ^ k - 1| *
          (((m : ℝ) / S) * (|c| * B_omega * rieszCycleCutoff R ^ (-psi))) ^ k :=
      add_le_add hsplit h2nd


section Restratify

/-! ### Distance stratification of pair sums (key input for the sharp band norms)

For the final assembly one needs the cutoff-decaying Frobenius bounds for the
mesh-difference and truncated matrices.  Both reduce to bounding, per row,
`sum_j f(Nat.dist i j)` by `2 * sum_{d ∈ range m} f d` — each integer distance
occurs for at most the two columns `i ± d`.  This is the lemma that converts
the crude `count * cap` band estimate into the sharp power-sum decay
`sum_{d < D} d^(-2 psi) <= D^(1-2 psi)/(1-2 psi)` of `Hurst.BandPowerSum`. -/

private theorem natDist (a b : ℕ) : Nat.dist a b = (a - b) + (b - a) := rfl

/-- **Row distance stratification.**  For any `f : ℕ → ℝ` and row `i`,
`sum_j f(Nat.dist i j) <= 2 * sum_{d ∈ range m} f d`: on each side of `i`
the map `j ↦ Nat.dist i j` is injective with values in `range m`. -/
theorem sum_row_dist_le {m : ℕ} (f : ℕ → ℝ) (hf : ∀ d, 0 ≤ f d) (i : Fin m) :
    (∑ j : Fin m, f (Nat.dist i.val j.val))
      ≤ 2 * ∑ d ∈ Finset.range m, f d := by
  classical
  have key : ∀ s : Finset (Fin m),
      (∀ j ∈ s, ∀ j' ∈ s, Nat.dist i.val j.val = Nat.dist i.val j'.val → j = j') →
      (∑ j ∈ s, f (Nat.dist i.val j.val)) ≤ ∑ d ∈ Finset.range m, f d := by
    intro s hinj
    have hval : ∀ j ∈ s, Nat.dist i.val j.val < m := by
      intro j _
      rw [natDist]
      have h1 : i.val < m := i.isLt
      have h2 : j.val < m := j.isLt
      omega
    have himg : (∑ d ∈ s.image (fun j : Fin m => Nat.dist i.val j.val), f d)
        = (∑ j ∈ s, f (Nat.dist i.val j.val)) :=
      Finset.sum_image (fun j hj j' hj' h => hinj j hj j' hj' h)
    have hsub : s.image (fun j : Fin m => Nat.dist i.val j.val) ⊆ Finset.range m := by
      intro d hd
      rw [Finset.mem_image] at hd
      obtain ⟨j, hj, hdj⟩ := hd
      subst hdj
      exact Finset.mem_range.mpr (hval j hj)
    calc (∑ j ∈ s, f (Nat.dist i.val j.val))
        = (∑ d ∈ s.image (fun j : Fin m => Nat.dist i.val j.val), f d) := himg.symm
      _ ≤ ∑ d ∈ Finset.range m, f d :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => hf d)
  have hsplit : (∑ j : Fin m, f (Nat.dist i.val j.val))
      = (∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val ≤ j.val),
          f (Nat.dist i.val j.val))
        + (∑ j ∈ Finset.univ.filter (fun j : Fin m => ¬(i.val ≤ j.val)),
          f (Nat.dist i.val j.val)) :=
    (Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun j : Fin m => i.val ≤ j.val) (fun j => f (Nat.dist i.val j.val))).symm
  have hright := key (Finset.univ.filter (fun j : Fin m => i.val ≤ j.val))
    (fun j hj j' hj' heq => by
      rw [natDist, natDist] at heq
      have hj : i.val ≤ j.val := (Finset.mem_filter.mp hj).2
      have hj' : i.val ≤ j'.val := (Finset.mem_filter.mp hj').2
      have h0 : j.val = j'.val := by omega
      exact Fin.ext h0)
  have hnotle : ∀ j ∈ Finset.univ.filter (fun j : Fin m => ¬(i.val ≤ j.val)),
      j.val ≤ i.val := by
    intro j hj
    have h1 := (Finset.mem_filter.mp hj).2
    omega
  have hleft' : (∑ j ∈ Finset.univ.filter (fun j : Fin m => ¬(i.val ≤ j.val)),
      f (Nat.dist i.val j.val))
      ≤ ∑ d ∈ Finset.range m, f d := by
    refine key _ (fun j hj j' hj' heq => ?_)
    rw [natDist, natDist] at heq
    have hj := hnotle j hj
    have hj' := hnotle j' hj'
    have h0 : j.val = j'.val := by omega
    exact Fin.ext h0
  rw [hsplit]
  calc (∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val ≤ j.val),
          f (Nat.dist i.val j.val))
        + (∑ j ∈ Finset.univ.filter (fun j : Fin m => ¬(i.val ≤ j.val)),
          f (Nat.dist i.val j.val))
      ≤ (∑ d ∈ Finset.range m, f d) + (∑ d ∈ Finset.range m, f d) :=
        add_le_add hright hleft'
    _ = 2 * ∑ d ∈ Finset.range m, f d := by ring

end Restratify

end Hurst
