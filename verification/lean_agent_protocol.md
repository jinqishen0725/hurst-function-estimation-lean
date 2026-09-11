# Lean agent acceleration protocol (append to every proof-agent prompt)

Project pins Mathlib v4.31.0 (see lean-toolchain). Your training-data Lean knowledge
is UNRELIABLE for this version — never trust a lemma name from memory. Use the
discovery ladder below; it is dramatically faster than guess-and-recompile.

## 1. Discovery ladder (in order)
1. **Local rg in the pinned Mathlib** (version-exact, fastest):
   `rg -n "lemma_name_fragment|docstring fragment" .lake/packages/mathlib/Mathlib -g '*.lean' | head`
   Deprecated names still resolve: rg the OLD name — the `deprecated` alias points to the new one.
2. **`exact?` / `apply?` / `rw?` diagnostic pass** (compiler-guided, zero hallucination):
   insert `exact?` at the stuck goal, run `lake env lean FILE`, READ the suggestions in
   stderr, replace with the suggested term. One diagnostic compile can replace 20 min of guessing.
   `simp?` similarly prints the simp set it would use.
3. **Loogle type search via WebFetch** (when you know the TYPE but no name fragment):
   GET `https://loogle.lean-lang.org/?q=<urlencoded>`. Metavariables `?x`; conclusion filter `|- concl`;
   e.g. `?q=%7Bx%20:%20%E2%84%9D%7D%20%E2%8A%A2%20?x%20%5E%20?y` or `?q=norm,%20|-%20_%20%E2%89%A4%20_`.
4. **`#check @Name` before using**: append `#check @The.Candidate.Name` lines at the end of the
   file, compile once, read exact signatures — kills type-mismatch round-trips before they happen.

## 2. Compile discipline
- Read the FIRST error only: Lean aborts each `by` block at its first failing tactic; fixing it
  exposes the next one. Fix top-down, recompile, repeat (expect a small cascade — that is normal).
- `set_option maxHeartbeats 1000000 in` in front of heavy theorems.
- Keep the file COMPILING between edits (comment out the unfinished theorem with `/- -/` rather
  than leaving a broken proof in place).

## 3. Proof style that survives this codebase
- Prefer explicit `have`-chains and `calc`; avoid `simp [a, b, c, ...]` with long lists (fragile);
  prefer `simp only [known lemma]`.
- Dependent `Fin.cons`/`Fin.snoc` need @-explicit type arguments:
  `@Fin.cons (k+1) (fun _ => Fin m) i (Fin.snoc z j)`.
- State induction lemmas with the data quantified after the induction variable:
  `theorem foo : ∀ k f i j, ...` + `induction k generalizing f i j`.
- Never `rw` under stuck applications; add rfl-provable one-line simp lemmas instead.
- `Matrix (Fin m) (Fin m) ℝ` breaks rw/dsimp under instances transparency — state matrix-entry
  lemmas over `Fin m → Fin m → ℝ` (definitionally equal) when motives misbehave.

## 4. v4.31.0 dialect dictionary (accumulated in this project — extend it in your report)
- `push_neg` deprecated → `push` / `Not` machinery; `Summable.of_nonneg_of_le` argument order
  changed (dominating series LAST); `Tendsto.congr_fun` → `Tendsto.congr`;
  `tsum_le_tsum` deleted → `HasSum.le` / `hasSum_le`; `Real.rpow_pow` does not exist →
  `Real.pow_rpow_inv_natCast`; `pow_le_pow_left` → `pow_le_pow_left₀`;
  `Metric.tendsto_atTop` is ∃N-form, not Eventually; `Real.tendsto_rpow_neg_atTop` does not
  exist → compose `tendsto_inv_atTop_zero` ∘ `Real.tendsto_rpow_atTop`;
  `Nat.le_add_left` vs `Nat.le_add_right` swapped orientation in some lemmas;
  `Tendsto.const_mul` produces `𝓝 (c * 0)` — simp after.
- `max_eq_left/right` not nameable bare → private lemmas via `le_antisymm`; `lt_or_le`/`le_or_lt`
  absent → `by_cases`.
- Hyperplane nullity: use `Measure.addHaar_submodule volume` (linear-subspace route), NOT pushforward.
- `Fin.succ` is the embedding Fin n → Fin (n+1); cyclic successor must be user-defined
  (`Hurst.cycleSucc`). `Matrix.IsHermitian.eigenvalues` is NOT sorted.
- Measure.pi hyperplane/finite-union results and pi-Fubini: check what
  Hurst/HyperplaneNull.lean and Hurst/ContinuumCutoffAssembly.lean already did — reuse.
- Frobenius: `Matrix.frobenius_norm_mul` (submultiplicativity) exists; |tr(AB)| ≤ ‖A‖_F‖B‖_op is
  FALSE (A=B=I) — use √n·‖·‖_F forms (Hurst/TracePowerTransfer.lean).

## 5. Honesty rules (unchanged)
No sorry/admit/axiom/native_decide. If a statement is false, prove the corrected statement and
document the deviation. If blocked, land compiling partials + report the exact gap. Report API
findings (new dictionary entries) in your final message.
