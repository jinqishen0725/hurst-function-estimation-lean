# Parallel wave prompts (2026-09-10 17:20 window, interrupted by rate limit)

## COORDINATOR PLAYBOOK (2026-09-11, from flow post-mortem)

Agent flow archetypes observed (success rate / typical time):
- A. Explorer-fail (goal-only prompt): ~0% useful output; time goes to repo reading + API guessing.
  FIX: paste exact definitions + exact target statement into the prompt (T1 vs T1' A/B: 0 output
  in 26 min vs landed in ~30 min).
- B. Assembler (all inputs already landed; prompt lists input lemma names + proof route): high
  success, 25-40 min (T3, T12d, T9a).
- C. Pure-math mini (self-contained statement): ~100% success, 10-45 min (T4, T7, T10, T9b).
- D. Repair (broken file + exact error lines + single-file ownership): high success, 25-45 min
  (T7-fix, T10-fix).
- E. Long-grind (big target in API-heavy area: integrals/rpow/Fubini/pi-Fubini): token burn,
  error cascades (T5' 5h/113M; C's two sessions). Split into C-sized pieces or use repair-mode.

Dispatch checklist (adopted 2026-09-11):
1. Prompt contains: exact target statement; exact signatures of every input lemma (generate via
   `rg -n "^theorem" <files>` before dispatch — T12d's hip-shape surprise would have been caught);
   repo dialect dictionary reference (verification/lean_agent_protocol.md — REQUIRED read).
2. Engines before assemblies: order tasks so every agent compiles against already-BUILT oleans;
   this is what makes 4-way parallelism coordination-free.
3. Mid-flight: check file mtimes each notification round; at ~2x budget STOP the agent and
   switch to repair-mode (prompt budgets are advisory only — T5' proved agents don't self-enforce).
4. On long-runners: send a status query offering land-now / breakdown-request / degrade-to-base-case
   options (T5c pattern).
5. After landing: verify compile myself, grep forbidden constructs, build olean, commit, fold new
   API gotchas into lean_agent_protocol.md.


## FINE-GRAINED WAVES (2026-09-10 ~17:40 plan; 4 concurrent max, ~25 min budget each)

Wave A (launched 17:40):
- T1 → Hurst/RieszWalkAlgebra*.lean: open-path identification
  matrixPathCoordinateSum A k i j = rieszOpenPathSum A k i j (induction on k via rieszVertexSeq_shift).
- T4 → Hurst/HyperplaneNull*.lean: {z : Fin k → ℝ | z i = z j} null under Measure.pi volume
  (incl. Icc-restricted variants).
- T7 → Hurst/PowerSumBound*.lean: ∑_{j<n}(j+1)^{−β} ≤ n^{1−β}/(1−β)+1 (0<β<1);
  bonus: (2*S n/m n)^psi → 1 from m n / S n → 2.
- T10 → Hurst/TailExtraction*.lean: (S_k^{(J)})^{1/k} → lambda J for decreasing nonneg ℓ2 lambda,
  S_k^{(J)} = ∑'_{j≥J} lambda j^k (ties + strict-tail squeeze; J=0 and lambda J=0 cases).

Wave B: T2 closed-walk/trace identification (extends T1); T5 Schur dominator ∫∏_i f(z_i,z_{i+1}) ≤ μ^k;
T8 mesh factorization ρ=(2S/m)^ψ→1 + single-edge band difference; T11 array max-extraction (J=0).
Wave C: assemblies — T3 Predicate 1; T6 Predicate 3 (dominated convergence); T9 Predicate 2;
T12 peeling induction + uniqueness corollary.
Wave D: R4 k=2 insurance; H1 eigenvalue perturbation; H2 trace-power transfer; H3 op-norm bound;
H4 eventual nondegeneracy padding.


All nine agents were launched in parallel on 2026-09-10 ~17:19 and were stopped after
~9 minutes (API rate limit [1302], no files produced — all were still in the
read/explore phase). The working tree was clean at stop time. Relaunch them after
the quota window resets. Common discipline block for every prompt:

- Work dir: /Users/jinqishen/repo/lean_verification/hurst_function_estimation
- Lean binary: /Users/jinqishen/.elan/bin/lake (exact path)
- Check a file: /Users/jinqishen/.elan/bin/lake env lean Hurst/YourFile.lean (exit 0 = pass)
- Build ONLY your own new modules; NEVER `lake build Hurst`; no scripts/, no git
- FORBIDDEN: sorry / admit / axiom / native_decide
- Ownership: only your own new files; never edit existing files (all existing
  modules are freshly built, so importing them is safe)
- Keep every file in a compiling state (small increments); a compiling partial
  lemma beats an unfinished grand theorem

## D: PowerSumMatching*.lean — power-sum peeling matching
Given (m : ℕ → ℕ), (x : ∀ n, Fin (m n) → ℝ), lambda : ℕ → ℝ with
(hb) ∃ B, ∀ n i, 0 ≤ x n i ≤ B; (hl) Antitone lambda, 0 ≤ lambda j, Summable (lambda ·^2);
(hp) ∀ k ≥ 2, Tendsto (fun n ↦ ∑ i, x n i ^ k) atTop (𝓝 (∑' j, lambda j ^ k)),
prove the zero-padded decreasing rearrangement of x n converges coefficientwise to lambda,
packaged to feed `centeredMatrixQuadratic_tendsto_secondChaos_of_decreasing_matching`
(Hurst/SpectralMatchingInterface.lean; reuse `decreasingSpectralPerm` from Hurst/SpectralMatchingSort).
Architecture: (1) tail extraction (S_k^{(J)})^{1/k} → lambda J (ties + strict-tail squeeze);
(2) max extraction (limsup via max^k ≤ sum; liminf via k-scaling contradiction with S_2 > 0);
(3) induction on J subtracting the converged top-J entries;
(4) uniqueness: two decreasing nonneg ℓ2 seqs with equal power sums ∀k≥2 are equal.

## R1: RieszReindex*.lean — Predicate 1 HasFixedCutoffMatrixLatticeReindex
Under ordinary hypotheses (omega continuous + bounded on [−1,1], m n → ∞, m n / S n → 2,
0 < psi), ∀ k ≥ 2 R: Tendsto (weightedTruncatedRieszDiscreteCycleValue (m n) k R (S n) psi c omega
− 2^k * unitCubeTruncatedRieszLatticeSum (m n) k R psi c omega) atTop (𝓝 0).
Import Hurst.TruncatedRieszCycleBridge + Hurst.RieszCutoffWalk (read both first).
Steps: (1) vertex-tuple form matrixClosedWalkCoordinateSum A (k+1) = ∑ w, ∏ c, A (w c) (w (finCyclicSucc c))
via rieszOpenPathSum + rieszVertexSeq_shift + trace identification tr(∏ F_t);
(2) boundary faces ≤ k(m+1)^{k−1}(B|c|(R+1)^ψ)^k/m^k → 0; (3) scalar (m/(2S))^k → 1.
Elaboration lessons from prior session: @-explicit Fin.cons/Fin.snoc (see rieszVertexSeq),
induction lemmas stated ∀ k f i j with `induction k generalizing f i j`, avoid rw under stuck
levelProd applications (use rfl-proved simp lemmas).

## R2: RieszContinuum*.lean — Predicate 3 HasContinuumRieszCutoffRemoval
Under 0 < psi < 1, c ≠ 0, omega bounded measurable: ∀ k ≥ 2,
Tendsto (fun R => weightedTruncatedRieszCycleIntegral k R psi c omega) atTop
(𝓝 (weightedRieszCycleIntegral k psi c omega)). Pure measure theory off the built
Hurst.TruncatedRieszCycleBridge. Steps: (1) a.e. pointwise convergence off diagonal
hyperplanes {z i = z (succ i)} (null under Measure.pi); (2) R-uniform integrable dominator
∏_i (Icc(−1,1) indicator)·B|c|·|z i − z (succ i)|^{−psi} via Schur-iteration/chain bound
∫ ∏_i f(z_i, z_{i+1}) ≤ (∫_{−2}^{2}|t|^{−psi} dt)^k; (3) tendsto_integral_of_dominated_convergence.
Isolate Measure.pi vs Measure.prod conversions + Fin.prod_univ_succ splitting as small named lemmas first.

## R3: RieszBand*.lean — Predicate 2 HasUniformDiscreteRieszCutoffRemoval
Under 0 < psi, 2*psi < 1, omega bounded, m n → ∞, m n / S n → 2: ∀ k ≥ 2 eps > 0,
∀ᶠ R in atTop, ∀ᶠ n in atTop, |weightedRieszDiscreteCycleValue − weightedTruncatedRieszDiscreteCycleValue| < eps.
Import Hurst.TruncatedRieszCycleBridge + Hurst.DiscreteRieszCycleBridge (signed band bounds,
two-cycle vanishing). Steps: (1) factorization c·S^ψ·d^{−ψ} = c·ρ·(m/2d)^ψ, ρ = (2S/m)^ψ → 1;
(2) walk-product pairing bound via even-position pairing, band edge ≤ (R+1)^ψ·β_R with
β_R ≍ (R+1)^{−(1−ψ)} + (R+1)^{2ψ}/m (trace representation tr(∏ F_t) + Matrix.trace_mul_comm rotation);
(3) FIRST land the power-sum bound ∑_{j<n}(j+1)^{−β} ≤ n^{1−β}/(1−β)+1 (AM-GM:
Real.geom_mean_le_arith_mean2_weighted); (4) diagonal term (R+1)^{2ψ}/m → 0; assembly (m/S)^k → 2^k.

## R4: SecondCycleQuadrature*.lean — k=2 trace-square (F2 insurance)
Target: Tendsto of the mesh double sum of squared capped Riesz kernel entries to
weightedRieszCycleIntegral 2 psi c omega (0 < psi < 1/2). Route: symmetry + two-cycle band
vanishing (DiscreteRieszCycleBridge); near-diagonal band ≤ C(R+1)^{−(1−2psi)} via 1D power-sum
bound; far band Riemann convergence (adapt unitCubeTruncatedRieszLatticeSum_tendsto);
cap removal by dominated convergence. Match repo's exact weightedRieszCycleIntegral /
weightedRieszDiscreteCycleValue definitions at k=2. Also note
Hurst/SpectralMatchingInterface.weightedFeatureQuadraticMatrix_sum_eigenvalues_sq reduces
matrix trace-square to the weighted correlation energy.

## H1: EigenvaluePerturbation*.lean — Hoffman–Wielandt / Weyl (insurance route)
Primary: ∑_i (λ_i↓(A) − λ_i↓(B))² ≤ ‖A−B‖_F² for Hermitian A B (sorted explicitly).
Fallbacks in order: (1) Weyl |λ_i↓(A) − λ_i↓(B)| ≤ ‖A−B‖_op; (2) dimension-weighted form.
Search mathlib first (Weyl / min-max / Rayleigh quotient / Matrix.IsHermitian API).

## H2: TracePowerTransfer*.lean — trace-power perturbation (needed for wiring)
|(A^k).trace − (B^k).trace| ≤ k · C^{k−1} · ‖A−B‖_F for Hermitian A B, C = max op-norms,
via telescoping A^k − B^k = ∑_t A^t (A−B) B^{k−1−t} and trace Cauchy–Schwarz
(|tr(XY)| ≤ ‖X‖_F ‖Y‖_F or the sharper ‖Y‖_op form; dimension-free preferred).
Corollary: fixed k, ‖A n − B n‖_F → 0 + uniform op-norm bound ⇒ trace powers converge.
Check built Hurst.MatrixFrobeniusTrace first.

## H3: ActualWeightedOperatorNorm*.lean — uniform op-norm bound for actual matrices
Pin the exact matrix (weightedFeatureQuadraticMatrix in Hurst/FeatureQuadraticSpectral +
Hurst/SpectralMatchingInterface; actual data in Hurst/ActualFirstLongWeightedKernel,
Hurst/FirstLongDiagonalBand, Hurst/FirstLongMeshHilbertSchmidt). Prove ∃ C, ∀ᶠ n, ‖A n‖_op ≤ C
via operator norm ≤ max row ℓ1, |corr| ≤ 1 (or kernel bound), weight-energy lemmas
(localPolynomialWeights_energy). Isolate any missing ingredient as a precisely stated def.

## H4: EventualNondegenerate*.lean — row padding for the consumption theorem
`gaussianLogQuadraticStatistic_tendsto_secondChaos_of_decreasing_matching` assumes global
nondegeneracy; actual model gives it only eventually. Prove a padding theorem: replace finitely
many exceptional rows by fixed unit rows with zero weight (statistic invariant under zero
weights — verify from definitions), globally nondegenerate, same limit; corollary: consumption
theorem holds under eventual nondegeneracy. Patterns: Hurst/ExactPaddedRow.lean,
Hurst/DenseRowOverride.lean, Hurst/DistributionVaryingLawTransfer.lean (all built).
