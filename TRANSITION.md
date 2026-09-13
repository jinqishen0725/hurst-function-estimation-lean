# Hurst function estimation Lean formalization: transition document

Last updated: 2026-09-09 (America/Los_Angeles)

This document is the handoff point for continuing the formalization of the main one-dimensional results in Shen and Hsing, *Hurst function estimation*. It records what has actually been checked, what is only locally compiled, what is still conditional, and the shortest path to a fresh full audit.

## 1. Acceptance rule

The user requires every internal supporting lemma to be proved in Lean. A final theorem may retain a premise only when that premise is an exact, cited theorem from the external literature and the Lean interface states all of its hypotheses. A premise that merely restates convergence of the statistic being proved is not acceptable.

Use these status labels consistently:

| Label | Meaning |
|---|---|
| **Integrated and audited** | Imported by `Hurst.lean`, full build passed, and the generated axiom audit passed for that snapshot. |
| **Independently compiled** | The file passed `lake env lean FILE`, but it was added or changed after the last full build. |
| **Conditional reduction** | Lean proves the reduction, but one or more named internal predicates remain as hypotheses. |
| **Written proof only** | A direct mathematical proof exists in `direct_proofs/`, but the corresponding internal Lean chain is incomplete. |
| **Backlog** | Deliberately excluded from the current one-dimensional mainline. |

Do not call the current repository head fully verified. The last integrated build predates several current files and imports.

## 2. Source material and project layout

Primary local sources:

- `19-AOS1825.pdf`: published paper.
- `suppdf_1.pdf`: 44-page supplement supplied by the user.
- `source/paper.txt` and `source/supplement.txt`: extracted searchable text.
- `verification/source_manifest.json`: source hashes and provenance.

Primary external theorem sources:

- Bardet and Surgailis, Theorem 1(2): [official arXiv HTML](https://arxiv.org/html/1104.4732) and [record](https://arxiv.org/abs/1104.4732). Its exact scalar polynomial/Hilbert-space specialization is encoded by `BardetSurgailisTheoremOnePartTwoScalarPolynomialHilbert`.
- The supplement informally invokes Taqqu, Proposition 6.1; bibliographic metadata is available from [Springer](https://link.springer.com/article/10.1007/BF00532868). That citation is not yet an exact usable interface for the actual long-memory statistic.

Important files:

- `Hurst.lean`: aggregate import and full-build target.
- `Hurst/`: Lean modules.
- `direct_proofs/`: repaired ordinary mathematical proofs.
- `results/`: one file for each numbered paper result.
- `summary.md`: intended final per-result report; its headline counts are stale at this checkpoint.
- `backlog.md`: extensions intentionally postponed.
- `verification/internal_input_inventory.json`: machine-readable internal input status; it still correctly marks `INT-CLT` and `INT-LONG` in progress.
- `verification/build.log`, `verification/axioms.log`, `verification/audit_result.json`, `verification/coverage.json`: validation artifacts. Their timestamps matter.

This directory is not a Git repository. All subagents share the same filesystem, so they must own disjoint files and must not run overlapping full builds.

## 3. Verified checkpoint and current-head caveat

The most recent full build is:

```text
2026-09-09 22:43:13 verification/build.log
Build completed successfully (9041 jobs).
```

A separate completed axiom audit from 22:33, before the final 22:43 build and before the later edits, reported dependencies limited to mathlib foundations:

```text
Classical.choice
Quot.sound
propext
```

That earlier audit reported no `sorryAx` and no custom axioms. Because its timestamp differs from the build timestamp, treat it as prior evidence rather than as an audit of the exact 22:43 source snapshot. The old declaration count in `verification/coverage.json` is stale because coverage was last generated at 14:25.

After that full build, `Hurst.lean` and multiple modules were changed. Therefore:

- the 9041-job build is the last known-good aggregate-build checkpoint;
- current source contains no textual `sorry`, `admit`, or `axiom` declarations;
- current head has **not** passed a fresh full build, coverage generation, or axiom audit;
- `FiniteSpectralArrayConvergence.lean` currently fails to compile and is not imported by `Hurst.lean`;
- `ActualActiveFiniteCLT.lean` and `DistributionVaryingLawTransfer.lean` independently compile, but are not directly imported by `Hurst.lean`.

All three parallel subagents were interrupted for this transition so that no background proof work continues to spend usage or mutate files. Their last file areas were:

- `int_clt_var`: actual q1/q2 active-row CLT instantiation; produced/edited `ActualActiveFiniteCLT.lean`.
- `int_long_resume`: permutation-aware finite spectral convergence; produced/edited `DistributionVaryingLawTransfer.lean` and `FiniteSpectralArrayConvergence.lean`.
- `riesz_cycle_bridge`: fixed-cutoff Riesz reindex and cutoff removal; last edited `TruncatedRieszCycleBridge.lean`.

## 4. Current mathematical status

The main one-dimensional minimax lower-bound chain, including the fixed-range `p = 1` repair, is internally formalized. The major unresolved work is concentrated in the asymptotic distribution results, especially the long-memory second-chaos endpoint.

Approximate status for planning, not an audit metric:

| Area | Current assessment | Main remaining work |
|---|---:|---|
| One-dimensional minimax lower bound | Complete on the chosen repaired scope | Fresh integration/audit only. |
| Risk, bias, variance, scale, and inverse-transfer chains | Largely complete | Fresh integration/audit and final report refresh. |
| Short-memory finite-Hermite CLT infrastructure | About 95% | Instantiate the generic theorem for actual q1/q2 active rows and transfer to the final statistic; joined two-scale pilot CLT remains. |
| Long-memory finite Gaussian spectral probability layer | Substantially complete | Finish permutation-aware array convergence and derive spectral inputs from the actual matrices. |
| Discrete-to-continuum Riesz bridge | Partial conditional reduction | Prove fixed-cutoff reindexing and both cutoff-removal estimates. |
| High-dimensional and model extensions | Backlog | See `backlog.md`; these do not block the one-dimensional mainline. |

The mainline is **not complete**. The short-memory blocker is mostly theorem instantiation and bookkeeping. The long-memory blocker is substantive deterministic analysis: spectral matching/order and singular Riesz quadrature.

## 5. Short-memory CLT chain

The following chain has been built and checked file by file during the latest work:

1. `Hurst/DenseRowOverride.lean`
2. `Hurst/ExactPaddedRow.lean`
3. `Hurst/ExactPaddedConditions.lean`
4. `Hurst/ExactPaddedHitLaw.lean`
5. `Hurst/ExactPaddedPolynomialProfile.lean`
6. `Hurst/BardetSurgailisFixedRow.lean`
7. `Hurst/EventualUniformRows.lean`
8. `Hurst/ExactPaddedBSCLT.lean`
9. `Hurst/VariableRowBSCLT.lean`
10. `Hurst/SafeStandardizedFeatureRow.lean`

The key endpoint is:

```lean
Hurst.variableRow_gaussianLogTruncation_clt
```

It proves the internal arbitrary-row reduction:

```text
every-subsequence criterion
  -> strictly increasing row-size subsubsequence
  -> dense predecessor selector
  -> exact-hit row override
  -> exact Bardet-Surgailis application
  -> IdentDistrib transfer
```

Only the exact external Bardet-Surgailis theorem and ordinary row, tail, profile, variance, and model hypotheses remain as premises. No internal premise restates convergence of the final finite-polynomial statistic.

`Hurst.exactPadded_gaussianLogTruncation_clt` proves the exact-row applicability conditions: unit norms, centering, Hermite rank two, row bound, correlation tail, L2 profile convergence and continuity, and the variance limit. The external interface now includes the missing centered-profile requirement `forall tau, integral (phi tau) = 0`.

Newly checked files after the last integrated build:

| File | Status | Content |
|---|---|---|
| `Hurst/DistributionVaryingLawTransfer.lean` | Independently compiled, exit 0 | Transfers convergence in distribution across rowwise `IdentDistrib` when both row spaces vary. |
| `Hurst/ActualActiveFiniteCLT.lean` | Independently compiled, exit 0 after building `SafeStandardizedFeatureRow` | Defines the actual active B&S coefficient and safe active row; proves its normalized finite-Hermite variance equals the original local-statistic variance under nondegeneracy. It does **not** yet prove the actual q1/q2 CLT. |

Remaining short-memory tasks:

1. Add an actual-model theorem that instantiates `variableRow_gaussianLogTruncation_clt` using `ActiveBSApplicability`, `ActualFullTruncatedVarianceLimit`, `OptimalActiveRowDensity`, and the safe active row.
2. Prove the law/equality bridge from that active-row statistic to the actual q1 and q2 optimal-bandwidth statistic.
3. Handle the finite exceptional rows through `SafeStandardizedFeatureRow` and eventual equality rather than imposing global nondegeneracy at every small sample size.
4. Transfer the finite-Hermite CLT through the already formalized truncation and inverse-function chains to the final estimator statement.
5. Formalize the joined two-scale pilot CLT if the final unknown-scale theorem uses its joint limit.
6. Import the stable new endpoint modules in `Hurst.lean` only after the endpoint theorem exists and direct compilation passes.

## 6. Long-memory second-chaos chain

### 6.1 Independently compiled finite-dimensional layer

- `Hurst/FiniteGaussianSpectral.lean`: exact diagonalization law for a finite Hermitian Gaussian quadratic form, second moment `2 * sum lambda_i^2`, and trace/entry identities.
- `Hurst/FiniteHermitianTracePowers.lean`: `trace (A^k) = sum lambda_i^k` and cyclic coordinate expansions.
- `Hurst/MatrixFrobeniusTrace.lean`: trace-product bound and fixed-dimensional Frobenius-to-power-trace convergence.
- `Hurst/FeatureQuadraticSpectral.lean`: represents the actual feature quadratic statistic by finite eigenvalue-weighted centered squares; proves the exact signed weighted Hilbert-Schmidt energy identity.
- `Hurst/StandardGaussianPrefix.lean`: canonical Gaussian prefix is measure preserving.
- `Hurst/FiniteGaussianSpectralTruncation.lean`: exact finite spectral prefix law and exact L2 tail.
- `Hurst/FiniteIidGaussianVector.lean`: iid Gaussian prefixes have the canonical finite Gaussian law.
- `Hurst/FiniteGaussianSpectralConvergence.lean`: finite spectral convergence infrastructure.
- `Hurst/FeatureQuadraticSpectralConvergence.lean`: actual feature-Gaussian quadratic convergence from padded eigenvalue convergence and a uniform spectral-tail bound. Its endpoint is `gaussianLogQuadraticStatistic_tendsto_secondChaos_of_spectral_data`.
- `Hurst/SpectralPermutation.lean`: Gaussian coordinate permutations preserve measure and centered spectral-square laws.

The permutation module is necessary because mathlib's Hermitian `eigenvalues : Fin m -> Real` enumeration is not documented as sorted. Coordinatewise eigenvalue convergence and tail bounds cannot be inferred from trace/Hilbert-Schmidt information without choosing rowwise permutations or providing an explicit ordering theorem.

### 6.2 Current compile failure

`Hurst/FiniteSpectralArrayConvergence.lean` is the active unfinished file. Its intended endpoint is:

```lean
centeredMatrixQuadratic_tendsto_secondChaos_of_permuted_spectral_data
```

The first current error is at line 96 in `centeredSpectralSquares_sub_prefix_L2`. Lean cannot rewrite `hpoint` under the squared integrand:

```text
Tactic `rewrite` failed: Did not find an occurrence of the pattern
fun x => centeredSpectralSquares lambda x - centeredSpectralPrefix lambda K x
```

Suggested repair: keep the first `MemLp` branch, which already elaborates, and replace the failing integral rewrite with an explicit equality between the squared integrand functions:

```lean
  · rwa [hpoint]
  · have hsquare :
        (fun x => (centeredSpectralSquares lambda x -
          centeredSpectralPrefix lambda K x) ^ 2) =
        (fun x => centeredSpectralSquares tail x ^ 2) := by
      funext x
      rw [congrFun hpoint x]
    rw [hsquare, centeredSpectralSquares_secondMoment]
    -- continue with the existing finite-sum calculation
```

After fixing the first error, compile again. Later lines use `tendstoInDistribution_of_identDistrib_rows_varying`, now available from the imported and independently compiled `DistributionVaryingLawTransfer` module, so the earlier “unknown constant” report may disappear.

### 6.3 Riesz-cycle bridge

`Hurst/DiscreteRieszCycleBridge.lean` independently compiles and proves:

- the weighted discrete Riesz matrix;
- symmetry of the rank-Riesz kernel;
- cyclic-path expansion of matrix powers and traces;
- the explicit two-cycle formula;
- signed near-diagonal band bounds;
- vanishing of the two-cycle band;
- transfer from a cycle-quadrature statement to trace and spectrum statements.

`Hurst/TruncatedRieszCycleBridge.lean` also independently compiles. It proves the continuous capped kernel, integrability on the cube, the regular unit-lattice Riemann-sum theorem from mathlib, the affine unit-cube/symmetric-cube integral identity, and a three-epsilon reduction.

The following are still internal obligations, expressed as named predicates rather than proved facts:

```lean
HasFixedCutoffMatrixLatticeReindex
HasUniformDiscreteRieszCutoffRemoval
HasContinuumRieszCutoffRemoval
```

`hasWeightedRieszCycleQuadrature_of_truncation` is therefore a conditional reduction, not the final internal proof. The most relevant mathlib theorem is `tendsto_tsum_div_pow_atTop_integral` in `Mathlib/Analysis/BoxIntegral/UnitPartition.lean`.

### 6.4 Actual-model link

Already compiled:

- `hurstHolder_q1_actual_weighted_kernel_hilbertSchmidt_to_riesz` in `Hurst/ActualFirstLongWeightedKernel.lean` proves actual weighted covariance-kernel convergence to the discrete Riesz kernel in Hilbert-Schmidt energy.
- The series and triangular L2 approximation layers are in `SecondChaosSeriesL2.lean`, `SecondChaosSeriesConvergence.lean`, and `SecondChaosTriangularSpectral.lean`.

Still unresolved:

1. Complete `FiniteSpectralArrayConvergence.lean`.
2. Derive a permutation and padded coefficient convergence from deterministic matrix/operator convergence. Trace-power convergence alone determines the multiset only after a separate compactness/matching argument.
3. Derive the uniform l2 spectral-tail bound from the actual weighted matrices.
4. Prove the three Riesz cutoff/reindex predicates above.
5. Connect the actual weighted kernel convergence to the spectral hypotheses of `gaussianLogQuadraticStatistic_tendsto_secondChaos_of_spectral_data`.
6. Replace the internal premise `GaussianQuadraticWeightedKernelContinuity` in `ActualFirstLongSecondChaosWeighted.lean` with the completed internal spectral/Riesz chain.
7. Repeat the joint argument for the pilot statistic only if required by the final theorem scope.

The supplement's sentence near `source/supplement.txt:2294`—roughly “follow Taqqu Proposition 6.1 and modify the matrix/weights”—is too short to discharge these obligations. The repaired ordinary proof is in `direct_proofs/14_q1_long_memory_limit.md`.

## 7. Ordered remaining work

Work in this order to minimize rework.

### P0: stabilize the current branch

1. Fix and directly compile `FiniteSpectralArrayConvergence.lean`.
2. Directly compile every file changed after 22:43 that is intended for the aggregate import.
3. Decide whether `DistributionVaryingLawTransfer`, `ActualActiveFiniteCLT`, and `FiniteSpectralArrayConvergence` are ready to import in `Hurst.lean`.
4. Do not regenerate coverage yet if any intended imported module fails.

### P1: close the short-memory actual endpoint

Implement the q1/q2 actual active-row instantiation of the generic B&S theorem. This is the shortest route to a major completed result and should be handled before the harder long-memory analysis.

### P2: close deterministic long-memory inputs

Run two disjoint efforts:

- spectral matching/permutation and l2 tail;
- fixed-cutoff Riesz reindex plus discrete and continuum cutoff removal.

Then connect both to the actual q1 quadratic statistic and remove `GaussianQuadraticWeightedKernelContinuity`.

### P3: joined pilot endpoints

Complete the two-scale joint CLT/second-chaos statements required by the unknown-scale result. Do this after the one-scale endpoints are stable so the joint proof reuses their lemmas.

### P4: integrate and audit

1. Add only compiled modules to `Hurst.lean`.
2. Regenerate coverage and the axiom audit input.
3. Run the full build once.
4. Run the axiom and internal-input checks.
5. Update `verification/internal_input_inventory.json`, `summary.md`, the per-result files, and any status JSON from the fresh evidence.

### P5: backlog only after the mainline passes

Keep the items in `backlog.md` postponed: dimensions 2 and 3, high-dimensional minimax, general `q >= 3`, full vector conclusions, extra boundary limits, irregular grids, nonconstant scale, numerical reproduction, and `s = infinity` extensions.

## 8. Validation runbook

Use the project-pinned executable:

```bash
/Users/jinqishen/.elan/bin/lake
```

### Inspect before editing

```bash
cd /Users/jinqishen/repo/lean_verification/hurst_function_estimation
rg -n "theorem_name|definition_name" Hurst
rg -n "sorry|admit|^\\s*axiom" Hurst Hurst.lean
rg -n "import Hurst\\." Hurst.lean
```

### Check one file

```bash
/Users/jinqishen/.elan/bin/lake env lean Hurst/FiniteSpectralArrayConvergence.lean
```

If Lean reports a missing `.olean`, build that imported module first, then retry:

```bash
/Users/jinqishen/.elan/bin/lake build Hurst.SafeStandardizedFeatureRow
/Users/jinqishen/.elan/bin/lake env lean Hurst/ActualActiveFiniteCLT.lean
```

A missing `.olean` is an environment/build-order problem. It is not evidence that the theorem source is wrong.

### Final validation sequence

Run sequentially, not in parallel:

```bash
python3 scripts/check_coverage.py
/Users/jinqishen/.elan/bin/lake build Hurst > verification/build.log
/Users/jinqishen/.elan/bin/lake env lean verification/AxiomAudit.lean > verification/axioms.log
python3 scripts/verify_axioms.py
python3 scripts/check_internal_inputs.py
```

Expected acceptance:

- every command exits 0;
- `verification/build.log` ends with `Build completed successfully`;
- axiom verification reports `sorryAx=false` and `custom_axioms=false`;
- internal inputs required by the declared completed scope are discharged;
- `coverage.json` was generated after the final source changes;
- `summary.md` reports the same status as the machine-readable artifacts.

Do not run `scripts/check_coverage.py` while unfinished files are imported, because it regenerates `verification/AxiomAudit.lean` and `verification/coverage.json` and can make the evidence harder to interpret.

## 9. Project-relevant tool usage illustrations

These examples are operational recipes for the next coordinating agent. They are not proof steps.

### 9.1 File search and inspection

Use `functions.exec` with `rg` for declarations and dependencies:

```text
exec_command(
  workdir = "/Users/jinqishen/repo/lean_verification/hurst_function_estimation",
  cmd = "rg -n 'centeredSpectralSquares_sub_prefix_L2|HasUniformDiscreteRieszCutoffRemoval' Hurst"
)
```

Batch independent read-only inspections with `Promise.allSettled`; keep edits, builds, and adaptive retries sequential.

### 9.2 Editing

Use `apply_patch` for changes:

```diff
*** Begin Patch
*** Update File: Hurst/FiniteSpectralArrayConvergence.lean
@@
-  rw [hpoint, centeredSpectralSquares_secondMoment]
+  ...replacement proof...
*** End Patch
```

Re-read the edited theorem and immediately run its single-file Lean check.

### 9.3 Parallel subagent partition

The user explicitly authorized subagents. Assign disjoint files and concrete acceptance criteria. A good three-way split is:

```text
spawn_agent task_name="short_actual_clt"
  Own only ActualActiveFiniteCLT.lean and a new actual endpoint file.
  Instantiate variableRow_gaussianLogTruncation_clt for q1/q2.
  Return theorem names, exact remaining hypotheses, and direct compile output.

spawn_agent task_name="spectral_matching"
  Own only FiniteSpectralArrayConvergence.lean and any new spectral-matching file.
  Fix the current L2 rewrite, prove the permutation-aware finite-array theorem,
  and identify the exact deterministic matching lemma still needed.

spawn_agent task_name="riesz_cutoff"
  Own only TruncatedRieszCycleBridge.lean and a new cutoff-estimate file.
  Prove fixed-cutoff reindexing and as much cutoff removal as possible.
  Do not replace an internal estimate by an assumption.
```

Coordination tools:

```text
list_agents()                         # inspect all active tasks
send_message(target, message)         # add a constraint without starting a new turn
followup_task(target, message)         # resume an idle task with concrete follow-up work
wait_agent(timeout_ms = 180000)        # wait for a useful status/final update
interrupt_agent(target)                # stop work when usage is tight or files conflict
```

The coordinator should compile and inspect every subagent's files independently. A subagent's verbal “done” is not validation.

Avoid assigning two agents to the same file. Avoid concurrent `lake build Hurst` runs; they waste time and can obscure which source snapshot a log represents.

### 9.4 External source verification

Use web search/open only for exact primary-source theorem statements and metadata. For technical claims, prefer the paper itself or official publisher/arXiv pages. Record:

- theorem number and source URL;
- every assumption used by the Lean interface;
- whether the theorem exactly implies the encoded premise;
- any specialization argument that remains internal.

Never turn an informal citation such as “follow Proposition 6.1” into an accepted external premise without locating and matching the exact statement.

### 9.5 Progress reporting

Report four separate facts:

1. mathematical proof status;
2. single-file Lean compile status;
3. aggregate import/build status;
4. axiom/coverage audit status.

This prevents a locally valid lemma or a conditional reduction from being mistaken for a complete paper theorem.

## 10. Known pitfalls

- **Stale `.olean` files:** build a missing dependency before diagnosing source code.
- **Universe mismatch:** the B&S specialization currently uses `.{0}` and `{E : Type}` intentionally; changing it to unconstrained `Type*` previously caused a mismatch.
- **Eigenvalue order:** do not assume mathlib's Hermitian eigenvalues are sorted. Carry an explicit permutation or prove an ordering construction.
- **Signed weights:** long-memory matrices and cycle sums use signed local-polynomial weights; absolute-value bounds must preserve the exact normalization and sign-sensitive identities.
- **Singular diagonal:** continuum Riesz kernels require truncation and diagonal-neighborhood control. Fixed-cutoff Riemann sums alone do not prove the singular limit.
- **Conditional predicates:** a theorem consuming `HasFixedCutoffMatrixLatticeReindex` or `GaussianQuadraticWeightedKernelContinuity` has not discharged that internal input.
- **Old status prose:** `summary.md` contains historical counts and statements such as “2/27” that no longer summarize the current internal progress. Update only from a fresh final audit.
- **No Git safety net:** make small patches and keep agent file ownership disjoint.

## 11. Completion definition

The current one-dimensional mainline is complete only when all of the following hold:

1. q1 and q2 actual short-memory estimator limits are derived from the exact B&S interface with every internal applicability hypothesis proved in Lean;
2. the q1 long-memory actual quadratic statistic converges to the stated second-chaos law without `GaussianQuadraticWeightedKernelContinuity` or an equivalent internal convergence premise;
3. every joint pilot limit used by the unknown-scale main theorem is proved;
4. all intended modules are imported by `Hurst.lean`;
5. the full build, generated coverage, axiom audit, and internal-input audit all pass on the same source snapshot;
6. `summary.md` gives a per-major-result verdict, required correction, mathematical scope, Lean status, and remaining external dependency consistent with those artifacts.

Until then, the accurate short description is: **the one-dimensional minimax and deterministic/risk backbone is largely formalized; the generic short-memory CLT is internally reduced to the exact external theorem; the actual short-memory instantiation and the long-memory spectral/Riesz closure remain.**


---

## 12. Status update: 2026-09-13 (long-memory second-chaos chain closed to one rate hypothesis)

This section supersedes the older status prose above wherever they disagree.

### What is now theorems (all imported, full build 9114 jobs, axiom audit green, 2169 proof declarations)

- **All three Riesz cutoff predicates are theorems** under ordinary hypotheses:
  `fixedCutoffMatrixLatticeReindex` (Hurst/FixedCutoffReindexAssembly.lean),
  `hasUniformDiscreteRieszCutoffRemoval` (Hurst/BandRemovalComplete.lean),
  `hasContinuumRieszCutoffRemoval` (Hurst/ContinuumCutoffNuGlue.lean via the peeling
  integrability in Hurst/DominatorIntegrability.lean and the uniform shift bounds in
  Hurst/TwoFactorShiftBound.lean).
- **`hasWeightedRieszCycleQuadrature_instance`** (Hurst/RieszQuadratureInstance.lean):
  the three-predicate confluence, ordinary hypotheses only.
- **The eigenvalue matching chain is complete**: tail extraction (Hurst/TailExtraction.lean),
  array max extraction (Hurst/MaxExtraction*.lean), residual subtraction
  (Hurst/PeelingSubtraction.lean), induction assembly (Hurst/PeelingInduction.lean —
  `paddedRearranged_tendsto`), signed variant (Hurst/EvenPeeling.lean —
  `paddedAbsRearranged_tendsto`, even power sums only, for signed spectra).
- **The actual q1 long-memory chain is assembled** through
  `actualQ1EigenvaluePowerSums_tendsto_ordinary` (Hurst/KernelEnergyRateDischarge.lean):
  ordinary hypotheses + the kernel-energy rate `hPert` + the cutoff satisfiability
  (PROVED: `ordinary_cutoff_satisfiable`, R = floor(S^gamma)+1 with 0 < gamma < 4h0−3).
- **The signed consumption interface is complete**:
  `gaussianLogQuadraticStatistic_tendsto_secondChaos_of_signedMatching`
  (Hurst/SignedInterfaceFinal.lean) — Slutsky/L2 transfer from |lambda|-matching plus
  negative-mass smallness; replaces the hNN-restricted consumption theorem.
- Short-memory P1 endpoints (Hurst/ActualActiveBSCLT.lean) and the unknown-scale
  marginal bridge (Hurst/JoinedPilotActualMarginal.lean) are unconditional (only the
  exact external Bardet–Surgailis theorem + ordinary model assumptions).

### The single remaining analysis item

- **`hPert`**: the dimension-weighted kernel-energy rate
  `card * realScaleMeshEnergy S (K_A − K_G) → 0`.  The unweighted convergence is a
  theorem; the rate is the last open item.  The investigation (Hurst/KernelEnergyRate.lean)
  proved the energy→0 chain fully quantitative and reduced the rate to three strengthened
  inputs; the band-parameter balance was then shown UNSATISFIABLE in one packaging
  (`strengthened_cutoff_unsatisfiable`) and the honest packaging now carries `hPert`
  directly (Hurst/KernelEnergyRateDischarge.lean).  Discharging it requires a quantitative
  upgrade of the kernel-approximation error (a rate on the mesh-Hilbert-Schmidt
  convergence; the weight-error upgrade is `localPolynomialWeights_active_rank_uniform_tendsto`
  made quantitative — its proof is explicit-algebra and believed mechanical).
- `hNegMass` of the signed interface reduces exactly to `hPert`'s rate
  (`||A_n − B_n|| = O(m^{-1/2−eta})`), documented in Hurst/SignedInterfaceFinal.lean.

### Negative findings recorded (documented, kept)

- `strengthened_cutoff_unsatisfiable`: the strengthened cutoff (extra S factor) is
  refuted — the naive hres bundle was vacuous and was replaced by honest hypotheses.
- Unconditional r=1 weight nonnegativity is FALSE (one-sided windows); weights are
  signed in general, hence the signed route (EvenPeeling + EigenvaluePerturbation +
  SignedInterfaceFinal) is the required path; the r=1 pointwise criterion
  (Hurst/LocalLinearWeightsNonneg.lean) remains available as a simplification.

### Restart guide

Everything is imported and audited.  Remaining work: (1) discharge `hPert`
(quantitative kernel-approximation rate — see above), then (2) the signed consumption
theorem chain gives the q1 long-memory endpoint unconditionally, (3) refresh
summary.md per-result verdicts.  Protocol and playbook:
verification/lean_agent_protocol.md, verification/parallel_wave_prompts.md.
