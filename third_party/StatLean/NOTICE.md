Selected source adapted from StatLean/Stat-Lean, revision 855b6afb69fead1bef066111732ed44df181040e.

Upstream: https://github.com/StatLean/Stat-Lean

License: Apache-2.0; the upstream LICENSE is retained here.

Hurst/GaussianKL.lean initially adapts StatLean/Minimaxity/ForMathlib/GaussianKL.lean by changing the namespace to Hurst. Local extensions and compatibility edits are identified in that file and lean_reuse.md.

Additional selected adaptations from the same revision:

- Hurst/KLDataProcessing.lean: KLDataProcessing.lean, namespace changed.
- Hurst/KLProduct.lean: the measurable-equivalence helper and two-factor product proof from KLDivergence.lean; other results omitted.
- Hurst/GaussianKLMulti.lean: GaussianKLMulti.lean, imports and namespace adapted; the scalar variance-change proof replaced by the already verified Hurst theorem; the mean-shift corollary omitted. Public lemmas use the theorem keyword for the local audit index.

Hurst/GaussianKLBound.lean and Hurst/GaussianLog.lean are local additions using these results and mathlib. No upstream source files in mathlib were modified.

Third-batch adaptations from the same revision:

- Hurst/FanoDefs.lean: StatLean/Minimaxity/Defs.lean.
- Hurst/EstimationToTesting.lean: StatLean/Minimaxity/EstimationToTesting.lean.
- Hurst/KLMixture.lean: mixture-minimization theorem and helpers from StatLean/Minimaxity/ForMathlib/KLDivergence.lean.
- Hurst/MutualInformation.lean: StatLean/Minimaxity/Fano/MutualInformation.lean.
- Hurst/FanoLowerBound.lean: StatLean/Minimaxity/Fano/FanoLowerBound.lean.

Namespaces/imports are adapted to Hurst. Public lemmas use the theorem keyword for the audit. Compatibility edits replace the old ENNReal multiplication-cancellation name and unqualified applications of zero_le. Definitions, separation conditions and the mathematical conclusions are preserved. Hurst/GaussianFano.lean and the widened bounds in GaussianKLBound.lean are local additions.
