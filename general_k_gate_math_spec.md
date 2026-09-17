# General-k gate: complete mathematical specification (2026-09-17)

Purpose: the **full mathematical proofs** of the remaining pieces of the general-k
spectral bridge (`hGen` / the operator-side gate), to be formalized in Lean by the
parallel agents. This file is the shared contract; the Lean statement interfaces are
frozen below. Everything else referenced is ALREADY LANDED (compiled, axiom-clean).

## 0. Setup and landed facts (do not re-prove)

* Unit interval `I := Set.Icc 0 1` (project's `HS.I`), `vol` = Lebesgue on `ℝ`
  (unit-interval restriction), `vol2` = the product encoding on `ℝ × ℝ`.
* **Riesz kernel** (`Hurst.HSOperatorLayer2.rieszKernel`, landed):
  `rieszKernel psi c omega p = (I : Set ℝ).indicator omega p.1 * c * |p.1 - p.2| ^ (-psi)`.
* **Capstone data hypotheses** (`Hurst.CapstoneV3`, verbatim shapes): `omega` is
  measurable and `|omega x| ≤ MR` for all x (`hbdd`); the indicator of `omega` is
  CONSTANT on `I` (`hconst`: `∀ x y, I.indicator omega x = I.indicator omega y`);
  `hg : Integrable (fun q => |q.1 - q.2| ^ (-2*psi)) vol2` where the capstone runs at
  `psi := 2 - 2 * f t`, `c := f t * (2 * f t - 1)`, `omega := equivalentKernel r`.
  *Feasibility*: `hg` forces `2 * psi < 1`; also `0 < psi < 1` in the capstone's window
  (`psi = 2 - 2 * f t`, `1/2 < f t < 1`).  Both agents may take `hpsi2 : 2 * psi < 1`
  and `hpsi1 : psi < 1` as hypotheses of their theorems (they are data hypotheses, not
  to be derived).
* **Kernel-side composition** (landed): `compKernel K L` with operator action
  `TOp (compKernel A B) v = TOp A (TOp B v)`; tower `compPowR n K`, `compPowL n K`
  (`Hurst.GeneralKPeel` / `Hurst.GeneralKPeelInduction`); **peel induction**
  `cycleIntegral (n+2) K = cycle2 (compPowL n K) K`
  (`Hurst.GeneralKPeelInduction.cycleIntegral_comp`).
* **cycle2** (`Hurst.HSOperatorFoundation.cycle2`): `cycle2 K L = ∫ p : ℝ × ℝ, K p * L p.swap ∂vol2`.
* **tr-side HasSum** (landed, `Hurst.GeneralKHasSumAssembled`):
  `hasSum_diag_inner_pow`: for the diagonal enumeration (`IsDiagEnum` + multiplicity
  clause `hmult`), for all `k ≥ 2`,
  `HasSum (fun j => ⟪(TOpEnd' K hK)^k (vec j), vec j⟫) (∑' j, val j ^ k)`, and
  `diag_inner_eq_pow`: `⟪(TOpEnd' K hK)^k (vec j), vec j⟫ = val j ^ k` when `vec j ≠ 0`
  is an eigenvector with eigenvalue `val j` (kernel vectors carry `val j = 0`).
* **Trace-pair peel step** (landed, `Hurst.TensorParsevalTracePair`):
  `tracePair_comp_tsum (hK : HSKernel K) (hL : HSKernel L) (e : HilbertBasis ℕ ℝ L2) :
     (∑' i, ⟪TOp K hK (TOp L hL (e i)), e i⟫) = cycle2 L K`,
  plus `tracePair_comp_summable` (absolute convergence) and the CS bound
  `abs_tracePair_comp_le : |∑' i, …| ≤ hsNorm L * hsNorm K`.
* **Assembled HasSum** (landed, `Hurst.GeneralKHasSumAssembled.hasSum_general_k_assembled`):
  for every `k ≥ 2`, given the diag-enum structure, `hP` (chain integrability), and
  the gate `∑' j, val j ^ k = cycle2 (compPowR (k-2) K) K`, it yields
  `HasSum (fun j => val j ^ k) (cycleIntegral k K)`.
* **Chain integrability** (landed, `Hurst.GeneralKIntegrabilityClosed`):
  `chainProd_integrable_of_sectionBounds {k} (hk : 2 ≤ k) (W : Fin k → ℝ × ℝ → ℝ)
   (hWm) (E D) (hE1 hE2 : uniform section-L² bounds, ENNReal.ofReal form)
   (hD1 : uniform section-L¹ bound) : Integrable (chainProd k W) (vol^k)`.
* **k=2 anchors** (landed): `cycleIntegral_two` (`cycleIntegral 2 K = cycle2 K K`),
  `cycle2_rieszKernel_eq_weighted`, `RieszK2Anchor.hasSum_two_riesz`.
* **Enumeration**: the constructed `(val, vec) := HS.rieszSpectrumVal …` comes with
  `IsDiagEnum` + the multiplicity clause (landed constructor in
  `Hurst.FrozenSpectralCount`; CapstoneV3Closed consumes exactly these — copy its
  instantiation pattern).

## 1. Lemma 1 — the singular section integral (`fract_section_bound`)

**Claim.** For every real `s` with `0 ≤ s < 1` and every `y ∈ ℝ`:
`∫ a : ℝ, (I : Set ℝ).indicator (fun a => |a - y| ^ (-s)) a ∂vol ≤ 2 + 2/(1 - s)`
(in fact `≤ 2/(1-s)`; the additive slack is deliberate, keep it).

**Proof.** The integrand vanishes off `I = [0,1]`, so the integral is over `[0,1]`.

*Case `y ∈ [0,1]`.* Split at `y`. On `[0,y]` substitute `u = y - a` (so `u : y → 0`,
`da = -du`): `∫_0^y (y-a)^{-s} da = ∫_0^y u^{-s} du = y^{1-s}/(1-s) ≤ 1/(1-s)` because
`0 ≤ y ≤ 1` and `1 - s > 0`. On `[y,1]` substitute `u = a - y`:
`∫_y^1 (a-y)^{-s} da = (1-y)^{1-s}/(1-s) ≤ 1/(1-s)`. Total `≤ 2/(1-s)`.
(Lean anchor: `intervalIntegral.integral_rpow` computes `∫ u^{-s} du` on nonneg
intervals; the substitution is `intervalIntegral.integral_comp_neg` /
`integral_subtype... `— or work with `Set.integralIcc…`/`∫ a in uIcc` forms directly.)

*Case `y > 1`.* Substitute `u = y - a`: the integral equals
`∫_{y-1}^{y} u^{-s} du`. An interval of length 1 at height `u ≥ m` contributes at most
`(m+1)^{1-s} − m^{1-s} ≤ 1/(1-s)`… concretely: `∫_{m}^{m+1} u^{-s} du
= ((m+1)^{1-s} − m^{1-s})/(1-s) ≤ 1/(1-s)` for all `m ≥ 0`, because by the MVT
`(m+1)^{1-s} − m^{1-s} = (1−s)ξ^{−s} ≤ (1−s)` (if `m ≥ 1`, `ξ ≥ 1`; if `m = 0` the
difference is `1`). Hence our integral `≤ 1/(1-s) ≤ 2/(1-s)`.

*Case `y < 0`.* Mirror of the previous case (`a ↦ -a`, `y ↦ -y`). ∎

## 2. Lemma 2 — uniform section `L²` bounds of the Riesz kernel

**Claim 2a (`rieszKernel_section_sq`).** Under `Measurable omega`, `∀ x, |omega x| ≤ MR`,
`hconst` (ω constant on I, value `w`), and `2 * psi < 1`, for EVERY `y ∈ ℝ`:
`∫ a : ℝ, |rieszKernel psi c omega (a, y)| ^ 2 ∂vol ≤ c ^ 2 * MR ^ 2 * (2 + 2/(1 - 2*psi))`.

**Proof.** `|rieszKernel psi c omega (a,y)|² = (I.indicator omega a)² · c² · |a-y|^{-2ψ}`
(the indicator is 0/1-valued, so its square is itself; everything is nonneg).
Integrate over `a`: off `I` the indicator vanishes; on `I` the indicator equals `w` and
`|w| ≤ MR` by `hconst`+`hbdd`. So the integral is `≤ c²·MR²·∫_0^1 |a-y|^{-2ψ} da ≤
c²·MR²·(2 + 2/(1-2ψ))` by Lemma 1 at `s := 2ψ < 1`. ∎

**Claim 2b (`rieszKernel_section_sq_symm`).** Same bound for the transposed section:
`∫ a : ℝ, |rieszKernel psi c omega (y, a)| ^ 2 ∂vol ≤ c ^ 2 * MR ^ 2 * (2 + 2/(1 - 2*psi))`.

**Proof.** Here the indicator `I.indicator omega y` is a CONSTANT with respect to `a`
(no `hconst` needed): the integral is `(I.indicator omega y)²·c²·∫_a |y-a|^{-2ψ} da ≤
MR²·c²·(2+2/(1-2ψ))` by Lemma 1 (symmetry `|y-a| = |a-y|`). ∎

**Claim 2c (`rieszKernel_section_l1`).** Under the same hypotheses with `psi < 1`
(instead of `2*psi < 1`), for every `y`:
`∫ a : ℝ, |rieszKernel psi c omega (a, y)| ∂vol ≤ |c| * MR * (2 + 2/(1 - psi))`, and
likewise for the transposed section `(y, a)`.

**Proof.** Identical: factor out the `≤ MR` indicator and apply Lemma 1 at `s := psi`.
∎

*(Note for the consumer: `chainProd_integrable_of_sectionBounds` wants these bounds in
`ENNReal.ofReal` form, `∫⁻ a, ENNReal.ofReal |W i (a,y)| ^ 2 ≤ ENNReal.ofReal E`; the
transport from the `∫`-form is `ENNReal.ofReal_le_ofReal` + measurability, since the
integrand is nonneg. The cycle factors are all the SAME kernel `rieszKernel psi c
omega`, so one pair of bounds serves all `i : Fin k`.)*

## 3. Theorem — the operator-side gate for all `k ≥ 2`

Setting: `K := rieszKernel psi c omega`, `hK : HSKernel K` (landed:
`hsKernel_rieszKernel`), `T := TOpEnd' K hK`. Data: the constructed enumeration
`(val, vec)` with `IsDiagEnum T val vec` + `hmult` (landed), the complete ON
eigenfamily `(v, κ)` with `hsNorm K² = ∑' i, κ i²` (`EigenFamilySplice`), and the
section bounds of §2 (giving `hP` for every `k ≥ 2` via
`chainProd_integrable_of_sectionBounds` applied to the constant family
`W i := K` — with `E, D` from Claims 2a/2b/2c).

**Claim (gate).** For every `k ≥ 2`:
`(∑' j : ℕ, val j ^ k) = cycle2 (compPowR (k-2) K) K`.

**Proof (induction on `k`, in the form: peel one `TOp K` factor at a time).**

Write `S_n := TOp (compPowR n K)` for the operator with kernel `compPowR n K` (so
`S_0 = T` — `compPowR 0 K = K` by rfl — and the landed eigen-action gives
`S_n (v i) = (κ i)^(n+1) • v i`, i.e. `S_n` has the same eigenfamily with eigenvalues
`κ i^(n+1)`).

*Step A (tr side).* By `diag_inner_eq_pow` + `hasSum_diag_inner_pow` (landed):
`HasSum (fun j => ⟪T^k (vec j), vec j⟫) (∑' j, val j ^ k)`.

*Step B (peel the last factor).* Fix a Hilbert basis `e` of `L2` extending the
eigenfamily in the sense that every basis vector is either some `v i` (eigen part) or
lies in `ker T` (kernel part) — such a basis exists by `EigenFamilySplice`'s
completeness (extend the ON family by an ONB of the orthogonal complement of its span,
which is exactly `ker T` for compact self-adjoint `T`; the splice file's orthocomplement
decomposition provides this). Then:
`∑'_i ⟪T (S_{k-2} (e i)), e i⟫ = cycle2 (compPowR (k-2) K) K` by
`tracePair_comp_tsum` with `K := K`, `L := compPowR (k-2) K`
(note `TOp L hL (e i) = S_{k-2} (e i)` by the landed compKernel/TOp action; kernel
vectors contribute `0` since `T (S_{k-2} x) = T^k x = 0` for `x ∈ ker T` — wait, more
precisely `T^k x = 0` needs `x ∈ ker T^k ⊇ ker T`, and `T^k x = T(T^{k-1} x)`: for
`x ∈ ker T`, `T x = 0` so `T^k x = 0`. ✔).

*Step C (enumeration ↔ basis bridge).* The two series are sums of the same pairing
`x ↦ ⟪T^k x, x⟫` over two listings of the same spectral data:
- over the basis `e`: terms for kernel-part vectors vanish (`T^k x = 0` as above);
- terms for eigen-part vectors `= ⟪T^k (v i), v i⟫ = κ i^k` (eigen-action, landed
  `hasEigenvector_CLM_pow` / `diag_inner_eq_pow`);
- the enumeration `(val, vec)` lists the SAME eigenpairs, each nonzero eigenvalue μ
  exactly `finrank (eigenspace μ)` times (that is the landed multiplicity clause
  `hmult`; kernel vectors are listed with `val j = 0` and contribute `0` to both).
- Hence, by absolute summability (`tracePair_comp_summable` bounds the basis series;
  the `val`-series is summable by `hSmV`-type landed facts / the CS bound), the two
  `∑'` coincide — formalize as a reindexing along the multiplicity-exact bijection
  (`HasSum`/`tsum` transport under a bijection of supports; both sides are
  nonneg? NO — pairings are REAL; use absolute summability, which makes the sum
  permutation-invariant: `Summable` + bijection ⇒ equal `tsum`s, Mathlib:
  `tsum_eq_tsum_of_bij`-style / `Summable.comp_bij` … pick the landed equivalent).
  The k=2 template of exactly this bookkeeping is
  `HS.tsum_kappaSq_eq_tsum_valSq` (CapstoneV3Closed) — generalize its fiber-grouping
  from `^2` to `^k`, or reindex (either route; whichever formalizes faster).

Combining A + B + C:
`∑' j, val j ^ k = ∑'_i ⟪T^k (e i), e i⟫ = cycle2 (compPowR (k-2) K) K`. ∎

*(Formalization note: A cleaner Lean route for Step C avoids the bijection entirely:
apply `hasSum_diag_inner_pow`'s own machinery — it was proved precisely to identify the
diag-pairing series with `∑' val^k` — and prove the gate in the form
`HasSum (fun j => ⟪T^k (vec j), vec j⟫) (cycle2 (compPowR (k-2) K) K)` by transporting
Step B's basis-sum through the kernel-part zero terms. Whichever of the two routes
compiles first; the MATH is the same.)*

## 4. Theorem — composition to `hGen` (and the full HasSum family)

**Claim.** For every `k ≥ 2`:
`HasSum (fun j => val j ^ k) (cycleIntegral k K)`, where `cycleIntegral k K` here is the
`weightedRieszCycleIntegral k psi c omega` of the capstone (bridge below). For `k ≥ 3`
this is verbatim `hGen` of `Hurst.CapstoneV3` at the constructed enumeration.

**Proof.** Apply the landed `hasSum_general_k_assembled` with: the diag-enum structure
(§0), `hP` discharged for each `k` by §2 + `chainProd_integrable_of_sectionBounds`
(constant kernel family; the `compPowR` tower keeps the bounds — landed
`compPowR_section_aux` + Claims 2a–2c give the UNIFORM `E, D` consumed by the master
theorem; `GeneralKHasSumFinal.compPowR_section_aux` is already landed for this), and
the gate of §3. The kernel-side identity `cycleIntegral k K = cycle2 (compPowR (k-2) K) K`
is the landed peel induction (`cycleIntegral_comp`) — matching the gate's `compPowR`
notation; if the peel file phrases it with `compPowL`, bridge by symmetry of `K`
(`rieszKernel_symm`, landed: `K p = K p.swap` since the ω-indicator is constant on I and
`|x-y|` is symmetric — a one-line induction over the composition tower). Finally
`cycleIntegral k (rieszKernel …) = weightedRieszCycleIntegral k psi c omega`:
landed for `k = 2` (`cycle2_rieszKernel_eq_weighted`); for general `k` both sides are
"integral of the cyclic kernel product" — check
`weightedRieszCycleIntegral_eq_kernelProd` (landed, general k) against the definition of
`HS.cycleIntegral`; if the two cyclic-product encodings differ by a measure-preserving
reindex, transport along it (the k=2 file's `measurePreserving_piFinTwo` route is the
template). Restricting to `k ≥ 3` yields `hGen` verbatim; `k = 2` recovers the (already
closed) `hTwo` — consistency only, do not re-state. ∎

## 5. Frozen Lean interfaces (contract between the two agents)

AGENT-F file `Hurst/RieszSectionBounds.lean` (namespace `HS`, imports ONLY committed
modules — no dependency on GeneralKHasSumFinal):

```lean
theorem fract_section_bound {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (y : ℝ) :
    ∫ a : ℝ, (I : Set ℝ).indicator (fun a : ℝ => |a - y| ^ (-s)) a ∂vol
      ≤ 2 + 2 / (1 - s)

theorem rieszKernel_section_sq {psi c : ℝ} {omega : ℝ → ℝ} {MR : ℝ}
    (hbdd : ∀ x : ℝ, |omega x| ≤ MR)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y)
    (hpsi : 2 * psi < 1) (y : ℝ) :
    ∫ a : ℝ, |rieszKernel psi c omega (a, y)| ^ 2 ∂vol
      ≤ c ^ 2 * MR ^ 2 * (2 + 2 / (1 - 2 * psi))

theorem rieszKernel_section_sq_symm {psi c : ℝ} {omega : ℝ → ℝ} {MR : ℝ}
    (hbdd : ∀ x : ℝ, |omega x| ≤ MR)
    (hpsi : 2 * psi < 1) (y : ℝ) :
    ∫ a : ℝ, |rieszKernel psi c omega (y, a)| ^ 2 ∂vol
      ≤ c ^ 2 * MR ^ 2 * (2 + 2 / (1 - 2 * psi))

theorem rieszKernel_section_l1 {psi c : ℝ} {omega : ℝ → ℝ} {MR : ℝ}
    (hbdd : ∀ x : ℝ, |omega x| ≤ MR)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y)
    (hpsi : psi < 1) (y : ℝ) :
    ∫ a : ℝ, |rieszKernel psi c omega (a, y)| ∂vol ≤ |c| * MR * (2 + 2 / (1 - psi))

theorem rieszKernel_section_l1_symm {psi c : ℝ} {omega : ℝ → ℝ} {MR : ℝ}
    (hbdd : ∀ x : ℝ, |omega x| ≤ MR)
    (hpsi : psi < 1) (y : ℝ) :
    ∫ a : ℝ, |rieszKernel psi c omega (y, a)| ∂vol ≤ |c| * MR * (2 + 2 / (1 - psi))
```

AGENT-D file `Hurst/GeneralKHasSumFinal.lean` consumes exactly these (plus all landed
material) to formalize §3 and §4, delivering:
(i) the gate `∑' j, val j ^ k = cycle2 (compPowR (k-2) K) K` (all `k ≥ 2`) at the
constructed enumeration; (ii) `HasSum (fun j => val j ^ k) (weightedRieszCycleIntegral
k …)` (all `k ≥ 2`); (iii) `hGen` verbatim in `Hurst.CapstoneV3`'s binder form.
