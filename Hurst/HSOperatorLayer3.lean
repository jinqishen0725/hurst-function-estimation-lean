import Hurst.HSOperatorLayer2

/-!
# HS operator layer 3: compactness prerequisites for spectral enumeration

Builds the compactness prerequisites for the spectral enumeration on the landed `HS`
layer (`Hurst.HSOperatorFoundation`, `Hurst.HSOperatorLayer2`), reusing its encoding
exactly: kernels `K : ℝ × ℝ → ℝ`, `HSKernel K = MemLp K 2 vol2`,
`hsNorm K = (∫∫ K² ∂vol2)^(1/2)`, `TOp K hK : L2 →L[ℝ] L2`.

## Main results (all landed, placeholder-free)

* Degenerate (finite-rank) kernels `K = ∑ j ∈ s, a j ⊗ b j` (`s : Finset ι`):
  * `memLp2_prod_fst_snd` — mixed-coordinate products `a ⊗ b` are `L²(vol2)`;
  * `memLp_sum_finset` — finite sums of `L²` kernels are `L²`;
  * `hsKernel_degenerate` — a degenerate kernel is a HSKernel;
  * `kpair_degenerate` — Fubini factorization of the kernel pairing:
    `kpair K f g = ∑ j ∈ s, (∫ b j · f) · (∫ a j · g)`;
  * `TOpFun_degenerate` — the operator is the explicit finite-rank map
    `f ↦ ∑ j ∈ s, (∫ b j · f) • (a j)` (by Riesz uniqueness);
  * `isCompactOperator_TOp_degenerate` — **finite-rank ⇒ compact**: the range sits in
    the span of the `a j` (finite-dimensional by `FiniteDimensional.span_of_finite`),
    whose unit ball is compact by `FiniteDimensional.proper`.
* `TOp_sub`, `TOp_norm_diff_le` — the norm bridge `‖TOp A − TOp B‖ ≤ hsNorm (A − B)`.
* `memLp_indicator_one` — bounded `I`-supported indicators are `L²(vol)` (mesh banking).
* `exists_continuous_approx` — **density (item 2)**: every HSKernel is `hsNorm`-
  approximated by bounded-continuous kernels; instantiates
  `MemLp.exists_boundedContinuous_integral_rpow_sub_le` on `vol2` (`vol2` is weakly
  regular as a finite measure on a metric space — instance-resolved automatically).
* `isCompactOperator_TOp_limit` — **compact-limit bridge**: operators within `1/(n+1)`
  in operator norm of `TOp K` that are compact force `TOp K` compact
  (`isCompactOperator_of_tendsto`).

## Gap report

* **Item (1), "continuous kernel ⇒ compact operator"**: reduced by
  `isCompactOperator_TOp_limit` + `TOp_norm_diff_le` to the mesh input: for a kernel
  continuous on `I ×ˢ I`, produce degenerate kernels `K_n = ∑_{i,j<n}
  K(x_i,x_j)·1_{I_i}⊗1_{I_j}` with `x_i = -1 + 2i/n`, `I_i = Ico (x_i) (x_{i+1})` and
  `hsNorm (K_n − K) ≤ 1/(n+1)`.  Architecture (verified, elementary, bookkeeping-heavy):
  uniform continuity on the compact square (`IsCompact.uniformContinuousOn_of_continuous`)
  with mesh width `< ε/2`; pointwise collapse of the mesh sum via
  `Finset.sum_eq_single_of_mem` from `Ico`-disjointness (coverage by `Nat.floor` of
  `(n/2)(x+1)`); the grid `⋃_{i≤n} {x_i}` is `vol`-null (`volume_singleton`), hence
  `vol2`-null, so `∫∫ (K_n − K)² ≤ (ε/2)² · 4 = ε²` by `integral_mono` against an
  indicator tower; `memLp_indicator_one` banks the `L²`-ness of the mesh indicators.
* **Item (2), Riesz-kernel compactness**: follows from item (1) + `exists_continuous_approx`
  + `TOp_norm_diff_le` + `isCompactOperator_TOp_limit` once item (1) lands.
* **Item (3), spectral corollaries**: blocked only by the above.  The mathlib v4.31
  compact-self-adjoint spectral inventory applies verbatim to `TOp K` once compactness
  lands: `ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot` and
  `ContinuousLinearMap.finite_dimensional_eigenspace`
  (`Analysis/InnerProductSpace/Spectrum.lean`), with the self-adjointness input already
  landed in layer 2 (`TOp_riesz_selfAdjoint`) and bridged by
  `ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric`.  The full enumeration corollary
  `Σ κ_j² = hsNorm²` additionally needs Schatten/Hilbert–Schmidt API and Parseval for
  compact self-adjoint operators, absent from mathlib v4.31 (layer-2 tail docstring).
  Pointwise-nonneg kernels do NOT have nonneg eigenvalues (moving-average counterexample),
  so no positivity corollary is attempted.
-/

open MeasureTheory Measure Real Set
open scoped Real

noncomputable section

namespace HS

/-! ### MemLp helpers on the square -/

/-- Mixed-coordinate products `u(x)·v(y)` of `L²(vol)` functions are `L²(vol2)`. -/
theorem memLp2_prod_fst_snd {u v : ℝ → ℝ} (hu : MemLp u 2 vol) (hv : MemLp v 2 vol) :
    MemLp (fun p : ℝ × ℝ => u p.1 * v p.2) 2 vol2 := by
  have hae : AEStronglyMeasurable (fun p : ℝ × ℝ => u p.1 * v p.2) vol2 :=
    (hu.1.comp_fst).mul (hv.1.comp_snd)
  have hprod : Integrable (fun p : ℝ × ℝ => u p.1 ^ 2 * v p.2 ^ 2) vol2 := by
    exact Integrable.op_fst_snd (op := fun a b : ℝ => a * b) (by fun_prop)
      ⟨1, fun x y => by simp [Real.norm_eq_abs, abs_mul]⟩ hu.integrable_sq hv.integrable_sq
  have h2 : Integrable (fun p : ℝ × ℝ => (u p.1 * v p.2) ^ 2) vol2 :=
    hprod.congr (Filter.Eventually.of_forall fun _p => by ring)
  rw [memLp_two_iff_integrable_sq_norm hae]
  exact h2.congr (Filter.Eventually.of_forall fun _p => by
    simp only [Real.norm_eq_abs, mul_pow, sq_abs])

/-- Finite sums of `L²(vol2)` kernels are `L²(vol2)`. -/
theorem memLp_sum_finset {ι : Type*} (s : Finset ι) (F : ι → ℝ × ℝ → ℝ)
    (hF : ∀ i ∈ s, MemLp (F i) 2 vol2) :
    MemLp (fun p => ∑ i ∈ s, F i p) 2 vol2 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine memLp_two_of_aemeasurable aestronglyMeasurable_const
        ((integrable_congr (Filter.Eventually.of_forall fun _p => by simp)).mpr
          (integrable_const 0))
  | insert i s hi ih =>
      have hpt : (fun p => ∑ j ∈ insert i s, F j p) = fun p => F i p + ∑ j ∈ s, F j p := by
        funext p
        rw [Finset.sum_insert hi]
      rw [hpt]
      exact MemLp.add (hF i (Finset.mem_insert_self i s))
        (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))

/-- Bounded `I`-supported indicators are `L²(vol)` (mesh banking). -/
theorem memLp_indicator_one {J : Set ℝ} (hJ : MeasurableSet J) (hJsub : J ⊆ I) :
    MemLp (Set.indicator J fun _ : ℝ => (1 : ℝ)) 2 vol := by
  have hme : Measurable (Set.indicator J fun _ : ℝ => (1 : ℝ)) :=
    measurable_const.indicator hJ
  have h2' : AEStronglyMeasurable
      (fun x : ℝ => (Set.indicator J (fun _ : ℝ => (1 : ℝ)) x) ^ 2) vol := by
    have hm : AEStronglyMeasurable
        (fun x : ℝ => (Set.indicator J (fun _ : ℝ => (1 : ℝ)) x) *
          (Set.indicator J (fun _ : ℝ => (1 : ℝ)) x)) vol :=
      (hme.mul hme).aestronglyMeasurable
    exact hm.congr (Filter.Eventually.of_forall fun _x => (pow_two _).symm)
  refine memLp_two_of_aemeasurable hme.aestronglyMeasurable
    (Integrable.mono (integrable_const (1 : ℝ)) h2' ?_)
  filter_upwards with x
  by_cases hx : x ∈ J <;> simp [hx]

/-! ### Degenerate (finite-rank) kernels -/

/-- A degenerate kernel `∑ j ∈ s, a j ⊗ b j` is a Hilbert–Schmidt kernel. -/
theorem hsKernel_degenerate {ι : Type*} (s : Finset ι) (a b : ι → ℝ → ℝ)
    (ha : ∀ j, MemLp (a j) 2 vol) (hb : ∀ j, MemLp (b j) 2 vol) :
    HSKernel (fun p => ∑ j ∈ s, a j p.1 * b j p.2) :=
  memLp_sum_finset s (fun j p => a j p.1 * b j p.2)
    (fun j _ => memLp2_prod_fst_snd (ha j) (hb j))

/-- Inner product with an `L²` element is the integral of the representative product. -/
theorem L2_inner_eq (F G : L2) : inner ℝ F G = ∫ x, ⇑F x * ⇑G x ∂vol := by
  rw [L2.inner_def]
  exact integral_congr_ae (Filter.Eventually.of_forall fun _x => by
    simp only [RCLike.inner_apply, RCLike.conj_to_real]
    ring)

theorem inner_toLp {u : ℝ → ℝ} (hu : MemLp u 2 vol) (G : L2) :
    inner ℝ (MemLp.toLp u hu) G = ∫ x, u x * ⇑G x ∂vol := by
  rw [L2_inner_eq]
  exact integral_congr_ae ((MemLp.coeFn_toLp hu).mul Filter.EventuallyEq.rfl)

/-- Fubini factorization of the kernel pairing of a degenerate kernel. -/
theorem kpair_degenerate {ι : Type*} (s : Finset ι) (a b : ι → ℝ → ℝ)
    (ha : ∀ j, MemLp (a j) 2 vol) (hb : ∀ j, MemLp (b j) 2 vol) (f g : L2) :
    kpair (fun p => ∑ j ∈ s, a j p.1 * b j p.2) f g
      = ∑ j ∈ s, (∫ y, b j y * ⇑f y ∂vol) * (∫ x, a j x * ⇑g x ∂vol) := by
  have hint : ∀ j ∈ s, Integrable (fun p : ℝ × ℝ => a j p.1 * b j p.2 * ⇑f p.2 * ⇑g p.1) vol2 := by
    intro j hj
    have h1 : MemLp (fun p : ℝ × ℝ => a j p.1 * b j p.2) 2 vol2 :=
      memLp2_prod_fst_snd (ha j) (hb j)
    refine (memLp_one_iff_integrable.mp (MemLp.mul (memLp_pair f g) h1)).congr
      (Filter.Eventually.of_forall fun p => ?_)
    simp only [Pi.mul_apply]
    ring
  have hcongr : ∀ p : ℝ × ℝ,
      (fun q : ℝ × ℝ => ∑ j ∈ s, a j q.1 * b j q.2) p * ⇑f p.2 * ⇑g p.1
        = ∑ j ∈ s, a j p.1 * b j p.2 * ⇑f p.2 * ⇑g p.1 := by
    intro p
    simp only [Finset.sum_mul]
  unfold kpair
  rw [integral_congr_ae (Filter.Eventually.of_forall hcongr),
    integral_finsetSum s fun j hj => hint j hj]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show (∫ p : ℝ × ℝ, a j p.1 * b j p.2 * ⇑f p.2 * ⇑g p.1 ∂vol2)
      = ∫ p : ℝ × ℝ, (a j p.1 * ⇑g p.1) * (b j p.2 * ⇑f p.2) ∂vol2 from
    integral_congr_ae (Filter.Eventually.of_forall fun _p => by ring),
    integral_prod_mul (μ := vol) (ν := vol)
      (f := fun x : ℝ => a j x * ⇑g x) (g := fun y : ℝ => b j y * ⇑f y),
    mul_comm]

/-- The operator attached to a degenerate kernel is the explicit finite-rank map. -/
theorem TOpFun_degenerate {ι : Type*} (s : Finset ι) (a b : ι → ℝ → ℝ)
    (ha : ∀ j, MemLp (a j) 2 vol) (hb : ∀ j, MemLp (b j) 2 vol) (f : L2) :
    TOpFun (fun p => ∑ j ∈ s, a j p.1 * b j p.2) (hsKernel_degenerate s a b ha hb) f
      = ∑ j ∈ s, (∫ y, b j y * ⇑f y ∂vol) • MemLp.toLp (a j) (ha j) := by
  refine eq_of_forall_inner_eq fun g => ?_
  have hR : inner ℝ (∑ j ∈ s, (∫ y, b j y * ⇑f y ∂vol) • MemLp.toLp (a j) (ha j)) g
      = ∑ j ∈ s, (∫ y, b j y * ⇑f y ∂vol) * (∫ x, a j x * ⇑g x ∂vol) := by
    rw [sum_inner]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_left, inner_toLp]
  rw [inner_TOpFun, hR]
  exact kpair_degenerate s a b ha hb f g

/-- **Finite-rank ⇒ compact**: the operator of a degenerate kernel is a compact
operator (its range lies in the span of the `a j`, a finite-dimensional subspace). -/
theorem isCompactOperator_TOp_degenerate {ι : Type*} (s : Finset ι) (a b : ι → ℝ → ℝ)
    (ha : ∀ j, MemLp (a j) 2 vol) (hb : ∀ j, MemLp (b j) 2 vol) :
    IsCompactOperator
      (TOp (fun p => ∑ j ∈ s, a j p.1 * b j p.2) (hsKernel_degenerate s a b ha hb)) := by
  have hafd : ((fun j : ι => MemLp.toLp (a j) (ha j)) '' (↑s : Set ι)).Finite :=
    (Finset.finite_toSet s).image _
  have hfd : FiniteDimensional ℝ
      ↥(Submodule.span ℝ ((fun j : ι => MemLp.toLp (a j) (ha j)) '' (↑s : Set ι))) :=
    FiniteDimensional.span_of_finite ℝ hafd
  have hmem : ∀ f : L2, TOp (fun p => ∑ j ∈ s, a j p.1 * b j p.2)
      (hsKernel_degenerate s a b ha hb) f ∈
      Submodule.span ℝ ((fun j : ι => MemLp.toLp (a j) (ha j)) '' (↑s : Set ι)) := by
    intro f
    rw [TOp_apply, TOpFun_degenerate s a b ha hb f]
    refine Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span ⟨j, hj, rfl⟩
  haveI := FiniteDimensional.proper ℝ
    (↥(Submodule.span ℝ ((fun j : ι => MemLp.toLp (a j) (ha j)) '' (↑s : Set ι))))
  refine ⟨(Submodule.subtypeL (Submodule.span ℝ
      ((fun j : ι => MemLp.toLp (a j) (ha j)) '' (↑s : Set ι)))) '' Metric.closedBall 0 1,
    (isCompact_closedBall (0 : ↥(Submodule.span ℝ
      ((fun j : ι => MemLp.toLp (a j) (ha j)) '' (↑s : Set ι)))) 1).image
      (Submodule.subtypeL (Submodule.span ℝ
        ((fun j : ι => MemLp.toLp (a j) (ha j)) '' (↑s : Set ι)))).continuous, ?_⟩
  refine Filter.mem_of_superset
    (Metric.closedBall_mem_nhds (0 : L2) (by positivity : (0:ℝ) < 1 / (‖TOp (fun p =>
      ∑ j ∈ s, a j p.1 * b j p.2) (hsKernel_degenerate s a b ha hb)‖ + 1))) ?_
  intro x hx
  have hx' : ‖x‖ ≤ 1 / (‖TOp (fun p => ∑ j ∈ s, a j p.1 * b j p.2)
      (hsKernel_degenerate s a b ha hb)‖ + 1) := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx
  refine ⟨(⟨TOp (fun p => ∑ j ∈ s, a j p.1 * b j p.2)
    (hsKernel_degenerate s a b ha hb) x, hmem x⟩ : ↥(Submodule.span ℝ
      ((fun j : ι => MemLp.toLp (a j) (ha j)) '' (↑s : Set ι)))), ?_, rfl⟩
  have hle2 : ‖TOp (fun p => ∑ j ∈ s, a j p.1 * b j p.2)
      (hsKernel_degenerate s a b ha hb) x‖
      ≤ ‖TOp (fun p => ∑ j ∈ s, a j p.1 * b j p.2)
        (hsKernel_degenerate s a b ha hb)‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ x
  have hnorm1 : ‖TOp (fun p => ∑ j ∈ s, a j p.1 * b j p.2)
      (hsKernel_degenerate s a b ha hb) x‖ ≤ 1 := by
    calc ‖TOp (fun p => ∑ j ∈ s, a j p.1 * b j p.2) (hsKernel_degenerate s a b ha hb) x‖
        ≤ ‖TOp (fun p => ∑ j ∈ s, a j p.1 * b j p.2)
          (hsKernel_degenerate s a b ha hb)‖ * ‖x‖ := hle2
      _ ≤ ‖TOp (fun p => ∑ j ∈ s, a j p.1 * b j p.2)
          (hsKernel_degenerate s a b ha hb)‖ *
          (1 / (‖TOp (fun p => ∑ j ∈ s, a j p.1 * b j p.2)
            (hsKernel_degenerate s a b ha hb)‖ + 1)) :=
        mul_le_mul_of_nonneg_left hx' (norm_nonneg _)
      _ ≤ 1 := by field_simp; linarith
  simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm1

/-! ### The norm bridge -/

/-- Linearity: `TOp (A − B) = TOp A − TOp B`. -/
theorem TOp_sub {A B : ℝ × ℝ → ℝ} (hA : HSKernel A) (hB : HSKernel B) :
    TOp (A - B) (hA.sub hB) = TOp A hA - TOp B hB := by
  refine ContinuousLinearMap.ext fun f => eq_of_forall_inner_eq fun g => ?_
  rw [_root_.sub_apply, inner_sub_left, inner_TOp (hA.sub hB), inner_TOp hA, inner_TOp hB]
  unfold kpair
  have hcongr : ∀ p : ℝ × ℝ,
      (A - B) p * ⇑f p.2 * ⇑g p.1
        = A p * ⇑f p.2 * ⇑g p.1 - B p * ⇑f p.2 * ⇑g p.1 := by
    intro p
    simp only [Pi.sub_apply]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hcongr),
    integral_sub (integrable_kintegrand hA f g) (integrable_kintegrand hB f g)]

/-- The operator-norm difference is controlled by the kernel `hsNorm` difference. -/
theorem TOp_norm_diff_le {A B : ℝ × ℝ → ℝ} (hA : HSKernel A) (hB : HSKernel B) :
    ‖TOp A hA - TOp B hB‖ ≤ hsNorm (A - B) := by
  rw [← TOp_sub hA hB]
  exact TOp_norm_le _

/-! ### Density of continuous kernels in `hsNorm` -/

/-- **Density**: every Hilbert–Schmidt kernel is approximated in `hsNorm` by bounded-
continuous kernels. -/
theorem exists_continuous_approx {K : ℝ × ℝ → ℝ} (hK : HSKernel K) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ × ℝ → ℝ, Continuous g ∧ HSKernel g ∧ hsNorm (fun p => K p - g p) ≤ ε := by
  obtain ⟨G, hint, hGm⟩ := MemLp.exists_boundedContinuous_integral_rpow_sub_le
    (p := (2 : ℝ)) (by norm_num) (f := K) (by rw [real_two_ofReal]; exact hK)
    (show (0:ℝ) < ε ^ 2 by positivity)
  have heq : ∫ p : ℝ × ℝ, (K p - (G : ℝ × ℝ → ℝ) p) ^ 2 ∂vol2
      = ∫ p : ℝ × ℝ, ‖K p - (G : ℝ × ℝ → ℝ) p‖ ^ 2 ∂vol2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun _p => ?_)
    simp [Real.norm_eq_abs, sq_abs]
  refine ⟨(G : ℝ × ℝ → ℝ), G.continuous, ?_, ?_⟩
  · rw [real_two_ofReal] at hGm
    exact hGm
  · rw [hsNorm_def]
    have heq2 : ∫ p : ℝ × ℝ, (K p - (G : ℝ × ℝ → ℝ) p) ^ (2 : ℝ) ∂vol2
        = ∫ p : ℝ × ℝ, ‖K p - (G : ℝ × ℝ → ℝ) p‖ ^ (2 : ℝ) ∂vol2 := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs]
    have h2 : ∫ p : ℝ × ℝ, (K p - (G : ℝ × ℝ → ℝ) p) ^ 2 ∂vol2 ≤ ε ^ 2 := by
      rw [← integral_pow_two, heq2]
      exact hint
    calc Real.sqrt (∫ p : ℝ × ℝ, (K p - (G : ℝ × ℝ → ℝ) p) ^ 2 ∂vol2)
        ≤ Real.sqrt (ε ^ 2) := Real.sqrt_le_sqrt h2
      _ = ε := Real.sqrt_sq hε.le

/-! ### The compact-limit bridge -/

/-- **Compact-limit bridge**: if `TOp K` is the operator-norm limit (at rate `1/(n+1)`)
of compact operators, then `TOp K` is compact. -/
theorem isCompactOperator_TOp_limit {K : ℝ × ℝ → ℝ} (hK : HSKernel K)
    (T : ℕ → (L2 →L[ℝ] L2)) (hTc : ∀ n, IsCompactOperator (T n))
    (hTn : ∀ n, ‖T n - TOp K hK‖ ≤ (1:ℝ)/((n:ℝ)+1)) :
    IsCompactOperator (TOp K hK) := by
  have htz : Filter.Tendsto (fun n => ‖T n - TOp K hK‖) Filter.atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    refine ⟨Nat.ceil (1/ε), fun n hn => ?_⟩
    have hcast : ((Nat.ceil (1/ε) : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hge : (1:ℝ)/ε + 1 ≤ (n:ℝ) + 1 := by linarith [Nat.le_ceil (1/ε)]
    have hlt : (1:ℝ)/((n:ℝ)+1) < ε := by
      rw [div_lt_iff₀ (by positivity : (0:ℝ) < (n:ℝ) + 1)]
      have hmul : ε * ((1:ℝ)/ε + 1) ≤ ε * ((n:ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hge hε.le
      have hkey : ε * ((1:ℝ)/ε + 1) = 1 + ε := by
        field_simp
      nlinarith [hε, hmul, hkey]
    have hd : dist (‖T n - TOp K hK‖) (0:ℝ) = ‖T n - TOp K hK‖ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
    rw [hd]
    exact lt_of_le_of_lt (hTn n) hlt
  have htz2 : Filter.Tendsto (fun n => T n) Filter.atTop (nhds (TOp K hK)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact htz
  exact isCompactOperator_of_tendsto htz2 (Filter.Eventually.of_forall hTc)

end HS

end
