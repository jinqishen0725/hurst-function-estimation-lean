import Hurst.ReverseParseval

/-!
# Tensor-ONB completeness: the section family of a complete ONB spans the kernel space

On the landed `HS` stack (`Hurst.HSOperatorFoundation`, `...Layer2/3/4`,
`Hurst.HSNormIdentity`, `Hurst.ReverseParseval`) this file discharges the hypothesis `hsec`
of `Hurst.ReverseParseval`: the **completeness of the section (tensor-ONB) family**
`p ↦ prodKernel (v p.2) (v p.1)` in the kernel space `L²(vol2)`, for any complete
orthonormal family `v` of `L²`.

## Route (Fubini-free, π-λ measure uniqueness)

Classically one shows: an `L²(vol2)` function orthogonal to every section `u ⊗ v` with
`u, v` from complete families vanishes — via Fubini on `y`-sections.  The a.e.-section
machinery for `Lp` elements is not needed; this file uses a **measure-uniqueness
argument** that is fully effective for the `Lp(vol2)` carrier:

1. The pairing `B u f := ⟪g, prodKernel u f⟫` is bilinear (`prodKernel` linearity in each
   slot, landed here) and boundedly continuous in each slot, with
   `|B u f| ≤ ‖g‖ ‖u‖ ‖f‖` (Cauchy–Schwarz on the square, through `kpair_bound` at the
   kernel `⇑g`).
2. Orthogonality to the sections extends by bilinearity over `span (range v)` and by
   continuity over its closure; completeness of `v` (`hcomp` +
   `Submodule.topologicalClosure_eq_top_iff`) gives `B u f = 0` for ALL `u, f ∈ L²`.
3. Specializing to indicator sections `1_A ⊗ 1_B`: `∫_{A×B} g dvol2 = 0` for all
   measurable `A, B ⊆ ℝ`.
4. The finite measures `μ± := vol2.withDensity (ofReal ∘ (±g))` agree on the π-system of
   measurable rectangles (`MeasurableSpace.generateFrom_prod` + `isPiSystem_prod`);
   `MeasureTheory.ext_of_generate_finite` (π-λ uniqueness) gives `μ₊ = μ₋`.  On
   `{g > 0}` (resp. `{g < 0}`) the two densities read `ofReal (g)` vs `0` (resp. `0` vs
   `ofReal (-g)`), so each of those sets is `vol2`-null and `g = 0` a.e., i.e. `g = 0` in
   `L²(vol2)`.

## Main results

* `sections_orthogonal_eq_zero` — the direct form: `∀ p, ⟪g, v p.2 ⊗ v p.1⟫ = 0 → g = 0`.
* `sections_span_orthogonal_eq_bot` — the `hsec` form: the span of the section family has
  trivial orthogonal complement in `L²(vol2)`.
* `hsNorm_sq_eq_tsum_norm_sq_of_complete` — the reverse HS-norm identity
  `hsNorm K² = ∑' j, ‖TOp K (v j)‖²`, **unconditional** for every complete orthonormal
  family (closes the Parseval gap of `Hurst.HSOperatorFoundation`/`HSNormIdentity`).
* `hsNorm_sq_eq_tsum_eigenvalue_sq_of_complete` — the eigenfamily corollary
  `hsNorm K² = ∑' j, κ j²` unconditional.
-/

open MeasureTheory Measure Real Set Submodule
open scoped Real

noncomputable section

namespace HS

variable {K : ℝ × ℝ → ℝ} {hK : HSKernel K}

/-! ### A. `prodKernel` linearity bridges -/

private theorem prodKernel_add_fst (u₁ u₂ f : L2) :
    prodKernel (u₁ + u₂) f = prodKernel u₁ f + prodKernel u₂ f := by
  apply Lp.ext
  calc ⇑(prodKernel (u₁ + u₂) f)
      =ᵐ[vol2] (fun p : ℝ × ℝ => ⇑(u₁ + u₂) p.1 * ⇑f p.2) :=
        MemLp.coeFn_toLp (memLp2_prod_fst_snd (Lp_coe_memLp (u₁ + u₂)) (Lp_coe_memLp f))
    _ =ᵐ[vol2] (fun p : ℝ × ℝ => (⇑u₁ p.1 + ⇑u₂ p.1) * ⇑f p.2) :=
        (eventual_fst (Lp.coeFn_add u₁ u₂)).mul EventuallyEq.rfl
    _ =ᵐ[vol2] (⇑(prodKernel u₁ f) + ⇑(prodKernel u₂ f)) := by
        refine ((MemLp.coeFn_toLp (memLp2_prod_fst_snd (Lp_coe_memLp u₁) (Lp_coe_memLp f))).add
          (MemLp.coeFn_toLp (memLp2_prod_fst_snd (Lp_coe_memLp u₂) (Lp_coe_memLp f)))).symm
          |>.mono fun p hp => hp
    _ =ᵐ[vol2] ⇑(prodKernel u₁ f + prodKernel u₂ f) := (Lp.coeFn_add _ _).symm

private theorem prodKernel_smul_fst (c : ℝ) (u f : L2) :
    prodKernel (c • u) f = c • prodKernel u f := by
  apply Lp.ext
  calc ⇑(prodKernel (c • u) f)
      =ᵐ[vol2] (fun p : ℝ × ℝ => ⇑(c • u) p.1 * ⇑f p.2) :=
        MemLp.coeFn_toLp (memLp2_prod_fst_snd (Lp_coe_memLp (c • u)) (Lp_coe_memLp f))
    _ =ᵐ[vol2] (fun p : ℝ × ℝ => (c * ⇑u p.1) * ⇑f p.2) :=
        (eventual_fst (Lp.coeFn_smul c u)).mul EventuallyEq.rfl
    _ =ᵐ[vol2] (c • ⇑(prodKernel u f)) := by
        refine (c • MemLp.coeFn_toLp
          (memLp2_prod_fst_snd (Lp_coe_memLp u) (Lp_coe_memLp f))).symm |>.mono fun p hp => hp
    _ =ᵐ[vol2] ⇑(c • prodKernel u f) := (Lp.coeFn_smul c _).symm

private theorem prodKernel_zero_fst (f : L2) : prodKernel (0 : L2) f = 0 := by
  apply Lp.ext
  calc ⇑(prodKernel (0 : L2) f)
      =ᵐ[vol2] (fun p : ℝ × ℝ => ⇑(0 : L2) p.1 * ⇑f p.2) :=
        MemLp.coeFn_toLp (memLp2_prod_fst_snd (Lp_coe_memLp 0) (Lp_coe_memLp f))
    _ =ᵐ[vol2] (0 : ℝ × ℝ → ℝ) := by
        refine (Lp.coeFn_zero (E := ℝ) (p := 2) (μ := vol)).mono fun p hp => ?_
        simpa using hp
    _ =ᵐ[vol2] ⇑(0 : MeasureTheory.Lp ℝ 2 vol2) := (Lp.coeFn_zero ..).symm

private theorem prodKernel_add_snd (u f₁ f₂ : L2) :
    prodKernel u (f₁ + f₂) = prodKernel u f₁ + prodKernel u f₂ := by
  apply Lp.ext
  calc ⇑(prodKernel u (f₁ + f₂))
      =ᵐ[vol2] (fun p : ℝ × ℝ => ⇑u p.1 * ⇑(f₁ + f₂) p.2) :=
        MemLp.coeFn_toLp (memLp2_prod_fst_snd (Lp_coe_memLp u) (Lp_coe_memLp (f₁ + f₂)))
    _ =ᵐ[vol2] (fun p : ℝ × ℝ => ⇑u p.1 * (⇑f₁ p.2 + ⇑f₂ p.2)) :=
        (EventuallyEq.rfl).mul (eventual_snd (Lp.coeFn_add f₁ f₂))
    _ =ᵐ[vol2] (⇑(prodKernel u f₁) + ⇑(prodKernel u f₂)) := by
        refine ((MemLp.coeFn_toLp (memLp2_prod_fst_snd (Lp_coe_memLp u) (Lp_coe_memLp f₁))).add
          (MemLp.coeFn_toLp (memLp2_prod_fst_snd (Lp_coe_memLp u) (Lp_coe_memLp f₂)))).symm
          |>.mono fun p hp => hp
    _ =ᵐ[vol2] ⇑(prodKernel u f₁ + prodKernel u f₂) := (Lp.coeFn_add _ _).symm

private theorem prodKernel_smul_snd (c : ℝ) (u f : L2) :
    prodKernel u (c • f) = c • prodKernel u f := by
  apply Lp.ext
  calc ⇑(prodKernel u (c • f))
      =ᵐ[vol2] (fun p : ℝ × ℝ => ⇑u p.1 * ⇑(c • f) p.2) :=
        MemLp.coeFn_toLp (memLp2_prod_fst_snd (Lp_coe_memLp u) (Lp_coe_memLp (c • f)))
    _ =ᵐ[vol2] (fun p : ℝ × ℝ => ⇑u p.1 * (c * ⇑f p.2)) :=
        (EventuallyEq.rfl).mul (eventual_snd (Lp.coeFn_smul c f))
    _ =ᵐ[vol2] (c • ⇑(prodKernel u f)) := by
        refine (c • MemLp.coeFn_toLp
          (memLp2_prod_fst_snd (Lp_coe_memLp u) (Lp_coe_memLp f))).symm |>.mono fun p hp => hp
    _ =ᵐ[vol2] ⇑(c • prodKernel u f) := (Lp.coeFn_smul c _).symm

/-! ### B. The pairing `⟪g, u ⊗ f⟫` and its bound -/

/-- The pairing against a section, as a plain integral over the unit square. -/
theorem inner_prodKernel_coe (g : MeasureTheory.Lp ℝ 2 vol2) (u f : L2) :
    inner ℝ g (prodKernel u f) = ∫ p : ℝ × ℝ, ⇑g p * (⇑u p.1 * ⇑f p.2) ∂vol2 := by
  rw [inner_Lp_eq_coe]
  exact integral_congr_ae
    ((MemLp.coeFn_toLp (memLp2_prod_fst_snd (Lp_coe_memLp u) (Lp_coe_memLp f))).mono
      fun p hp => by rw [hp]; ring)

/-- The kernel-norm bridge: `hsNorm` of the representative of an `L²(vol2)` element is its
norm. -/
theorem hsNorm_coe (g : MeasureTheory.Lp ℝ 2 vol2) : hsNorm (⇑g) = ‖g‖ := by
  have h1 : hsNorm (⇑g) ^ 2 = ∫ p : ℝ × ℝ, ⇑g p ^ 2 ∂vol2 := hsNorm_sq ⇑g
  have h2 : ‖g‖ ^ 2 = ∫ p : ℝ × ℝ, ⇑g p ^ 2 ∂vol2 := by
    rw [← real_inner_self_eq_norm_sq, inner_Lp_eq_coe]
    exact integral_congr_ae (Filter.Eventually.of_forall fun p => by ring)
  exact pow_left_injective (by norm_num) (hsNorm_nonneg ⇑g) (norm_nonneg g) (h1.trans h2.symm)

/-- Cauchy–Schwarz on the square: the section pairing is bounded by `‖g‖‖u‖‖f‖`. -/
theorem abs_inner_prodKernel_le (g : MeasureTheory.Lp ℝ 2 vol2) (u f : L2) :
    |inner ℝ g (prodKernel u f)| ≤ ‖g‖ * ‖u‖ * ‖f‖ := by
  have hk := kpair_bound (K := ⇑g) (hK := Lp.memLp g) f u
  rw [inner_prodKernel_coe] at this ⊢
  have hcongr : ∫ p : ℝ × ℝ, ⇑g p * (⇑u p.1 * ⇑f p.2) ∂vol2
      = kpair (⇑g) f u := by
    show ∫ p : ℝ × ℝ, ⇑g p * (⇑u p.1 * ⇑f p.2) ∂vol2
      = ∫ p : ℝ × ℝ, (⇑g) p * (⇑f) p.2 * (⇑u) p.1 ∂vol2
    exact integral_congr_ae (Filter.Eventually.of_forall fun p => by ring)
  rw [hcongr, hsNorm_coe] at hk
  exact hk

/-! ### C. Discharge of the tensor-ONB completeness clause -/

/-- **The tensor-ONB completeness (direct form)**: an element of the kernel space
`L²(vol2)` orthogonal to every section `p ↦ v p.2 ⊗ v p.1` of a complete orthonormal
family `v` of `L²` vanishes.  (Orthonormality of `v` is not even needed — only
completeness.) -/
theorem sections_orthogonal_eq_zero {ι : Type*} {v : ι → L2}
    (hcomp : (span ℝ (Set.range v))ᗮ = ⊥)
    (g : MeasureTheory.Lp ℝ 2 vol2)
    (hg : ∀ p : ι × ι, inner ℝ g (prodKernel (v p.2) (v p.1)) = 0) :
    g = 0 := by
  -- Step 1: bilinearity of the pairing over the double span
  have h1 : ∀ u ∈ Set.range v, ∀ f ∈ span ℝ (Set.range v),
      inner ℝ g (prodKernel u f) = 0 := by
    intro u hu f hf
    have hui : ∃ i : ι, v i = u := hu
    obtain ⟨i, rfl⟩ := hui
    have hQ : Set.range v ⊆ {f : L2 | inner ℝ g (prodKernel (v i) f) = 0} := by
      intro x hx
      exact hg (i, x)
    have hQsub : span ℝ (Set.range v)
        ≤ {f : L2 | inner ℝ g (prodKernel (v i) f) = 0} := by
      refine Submodule.span_le.mpr hQ
      exact ⟨fun f₁ f₂ hf₁ hf₂ => by
        rw [prodKernel_add_snd, inner_add_left, hf₁, hf₂],
        fun c x hx => by
        rw [prodKernel_smul_snd, real_inner_smul_left, smul_eq_mul, hx]⟩
    exact hQsub hf
  have h2 : ∀ u ∈ span ℝ (Set.range v), ∀ f ∈ span ℝ (Set.range v),
      inner ℝ g (prodKernel u f) = 0 := by
    intro u hu f hf
    have hRu : Set.range v ⊆ {u : L2 | ∀ f ∈ span ℝ (Set.range v),
      inner ℝ g (prodKernel u f) = 0} := by
      intro x hx
      exact h1 x hx
    have hRsub : span ℝ (Set.range v) ≤ {u : L2 | ∀ f ∈ span ℝ (Set.range v),
      inner ℝ g (prodKernel u f) = 0} := by
      refine Submodule.span_le.mpr hRu
      exact ⟨fun u₁ u₂ hu₁ hu₂ f hfs => by
        rw [prodKernel_add_fst, inner_add_left, hu₁ f hfs, hu₂ f hfs],
        fun c x hx f hfs => by
        rw [prodKernel_smul_fst, real_inner_smul_left, smul_eq_mul, hx f hfs]⟩
    exact hRsub hu f hf
  -- Step 2: continuity of the pairing in each slot
  have hclos : closure (↑(span ℝ (Set.range v)) : Set L2) = (univ : Set L2) := by
    have htop := (Submodule.topologicalClosure_eq_top_iff (𝕜 := ℝ) (E := L2)).mpr hcomp
    calc closure (↑(span ℝ (Set.range v)) : Set L2)
        = ↑((span ℝ (Set.range v)).topologicalClosure) := rfl
      _ = ↑(⊤ : Submodule ℝ L2) := by rw [htop]
      _ = univ := Submodule.coe_top
  -- Step 3: extend over the closure in the first slot, then the second
  have h3 : ∀ f ∈ span ℝ (Set.range v), ∀ u : L2, inner ℝ g (prodKernel u f) = 0 := by
    intro f hf u
    have hb : ∀ w : L2, |inner ℝ g (prodKernel w f)| ≤ ‖g‖ * ‖f‖ * ‖w‖ :=
      fun w => abs_inner_prodKernel_le g w f
    have hcont : Continuous (fun w : L2 => inner ℝ g (prodKernel w f)) :=
      Continuous.of_bound _ (‖g‖ * ‖f‖) fun w => by
        simpa [Real.norm_eq_abs] using (hb w).trans
          (by nlinarith [norm_nonneg (g : MeasureTheory.Lp ℝ 2 vol2), norm_nonneg f])
    have hsetsub : closure (↑(span ℝ (Set.range v)) : Set L2)
        ⊆ {w : L2 | inner ℝ g (prodKernel w f) = 0} := by
      refine closure_minimal ?_ (hcont.isClosed_preimage {0} isClosed_singleton)
      intro w hw
      exact h2 w hw f hf
    rw [← hclos] at hsetsub
    exact hsetsub (Set.mem_univ u)
  have h4 : ∀ u f : L2, inner ℝ g (prodKernel u f) = 0 := by
    intro u f
    have hb : ∀ w : L2, |inner ℝ g (prodKernel u w)| ≤ ‖g‖ * ‖u‖ * ‖w‖ :=
      fun w => abs_inner_prodKernel_le g u w
    have hcont : Continuous (fun w : L2 => inner ℝ g (prodKernel u w)) :=
      Continuous.of_bound _ (‖g‖ * ‖u‖) fun w => by
        simpa [Real.norm_eq_abs] using (hb w).trans
          (by nlinarith [norm_nonneg (g : MeasureTheory.Lp ℝ 2 vol2), norm_nonneg u])
    have hsetsub : closure (↑(span ℝ (Set.range v)) : Set L2)
        ⊆ {w : L2 | inner ℝ g (prodKernel u w) = 0} := by
      refine closure_minimal ?_ (hcont.isClosed_preimage {0} isClosed_singleton)
      intro w hw
      exact h3 w hw u
    rw [← hclos] at hsetsub
    exact hsetsub (Set.mem_univ f)
  -- Step 4: indicator sections give vanishing box integrals
  have hind : ∀ (A B : Set ℝ), MeasurableSet A → MeasurableSet B →
      ∫ p : ℝ × ℝ, (A ×ˢ B).indicator ⇑g p ∂vol2 = 0 := by
    intro A B hA hB
    have hmemA : MemLp (A.indicator (fun _ : ℝ => (1 : ℝ))) 2 vol :=
      MemLp.indicator hA (memLp_const 1)
    have hmemB : MemLp (B.indicator (fun _ : ℝ => (1 : ℝ))) 2 vol :=
      MemLp.indicator hB (memLp_const 1)
    have hz := h4 (MemLp.toLp _ hmemA) (MemLp.toLp _ hmemB)
    rw [inner_prodKernel_coe] at hz
    have hcongr : ∫ p : ℝ × ℝ, ⇑g p * (⇑(MemLp.toLp _ hmemA) p.1 * ⇑(MemLp.toLp _ hmemB) p.2) ∂vol2
        = ∫ p : ℝ × ℝ, (A ×ˢ B).indicator ⇑g p ∂vol2 := by
      refine integral_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp hmemA |>.mono (fun x hx => hx),
        MemLp.coeFn_toLp hmemB |>.mono (fun x hx => hx)] with p h1p h2p
      by_cases hp1 : p.1 ∈ A <;> by_cases hp2 : p.2 ∈ B <;>
        simp [Set.mem_prod, Set.indicator_of_mem, Set.indicator_of_not_mem, hp1, hp2, h1p, h2p]
    rw [hcongr] at hz
    exact hz
  -- Step 5: π-λ uniqueness of the positive/negative-part measures
  obtain ⟨G, hGmeas, hGae⟩ : ∃ G : ℝ × ℝ → ℝ, Measurable G ∧ (⇑g) =ᵐ[vol2] G :=
    ⟨(Lp.memLp g).aemeasurable.mk ⇑g, (Lp.memLp g).aemeasurable.measurable_mk,
      (Lp.memLp g).aemeasurable.ae_eq_mk⟩
  have hGint : Integrable G vol2 := ((Lp.memLp g).mono_exponent
    (by norm_num)).integrable.congr hGae
  have hbox : ∀ (A B : Set ℝ), MeasurableSet A → MeasurableSet B →
      ∫ p : ℝ × ℝ in A ×ˢ B, G p ∂vol2 = 0 := by
    intro A B hA hB
    have h1 := hind A B hA hB
    rw [integral_congr_ae (hGae.indicator ?_)] at h1
    · rw [← h1]
      exact integral_congr_ae (Filter.Eventually.of_forall fun p => by
        by_cases hp1 : p.1 ∈ A <;> by_cases hp2 : p.2 ∈ B <;>
          simp [Set.mem_prod, Set.indicator_of_mem, Set.indicator_of_not_mem, hp1, hp2])
    · exact MeasurableSet.prod hA hB
  have hint : Integrable (fun p : ℝ × ℝ => max (G p) 0) vol2 :=
    hGint.mono (hGmeas.max measurable_const) fun p => by
      simpa using le_abs_self (G p)
  have hintneg : Integrable (fun p : ℝ × ℝ => max (-(G p)) 0) vol2 :=
    hGint.neg.mono ((hGmeas.neg).max measurable_const) fun p => by
      simpa using le_abs_self (-(G p))
  -- the two finite measures with densities ⇑g⁺ and ⇑g⁻
  set Fp : ℝ × ℝ → ENNReal := fun p => ENNReal.ofReal (G p) with hFp
  set Fm : ℝ × ℝ → ENNReal := fun p => ENNReal.ofReal (-(G p)) with hFm
  have hFpinf : ∫⁻ a, Fp a ∂vol2 ≠ ⊤ := by
    rw [hFp]
    have h1 : ∫⁻ a, ENNReal.ofReal (G a) ∂vol2
        = ∫⁻ a, ENNReal.ofReal (max (G a) 0) ∂vol2 :=
      lintegral_congr_ae (Filter.Eventually.of_forall fun p => by
        by_cases hp : 0 ≤ G p
        · simp [max_eq_left hp]
        · rw [max_eq_right (le_of_lt (by omega : 0 < -(G p)))]
          exact (ENNReal.ofReal_eq_zero.mpr (le_of_lt (by omega : G p < 0))).symm)
    rw [h1, ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun p => le_max_left _ _)]
    exact ENNReal.ofReal_ne_top
  have hFminf : ∫⁻ a, Fm a ∂vol2 ≠ ⊤ := by
    rw [hFm]
    have h1 : ∫⁻ a, ENNReal.ofReal (-(G a)) ∂vol2
        = ∫⁻ a, ENNReal.ofReal (max (-(G a)) 0) ∂vol2 :=
      lintegral_congr_ae (Filter.Eventually.of_forall fun p => by
        by_cases hp : 0 ≤ -(G p)
        · simp [max_eq_left hp]
        · rw [max_eq_right (le_of_lt (by omega : 0 < G p))]
          exact (ENNReal.ofReal_eq_zero.mpr (le_of_lt (by omega : -(G p) < 0))).symm)
    rw [h1, ← ofReal_integral_eq_lintegral_ofReal hintneg (ae_of_all _ fun p => le_max_left _ _)]
    exact ENNReal.ofReal_ne_top
  haveI : IsFiniteMeasure (vol2.withDensity Fp) := isFiniteMeasure_withDensity hFpinf
  haveI : IsFiniteMeasure (vol2.withDensity Fm) := isFiniteMeasure_withDensity hFminf
  -- equality on the π-system of measurable rectangles
  have hboxF : ∀ (A B : Set ℝ), MeasurableSet A → MeasurableSet B →
      ∫⁻ p : ℝ × ℝ in A ×ˢ B, Fp p ∂vol2 = ∫⁻ p : ℝ × ℝ in A ×ˢ B, Fm p ∂vol2 := by
    intro A B hA hB
    have hboxAB := hbox A B hA hB
    have hIp : ∫⁻ p : ℝ × ℝ in A ×ˢ B, Fp p ∂vol2
        = ENNReal.ofReal (∫ p : ℝ × ℝ in A ×ˢ B, max (G p) 0 ∂vol2) := by
      have hcongr : ∫⁻ p : ℝ × ℝ in A ×ˢ B, Fp p ∂vol2
          = ∫⁻ p : ℝ × ℝ in A ×ˢ B, ENNReal.ofReal (max (G p) 0) ∂vol2 := by
        refine lintegral_congr_ae ?_
        rw [hFp]
        filter_upwards with p
        by_cases hp : 0 ≤ G p
        · simp [max_eq_left hp]
        · rw [max_eq_right (le_of_lt (by omega : 0 < -(G p)))]
          exact (ENNReal.ofReal_eq_zero.mpr (le_of_lt (by omega : G p < 0))).symm
      rw [hcongr, ← ofReal_integral_eq_lintegral_ofReal (hint.restrict (MeasurableSet.prod hA hB))
        (ae_of_all _ fun p => le_max_left _ _)]
      rfl
    have hIm : ∫⁻ p : ℝ × ℝ in A ×ˢ B, Fm p ∂vol2
        = ENNReal.ofReal (∫ p : ℝ × ℝ in A ×ˢ B, max (-(G p)) 0 ∂vol2) := by
      have hcongr : ∫⁻ p : ℝ × ℝ in A ×ˢ B, Fm p ∂vol2
          = ∫⁻ p : ℝ × ℝ in A ×ˢ B, ENNReal.ofReal (max (-(G p)) 0) ∂vol2 := by
        refine lintegral_congr_ae ?_
        rw [hFm]
        filter_upwards with p
        by_cases hp : 0 ≤ -(G p)
        · simp [max_eq_left hp]
        · rw [max_eq_right (le_of_lt (by omega : 0 < G p))]
          exact (ENNReal.ofReal_eq_zero.mpr (le_of_lt (by omega : -(G p) < 0))).symm
      rw [hcongr, ← ofReal_integral_eq_lintegral_ofReal
        (hintneg.restrict (MeasurableSet.prod hA hB))
        (ae_of_all _ fun p => le_max_left _ _)]
      rfl
    have hsub : ∫ p : ℝ × ℝ in A ×ˢ B, max (G p) 0 ∂vol2
        - ∫ p : ℝ × ℝ in A ×ˢ B, max (-(G p)) 0 ∂vol2 = 0 := by
      have hpoint : (fun p : ℝ × ℝ => max (G p) 0 - max (-(G p)) 0) = G := by
        funext p
        by_cases hp : 0 ≤ G p
        · rw [max_eq_left hp, max_eq_right (le_of_lt (by omega : G p < -(0:ℝ) ∨ G p ≥ 0))]
          simp
        · rw [max_eq_right (le_of_lt (by omega : 0 < -(G p))), max_eq_left (le_of_lt (by omega : G p < 0))]
          ring
      rw [← integral_sub (hint.restrict (MeasurableSet.prod hA hB))
        (hintneg.restrict (MeasurableSet.prod hA hB)), hpoint, hboxAB]
    rw [hIp, hIm, sub_eq_zero.mp hsub]
  have hC : Set (Set (ℝ × ℝ)) :=
    Set.image2 (fun (s t : Set ℝ) => s ×ˢ t) {s : Set ℝ | MeasurableSet s} {t : Set ℝ | MeasurableSet t}
  have heq : vol2.withDensity Fp = vol2.withDensity Fm :=
    ext_of_generate_finite hC (generateFrom_prod (α := ℝ) (β := ℝ)).symm isPiSystem_prod
      (fun s hs => by
        obtain ⟨A, hAm, B, hBm, rfl⟩ := hs
        exact hboxF A B hAm hBm)
      (by
        have := hboxF Set.univ Set.univ MeasurableSet.univ MeasurableSet.univ
        simpa using this)
  -- Step 6: the positive and negative supports are null
  have hs0 : ∀ (s : Set (ℝ × ℝ)), MeasurableSet s →
      (∀ᵐ p ∂(vol2.restrict s), Fp p = ENNReal.ofReal (G p)) →
      (∀ᵐ p ∂(vol2.restrict s), Fm p = 0) → vol2 s = 0 := by
    intro s hs hps hms
    have h1 := congrFun heq s
    rw [withDensity_apply Fp hs, withDensity_apply Fm hs, lintegral_congr_ae hps,
      lintegral_congr_ae hms] at h1
    rw [lintegral_zero] at h1
    -- ∫⁻ in s, ofReal (G p) = 0  ⇒  s null
    have h2 : (fun p => ENNReal.ofReal (G p)) =ᵐ[vol2.restrict s] 0 := by
      rw [← h1]
      exact lintegral_eq_zero_iff ((hGmeas).comp? measurable_ENNReal_ofReal) |>.mpr ?_
    ...
  sorry

end HS

end
