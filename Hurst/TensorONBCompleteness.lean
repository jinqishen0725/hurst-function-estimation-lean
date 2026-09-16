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
  family (closes the Parseval gap carried by `Hurst.ReverseParseval`).
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
  have h2 : ⇑(prodKernel u₁ f) =ᵐ[vol2] (fun p : ℝ × ℝ => ⇑u₁ p.1 * ⇑f p.2) :=
    MemLp.coeFn_toLp _
  have h3 : ⇑(prodKernel u₂ f) =ᵐ[vol2] (fun p : ℝ × ℝ => ⇑u₂ p.1 * ⇑f p.2) :=
    MemLp.coeFn_toLp _
  calc ⇑(prodKernel (u₁ + u₂) f)
      =ᵐ[vol2] (fun p : ℝ × ℝ => ⇑(u₁ + u₂) p.1 * ⇑f p.2) :=
        MemLp.coeFn_toLp (memLp2_prod_fst_snd (Lp_coe_memLp (u₁ + u₂)) (Lp_coe_memLp f))
    _ =ᵐ[vol2] (fun p : ℝ × ℝ => ⇑u₁ p.1 * ⇑f p.2 + ⇑u₂ p.1 * ⇑f p.2) := by
        filter_upwards [eventual_fst (Lp.coeFn_add u₁ u₂)] with p hp
        rw [hp]
        simp only [Pi.add_apply]
        ring
    _ =ᵐ[vol2] (⇑(prodKernel u₁ f) + ⇑(prodKernel u₂ f)) := (h2.add h3).symm
    _ =ᵐ[vol2] ⇑(prodKernel u₁ f + prodKernel u₂ f) := (Lp.coeFn_add _ _).symm

private theorem prodKernel_smul_fst (c : ℝ) (u f : L2) :
    prodKernel (c • u) f = c • prodKernel u f := by
  apply Lp.ext
  have h2 : ⇑(prodKernel u f) =ᵐ[vol2] (fun p : ℝ × ℝ => ⇑u p.1 * ⇑f p.2) :=
    MemLp.coeFn_toLp _
  calc ⇑(prodKernel (c • u) f)
      =ᵐ[vol2] (fun p : ℝ × ℝ => ⇑(c • u) p.1 * ⇑f p.2) :=
        MemLp.coeFn_toLp (memLp2_prod_fst_snd (Lp_coe_memLp (c • u)) (Lp_coe_memLp f))
    _ =ᵐ[vol2] (fun p : ℝ × ℝ => c * (⇑u p.1 * ⇑f p.2)) := by
        filter_upwards [eventual_fst (Lp.coeFn_smul c u)] with p hp
        rw [hp]
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
    _ =ᵐ[vol2] ⇑(c • prodKernel u f) := by
        filter_upwards [Lp.coeFn_smul c (prodKernel u f), h2] with p hcs hp
        show c * (⇑u p.1 * ⇑f p.2) = ⇑(c • prodKernel u f) p
        rw [hcs, Pi.smul_apply, hp, smul_eq_mul]

private theorem prodKernel_zero_fst (f : L2) : prodKernel (0 : L2) f = 0 := by
  apply Lp.ext
  have h2 : ⇑(prodKernel (0 : L2) f)
      =ᵐ[vol2] (fun p : ℝ × ℝ => ⇑(0 : L2) p.1 * ⇑f p.2) :=
    MemLp.coeFn_toLp _
  refine h2.trans ?_
  filter_upwards [eventual_fst (Lp.coeFn_zero (E := ℝ) (p := 2) (μ := vol)),
    Lp.coeFn_zero (E := ℝ) (p := 2) (μ := vol2)] with p hp hp2
  show ⇑(0 : L2) p.1 * ⇑f p.2 = ⇑(0 : MeasureTheory.Lp ℝ 2 vol2) p
  rw [hp, Pi.zero_apply, zero_mul, hp2, Pi.zero_apply]

private theorem prodKernel_zero_snd (u : L2) : prodKernel u (0 : L2) = 0 := by
  apply Lp.ext
  have h2 : ⇑(prodKernel u (0 : L2))
      =ᵐ[vol2] (fun p : ℝ × ℝ => ⇑u p.1 * ⇑(0 : L2) p.2) :=
    MemLp.coeFn_toLp _
  refine h2.trans ?_
  filter_upwards [eventual_snd (Lp.coeFn_zero (E := ℝ) (p := 2) (μ := vol)),
    Lp.coeFn_zero (E := ℝ) (p := 2) (μ := vol2)] with p hp hp2
  show ⇑u p.1 * ⇑(0 : L2) p.2 = ⇑(0 : MeasureTheory.Lp ℝ 2 vol2) p
  rw [hp, Pi.zero_apply, mul_zero, hp2, Pi.zero_apply]

private theorem prodKernel_add_snd (u f₁ f₂ : L2) :
    prodKernel u (f₁ + f₂) = prodKernel u f₁ + prodKernel u f₂ := by
  apply Lp.ext
  have h2 : ⇑(prodKernel u f₁) =ᵐ[vol2] (fun p : ℝ × ℝ => ⇑u p.1 * ⇑f₁ p.2) :=
    MemLp.coeFn_toLp _
  have h3 : ⇑(prodKernel u f₂) =ᵐ[vol2] (fun p : ℝ × ℝ => ⇑u p.1 * ⇑f₂ p.2) :=
    MemLp.coeFn_toLp _
  calc ⇑(prodKernel u (f₁ + f₂))
      =ᵐ[vol2] (fun p : ℝ × ℝ => ⇑u p.1 * ⇑(f₁ + f₂) p.2) :=
        MemLp.coeFn_toLp (memLp2_prod_fst_snd (Lp_coe_memLp u) (Lp_coe_memLp (f₁ + f₂)))
    _ =ᵐ[vol2] (fun p : ℝ × ℝ => ⇑u p.1 * ⇑f₁ p.2 + ⇑u p.1 * ⇑f₂ p.2) := by
        filter_upwards [eventual_snd (Lp.coeFn_add f₁ f₂)] with p hp
        rw [hp]
        simp only [Pi.add_apply]
        ring
    _ =ᵐ[vol2] (⇑(prodKernel u f₁) + ⇑(prodKernel u f₂)) := (h2.add h3).symm
    _ =ᵐ[vol2] ⇑(prodKernel u f₁ + prodKernel u f₂) := (Lp.coeFn_add _ _).symm

private theorem prodKernel_smul_snd (c : ℝ) (u f : L2) :
    prodKernel u (c • f) = c • prodKernel u f := by
  apply Lp.ext
  have h2 : ⇑(prodKernel u f) =ᵐ[vol2] (fun p : ℝ × ℝ => ⇑u p.1 * ⇑f p.2) :=
    MemLp.coeFn_toLp _
  calc ⇑(prodKernel u (c • f))
      =ᵐ[vol2] (fun p : ℝ × ℝ => ⇑u p.1 * ⇑(c • f) p.2) :=
        MemLp.coeFn_toLp (memLp2_prod_fst_snd (Lp_coe_memLp u) (Lp_coe_memLp (c • f)))
    _ =ᵐ[vol2] (fun p : ℝ × ℝ => c * (⇑u p.1 * ⇑f p.2)) := by
        filter_upwards [eventual_snd (Lp.coeFn_smul c f)] with p hp
        rw [hp]
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
    _ =ᵐ[vol2] ⇑(c • prodKernel u f) := by
        filter_upwards [Lp.coeFn_smul c (prodKernel u f), h2] with p hcs hp
        show c * (⇑u p.1 * ⇑f p.2) = ⇑(c • prodKernel u f) p
        rw [hcs, Pi.smul_apply, hp, smul_eq_mul]

/-! ### B. The pairing `⟪g, u ⊗ f⟫` and its bound -/

/-- The pairing against a section, as a plain integral over the unit square. -/
theorem inner_prodKernel_coe (g : MeasureTheory.Lp ℝ 2 vol2) (u f : L2) :
    inner ℝ g (prodKernel u f) = ∫ p : ℝ × ℝ, ⇑g p * (⇑u p.1 * ⇑f p.2) ∂vol2 := by
  rw [inner_Lp_eq_coe]
  have hcoeprod : ⇑(prodKernel u f) =ᵐ[vol2] (fun p : ℝ × ℝ => ⇑u p.1 * ⇑f p.2) :=
    MemLp.coeFn_toLp (memLp2_prod_fst_snd (Lp_coe_memLp u) (Lp_coe_memLp f))
  refine integral_congr_ae ?_
  filter_upwards [hcoeprod] with p hp
  rw [hp]

/-- The kernel-norm bridge: `hsNorm` of the representative function of an `L²(vol2)`
element is its norm. -/
theorem hsNorm_coe (g : MeasureTheory.Lp ℝ 2 vol2) : hsNorm (⇑g) = ‖g‖ := by
  have h1 : hsNorm (⇑g) ^ 2 = ∫ p : ℝ × ℝ, ⇑g p ^ 2 ∂vol2 := hsNorm_sq ⇑g
  have h2 : ‖g‖ ^ 2 = ∫ p : ℝ × ℝ, ⇑g p ^ 2 ∂vol2 := by
    rw [← real_inner_self_eq_norm_sq, inner_Lp_eq_coe]
    exact integral_congr_ae (Filter.Eventually.of_forall fun p => by ring)
  have key : Real.sqrt (∫ p : ℝ × ℝ, ⇑g p ^ 2 ∂vol2) = ‖g‖ := by
    rw [← h2, Real.sqrt_sq (norm_nonneg g)]
  rw [hsNorm_def, key]

/-- Cauchy–Schwarz on the square: the section pairing is bounded by `‖g‖‖u‖‖f‖`. -/
theorem abs_inner_prodKernel_le (g : MeasureTheory.Lp ℝ 2 vol2) (u f : L2) :
    |inner ℝ g (prodKernel u f)| ≤ ‖g‖ * ‖f‖ * ‖u‖ := by
  have hk := kpair_bound (K := ⇑g) (hK := Lp.memLp g) f u
  rw [inner_prodKernel_coe]
  have hcongr : kpair (⇑g) f u = ∫ p : ℝ × ℝ, ⇑g p * (⇑u p.1 * ⇑f p.2) ∂vol2 := by
    show ∫ p : ℝ × ℝ, (⇑g) p * (⇑f) p.2 * (⇑u) p.1 ∂vol2
      = ∫ p : ℝ × ℝ, ⇑g p * (⇑u p.1 * ⇑f p.2) ∂vol2
    exact integral_congr_ae (Filter.Eventually.of_forall fun p => by ring)
  rw [hcongr, hsNorm_coe] at hk
  exact hk

/-! ### C. Discharge of the tensor-ONB completeness clause -/

/-- **The tensor-ONB completeness (direct form)**: an element of the kernel space
`L²(vol2)` orthogonal to every section `p ↦ v p.2 ⊗ v p.1` of a complete orthonormal
family `v` of `L²` vanishes.  (Orthonormality of `v` is not needed — only completeness.) -/
theorem sections_orthogonal_eq_zero {ι : Type*} {v : ι → L2}
    (hcomp : (span ℝ (Set.range v))ᗮ = ⊥)
    (g : MeasureTheory.Lp ℝ 2 vol2)
    (hg : ∀ p : ι × ι, inner ℝ g (prodKernel (v p.2) (v p.1)) = 0) :
    g = 0 := by
  -- Step 1: bilinearity of the pairing over the double span
  have h1 : ∀ u ∈ Set.range v, ∀ f ∈ span ℝ (Set.range v),
      inner ℝ g (prodKernel u f) = 0 := by
    intro u hu
    obtain ⟨i, rfl⟩ := hu
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨y, rfl⟩ := hx
        exact hg (y, i)
    | zero => rw [prodKernel_zero_snd]; simp
    | add x y _ _ hxp hyp =>
        rw [prodKernel_add_snd, inner_add_right, hxp, hyp, add_zero]
    | smul c x _ hxs => rw [prodKernel_smul_snd, real_inner_smul_right, hxs, mul_zero]
  have h2 : ∀ u ∈ span ℝ (Set.range v), ∀ f ∈ span ℝ (Set.range v),
      inner ℝ g (prodKernel u f) = 0 := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx => exact fun f hf => h1 x hx f hf
    | zero => exact fun f hf => by rw [prodKernel_zero_fst]; simp
    | add x y _ _ hxp hyp =>
        exact fun f hf => by
          rw [prodKernel_add_fst, inner_add_right, hxp f hf, hyp f hf, add_zero]
    | smul c x _ hxs =>
        exact fun f hf => by
          rw [prodKernel_smul_fst, real_inner_smul_right, hxs f hf, mul_zero]
  -- Step 2: the span is dense (completeness of v)
  have hclos : closure (↑(span ℝ (Set.range v)) : Set L2) = (univ : Set L2) := by
    have htop := (Submodule.topologicalClosure_eq_top_iff (𝕜 := ℝ) (E := L2)).mpr hcomp
    calc closure (↑(span ℝ (Set.range v)) : Set L2)
        = ↑((span ℝ (Set.range v)).topologicalClosure) := rfl
      _ = ↑(⊤ : Submodule ℝ L2) := by rw [htop]
      _ = univ := Submodule.top_coe
  -- Step 3: extend over the closure in the first slot, then the second
  have h3 : ∀ f ∈ span ℝ (Set.range v), ∀ u : L2, inner ℝ g (prodKernel u f) = 0 := by
    intro f hf u
    have hb : ∀ w : L2, |inner ℝ g (prodKernel w f)| ≤ ‖g‖ * ‖f‖ * ‖w‖ :=
      fun w => abs_inner_prodKernel_le g w f
    have hcont : Continuous (fun w : L2 => inner ℝ g (prodKernel w f)) :=
      (LinearMap.mkContinuous
        { toFun := fun w : L2 => inner ℝ g (prodKernel w f)
          map_add' := by
            intro a b
            rw [prodKernel_add_fst, inner_add_right]
          map_smul' := by
            intro c a
            rw [prodKernel_smul_fst, real_inner_smul_right, RingHom.id_apply, smul_eq_mul] }
        (‖g‖ * ‖f‖) (fun w => by rw [Real.norm_eq_abs]; exact hb w)).continuous
    have hsetsub : closure (↑(span ℝ (Set.range v)) : Set L2)
        ⊆ {w : L2 | inner ℝ g (prodKernel w f) = 0} := by
      refine closure_minimal ?_ (IsClosed.preimage hcont isClosed_singleton)
      exact fun w hw => h2 w hw f hf
    rw [hclos] at hsetsub
    exact hsetsub (Set.mem_univ u)
  have h4 : ∀ u f : L2, inner ℝ g (prodKernel u f) = 0 := by
    intro u f
    have hb : ∀ w : L2, |inner ℝ g (prodKernel u w)| ≤ ‖g‖ * ‖u‖ * ‖w‖ :=
      fun w => (abs_inner_prodKernel_le g u w).trans_eq (by ring)
    have hcont : Continuous (fun w : L2 => inner ℝ g (prodKernel u w)) :=
      (LinearMap.mkContinuous
        { toFun := fun w : L2 => inner ℝ g (prodKernel u w)
          map_add' := by
            intro a b
            rw [prodKernel_add_snd, inner_add_right]
          map_smul' := by
            intro c a
            rw [prodKernel_smul_snd, real_inner_smul_right, RingHom.id_apply, smul_eq_mul] }
        (‖g‖ * ‖u‖) (fun w => by rw [Real.norm_eq_abs]; exact hb w)).continuous
    have hsetsub : closure (↑(span ℝ (Set.range v)) : Set L2)
        ⊆ {w : L2 | inner ℝ g (prodKernel u w) = 0} := by
      refine closure_minimal ?_ (IsClosed.preimage hcont isClosed_singleton)
      exact fun w hw => h3 w hw u
    rw [hclos] at hsetsub
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
    have hcongr : ∫ p : ℝ × ℝ,
        ⇑g p * (⇑(MemLp.toLp (A.indicator (fun _ : ℝ => (1 : ℝ))) hmemA) p.1
          * ⇑(MemLp.toLp (B.indicator (fun _ : ℝ => (1 : ℝ))) hmemB) p.2) ∂vol2
        = ∫ p : ℝ × ℝ, (A ×ˢ B).indicator ⇑g p ∂vol2 := by
      refine integral_congr_ae ?_
      have hmemAB : ∀ q : ℝ × ℝ, q ∈ A ×ˢ B ↔ (q.1 ∈ A ∧ q.2 ∈ B) := fun q => Set.mem_prod
      filter_upwards [(eventual_fst (MemLp.coeFn_toLp hmemA)),
        (eventual_snd (MemLp.coeFn_toLp hmemB))] with p h1p h2p
      by_cases hp1 : p.1 ∈ A <;> by_cases hp2 : p.2 ∈ B <;> rw [h1p, h2p]
      · rw [Set.indicator_of_mem hp1, Set.indicator_of_mem hp2,
          Set.indicator_of_mem ((hmemAB p).mpr ⟨hp1, hp2⟩)]
        ring
      · rw [Set.indicator_of_mem hp1, Set.indicator_of_notMem hp2,
          Set.indicator_of_notMem
            (fun hmem => absurd ((hmemAB p).mp hmem).2 hp2 : p ∉ A ×ˢ B)]
        ring
      · rw [Set.indicator_of_notMem hp1, Set.indicator_of_mem hp2,
          Set.indicator_of_notMem
            (fun hmem => absurd ((hmemAB p).mp hmem).1 hp1 : p ∉ A ×ˢ B)]
        ring
      · rw [Set.indicator_of_notMem hp1, Set.indicator_of_notMem hp2,
          Set.indicator_of_notMem
            (fun hmem => absurd ((hmemAB p).mp hmem).1 hp1 : p ∉ A ×ˢ B)]
        ring
    rw [← hcongr]
    exact hz
  -- Step 5: π-λ uniqueness of the positive/negative-part measures
  obtain ⟨G, hGmeas, hGae⟩ : ∃ G : ℝ × ℝ → ℝ, Measurable G ∧ (⇑g) =ᵐ[vol2] G :=
    ⟨(Lp.memLp g).aemeasurable.mk ⇑g, (Lp.memLp g).aemeasurable.measurable_mk,
      (Lp.memLp g).aemeasurable.ae_eq_mk⟩
  have hGint : Integrable G vol2 :=
    (memLp_one_iff_integrable.mp ((Lp.memLp g).mono_exponent (by norm_num))).congr hGae
  have hbox : ∀ (A B : Set ℝ), MeasurableSet A → MeasurableSet B →
      ∫ p : ℝ × ℝ in A ×ˢ B, G p ∂vol2 = 0 := by
    intro A B hA hB
    have h1 := hind A B hA hB
    have h1i : (A ×ˢ B).indicator ⇑g =ᵐ[vol2] (A ×ˢ B).indicator G :=
      hGae.indicator
    have h2 : ∫ p : ℝ × ℝ, (A ×ˢ B).indicator G p ∂vol2 = 0 := by
      rw [← integral_congr_ae h1i]
      exact h1
    rw [← integral_indicator (MeasurableSet.prod hA hB)]
    exact h2
  have hint : Integrable (fun p : ℝ × ℝ => max (G p) 0) vol2 :=
    hGint.mono
      ((hGmeas.max (measurable_const : Measurable (fun _ : ℝ × ℝ => (0:ℝ)))).aestronglyMeasurable)
      (ae_of_all vol2 fun p => by
        simp only [Real.norm_eq_abs]
        rw [max_comm, abs_of_nonneg (le_max_left (0:ℝ) (G p))]
        exact max_le (abs_nonneg (G p)) (le_abs_self (G p)))
  have hintneg : Integrable (fun p : ℝ × ℝ => max (-(G p)) 0) vol2 :=
    hGint.neg.mono
      ((hGmeas.neg.max (measurable_const : Measurable (fun _ : ℝ × ℝ => (0:ℝ)))).aestronglyMeasurable)
      (ae_of_all vol2 fun p => by
        simp only [Real.norm_eq_abs]
        rw [max_comm, abs_of_nonneg (le_max_left (0:ℝ) (-(G p)))]
        exact max_le (abs_nonneg (-(G p))) (le_abs_self (-(G p))))
  set Fp : ℝ × ℝ → ENNReal := fun p => ENNReal.ofReal (G p) with hFp
  set Fm : ℝ × ℝ → ENNReal := fun p => ENNReal.ofReal (-(G p)) with hFm
  have hFpinf : ∫⁻ a, Fp a ∂vol2 ≠ ⊤ := by
    rw [hFp]
    have h1 : ∫⁻ a, ENNReal.ofReal (G a) ∂vol2
        = ∫⁻ a, ENNReal.ofReal (max (G a) 0) ∂vol2 :=
      lintegral_congr_ae (Filter.Eventually.of_forall fun p => by
        show ENNReal.ofReal (G p) = ENNReal.ofReal (max (G p) 0)
        by_cases hp : 0 ≤ G p
        · rw [max_eq_left hp]
        · rw [max_eq_right (show G p ≤ 0 by linarith), ENNReal.ofReal_zero]
          exact ENNReal.ofReal_eq_zero.mpr (show G p ≤ 0 by linarith))
    rw [h1, ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun p => le_max_right _ _)]
    exact ENNReal.ofReal_ne_top
  have hFminf : ∫⁻ a, Fm a ∂vol2 ≠ ⊤ := by
    rw [hFm]
    have h1 : ∫⁻ a, ENNReal.ofReal (-(G a)) ∂vol2
        = ∫⁻ a, ENNReal.ofReal (max (-(G a)) 0) ∂vol2 :=
      lintegral_congr_ae (Filter.Eventually.of_forall fun p => by
        show ENNReal.ofReal (-(G p)) = ENNReal.ofReal (max (-(G p)) 0)
        by_cases hp : 0 ≤ -(G p)
        · rw [max_eq_left hp]
        · rw [max_eq_right (show -(G p) ≤ 0 by linarith), ENNReal.ofReal_zero]
          exact ENNReal.ofReal_eq_zero.mpr (show -(G p) ≤ 0 by linarith))
    rw [h1, ← ofReal_integral_eq_lintegral_ofReal hintneg
      (ae_of_all _ fun p => le_max_right _ _)]
    exact ENNReal.ofReal_ne_top
  haveI : IsFiniteMeasure (vol2.withDensity Fp) := isFiniteMeasure_withDensity hFpinf
  haveI : IsFiniteMeasure (vol2.withDensity Fm) := isFiniteMeasure_withDensity hFminf
  -- equality of the box integrals of the two densities
  have hboxF : ∀ (A B : Set ℝ), MeasurableSet A → MeasurableSet B →
      ∫⁻ p : ℝ × ℝ in A ×ˢ B, Fp p ∂vol2 = ∫⁻ p : ℝ × ℝ in A ×ˢ B, Fm p ∂vol2 := by
    intro A B hA hB
    have hboxAB := hbox A B hA hB
    have hintP : Integrable (fun p : ℝ × ℝ => max (G p) 0) (vol2.restrict (A ×ˢ B)) :=
      hint.restrict
    have hintM : Integrable (fun p : ℝ × ℝ => max (-(G p)) 0) (vol2.restrict (A ×ˢ B)) :=
      hintneg.restrict
    have hIp : ∫⁻ p : ℝ × ℝ in A ×ˢ B, Fp p ∂vol2
        = ENNReal.ofReal (∫ p : ℝ × ℝ in A ×ˢ B, max (G p) 0 ∂vol2) := by
      rw [hFp]
      rw [show ∫⁻ p : ℝ × ℝ in A ×ˢ B, ENNReal.ofReal (G p) ∂vol2
          = ∫⁻ p : ℝ × ℝ in A ×ˢ B, ENNReal.ofReal (max (G p) 0) ∂vol2 from
        lintegral_congr_ae (Filter.Eventually.of_forall fun p => by
          show ENNReal.ofReal (G p) = ENNReal.ofReal (max (G p) 0)
          by_cases hp : 0 ≤ G p
          · rw [max_eq_left hp]
          · rw [max_eq_right (show G p ≤ 0 by linarith), ENNReal.ofReal_zero]
            exact ENNReal.ofReal_eq_zero.mpr (show G p ≤ 0 by linarith))]
      rw [← ofReal_integral_eq_lintegral_ofReal hintP
        (ae_of_all _ fun p => le_max_right _ _)]
      rfl
    have hIm : ∫⁻ p : ℝ × ℝ in A ×ˢ B, Fm p ∂vol2
        = ENNReal.ofReal (∫ p : ℝ × ℝ in A ×ˢ B, max (-(G p)) 0 ∂vol2) := by
      rw [hFm]
      rw [show ∫⁻ p : ℝ × ℝ in A ×ˢ B, ENNReal.ofReal (-(G p)) ∂vol2
          = ∫⁻ p : ℝ × ℝ in A ×ˢ B, ENNReal.ofReal (max (-(G p)) 0) ∂vol2 from
        lintegral_congr_ae (Filter.Eventually.of_forall fun p => by
          show ENNReal.ofReal (-(G p)) = ENNReal.ofReal (max (-(G p)) 0)
          by_cases hp : 0 ≤ -(G p)
          · rw [max_eq_left hp]
          · rw [max_eq_right (show -(G p) ≤ 0 by linarith), ENNReal.ofReal_zero]
            exact ENNReal.ofReal_eq_zero.mpr (show -(G p) ≤ 0 by linarith))]
      rw [← ofReal_integral_eq_lintegral_ofReal hintM
        (ae_of_all _ fun p => le_max_right _ _)]
      rfl
    have hsub : ∫ p : ℝ × ℝ in A ×ˢ B, max (G p) 0 ∂vol2
        - ∫ p : ℝ × ℝ in A ×ˢ B, max (-(G p)) 0 ∂vol2 = 0 := by
      have hpoint : (fun p : ℝ × ℝ => max (G p) 0 - max (-(G p)) 0) = G := by
        funext p
        by_cases hp : 0 ≤ G p
        · rw [max_eq_left hp, max_eq_right (by linarith : -(G p) ≤ 0)]; ring
        · rw [max_eq_right ((show G p ≤ 0 by linarith)),
            max_eq_left (le_of_lt (by linarith : 0 ≤ -(G p)))]
          ring
      rw [← integral_sub hintP hintM, hpoint, hboxAB]
    rw [hIp, hIm, sub_eq_zero.mp hsub]
  have heq : vol2.withDensity Fp = vol2.withDensity Fm :=
    ext_of_generate_finite
      (Set.image2 (fun (s t : Set ℝ) => s ×ˢ t)
        {s : Set ℝ | MeasurableSet s} {t : Set ℝ | MeasurableSet t})
      (generateFrom_prod (α := ℝ) (β := ℝ)).symm isPiSystem_prod
      (fun s hs => by
        obtain ⟨A, hAm, B, hBm, rfl⟩ := hs
        exact hboxF A B hAm hBm)
      (by
        have h := hboxF Set.univ Set.univ MeasurableSet.univ MeasurableSet.univ
        rwa [Set.univ_prod_univ] at h)
  -- Step 6: the positive and negative supports are null
  have hmeasG : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (G p)) := by measurability
  have hpos : vol2 {p : ℝ × ℝ | 0 < G p} = 0 := by
    have hs : MeasurableSet {p : ℝ × ℝ | 0 < G p} := by measurability
    have hae1 : ∀ᵐ p ∂(vol2.restrict {p : ℝ × ℝ | 0 < G p}), Fp p = ENNReal.ofReal (G p) := by
      filter_upwards [ae_restrict_mem hs] with p hp
      simp only [Set.mem_setOf_eq] at hp
      rw [hFp, max_eq_left (le_of_lt hp)]
    have hae2 : ∀ᵐ p ∂(vol2.restrict {p : ℝ × ℝ | 0 < G p}), Fm p = 0 := by
      filter_upwards [ae_restrict_mem hs] with p hp
      simp only [Set.mem_setOf_eq] at hp
      rw [hFm, ENNReal.ofReal_eq_zero.mpr (le_of_lt (by linarith : (0:ℝ) < -(G p)))]
    have h1 := congrFun heq {p : ℝ × ℝ | 0 < G p}
    rw [withDensity_apply Fp hs, withDensity_apply Fm hs,
      lintegral_congr_ae hae1, lintegral_congr_ae hae2, lintegral_zero] at h1
    have h1' : ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (G p) ∂(vol2.restrict {p : ℝ × ℝ | 0 < G p}) = 0 := h1
    have h2 := (lintegral_eq_zero_iff hmeasG).mp h1'
    have hsub : {p : ℝ × ℝ | 0 < G p} ⊆ {p : ℝ × ℝ | ENNReal.ofReal (G p) ≠ 0} := by
      intro p hp
      simp only [Set.mem_setOf_eq, ne_eq]
      intro hcon
      have hcon' := ENNReal.ofReal_eq_zero.mp hcon
      simp only [Set.mem_setOf_eq] at hp
      omega
    calc vol2 {p : ℝ × ℝ | 0 < G p}
        = (vol2.restrict {p : ℝ × ℝ | 0 < G p}) {p : ℝ × ℝ | 0 < G p} := by
          rw [Measure.restrict_apply hs, Set.inter_self]
      _ ≤ (vol2.restrict {p : ℝ × ℝ | 0 < G p}) {p : ℝ × ℝ | ENNReal.ofReal (G p) ≠ 0} :=
          measure_mono hsub
      _ = 0 := ae_iff.mp h2
  have hneg : vol2 {p : ℝ × ℝ | G p < 0} = 0 := by
    have hs : MeasurableSet {p : ℝ × ℝ | G p < 0} := by measurability
    have hae1 : ∀ᵐ p ∂(vol2.restrict {p : ℝ × ℝ | G p < 0}), Fp p = 0 := by
      filter_upwards [ae_restrict_mem hs] with p hp
      simp only [Set.mem_setOf_eq] at hp
      rw [hFp, ENNReal.ofReal_eq_zero.mpr (le_of_lt (by linarith : (0:ℝ) < -(G p)))]
    have hae2 : ∀ᵐ p ∂(vol2.restrict {p : ℝ × ℝ | G p < 0}), Fm p = ENNReal.ofReal (-(G p)) := by
      filter_upwards [ae_restrict_mem hs] with p hp
      simp only [Set.mem_setOf_eq] at hp
      rw [hFm, max_eq_left (le_of_lt (by linarith : (0:ℝ) < -(G p)))]
    have h1 := congrFun heq {p : ℝ × ℝ | G p < 0}
    rw [withDensity_apply Fp hs, withDensity_apply Fm hs,
      lintegral_congr_ae hae1, lintegral_congr_ae hae2, lintegral_zero] at h1
    have h1' : ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (-(G p)) ∂(vol2.restrict {p : ℝ × ℝ | G p < 0}) = 0 := h1
    have h2 := (lintegral_eq_zero_iff (by measurability)).mp h1'
    have hsub : {p : ℝ × ℝ | G p < 0} ⊆ {p : ℝ × ℝ | ENNReal.ofReal (-(G p)) ≠ 0} := by
      intro p hp
      simp only [Set.mem_setOf_eq, ne_eq]
      intro hcon
      have hcon' := ENNReal.ofReal_eq_zero.mp hcon
      simp only [Set.mem_setOf_eq] at hp
      omega
    calc vol2 {p : ℝ × ℝ | G p < 0}
        = (vol2.restrict {p : ℝ × ℝ | G p < 0}) {p : ℝ × ℝ | G p < 0} := by
          rw [Measure.restrict_apply hs, Set.inter_self]
      _ ≤ (vol2.restrict {p : ℝ × ℝ | G p < 0}) {p : ℝ × ℝ | ENNReal.ofReal (-(G p)) ≠ 0} :=
          measure_mono hsub
      _ = 0 := ae_iff.mp h2
  have hae : G =ᵐ[vol2] 0 := by
    rw [ae_iff]
    have hunion : {p : ℝ × ℝ | G p ≠ 0}
        = {p : ℝ × ℝ | 0 < G p} ∪ {p : ℝ × ℝ | G p < 0} := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_union, ne_eq]
      by_cases hp0 : G p = 0
      · simp [hp0]
      · by_cases hp1 : 0 < G p
        · simp [hp1]
        · simp [hp0, hp1, lt_of_le_of_ne (le_of_not_gt hp1) (fun h => hp0 h.symm)]
    rw [hunion, measure_union_null hpos hneg]
  exact Lp.ext (hGae.trans hae)

/-- **The tensor-ONB completeness (`hsec` discharged)**: for a complete orthonormal family
`v` of `L²`, the section family `p ↦ prodKernel (v p.2) (v p.1)` has trivial orthogonal
complement in the kernel space `L²(vol2)` — its span is dense. -/
theorem sections_span_orthogonal_eq_bot {ι : Type*} {v : ι → L2}
    (hcomp : (span ℝ (Set.range v))ᗮ = ⊥) :
    (span ℝ (Set.range (fun p : ι × ι => prodKernel (v p.2) (v p.1))))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hx' : ∀ y ∈ span ℝ (Set.range fun p : ι × ι => prodKernel (v p.2) (v p.1)),
      inner ℝ y x = 0 := (Submodule.mem_orthogonal _ x).mp hx
  refine sections_orthogonal_eq_zero hcomp x fun p => ?_
  have hxmem : prodKernel (v p.2) (v p.1)
      ∈ span ℝ (Set.range fun q : ι × ι => prodKernel (v q.2) (v q.1)) :=
    Submodule.subset_span (Set.mem_range.mpr ⟨p, rfl⟩)
  rw [real_inner_comm]
  exact hx' _ hxmem

/-! ### D. Unconditional composition: the reverse HS-norm identity -/

/-- **The reverse HS-norm identity, unconditional**: for a complete orthonormal family `v`
of `L²`, `hsNorm K² = ∑' j, ‖TOp K (v j)‖²`.  This closes the Parseval boundary carried by
`Hurst.ReverseParseval.hsNorm_sq_eq_tsum_norm_sq_of_complete_sections`, whose `hsec`
clause is now supplied by `sections_span_orthogonal_eq_bot`. -/
theorem hsNorm_sq_eq_tsum_norm_sq_of_orthonormal_complete {ι : Type*} {v : ι → L2}
    (hv : Orthonormal ℝ v) (hcomp : (span ℝ (Set.range v))ᗮ = ⊥) :
    hsNorm K ^ 2 = ∑' j, ‖TOp K hK (v j)‖ ^ 2 :=
  hsNorm_sq_eq_tsum_norm_sq_of_complete_sections hv hcomp
    (sections_span_orthogonal_eq_bot hcomp)

/-- **The eigenfamily corollary, unconditional**: for a complete orthonormal eigenfamily
`v j` of `L²` with eigenvalues `κ j` (`TOp K (v j) = κ j • v j`),
`hsNorm K² = ∑' j, κ j²`. -/
theorem hsNorm_sq_eq_tsum_eigenvalue_sq_of_orthonormal_complete {ι : Type*} {v : ι → L2}
    {κ : ι → ℝ} (hv : Orthonormal ℝ v) (hcomp : (span ℝ (Set.range v))ᗮ = ⊥)
    (he : ∀ i, TOp K hK (v i) = κ i • v i) :
    hsNorm K ^ 2 = ∑' i, κ i ^ 2 :=
  hsNorm_sq_eq_tsum_eigenvalue_sq_of_complete_sections hv hcomp
    (sections_span_orthogonal_eq_bot hcomp) he

end HS

end
