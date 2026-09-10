import Hurst.HolderJets
import Hurst.SmoothJetBounds
import Hurst.JetComposition

noncomputable section
open Set
open scoped ContDiff
namespace Hurst

/-- A smooth scalar composition preserves the uniform Holder control needed for local bias. -/
theorem hurstHolder_smooth_composite_highest_holder (p a b M : ℝ) (phi : ℝ → ℝ)
    (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1) (hM : 0 ≤ M)
    (hphi : ContDiffOn ℝ (⊤ : ℕ∞) phi (Ioo (0 : ℝ) 1)) :
    ∃ K ≥ 0, ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) →
      ∀ x ∈ Ioo (0 : ℝ) 1, ∀ y ∈ Ioo (0 : ℝ) 1,
      |iteratedDeriv (Nat.ceil p - 1) (phi ∘ f) x - iteratedDeriv (Nat.ceil p - 1) (phi ∘ f) y| ≤
        K * |x - y| ^ (p - (Nat.ceil p - 1 : ℕ)) := by
  classical
  let m := Nat.ceil p - 1
  obtain ⟨P, hP, hphiJet⟩ := smooth_uniform_jet_control phi hphi m a b ha hb
  obtain ⟨J, hJ, hJet⟩ := hurstHolder_uniform_jets p hp
  let A := J * (1 + M)
  let B := 1 + P + A
  let D := (P + 1) * A
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 1 ≤ B := by dsimp [B]; linarith
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hAB : A ≤ B := by dsimp [B]; linarith
  have hPB : P ≤ B := by dsimp [B]; linarith
  have hAD : A ≤ D := by dsimp [D]; nlinarith
  have hPAD : P * A ≤ D := by dsimp [D]; nlinarith
  refine ⟨Fintype.card (OrderedFinpartition m) * ((m + 1 : ℕ) : ℝ) * D * B ^ (m + 1), by positivity, ?_⟩
  intro f hf hF x hx y hy
  have hfc := hurstHolder_contDiff_degree p M hp hM f hf
  have hfx : ContDiffAt ℝ m f x := hfc.contDiffAt (isOpen_Ioo.mem_nhds hx)
  have hfy : ContDiffAt ℝ m f y := hfc.contDiffAt (isOpen_Ioo.mem_nhds hy)
  have hpx : ContDiffAt ℝ m phi (f x) :=
    (hphi.contDiffAt (isOpen_Ioo.mem_nhds (hf.1 hx))).of_le
      (by exact_mod_cast (show (m : ℕ∞) ≤ ⊤ from le_top))
  have hpy : ContDiffAt ℝ m phi (f y) :=
    (hphi.contDiffAt (isOpen_Ioo.mem_nhds (hf.1 hy))).of_le
      (by exact_mod_cast (show (m : ℕ∞) ≤ ⊤ from le_top))
  have hfb : ∀ j ≤ m, |iteratedDeriv j f x| ≤ B ∧ |iteratedDeriv j f y| ≤ B := by
    intro j hj
    exact ⟨((hJet M hM f hf j hj x hx).1).trans hAB, ((hJet M hM f hf j hj y hy).1).trans hAB⟩
  have hfd : ∀ j ≤ m, |iteratedDeriv j f x - iteratedDeriv j f y| ≤ D * |x - y| ^ (p - (m : ℝ)) := by
    intro j hj
    exact ((hJet M hM f hf j hj y hy).2 x hx).trans
      (mul_le_mul_of_nonneg_right hAD (Real.rpow_nonneg (abs_nonneg _) _))
  have hpb : ∀ j ≤ m, |iteratedDeriv j phi (f x)| ≤ B ∧ |iteratedDeriv j phi (f y)| ≤ B := by
    intro j hj
    exact ⟨((hphiJet j hj).1 _ (hF hx)).trans hPB, ((hphiJet j hj).1 _ (hF hy)).trans hPB⟩
  have hpd : ∀ j ≤ m, |iteratedDeriv j phi (f x) - iteratedDeriv j phi (f y)| ≤ D * |x - y| ^ (p - (m : ℝ)) := by
    intro j hj
    have h1 := (hphiJet j hj).2 (f y) (hF hy) (f x) (hF hx)
    have h2 := (hJet M hM f hf 0 (Nat.zero_le _) y hy).2 x hx
    simp only [iteratedDeriv_zero] at h2
    have h3 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ P by linarith)
    have h4 := mul_le_mul_of_nonneg_right hPAD (Real.rpow_nonneg (abs_nonneg (x - y)) (p - (m : ℝ)))
    exact (h1.trans h3).trans (by simpa only [A, m, mul_assoc] using h4)
  exact composite_derivative_difference_bound m f phi x y B D _ hB hD (by positivity) hpx hpy hfx hfy hfb hfd hpb hpd

theorem contDiffOn_differentiable_iteratedDeriv (f : ℝ → ℝ) (m k : ℕ)
    (hf : ContDiffOn ℝ m f (Ioo (0 : ℝ) 1)) (hk : k < m) :
    ∀ x ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ (iteratedDeriv k f) x := by
  have hd0 := hf.differentiableOn_iteratedDerivWithin (m := k) (by exact_mod_cast hk) isOpen_Ioo.uniqueDiffOn
  have hd : DifferentiableOn ℝ (iteratedDeriv k f) (Ioo (0 : ℝ) 1) := by
    apply hd0.congr
    intro u hu
    exact (iteratedDerivWithin_of_isOpen (n := k) isOpen_Ioo hu).symm
  exact fun x hx => hd.differentiableAt (isOpen_Ioo.mem_nhds hx)

/-- Full p-order Taylor remainder of the nonlinear calibration, with the original degree. -/
theorem hurstHolder_smooth_composite_remainder (p a b M : ℝ) (phi : ℝ → ℝ)
    (hp : 2 ≤ p) (ha : 0 < a) (hb : b < 1) (hM : 0 ≤ M)
    (hphi : ContDiffOn ℝ (⊤ : ℕ∞) phi (Ioo (0 : ℝ) 1)) :
    ∃ K ≥ 0, ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) →
      ∀ x ∈ Ioo (0 : ℝ) 1, ∀ y ∈ Ioo (0 : ℝ) 1,
      |(phi ∘ f) y - taylorJet (Nat.ceil p - 1) (phi ∘ f) x y| ≤ K * |y - x| ^ p := by
  let m := Nat.ceil p - 1
  have hmpos : 1 ≤ m := by
    have hceil : 2 ≤ Nat.ceil p := by exact_mod_cast (hp.trans (Nat.le_ceil p))
    dsimp [m]
    omega
  obtain ⟨K, hK, hholder⟩ := hurstHolder_smooth_composite_highest_holder p a b M phi (by linarith) ha hb hM hphi
  refine ⟨K / (m.factorial : ℝ), by positivity, ?_⟩
  intro f hf hF x hx y hy
  have hfc := hurstHolder_contDiff_degree p M (by linarith) hM f hf
  have hpc : ContDiffOn ℝ m phi (Ioo (0 : ℝ) 1) :=
    hphi.of_le (by exact_mod_cast (show (m : ℕ∞) ≤ ⊤ from le_top))
  have hc : ContDiffOn ℝ m (phi ∘ f) (Ioo (0 : ℝ) 1) := hpc.comp hfc hf.1
  have hd := contDiffOn_differentiable_iteratedDeriv (phi ∘ f) m
  have hm : m - 1 + 1 = m := by omega
  have he := holder_taylor_remainder (phi ∘ f) (m - 1) K (p - (m : ℝ)) hK
    (ceil_degree_exponent p (by linarith)).2.1.le
    (fun k hk => hd k hc (by omega))
    (by simpa only [hm] using hholder f hf hF) x y hx hy
  rw [hm] at he
  have hexp : (m : ℝ) + (p - (m : ℝ)) = p := by ring
  simpa only [hexp] using he

end Hurst
