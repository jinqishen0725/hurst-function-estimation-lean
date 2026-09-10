import Hurst.DenseRowSelector

noncomputable section
open Filter
open scoped Topology
namespace Hurst

local instance (p : Prop) : Decidable p := Classical.propDecidable p

def rowSizeHit (R : ℕ → ℕ) (N : ℕ) : Prop := ∃ k, R k = N

def rowSizeHitIndex (R : ℕ → ℕ) (N : ℕ) : ℕ :=
  if h : rowSizeHit R N then Nat.find h else 0

theorem rowSizeHitIndex_spec (R : ℕ → ℕ) (N : ℕ)
    (h : rowSizeHit R N) : R (rowSizeHitIndex R N) = N := by
  simp only [rowSizeHitIndex, dif_pos h]
  exact Nat.find_spec h

theorem rowSizeHitIndex_eq (R : ℕ → ℕ) (hR : StrictMono R) (k : ℕ) :
    rowSizeHitIndex R (R k) = k := by
  apply hR.injective
  exact rowSizeHitIndex_spec R (R k) ⟨k, rfl⟩

/-- On row sizes singled out by `R`, use the requested source row.  On all
other exact row sizes, use the dense predecessor selector. -/
def overrideDenseSelector (R source dense : ℕ → ℕ) (N : ℕ) : ℕ :=
  if h : rowSizeHit R N then source (rowSizeHitIndex R N) else dense N

theorem overrideDenseSelector_at_hit
    (R source dense : ℕ → ℕ) (hR : StrictMono R) (k : ℕ) :
    overrideDenseSelector R source dense (R k) = source k := by
  simp [overrideDenseSelector, rowSizeHit, rowSizeHitIndex_eq R hR k]

theorem tendsto_ite_same
    {α β : Type*} [TopologicalSpace β] {l : Filter α}
    (p : α → Prop) [DecidablePred p] (f g : α → β) (x : β)
    (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 x)) :
    Tendsto (fun a => if p a then f a else g a) l (𝓝 x) := by
  intro s hs
  have hfs : ∀ᶠ a in l, f a ∈ s := hf hs
  have hgs : ∀ᶠ a in l, g a ∈ s := hg hs
  change ∀ᶠ a in l, (if p a then f a else g a) ∈ s
  filter_upwards [hfs, hgs] with a hfa hga
  by_cases ha : p a <;> simp [ha, hfa, hga]

/-- The override selector is cofinal: hit rows use a cofinal requested
subsequence, while non-hit rows use the cofinal dense selector. -/
theorem overrideDenseSelector_tendsto_atTop
    (R source dense : ℕ → ℕ) (hR : StrictMono R)
    (hsource : Tendsto source atTop atTop)
    (hdense : Tendsto dense atTop atTop) :
    Tendsto (overrideDenseSelector R source dense) atTop atTop := by
  rw [tendsto_atTop]
  intro K
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 (hsource.eventually_ge_atTop K)
  have hd := hdense.eventually_ge_atTop K
  filter_upwards [eventually_ge_atTop (R k₀), hd] with N hN hdN
  unfold overrideDenseSelector
  split_ifs with hhit
  · have hspec := rowSizeHitIndex_spec R N hhit
    have hk : k₀ ≤ rowSizeHitIndex R N := by
      apply (hR.le_iff_le).mp
      rw [hspec]
      exact hN
    exact hk₀ _ hk
  · exact hdN

/-- If `R k` is the size of requested source row `source k`, then every hit
row fits exactly.  Non-hit rows inherit the eventual dense-fit property. -/
theorem overrideDenseSelector_eventually_fits
    (m R source dense : ℕ → ℕ)
    (hRsize : ∀ k, R k = m (source k))
    (hdense : ∀ᶠ N : ℕ in atTop, m (dense N) ≤ N) :
    ∀ᶠ N : ℕ in atTop,
      m (overrideDenseSelector R source dense N) ≤ N := by
  filter_upwards [hdense] with N hdN
  unfold overrideDenseSelector
  split_ifs with hhit
  · rw [← hRsize (rowSizeHitIndex R N), rowSizeHitIndex_spec R N hhit]
  · exact hdN

/-- Exact hit rows have ratio one, while the remaining rows inherit the dense
selector ratio. -/
theorem overrideDenseSelector_size_ratio_tendsto_one
    (m R source dense : ℕ → ℕ)
    (hRsize : ∀ k, R k = m (source k))
    (hdense : Tendsto (fun N : ℕ => (m (dense N) : ℝ) / (N : ℝ))
      atTop (𝓝 1)) :
    Tendsto (fun N : ℕ =>
      (m (overrideDenseSelector R source dense N) : ℝ) / (N : ℝ))
      atTop (𝓝 1) := by
  have hmix := tendsto_ite_same (rowSizeHit R)
    (fun _ : ℕ => (1 : ℝ))
    (fun N : ℕ => (m (dense N) : ℝ) / (N : ℝ)) 1
    tendsto_const_nhds hdense
  apply hmix.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  unfold overrideDenseSelector
  split_ifs with hhit
  · rw [← hRsize (rowSizeHitIndex R N), rowSizeHitIndex_spec R N hhit]
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    exact (div_self hNR.ne').symm
  · rfl

end Hurst
