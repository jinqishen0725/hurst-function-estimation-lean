import Hurst.InverseRepair

noncomputable section
open Set
namespace Hurst

theorem clippedInverse_calibration_excess (G : ℝ → ℝ) (a b m H d y x : ℝ)
    (hm : 0<m) (hd : 0<d) (hHa : a+d≤H) (hHb : H+d≤b)
    (hG : StrongDecrease G a b m) (hx : ClippedInverseAt G a b y x) :
    |y-G x|≤(y-G H)^2/(m*d) := by
  have hH : H∈Icc a b := ⟨by linarith,by linarith⟩
  have hab : a≤b := hH.1.trans hH.2
  rcases hx.2 with h | h | h
  · rw [h,sub_self,abs_zero]
    positivity
  · obtain ⟨hxa,hy⟩ := h
    rw [hxa]
    have hg := hG a ⟨le_rfl,hab⟩ H hH hH.1
    have hh : m*d≤y-G H := by nlinarith
    have he : 0≤y-G H := (mul_pos hm hd).le.trans hh
    rw [abs_of_nonneg (sub_nonneg.mpr hy)]
    apply (le_div_iff₀ (mul_pos hm hd)).mpr
    have h1 : y-G a≤y-G H := by nlinarith
    have h2 := mul_le_mul_of_nonneg_right h1 (mul_nonneg hm.le hd.le)
    have h3 := mul_le_mul_of_nonneg_left hh he
    nlinarith
  · obtain ⟨hxb,hy⟩ := h
    rw [hxb]
    have hg := hG H hH b ⟨hab,le_rfl⟩ hH.2
    have hh : m*d≤G H-y := by nlinarith
    have he : 0≤G H-y := (mul_pos hm hd).le.trans hh
    rw [abs_of_nonpos (sub_nonpos.mpr hy)]
    apply (le_div_iff₀ (mul_pos hm hd)).mpr
    have h1 : G b-y≤G H-y := by nlinarith
    have h2 := mul_le_mul_of_nonneg_right h1 (mul_nonneg hm.le hd.le)
    have h3 := mul_le_mul_of_nonneg_left hh he
    nlinarith

theorem clippedInverse_linearization (φ : ℝ → ℝ) (a b m c H d K y x : ℝ)
    (hm : 0<m) (hd : 0<d) (hK : 0≤K) (hHa : a+d≤H) (hHb : H+d≤b)
    (hφ : ∀ z∈Icc a b,|φ z-φ H|≤K*|z-H|)
    (hG : StrongDecrease (fun z => -m*z+φ z+c) a b m)
    (hx : ClippedInverseAt (fun z => -m*z+φ z+c) a b y x) :
    |x-H+(y-(-m*H+φ H+c))/m| ≤
      K*|y-(-m*H+φ H+c)|/m^2+(y-(-m*H+φ H+c))^2/(m^2*d) := by
  let G := fun z => -m*z+φ z+c
  have hH : H∈Icc a b := ⟨by linarith,by linarith⟩
  have hcon := clippedInverse_contraction G a b m y (G H) x H hm hG hx ⟨hH,Or.inl rfl⟩
  have hex := clippedInverse_calibration_excess G a b m H d y x hm hd hHa hHb hG hx
  have hphi := (hφ x hx.1).trans (mul_le_mul_of_nonneg_left hcon hK)
  have hid : x-H+(y-G H)/m=((φ x-φ H)+(y-G x))/m := by
    dsimp [G]
    field_simp
    <;> ring
  change |x-H+(y-G H)/m|≤_
  rw [hid,abs_div,abs_of_pos hm]
  calc
    _ ≤ (|φ x-φ H|+|y-G x|)/m := div_le_div_of_nonneg_right (abs_add_le _ _) hm.le
    _ ≤ (K*(|y-G H|/m)+(y-G H)^2/(m*d))/m :=
      div_le_div_of_nonneg_right (add_le_add hphi hex) hm.le
    _ = _ := by dsimp [G]; ring

theorem boundedInverse_linearization (φ : ℝ → ℝ) (a b m c H d K y : ℝ)
    (hm : 0<m) (hd : 0<d) (hK : 0≤K) (hHa : a+d≤H) (hHb : H+d≤b)
    (hc : ContinuousOn (fun z => -m*z+φ z+c) (Icc a b))
    (hφ : ∀ z∈Icc a b,|φ z-φ H|≤K*|z-H|)
    (hG : StrongDecrease (fun z => -m*z+φ z+c) a b m) :
    |boundedInverse (fun z => -m*z+φ z+c) a b y-H+(y-(-m*H+φ H+c))/m| ≤
      K*|y-(-m*H+φ H+c)|/m^2+(y-(-m*H+φ H+c))^2/(m^2*d) :=
  clippedInverse_linearization φ a b m c H d K y _ hm hd hK hHa hHb hφ hG
    (boundedInverse_spec _ a b y (by linarith) hc)

end Hurst
