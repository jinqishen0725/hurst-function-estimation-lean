import Hurst.SecondScaleFineComponents
import Hurst.ScaleMeasurability

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology ENNReal
namespace Hurst
set_option maxHeartbeats 1500000

theorem integral_abs_sub_le_sqrt_variance_add_bias {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (θ : ℝ)
    (hX : MemLp X 2 P) :
    (∫ x,|X x-θ| ∂P)≤Real.sqrt (Var[X;P])+|(∫ x,X x ∂P)-θ| := by
  let μ := ∫ x,X x ∂P
  have hc : MemLp (fun x => X x-μ) 2 P := hX.sub (memLp_const μ)
  have hL2 := integral_abs_le_sqrt_second_moment P (fun x => X x-μ) hc
  have hcenter : (∫ x,(X x-μ)^2 ∂P)=Var[X;P] := by
    have h := mse_decomposition X μ hX
    dsimp [μ] at h ⊢
    nlinarith
  rw [hcenter] at hL2
  have hpoint : ∀ x,|X x-θ|≤|X x-μ|+|μ-θ| := by
    intro x
    rw [show X x-θ=(X x-μ)+(μ-θ) by ring]
    exact abs_add_le _ _
  calc
    (∫ x,|X x-θ| ∂P)≤∫ x,|X x-μ|+|μ-θ| ∂P :=
      integral_mono ((hX.sub (memLp_const θ)).integrable one_le_two |>.abs)
        (hc.integrable one_le_two |>.abs |>.add (integrable_const |μ-θ|)) hpoint
    _=(∫ x,|X x-μ| ∂P)+|μ-θ| := by
      rw [integral_add (hc.integrable one_le_two |>.abs) (integrable_const _),integral_const]
      simp
    _≤Real.sqrt (Var[X;P])+|(∫ x,X x ∂P)-θ| := by
      have h := add_le_add_left hL2 |μ-θ|
      dsimp [μ] at h ⊢
      linarith

theorem finite_average_integral_abs_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (m : ℕ) (hm : 0<m) (X : Fin m → Ω → ℝ) (R : ℝ)
    (hX : ∀ j,Integrable (X j) P) (hb : ∀ j,(∫ x,|X j x| ∂P)≤R) :
    (∫ x,|(∑ j,X j x)/(m:ℝ)| ∂P)≤R := by
  have hmR : (0:ℝ)<m := by exact_mod_cast hm
  have hsum : Integrable (fun x => ∑ j,|X j x|) P :=
    integrable_finsetSum _ (fun j _ => (hX j).abs)
  have havg : Integrable (fun x => (∑ j,X j x)/(m:ℝ)) P := by
    exact (integrable_finsetSum _ (fun j _ => hX j)).div_const _
  have hp : ∀ x,|(∑ j,X j x)/(m:ℝ)|≤(∑ j,|X j x|)/(m:ℝ) := by
    intro x
    rw [abs_div,abs_of_pos hmR]
    exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hmR.le
  have hi := integral_mono havg.abs (hsum.div_const _) hp
  rw [integral_div,integral_finsetSum _ (fun j _ => (hX j).abs)] at hi
  apply hi.trans
  apply (div_le_iff₀ hmR).mpr
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => hb j)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_comm] using hs

/-- Complete finite-sample L1 estimate behind the q=2 unknown-scale short-memory
transfer.  Every term is obtained from the actual harmonizable Gaussian model. -/
theorem hurstHolder_q2_logScale_fine_L1 (p a b M u : ℝ)
    (hp : 2≤p) (ha : 0<a) (hb : b<1) (hab : a≤b) (hM : 0≤M)
    (hu : u<1) (hbu : b<u) :
    ∃ N₀>0,∃ C₁≥0,∃ C₂≥0,∃ C₃≥0,∃ C₄≥0,∃ C₅≥0,
      ∀ᶠ n : ℕ in atTop,∀ f : ℝ → ℝ,∀ hf : f∈hurstHolderClass p M,
      MapsTo f (Ioo (0:ℝ) 1) (Icc a b) → ∀ m : ℕ,0<m →
      ∀ δ : ℝ,0<δ → δ≤1/2 → N₀≤(n:ℝ)*δ → 1≤(m:ℝ)*δ → 1≤Real.log n →
      MemLp (q2LogScaleEstimator (a/2) u (Nat.ceil p-1) n m δ) 2
        (featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) ∧
      (∫ x,|q2LogScaleEstimator (a/2) u (Nat.ceil p-1) n m δ x|
        ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))≤
        Real.sqrt (C₁*(Real.log n)^2/(n:ℝ))+C₂*δ^p+
        Real.log n*gridCovarianceError (1/2) C₃ n+
        Real.sqrt (C₄/(n:ℝ))+C₅*(δ^p+gridCovarianceError (1/2) 1 n+
          1/((n:ℝ)*δ)+(δ^p)^2+(gridCovarianceError (1/2) 1 n)^2) := by
  obtain ⟨Nl,hNl,Bl,hBl,El,hEl,hlin⟩ := hurstHolder_q2_linearScale_fine_bias p a b M hp ha hb hab hM
  obtain ⟨Nv,hNv,Vl,hVl,Nvn,hNvn,hvar⟩ := hurstHolder_q2_linearScale_variance p a b M (Nat.ceil p-1) hp ha hb hab hM
  obtain ⟨Nj,hNj,Vj,hVj,hjvar⟩ := hurstHolder_q2_coefficientAveraged_pilot_variance p a b M (Nat.ceil p-1) hp ha hb hab hM
  obtain ⟨Np,hNp,Bp,hBp,Ep,hEp,Vp,hVp,Npn,hNpn,hpm⟩ := hurstHolder_q2_pilot_moments p a b M hp ha hb hab hM
  obtain ⟨_,_,hm₁⟩ := hurstHolder_common_stride_log_mean p a b M 1 4 hp ha hb hab hM (by norm_num) (by norm_num)
  obtain ⟨_,_,hm₂⟩ := hurstHolder_common_stride_log_mean p a b M 2 4 hp ha hb hab hM (by norm_num) (by norm_num)
  let d := min (a/2) (u-b)
  have hd : 0<d := lt_min (by linarith) (by linarith)
  obtain ⟨Cq,hCq,hquad⟩ := q2LogCorrection_clipped_quadratic (a/2) u d (by linarith) hu (by linarith) hd
  obtain ⟨Kd,hKd,hderiv⟩ := q2LogCorrection_uniform_derivative a b ha hb
  let N₀ := max (max Nl Nv) (max Nj Np)
  refine ⟨N₀,lt_of_lt_of_le hNl ((le_max_left Nl Nv).trans (le_max_left _ _)),Vl,hVl,Bl,hBl,El,hEl,
    Vj*Kd^2,by positivity,max 1 (Kd*(Bp+Ep)+Cq*(Vp+2*Bp^2+2*Ep^2)),by positivity,?_⟩
  filter_upwards [hlin,hjvar,hm₁,hm₂,eventually_ge_atTop (max Nvn Npn)] with n hlin hjvar hm1 hm2 hn
  intro f hf hF m hm δ hδ hδhalf hnd hmd hL
  have hn4 : 4≤n := hNvn.trans ((le_max_left _ _).trans hn)
  have hnP : Npn≤n := (le_max_right _ _).trans hn
  have hn0 : 0<n := by omega
  have hNl' : Nl≤(n:ℝ)*δ := (le_max_left Nl Nv).trans (le_max_left (max Nl Nv) (max Nj Np)) |>.trans hnd
  have hNv' : Nv≤(n:ℝ)*δ := (le_max_right Nl Nv).trans (le_max_left (max Nl Nv) (max Nj Np)) |>.trans hnd
  have hNj' : Nj≤(n:ℝ)*δ := (le_max_left Nj Np).trans (le_max_right (max Nl Nv) (max Nj Np)) |>.trans hnd
  have hNp' : Np≤(n:ℝ)*δ := (le_max_right Nj Np).trans (le_max_right (max Nl Nv) (max Nj Np)) |>.trans hnd
  let P := featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
  let L := Real.log n
  let X := q2LinearScale (Nat.ceil p-1) n m δ
  let H := fun j : Fin m => f (grid m j.val)
  let pilot := fun j : Fin m => q2Pilot (Nat.ceil p-1) n δ (grid m j.val)
  let derivs := fun j : Fin m => deriv q2LogCorrection (H j)
  let J := fun x => (∑ j : Fin m,derivs j*(pilot j x-H j))/(m:ℝ)
  let R := fun x => (∑ j : Fin m,(q2LogCorrection (clip (a/2) u (pilot j x))-q2LogCorrection (H j)-
    (pilot j x-H j)*derivs j))/(m:ℝ)
  let θ := (∑ j : Fin m,(q2LogCorrection (H j)+gaussianLogSquareMean))/(m:ℝ)
  obtain ⟨hXmem,hXvar⟩ := hvar n ((le_max_left _ _).trans hn) hL f hf hF m hm δ hδ hδhalf hNv' hmd
  have hXbias := hlin f hf hF m hm δ hδ hδhalf hNl' hL
  have hdb : ∀ j,|derivs j|≤Kd := fun j => hderiv (H j) (hF (grid_mem m j.val hm j.isLt))
  obtain ⟨hJPilotMem,hJPilotVar⟩ := hjvar f hf hF m hm δ hδ hδhalf hNj' hmd derivs Kd hKd hdb
  obtain ⟨g,hg,heq,hgmap,hpilotMom⟩ := hpm f hf hF
  have hjint : ∀ j : Fin m,grid m j.val∈Ioo (0:ℝ) 1 := fun j => grid_mem m j.val hm j.isLt
  have hjclosed : ∀ j : Fin m,grid m j.val∈Icc (0:ℝ) 1 := fun j => ⟨(hjint j).1.le,(hjint j).2.le⟩
  have hHinterior : ∀ j : Fin m,H j∈Icc (a/2+d) (u-d) := by
    intro j
    have hh := hF (hjint j)
    dsimp [H,d]
    constructor
    · nlinarith [min_le_left (a/2) (u-b),hh.1]
    · nlinarith [min_le_right (a/2) (u-b),hh.2]
  have hpMom : ∀ j,MemLp (pilot j) 2 P ∧
      |(∫ x,pilot j x ∂P)-H j|≤Bp*δ^p+gridCovarianceError (1/2) Ep n ∧
      Var[pilot j;P]≤Vp/((n:ℝ)*δ) := by
    intro j
    have h := hpilotMom n hnP δ (grid m j.val) hδ hδhalf (hjclosed j) hNp'
    rw [← heq (hjint j)] at h
    exact h
  have hJmem : MemLp J 2 P := by
    have hc : MemLp (fun _ => (∑ j : Fin m,derivs j*H j)/(m:ℝ)) 2 P := memLp_const _
    have hid : J = fun x => (∑ j : Fin m,derivs j*pilot j x)/(m:ℝ)-
        (∑ j : Fin m,derivs j*H j)/(m:ℝ) := by
      funext x
      dsimp [J]
      simp only [mul_sub,Finset.sum_sub_distrib]
      rw [sub_div]
    rw [hid]
    exact hJPilotMem.sub hc
  have hJvar : Var[J;P]≤Vj*Kd^2/(n:ℝ) := by
    have hid : J = fun x => (∑ j : Fin m,derivs j*pilot j x)/(m:ℝ)-
        (∑ j : Fin m,derivs j*H j)/(m:ℝ) := by
      funext x
      dsimp [J]
      simp only [mul_sub,Finset.sum_sub_distrib]
      rw [sub_div]
    rw [hid,variance_sub_const hJPilotMem.aestronglyMeasurable]
    exact hJPilotVar
  have hJbias : |∫ x,J x ∂P|≤Kd*(Bp*δ^p+gridCovarianceError (1/2) Ep n) := by
    have hmR : (0:ℝ)<m := by exact_mod_cast hm
    have hInt : ∀ j,Integrable (fun x => derivs j*(pilot j x-H j)) P := fun j =>
      (((hpMom j).1.sub (memLp_const _)).integrable one_le_two).const_mul _
    rw [integral_div,integral_finsetSum _ (fun j _ => hInt j)]
    apply finite_average_abs_le m hm _ _
    intro j
    rw [integral_const_mul,abs_mul]
    have hi : (∫ x,pilot j x-H j ∂P)=(∫ x,pilot j x ∂P)-H j := by
      rw [integral_sub ((hpMom j).1.integrable one_le_two) (integrable_const _),integral_const]
      simp
    rw [hi]
    exact mul_le_mul (hdb j) (hpMom j).2.1 (abs_nonneg _) hKd
  have hRint : ∀ j,Integrable (fun x => q2LogCorrection (clip (a/2) u (pilot j x))-q2LogCorrection (H j)-
      (pilot j x-H j)*derivs j) P := by
    intro j
    have hmeas : AEStronglyMeasurable (fun x => q2LogCorrection (clip (a/2) u (pilot j x))-
        q2LogCorrection (H j)-(pilot j x-H j)*derivs j) P := by
      apply AEStronglyMeasurable.sub
      · apply AEStronglyMeasurable.sub
        · exact ((q2LogCorrection_smooth.continuousOn.mono (fun y hy =>
            ⟨lt_of_lt_of_le (by linarith : 0<a/2) hy.1,hy.2.trans_lt hu⟩)).comp_continuous
            (clip_continuous (a/2) u) (fun y => clip_mem (a/2) u y (by linarith))).comp_aestronglyMeasurable
              (hpMom j).1.aestronglyMeasurable
        · exact aestronglyMeasurable_const
      · exact ((hpMom j).1.aestronglyMeasurable.sub aestronglyMeasurable_const).mul aestronglyMeasurable_const
    have hdom : ∀ x,‖q2LogCorrection (clip (a/2) u (pilot j x))-q2LogCorrection (H j)-
        (pilot j x-H j)*derivs j‖≤Cq*(pilot j x-H j)^2 := by
      intro x
      dsimp [derivs]
      simpa only [Real.norm_eq_abs,sq_abs] using hquad (pilot j x) (H j) (hHinterior j)
    have hsq : Integrable (fun x => (pilot j x-H j)^2) P :=
      ((hpMom j).1.sub (memLp_const _)).integrable_sq
    exact Integrable.mono' (hsq.const_mul Cq) hmeas (Filter.Eventually.of_forall hdom)
  have hRbound : (∫ x,|R x| ∂P)≤Cq*(Vp/((n:ℝ)*δ)+2*(Bp*δ^p)^2+
      2*(gridCovarianceError (1/2) Ep n)^2) := by
    apply finite_average_integral_abs_le P m hm _ _ hRint
    intro j
    have hquadj := hquad
    have hsq : Integrable (fun x => (pilot j x-H j)^2) P :=
      ((hpMom j).1.sub (memLp_const _)).integrable_sq
    have hi := integral_mono (hRint j).abs
      (hsq.const_mul Cq) (fun x => by
        dsimp [derivs]
        simpa only [Real.norm_eq_abs,sq_abs] using hquadj (pilot j x) (H j) (hHinterior j))
    rw [integral_const_mul,mse_decomposition (pilot j) (H j) (hpMom j).1] at hi
    have hbias2 := pow_le_pow_left₀ (abs_nonneg _) (hpMom j).2.1 2
    rw [sq_abs] at hbias2
    have hv := (hpMom j).2.2
    nlinarith [sq_nonneg (Bp*δ^p-gridCovarianceError (1/2) Ep n)]
  have hSmem := q2LogScaleEstimator_memLp (Nat.ceil p-1) n m δ (a/2) u (by linarith) hu (by linarith)
    _ (fun i => (hm1 f hf hF i).1) (fun i => (hm2 f hf hF i).1)
  refine ⟨hSmem,?_⟩
  have hdecomp : q2LogScaleEstimator (a/2) u (Nat.ceil p-1) n m δ =
      fun x => (X x-θ)-J x-R x := by
    funext x
    rw [q2LogScaleEstimator_decomposition (a/2) u (Nat.ceil p-1) n m hm δ f x]
    have hsum : (∑ j : Fin m,derivs j*(pilot j x-H j))+
        (∑ j : Fin m,(q2LogCorrection (clip (a/2) u (pilot j x))-q2LogCorrection (H j)-
          (pilot j x-H j)*derivs j))=
        ∑ j : Fin m,(q2LogCorrection (clip (a/2) u (pilot j x))-q2LogCorrection (H j)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    dsimp [X,θ,J,R,H,pilot]
    dsimp [H,pilot] at hsum
    have hmR : (m:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hm)
    field_simp
    linarith
  have hRintegrable : Integrable R P := by
    dsimp [R]
    exact (integrable_finsetSum _ (fun j _ => hRint j)).div_const _
  have hpoint : ∀ x,|(X x-θ)-J x-R x|≤|X x-θ|+|J x|+|R x| := by
    intro x
    calc
      |(X x-θ)-J x-R x| ≤ |(X x-θ)-J x|+|R x| := abs_sub _ _
      _ ≤ |X x-θ|+|J x|+|R x| := by
        gcongr
        exact abs_sub _ _
  have htargetint : Integrable (fun x => (X x-θ)-J x-R x) P := by
    rw [← hdecomp]
    exact hSmem.integrable one_le_two
  rw [hdecomp]
  have hmono := integral_mono
    htargetint.abs
    (((hXmem.sub (memLp_const θ)).integrable one_le_two).abs.add
      ((hJmem.integrable one_le_two).abs) |>.add hRintegrable.abs)
    hpoint
  change (∫ x,|(X x-θ)-J x-R x| ∂P)≤
      ∫ x,(|X x-θ|+|J x|)+|R x| ∂P at hmono
  have hAint : Integrable (fun x => |X x-θ|) P :=
    (hXmem.sub (memLp_const θ)).integrable one_le_two |>.abs
  have hJint : Integrable (fun x => |J x|) P := (hJmem.integrable one_le_two).abs
  have hrhs : (∫ x,(|X x-θ|+|J x|)+|R x| ∂P)=
      (∫ x,|X x-θ| ∂P)+(∫ x,|J x| ∂P)+(∫ x,|R x| ∂P) := by
    calc
      _=(∫ x,|X x-θ|+|J x| ∂P)+(∫ x,|R x| ∂P) := by
        simpa only [Pi.add_apply] using integral_add (hAint.add hJint) hRintegrable.abs
      _=((∫ x,|X x-θ| ∂P)+(∫ x,|J x| ∂P))+(∫ x,|R x| ∂P) := by
        rw [integral_add hAint hJint]
  rw [hrhs] at hmono
  · have hXabs := integral_abs_sub_le_sqrt_variance_add_bias P X θ hXmem
    have hJabs := integral_abs_sub_le_sqrt_variance_add_bias P J 0 hJmem
    simp only [sub_zero] at hJabs
    have hsX : Real.sqrt (Var[X;P])≤Real.sqrt (Vl*(Real.log n)^2/(n:ℝ)) :=
      Real.sqrt_le_sqrt hXvar
    have hsJ : Real.sqrt (Var[J;P])≤Real.sqrt (Vj*Kd^2/(n:ℝ)) :=
      Real.sqrt_le_sqrt hJvar
    have hgridEp : gridCovarianceError (1/2) Ep n=
        Ep*gridCovarianceError (1/2) 1 n := by
      unfold gridCovarianceError
      ring
    have hlarge : Kd*(Bp+Ep)+Cq*(Vp+2*Bp^2+2*Ep^2)≤
        max 1 (Kd*(Bp+Ep)+Cq*(Vp+2*Bp^2+2*Ep^2)) := le_max_right _ _
    have hcoeff : 0≤Kd*(Bp+Ep)+Cq*(Vp+2*Bp^2+2*Ep^2) := by positivity
    have hδp : 0≤δ^p := Real.rpow_nonneg hδ.le p
    have hge : 0≤gridCovarianceError (1/2) 1 n := by
      unfold gridCovarianceError
      have hnR : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
      have hl : 0≤Real.log (2*(n:ℝ)) := Real.log_nonneg (by linarith)
      positivity
    have hndelta : 0≤1/((n:ℝ)*δ) := by positivity
    have hJR : |∫ x,J x ∂P|+(∫ x,|R x| ∂P)≤
        max 1 (Kd*(Bp+Ep)+Cq*(Vp+2*Bp^2+2*Ep^2))*
          (δ^p+gridCovarianceError (1/2) 1 n+1/((n:ℝ)*δ)+
            (δ^p)^2+(gridCovarianceError (1/2) 1 n)^2) := by
      rw [hgridEp] at hJbias hRbound
      have hpre := add_le_add hJbias hRbound
      apply hpre.trans
      have hBp : 0≤Bp := hBp
      have hEp : 0≤Ep := hEp
      have hVp : 0≤Vp := hVp
      have hCq : 0≤Cq := hCq
      have hKd : 0≤Kd := hKd
      let A := Kd*(Bp+Ep)+Cq*(Vp+2*Bp^2+2*Ep^2)
      have hc1 : Kd*Bp≤A := by
        dsimp [A]
        exact (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hEp) hKd).trans
          (le_add_of_nonneg_right (mul_nonneg hCq (by positivity)))
      have hc2 : Kd*Ep≤A := by
        dsimp [A]
        exact (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hBp) hKd).trans
          (le_add_of_nonneg_right (mul_nonneg hCq (by positivity)))
      have hc3 : Cq*Vp≤A := by
        dsimp [A]
        have hins : Vp≤Vp+2*Bp^2+2*Ep^2 :=
          (le_add_of_nonneg_right (by positivity)).trans (le_add_of_nonneg_right (by positivity))
        have h : Cq*Vp≤Cq*(Vp+2*Bp^2+2*Ep^2) :=
          mul_le_mul_of_nonneg_left hins hCq
        exact h.trans (le_add_of_nonneg_left (mul_nonneg hKd (by positivity)))
      have hc4 : 2*Cq*Bp^2≤A := by
        dsimp [A]
        have h : 2*Cq*Bp^2≤Cq*(Vp+2*Bp^2+2*Ep^2) := by
          have hinside : 2*Bp^2≤Vp+2*Bp^2+2*Ep^2 :=
            (le_add_of_nonneg_left hVp).trans (le_add_of_nonneg_right (by positivity))
          calc
            2*Cq*Bp^2=Cq*(2*Bp^2) := by ring
            _≤Cq*(Vp+2*Bp^2+2*Ep^2) := mul_le_mul_of_nonneg_left hinside hCq
        exact h.trans (le_add_of_nonneg_left (mul_nonneg hKd (by positivity)))
      have hc5 : 2*Cq*Ep^2≤A := by
        dsimp [A]
        have h : 2*Cq*Ep^2≤Cq*(Vp+2*Bp^2+2*Ep^2) := by
          have hinside : 2*Ep^2≤Vp+2*Bp^2+2*Ep^2 :=
            le_add_of_nonneg_left (by positivity)
          calc
            2*Cq*Ep^2=Cq*(2*Ep^2) := by ring
            _≤Cq*(Vp+2*Bp^2+2*Ep^2) :=
              mul_le_mul_of_nonneg_left hinside hCq
        exact h.trans (le_add_of_nonneg_left (mul_nonneg hKd (by positivity)))
      calc
        Kd*(Bp*δ^p+Ep*gridCovarianceError (1/2) 1 n)+
            Cq*(Vp/((n:ℝ)*δ)+2*(Bp*δ^p)^2+
              2*(Ep*gridCovarianceError (1/2) 1 n)^2)
          ≤ (Kd*(Bp+Ep)+Cq*(Vp+2*Bp^2+2*Ep^2))*
              (δ^p+gridCovarianceError (1/2) 1 n+1/((n:ℝ)*δ)+
                (δ^p)^2+(gridCovarianceError (1/2) 1 n)^2) := by
            have h1 := mul_le_mul_of_nonneg_right hc1 hδp
            have h2 := mul_le_mul_of_nonneg_right hc2 hge
            have h3 := mul_le_mul_of_nonneg_right hc3 hndelta
            have h4 := mul_le_mul_of_nonneg_right hc4 (sq_nonneg (δ^p))
            have h5 := mul_le_mul_of_nonneg_right hc5
              (sq_nonneg (gridCovarianceError (1/2) 1 n))
            calc
              _=Kd*Bp*δ^p+Kd*Ep*gridCovarianceError (1/2) 1 n+
                  Cq*Vp*(1/((n:ℝ)*δ))+(2*Cq*Bp^2)*(δ^p)^2+
                  (2*Cq*Ep^2)*(gridCovarianceError (1/2) 1 n)^2 := by ring
              _≤A*δ^p+A*gridCovarianceError (1/2) 1 n+A*(1/((n:ℝ)*δ))+
                  A*(δ^p)^2+A*(gridCovarianceError (1/2) 1 n)^2 :=
                add_le_add (add_le_add (add_le_add (add_le_add h1 h2) h3) h4) h5
              _=_ := by dsimp [A]; ring
          _ ≤ max 1 (Kd*(Bp+Ep)+Cq*(Vp+2*Bp^2+2*Ep^2))*
              (δ^p+gridCovarianceError (1/2) 1 n+1/((n:ℝ)*δ)+
                (δ^p)^2+(gridCovarianceError (1/2) 1 n)^2) := by
            gcongr
    calc
      (∫ x,|(X x-θ)-J x-R x| ∂P)
          ≤ (∫ x,|X x-θ| ∂P)+(∫ x,|J x| ∂P)+(∫ x,|R x| ∂P) := hmono
      _ ≤ (Real.sqrt (Var[X;P])+|(∫ x,X x ∂P)-θ|)+
          (Real.sqrt (Var[J;P])+|∫ x,J x ∂P|)+(∫ x,|R x| ∂P) := by
            gcongr
      _ ≤ Real.sqrt (Vl*(Real.log n)^2/(n:ℝ))+
          (Bl*δ^p+Real.log n*gridCovarianceError (1/2) El n)+
          Real.sqrt (Vj*Kd^2/(n:ℝ))+
          (|∫ x,J x ∂P|+(∫ x,|R x| ∂P)) := by
            linarith [hsX,hXbias,hsJ]
      _ ≤ Real.sqrt (Vl*(Real.log n)^2/(n:ℝ))+Bl*δ^p+
          Real.log n*gridCovarianceError (1/2) El n+
          Real.sqrt (Vj*Kd^2/(n:ℝ))+
          max 1 (Kd*(Bp+Ep)+Cq*(Vp+2*Bp^2+2*Ep^2))*
            (δ^p+gridCovarianceError (1/2) 1 n+1/((n:ℝ)*δ)+
              (δ^p)^2+(gridCovarianceError (1/2) 1 n)^2) := by
            linarith

end Hurst
