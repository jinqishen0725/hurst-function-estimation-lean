import Hurst.SecondScaleFineL1
import Hurst.OptimalNormalization
import Hurst.OptimalBiasBandwidth
import Hurst.GridBiasRemainderLimit

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Hurst

set_option maxHeartbeats 1200000

theorem optimalLocalBandwidth_log_sq_tendsto_zero (p : ℝ) (hp : 1≤p) :
    Tendsto (fun n : ℕ => optimalLocalBandwidth p n*(Real.log n)^2) atTop (𝓝 0) := by
  have hα : 0<1/(2*p+1) := by positivity
  have ht := nat_log_power_div_rpow_tendsto (1/(2*p+1)) hα 2
  apply squeeze_zero' _ _ ht
  · filter_upwards [optimalLocalBandwidth_eventual_design p 1 hp] with n hn
    exact mul_nonneg hn.2.1.le (sq_nonneg _)
  · filter_upwards [optimalLocalBandwidth_eventual_design p 1 hp] with n hn
    have hu := optimalLocalBandwidth_upper p hp n (by omega) hn.2.2.2.2.2
    have hl2 : 0≤(Real.log (n:ℝ))^2 := sq_nonneg _
    have hm := mul_le_mul_of_nonneg_right hu hl2
    rw [show -1/(2*p+1)=-(1/(2*p+1)) by ring,
      Real.rpow_neg (by positivity : (0:ℝ)≤n)] at hm
    simpa only [div_eq_mul_inv,one_mul,mul_comm] using hm

theorem optimal_scale_log_power_tendsto_zero (r : ℕ) :
    Tendsto (fun n : ℕ => Real.log n*(optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1))
      atTop (𝓝 0) := by
  have hp : (1:ℝ)≤(r:ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) r]
  have hbase := optimalLocalBandwidth_log_sq_tendsto_zero ((r:ℝ)+1) hp
  apply squeeze_zero' _ _ hbase
  · filter_upwards [optimalLocalBandwidth_eventual_design ((r:ℝ)+1) 1 hp] with n hn
    exact mul_nonneg (by linarith [hn.2.2.2.2.2]) (pow_nonneg hn.2.1.le _)
  · filter_upwards [optimalLocalBandwidth_eventual_design ((r:ℝ)+1) 1 hp] with n hn
    have hδ1 : optimalLocalBandwidth ((r:ℝ)+1) n≤1 := hn.2.2.1.trans (by norm_num)
    have hk : 1≤r+1 := by omega
    have hpw : (optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1)≤
        optimalLocalBandwidth ((r:ℝ)+1) n := by
      simpa only [pow_one] using pow_le_pow_of_le_one hn.2.1.le hδ1 hk
    have hlog : 0≤Real.log (n:ℝ) := by linarith [hn.2.2.2.2.2]
    have hlog1 : Real.log (n:ℝ)≤(Real.log n)^2 := by nlinarith [hn.2.2.2.2.2]
    have hh := mul_le_mul hlog1 hpw (pow_nonneg hn.2.1.le _) (sq_nonneg _)
    simpa only [mul_comm] using hh

/-- The grid covariance error is polynomially smaller than the optimal bias.
This is the extra rate needed after the exact `log n` cancellation. -/
theorem q2_grid_error_div_optimal_bias_tendsto_zero (r : ℕ) :
    Tendsto (fun n : ℕ => gridCovarianceError (1/2) 1 n/
      (optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1)) atTop (𝓝 0) := by
  let p : ℝ := (r:ℝ)+1
  let k : ℕ := r+1
  have hkpos : 0<k := by omega
  have hs : (k:ℝ)/(2*p+1)<3/4 := by
    dsimp [p,k]
    push_cast
    have hr0 : (0:ℝ)≤r := Nat.cast_nonneg r
    apply (div_lt_iff₀ (by linarith : 0<2*((r:ℝ)+1)+1)).mpr
    linarith
  have hgrowth := optimalLocalBandwidth_power_growth p (3/4 : ℝ) k hs
  have hinv : Tendsto (fun n : ℕ => ((n:ℝ)^(3/4 : ℝ)*(optimalLocalBandwidth p n)^k)⁻¹)
      atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hgrowth
  have hmesh := mesh_log_rpow_tendsto (-1/4 : ℝ) (by norm_num)
  have hprod := (hmesh.mul hinv).const_mul 2
  simp only [mul_zero,zero_mul] at hprod
  apply hprod.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hδ := optimalLocalBandwidth_pos p n (by omega)
  dsimp [p,k]
  unfold gridCovarianceError
  rw [show (2:ℝ)*(1/2)-2=-1 by norm_num]
  rw [Real.rpow_neg_one]
  have hpow : (n:ℝ)^(-1/4 : ℝ)*((n:ℝ)^(3/4 : ℝ)*
      (optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1))⁻¹=
      (n:ℝ)⁻¹*((optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1))⁻¹ := by
    rw [mul_inv_rev,show ((n:ℝ)^(3/4 : ℝ))⁻¹=(n:ℝ)^(-3/4 : ℝ) by
      rw [← Real.rpow_neg hnR.le]; congr 1; ring]
    calc
      _=((n:ℝ)^(-1/4 : ℝ)*(n:ℝ)^(-3/4 : ℝ))*
          ((optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1))⁻¹ := by ring
      _=(n:ℝ)^(-1 : ℝ)*((optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1))⁻¹ := by
        rw [← Real.rpow_add hnR]
        norm_num
      _=_ := by rw [Real.rpow_neg_one]
  rw [mul_assoc,hpow]
  field_simp
  ring

theorem optimal_q2_fine_bound_scaled_tendsto (r : ℕ) (C₁ C₂ C₃ C₄ C₅ : ℝ)
    (hC₁ : 0≤C₁) (hC₄ : 0≤C₄) :
    Tendsto (fun n : ℕ =>
      Real.sqrt ((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n)*
        (Real.sqrt (C₁*(Real.log n)^2/(n:ℝ))+C₂*(optimalLocalBandwidth ((r:ℝ)+1) n)^((r:ℝ)+1)+
        Real.log n*gridCovarianceError (1/2) C₃ n+
        Real.sqrt (C₄/(n:ℝ))+C₅*((optimalLocalBandwidth ((r:ℝ)+1) n)^((r:ℝ)+1)+
          gridCovarianceError (1/2) 1 n+1/((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n)+
          ((optimalLocalBandwidth ((r:ℝ)+1) n)^((r:ℝ)+1))^2+
          (gridCovarianceError (1/2) 1 n)^2))) atTop (𝓝 0) := by
  let p : ℝ := (r:ℝ)+1
  let k : ℕ := r+1
  let δ := optimalLocalBandwidth p
  let e := gridCovarianceError (1/2) 1
  have hp : (1:ℝ)≤p := by dsimp [p]; linarith [Nat.cast_nonneg (α := ℝ) r]
  have hδ0 : Tendsto δ atTop (𝓝 0) := optimalLocalBandwidth_tendsto_zero p hp
  have hδpos : ∀ᶠ n in atTop,0<δ n :=
    (eventually_gt_atTop 1).mono (fun n hn => optimalLocalBandwidth_pos p n hn)
  have hk : k≠0 := by dsimp [k]; omega
  have hδk : Tendsto (fun n => (δ n)^k) atTop (𝓝 0) := by
    simpa only [zero_pow hk] using hδ0.pow k
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinvlog : Tendsto (fun n : ℕ => (Real.log n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hlog
  have hlogδk : Tendsto (fun n : ℕ => Real.log n*(δ n)^k) atTop (𝓝 0) := by
    simpa only [p,k,δ] using optimal_scale_log_power_tendsto_zero r
  have hgridbias : Tendsto (fun n : ℕ => e n/(δ n)^k) atTop (𝓝 0) := by
    simpa only [p,k,δ,e] using q2_grid_error_div_optimal_bias_tendsto_zero r
  have hs : (k:ℝ)/(2*p+1)<1 := by
    dsimp [p,k]
    push_cast
    have hr0 : (0:ℝ)≤r := Nat.cast_nonneg r
    apply (div_lt_iff₀ (by linarith : 0<2*((r:ℝ)+1)+1)).mpr
    linarith
  have hgrowth := optimalLocalBandwidth_power_growth p 1 k hs
  have hgrowth' : Tendsto (fun n : ℕ => (n:ℝ)*(δ n)^k) atTop atTop := by
    simpa only [Real.rpow_one,δ] using hgrowth
  have hgrowth2 : Tendsto (fun n : ℕ => (n:ℝ)^(2-2*(1/2:ℝ))*(δ n)^k) atTop atTop := by
    simpa only [show (2:ℝ)-2*(1/2)=1 by norm_num,Real.rpow_one] using hgrowth'
  have hgridnorm : Tendsto (fun n : ℕ => e n/(Real.log n*(δ n)^k)) atTop (𝓝 0) := by
    exact gridCovarianceError_scaled_tendsto (1/2) 1 k δ hδpos hgrowth' hgrowth2
  have he0 : Tendsto e atTop (𝓝 0) := gridCovarianceError_tendsto (1/2) 1 (by norm_num)
  have hlogsqδ : Tendsto (fun n : ℕ => δ n*(Real.log n)^2) atTop (𝓝 0) := by
    simpa only [p,δ] using optimalLocalBandwidth_log_sq_tendsto_zero p hp
  have hU : Tendsto (fun n : ℕ =>
      Real.sqrt (C₁*(δ n*(Real.log n)^2))+C₂*(Real.log n)⁻¹+C₃*(e n/(δ n)^k)+
      Real.sqrt (C₄*δ n)+C₅*((Real.log n)⁻¹+e n/(Real.log n*(δ n)^k)+
        Real.log n*(δ n)^k+(δ n)^k*(Real.log n)⁻¹+
        (e n/(Real.log n*(δ n)^k))*e n)) atTop (𝓝 0) := by
    have h1 := (hlogsqδ.const_mul C₁).sqrt
    have h4 := (hδ0.const_mul C₄).sqrt
    have hrest := ((((hinvlog.add hgridnorm).add hlogδk).add
      (hδk.mul hinvlog)).add (hgridnorm.mul he0)).const_mul C₅
    simpa only [mul_zero,Real.sqrt_zero,add_zero] using
      (((h1.add (hinvlog.const_mul C₂)).add (hgridbias.const_mul C₃)).add h4).add hrest
  apply hU.congr'
  filter_upwards [optimalLocalBandwidth_eventual_design p 1 hp] with n hn
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hln : 0<Real.log (n:ℝ) := by linarith [hn.2.2.2.2.2]
  have hd := hn.2.1
  have hb := optimalLocalBandwidth_fluctuation_balance r n hn.1
  have hpow : (δ n)^k=(optimalLocalBandwidth ((r:ℝ)+1) n)^((r:ℝ)+1) := by
    dsimp [δ,p,k]
    rw [← Real.rpow_natCast]
    congr 1
    push_cast
    rfl
  have heC : gridCovarianceError (1/2) C₃ n=C₃*e n := by
    dsimp [e]
    unfold gridCovarianceError
    ring
  have hs1 : Real.sqrt ((n:ℝ)*δ n)*Real.sqrt (C₁*(Real.log n)^2/(n:ℝ))=
      Real.sqrt (C₁*(δ n*(Real.log n)^2)) := by
    rw [← Real.sqrt_mul (by positivity : 0≤(n:ℝ)*δ n)]
    congr 1
    field_simp
  have hs4 : Real.sqrt ((n:ℝ)*δ n)*Real.sqrt (C₄/(n:ℝ))=
      Real.sqrt (C₄*δ n) := by
    rw [← Real.sqrt_mul (by positivity : 0≤(n:ℝ)*δ n)]
    congr 1
    field_simp
  let A := Real.sqrt ((n:ℝ)*δ n)
  have hApos : 0<A := Real.sqrt_pos.2 (mul_pos hnR hd)
  have hdpk : 0<(δ n)^k := pow_pos hd k
  have hAδ : A*(δ n)^k=(Real.log n)⁻¹ := by
    rw [inv_eq_one_div]
    apply (eq_div_iff hln.ne').2
    dsimp [A]
    nlinarith [hb]
  have hAlge : A*Real.log n*e n=e n/(δ n)^k := by
    apply (eq_div_iff hdpk.ne').2
    dsimp [A]
    calc
      Real.sqrt ((n:ℝ)*δ n)*Real.log n*e n*(δ n)^k=
          e n*(Real.sqrt ((n:ℝ)*δ n)*Real.log n*(δ n)^k) := by ring
      _=e n := by rw [hb]; ring
  have hAe : A*e n=e n/(Real.log n*(δ n)^k) := by
    apply (eq_div_iff (mul_pos hln hdpk).ne').2
    calc
      A*e n*(Real.log n*(δ n)^k)=
          e n*(A*Real.log n*(δ n)^k) := by ring
      _=e n := by dsimp [A]; rw [hb]; ring
  have hraw : 1/((n:ℝ)*δ n)=(Real.log n)^2*((δ n)^k)^2 := by
    simpa only [p,k,δ] using optimalLocalBandwidth_raw_variance_balance r n hn.1
  have hAraw : A*(1/((n:ℝ)*δ n))=Real.log n*(δ n)^k := by
    rw [hraw]
    dsimp [A]
    calc
      Real.sqrt ((n:ℝ)*δ n)*((Real.log n)^2*((δ n)^k)^2)=
          (Real.sqrt ((n:ℝ)*δ n)*Real.log n*(δ n)^k)*
            (Real.log n*(δ n)^k) := by ring
      _=Real.log n*(δ n)^k := by rw [hb]; ring
  have hAδsq : A*((δ n)^k)^2=(δ n)^k*(Real.log n)⁻¹ := by
    calc
      A*((δ n)^k)^2=(A*(δ n)^k)*(δ n)^k := by ring
      _=(Real.log n)⁻¹*(δ n)^k := by rw [hAδ]
      _=_ := by ring
  have hAesq : A*(e n)^2=(e n/(Real.log n*(δ n)^k))*e n := by
    calc
      A*(e n)^2=(A*e n)*e n := by ring
      _=_ := by rw [hAe]
  rw [← hs1, ← hs4, heC]
  rw [← hpow]
  symm
  change A*(Real.sqrt (C₁*(Real.log n)^2/(n:ℝ))+C₂*(δ n)^k+
      Real.log n*(C₃*e n)+Real.sqrt (C₄/(n:ℝ))+C₅*((δ n)^k+e n+
        1/((n:ℝ)*δ n)+((δ n)^k)^2+(e n)^2))=
    A*Real.sqrt (C₁*(Real.log n)^2/(n:ℝ))+C₂*(Real.log n)⁻¹+
      C₃*(e n/(δ n)^k)+A*Real.sqrt (C₄/(n:ℝ))+C₅*((Real.log n)⁻¹+
        e n/(Real.log n*(δ n)^k)+Real.log n*(δ n)^k+
        (δ n)^k*(Real.log n)⁻¹+(e n/(Real.log n*(δ n)^k))*e n)
  calc
    A*(Real.sqrt (C₁*(Real.log n)^2/(n:ℝ))+C₂*(δ n)^k+
        Real.log n*(C₃*e n)+Real.sqrt (C₄/(n:ℝ))+C₅*((δ n)^k+e n+
          1/((n:ℝ)*δ n)+((δ n)^k)^2+(e n)^2))=
      A*Real.sqrt (C₁*(Real.log n)^2/(n:ℝ))+C₂*(A*(δ n)^k)+
        C₃*(A*Real.log n*e n)+A*Real.sqrt (C₄/(n:ℝ))+
        C₅*(A*(δ n)^k+A*e n+A*(1/((n:ℝ)*δ n))+A*((δ n)^k)^2+A*(e n)^2) := by ring
    _=_ := by rw [hAδ,hAlge,hAe,hAraw,hAδsq,hAesq]

end Hurst
