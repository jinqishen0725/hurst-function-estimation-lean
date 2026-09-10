import Hurst.SecondWeightedPilotVariance
import Hurst.ActualMeanResidual
import Hurst.CompositeLocalBias
import Hurst.ClippedQuadratic
import Hurst.ActualScaleVariance
import Hurst.FiniteAverageMSE
import Hurst.L2TestApproximation

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology ENNReal
namespace Hurst
set_option maxHeartbeats 1200000

/-- Mean of the actual q=2 pilot relative to the *smoothed* Hurst function.
Keeping this intermediate centre is what exposes the cancellation in the
log-scale estimator. -/
theorem hurstHolder_q2_pilot_mean_smooth (p a b M : ℝ) (r : ℕ)
    (hp : 2≤p) (ha : 0<a) (hb : b<1) (hab : a≤b) (hM : 0≤M) :
    ∃ N₀>0,∃ E≥0,∀ᶠ n : ℕ in atTop,∀ f : ℝ → ℝ,
      ∀ hf : f∈hurstHolderClass p M,MapsTo f (Ioo (0:ℝ) 1) (Icc a b) →
      ∀ δ t : ℝ,0<δ → δ≤1/2 → t∈Icc (0:ℝ) 1 → N₀≤(n:ℝ)*δ →
      |(∫ x,q2Pilot r n δ t x
          ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))-
        smooth (localPolynomialWeights r n 4 δ t) (fun i => f (grid n i.val))|≤
          gridCovarianceError (1/2) E n := by
  obtain ⟨Nw,hNw,D,hD,hw⟩ := localPolynomialWeights_uniform_stability r 4
  obtain ⟨E₁,hE₁,hm₁⟩ := hurstHolder_common_stride_log_mean p a b M 1 4 hp ha hb hab hM (by norm_num) (by norm_num)
  obtain ⟨E₂,hE₂,hm₂⟩ := hurstHolder_common_stride_log_mean p a b M 2 4 hp ha hb hab hM (by norm_num) (by norm_num)
  refine ⟨Nw,hNw,D*(E₁+E₂)/(2*Real.log 2),by positivity,?_⟩
  filter_upwards [hm₁,hm₂,eventually_ge_atTop 4] with n hm1 hm2 hn4
  intro f hf hF δ t hδ hδhalf ht hnd
  have hn0 : 0<n := by omega
  let H := midpointSampleHurst f hf.1 n
  let v := gridObservationFeatures n H
  let w := localPolynomialWeights r n 4 δ t
  let a₁ := commonStrideCoefficients n 1 4 (by norm_num)
  let a₂ := commonStrideCoefficients n 2 4 (by norm_num)
  let base := fun i : Fin (n-4) => -2*f (grid n i.val)*Real.log n+
    q2LogCorrection (f (grid n i.val))+gaussianLogSquareMean
  let m₁ := fun i => Real.log (‖∑ j,a₁ i j • v j‖^2)+gaussianLogSquareMean
  let m₂ := fun i => Real.log (‖∑ j,a₂ i j • v j‖^2)+gaussianLogSquareMean
  have hz₁ : ∀ i,∑ j,a₁ i j • v j≠0 := fun i => (hm1 f hf hF i).1
  have hz₂ : ∀ i,∑ j,a₂ i j • v j≠0 := fun i => (hm2 f hf hF i).1
  have he₁ : ∀ i,|m₁ i-base i|≤gridCovarianceError (1/2) E₁ n := by
    intro i
    simpa only [Nat.cast_one,Real.log_one,mul_zero,add_zero,m₁,base,a₁,v,H] using (hm1 f hf hF i).2
  have he₂ : ∀ i,|m₂ i-(base i+2*Real.log 2*f (grid n i.val))|≤
      gridCovarianceError (1/2) E₂ n := by
    intro i
    convert (hm2 f hf hF i).2 using 1
    congr 1
    dsimp [m₂,base,a₂,v,H]
    ring
  have hG₁ := gaussianLogStatistic_memLp_two v w a₁ hz₁
  have hG₂ := gaussianLogStatistic_memLp_two v w a₂ hz₂
  have hp := twoScalePilot_weighted_bias w (fun i => f (grid n i.val)) base m₁ m₂
    (smooth w (fun i => f (grid n i.val)))
    (gridCovarianceError (1/2) E₁ n) (gridCovarianceError (1/2) E₂ n) 0 he₁ he₂ (by simp)
  change |(∫ x,twoScalePilot (gaussianLogStatistic w a₁) (gaussianLogStatistic w a₂) x
      ∂featureGaussian v)-smooth w (fun i => f (grid n i.val))|≤_
  rw [twoScalePilot_expectation _ _ _ (hG₁.integrable one_le_two) (hG₂.integrable one_le_two),
    gaussianLogStatistic_expectation v w a₂ hz₂,gaussianLogStatistic_expectation v w a₁ hz₁]
  apply hp.trans
  have hsum := (hw n hn0 hn4 δ t hδ hδhalf ht hnd).2.2.1
  have herr : 0≤gridCovarianceError (1/2) E₁ n+gridCovarianceError (1/2) E₂ n := by
    unfold gridCovarianceError
    have hnR : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
    have hl := Real.log_nonneg (show (1:ℝ)≤2*n by linarith)
    positivity
  have hh := (div_le_div_iff_of_pos_right (show 0<2*Real.log 2 by positivity)).mpr
    (mul_le_mul_of_nonneg_right hsum herr)
  rw [zero_add]
  apply hh.trans_eq
  unfold gridCovarianceError
  ring

theorem hurstHolder_q2_common_log_mean_smooth (p a b M : ℝ) (r : ℕ)
    (hp : 2≤p) (ha : 0<a) (hb : b<1) (hab : a≤b) (hM : 0≤M) :
    ∃ N₀>0,∃ E≥0,∀ᶠ n : ℕ in atTop,∀ f : ℝ → ℝ,
      ∀ hf : f∈hurstHolderClass p M,MapsTo f (Ioo (0:ℝ) 1) (Icc a b) →
      ∀ δ t : ℝ,0<δ → δ≤1/2 → t∈Icc (0:ℝ) 1 → N₀≤(n:ℝ)*δ →
      |(∫ x,gaussianLogStatistic (localPolynomialWeights r n 4 δ t)
          (commonStrideCoefficients n 1 4 (by norm_num)) x
          ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))-
        smooth (localPolynomialWeights r n 4 δ t)
          (fun i => -2*Real.log n*f (grid n i.val)+q2LogCorrection (f (grid n i.val))+
            gaussianLogSquareMean)|≤E*gridCovarianceError (1/2) 1 n := by
  obtain ⟨E,hE,hm⟩ := hurstHolder_common_stride_log_mean p a b M 1 4 hp ha hb hab hM (by norm_num) (by norm_num)
  obtain ⟨N₀,hN₀,D,hD,hw⟩ := localPolynomialWeights_uniform_stability r 4
  refine ⟨N₀,hN₀,D*E,by positivity,?_⟩
  filter_upwards [hm,eventually_ge_atTop 4] with n hm hn4
  intro f hf hF δ t hδ hδhalf ht hnd
  have hn0 : 0<n := by omega
  let v := gridObservationFeatures n (midpointSampleHurst f hf.1 n)
  let w := localPolynomialWeights r n 4 δ t
  let coeff := commonStrideCoefficients n 1 4 (by norm_num)
  have hz : ∀ i,∑ j,coeff i j • v j≠0 := fun i => (hm f hf hF i).1
  let target := fun i : Fin (n-4) => -2*Real.log n*f (grid n i.val)+
    q2LogCorrection (f (grid n i.val))+gaussianLogSquareMean
  have he : ∀ i,|Real.log (‖∑ j,coeff i j • v j‖^2)+gaussianLogSquareMean-target i|≤
      gridCovarianceError (1/2) E n := by
    intro i
    convert (hm f hf hF i).2 using 1
    congr 1
    dsimp [coeff,v,target]
    simp only [Nat.cast_one,Real.log_one,mul_zero,add_zero]
    ring
  have hb := gaussianLogStatistic_mean_approximation v w coeff hz _ _ he
  have hsum := (hw n hn0 hn4 δ t hδ hδhalf ht hnd).2.2.1
  have herr : 0≤gridCovarianceError (1/2) E n := by
    unfold gridCovarianceError
    have hnR : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
    have hl := Real.log_nonneg (show (1:ℝ)≤2*n by linarith)
    positivity
  exact hb.trans ((mul_le_mul_of_nonneg_right hsum herr).trans_eq (by
    unfold gridCovarianceError
    ring))

/-- Refined deterministic bias of the linear part of the q=2 scale
estimator.  The potentially leading `log n * δ^p` terms cancel. -/
theorem hurstHolder_q2_linearScale_fine_bias (p a b M : ℝ)
    (hp : 2≤p) (ha : 0<a) (hb : b<1) (hab : a≤b) (hM : 0≤M) :
    ∃ N₀>0,∃ B≥0,∃ E≥0,∀ᶠ n : ℕ in atTop,∀ f : ℝ → ℝ,
      ∀ hf : f∈hurstHolderClass p M,MapsTo f (Ioo (0:ℝ) 1) (Icc a b) →
      ∀ m : ℕ,0<m → ∀ δ : ℝ,0<δ → δ≤1/2 → N₀≤(n:ℝ)*δ → 1≤Real.log n →
      |(∫ x,q2LinearScale (Nat.ceil p-1) n m δ x
          ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))-
        (∑ j : Fin m,(q2LogCorrection (f (grid m j.val))+gaussianLogSquareMean))/(m:ℝ)|≤
          B*δ^p+Real.log n*gridCovarianceError (1/2) E n := by
  obtain ⟨Ng,hNg,Eg,hEg,hg⟩ := hurstHolder_q2_common_log_mean_smooth p a b M (Nat.ceil p-1) hp ha hb hab hM
  obtain ⟨Np,hNp,Ep,hEp,hpilot⟩ := hurstHolder_q2_pilot_mean_smooth p a b M (Nat.ceil p-1) hp ha hb hab hM
  obtain ⟨Nc,hNc,B,hB,hcomp⟩ := hurstHolder_smooth_composite_local_bias p a b M q2LogCorrection 4
    hp ha hb hM q2LogCorrection_smooth
  obtain ⟨Nw,hNw,D,hD,hw⟩ := localPolynomialWeights_uniform_stability (Nat.ceil p-1) 4
  obtain ⟨E₁,_,hm₁⟩ := hurstHolder_common_stride_log_mean p a b M 1 4 hp ha hb hab hM (by norm_num) (by norm_num)
  obtain ⟨E₂,_,hm₂⟩ := hurstHolder_common_stride_log_mean p a b M 2 4 hp ha hb hab hM (by norm_num) (by norm_num)
  let N₀ := max (max Ng Np) (max Nc Nw)
  refine ⟨N₀,lt_of_lt_of_le hNg ((le_max_left Ng Np).trans (le_max_left _ _)),B,hB,Eg+2*Ep,by positivity,?_⟩
  filter_upwards [hg,hpilot,hm₁,hm₂,eventually_ge_atTop 4] with n hg hpilot hm1 hm2 hn4
  intro f hf hF m hm δ hδ hδhalf hnd hL
  obtain ⟨Dext,hDext,hext⟩ := hurstHolder_uniform_lipschitz_extension p (by linarith)
  obtain ⟨g,heq,hgLip,hgmap⟩ := hext M hM f hf
  have hgcont : Continuous g := hgLip.continuous
  have hn0 : 0<n := by omega
  have hNg' : Ng≤(n:ℝ)*δ := (le_max_left Ng Np).trans (le_max_left (max Ng Np) (max Nc Nw)) |>.trans hnd
  have hNp' : Np≤(n:ℝ)*δ := (le_max_right Ng Np).trans (le_max_left (max Ng Np) (max Nc Nw)) |>.trans hnd
  have hNc' : Nc≤(n:ℝ)*δ := (le_max_left Nc Nw).trans (le_max_right (max Ng Np) (max Nc Nw)) |>.trans hnd
  have hNw' : Nw≤(n:ℝ)*δ := (le_max_right Nc Nw).trans (le_max_right (max Ng Np) (max Nc Nw)) |>.trans hnd
  let P := featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
  let w := fun j : Fin m => localPolynomialWeights (Nat.ceil p-1) n 4 δ (grid m j.val)
  let G := fun j : Fin m => gaussianLogStatistic (w j) (commonStrideCoefficients n 1 4 (by norm_num))
  let pilot := fun j : Fin m => q2Pilot (Nat.ceil p-1) n δ (grid m j.val)
  let X := fun j : Fin m => fun x => G j x+2*Real.log n*pilot j x
  let θ := fun j : Fin m => q2LogCorrection (f (grid m j.val))+gaussianLogSquareMean
  have hj : ∀ j : Fin m,grid m j.val∈Ioo (0:ℝ) 1 := fun j => grid_mem m j.val hm j.isLt
  have hjc : ∀ j : Fin m,grid m j.val∈Icc (0:ℝ) 1 := fun j => ⟨(hj j).1.le,(hj j).2.le⟩
  have hz₁ : ∀ i,∑ k,commonStrideCoefficients n 1 4 (by norm_num) i k •
      gridObservationFeatures n (midpointSampleHurst f hf.1 n) k≠0 := fun i => (hm1 f hf hF i).1
  have hz₂ : ∀ i,∑ k,commonStrideCoefficients n 2 4 (by norm_num) i k •
      gridObservationFeatures n (midpointSampleHurst f hf.1 n) k≠0 := fun i => (hm2 f hf hF i).1
  have hmemG : ∀ j,MemLp (G j) 2 P := fun j => gaussianLogStatistic_memLp_two _ _ _ hz₁
  have hmemPilot : ∀ j,MemLp (pilot j) 2 P := fun j => twoScalePilot_memLp P _ _
    (gaussianLogStatistic_memLp_two _ _ _ hz₁) (gaussianLogStatistic_memLp_two _ _ _ hz₂)
  have hInt : ∀ j,Integrable (X j) P := fun j => ((hmemG j).add ((hmemPilot j).const_mul _)).integrable one_le_two
  have hbias : ∀ j,|(∫ x,X j x ∂P)-θ j|≤B*δ^p+Real.log n*gridCovarianceError (1/2) (Eg+2*Ep) n := by
    intro j
    let sj := grid m j.val
    let sw := localPolynomialWeights (Nat.ceil p-1) n 4 δ sj
    let Hs := fun i : Fin (n-4) => f (grid n i.val)
    have hG := hg f hf hF δ sj hδ hδhalf (hjc j) hNg'
    have hP := hpilot f hf hF δ sj hδ hδhalf (hjc j) hNp'
    have hC := hcomp f hf hF g hgcont heq n hn0 hn4 δ hδ hδhalf hNc' sj (hjc j)
    rw [← heq (hj j)] at hC
    have hmass := (hw n hn0 hn4 δ sj hδ hδhalf (hjc j) hNw').2.2.2 0
    have hmass1 : ∑ i,sw i=1 := by simpa [sw] using hmass
    rw [integral_add ((hmemG j).integrable one_le_two) (((hmemPilot j).integrable one_le_two).const_mul _),integral_const_mul]
    have hcal : smooth sw (fun i => -2*Real.log n*Hs i+q2LogCorrection (Hs i)+gaussianLogSquareMean)=
        -2*Real.log n*smooth sw Hs+smooth sw (fun i => q2LogCorrection (Hs i))+gaussianLogSquareMean := by
      unfold smooth
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
      simp only [← Finset.sum_mul,hmass1]
      have hlinear : (∑ x,sw x*(-2*Real.log n*Hs x))=
          -2*Real.log n*(∑ x,sw x*Hs x) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      rw [hlinear]
      ring
    have hid : (∫ x,G j x ∂P)+2*Real.log n*(∫ x,pilot j x ∂P)-θ j =
        ((∫ x,G j x ∂P)-smooth sw (fun i => -2*Real.log n*Hs i+q2LogCorrection (Hs i)+gaussianLogSquareMean))+
        2*Real.log n*((∫ x,pilot j x ∂P)-smooth sw Hs)+
        (smooth sw (fun i => q2LogCorrection (Hs i))-q2LogCorrection (f sj)) := by
      rw [hcal]
      dsimp [θ]
      ring
    rw [hid]
    apply (abs_add_le _ _).trans
    apply (add_le_add (abs_add_le _ _) hC).trans
    rw [abs_mul,abs_of_nonneg (by linarith : 0≤2*Real.log n)]
    have hnonneg : 0≤gridCovarianceError (1/2) Eg n := by
      unfold gridCovarianceError
      have hlog : 0≤Real.log (2*(n:ℝ)) := Real.log_nonneg (by
        have hnR : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
        linarith)
      positivity
    have hnonneg' : 0≤gridCovarianceError (1/2) Ep n := by
      unfold gridCovarianceError
      have hlog : 0≤Real.log (2*(n:ℝ)) := Real.log_nonneg (by
        have hnR : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
        linarith)
      positivity
    calc
      _ ≤ Eg*gridCovarianceError (1/2) 1 n+2*Real.log n*gridCovarianceError (1/2) Ep n+B*δ^p :=
        add_le_add (add_le_add hG (mul_le_mul_of_nonneg_left hP (by positivity))) le_rfl
      _ ≤ B*δ^p+Real.log n*gridCovarianceError (1/2) (Eg+2*Ep) n := by
        unfold gridCovarianceError at *
        nlinarith
  change |(∫ x,q2LinearScale (Nat.ceil p-1) n m δ x ∂P)-
    (∑ j : Fin m,θ j)/(m:ℝ)|≤_
  have hidfun : q2LinearScale (Nat.ceil p-1) n m δ = fun x => (∑ j : Fin m,X j x)/(m:ℝ) := by
    funext x
    exact q2LinearScale_eq_average (Nat.ceil p-1) n m δ x
  rw [hidfun]
  exact finite_average_expectation_bias P m hm X θ _ hInt hbias

end Hurst
