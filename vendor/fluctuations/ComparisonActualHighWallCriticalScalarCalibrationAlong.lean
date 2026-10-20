module

public import ComparisonActualHighWallCriticalScalarCalibration

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy NativeOverlapMinimum
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 18000000

namespace ActualHighWallOverlapMinimum

theorem exists_actual_high_wall_critical_scalar_calibration_along
    {m delta cl cu Az C0 Ct D Bclock T0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hT0 : 0 < T0)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hxlim : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).xs) atTop (𝓝 0))
    (hT : ∀n,T0≤(M n).data.T)
    (hgap : Tendsto (fun n=>
      (∫u in 0..(calibratedBandStart cu Az+4)*(M n).xs,
        |orderedPathS (dim n+1) (M n).bf (M n).hf u-
          scalarCovarianceResponse (M n).data.hTpos
            ((M n).data.scalarMassProfile (M n).alpha)
            (actualMixedClock (dim n+1) (M n).bf (M n).hf u)|)/(M n).xs^4)
      atTop (𝓝 0)) :
    ∃c R B : ℝ,0<c ∧ 0<R ∧ 0≤B ∧ ∀ᶠn in atTop,∃q : ℝ,
      c*(M n).xs ≤ q ∧ q ≤ R*(M n).xs ∧
      |scalarCovarianceResponse (M n).data.hTpos
        ((M n).data.scalarMassProfile (M n).alpha) ((M n).data.T*q)-q|
        ≤ B*(M n).xs^3 := by
  let a := calibratedBandStart cu Az
  let b := a+4
  let c := 3*(starMassBandConstant cu Az/cu)/4
  have hc : 0<c := by dsimp only [c]; positivity [star_mass_band_constant_pos hcu hAz]
  obtain ⟨Cs,hCs,Hband⟩ := eventually_actual_high_wall_calibrated_mass_band_along
    (L:=1) hm hdelta hroom hcl hcu hAz hC0 hCt hT0 (by norm_num)
    dim hdim M (fun n=>(M n).xs)
    (fun n=>(hfixed n).le) (fun n=>(hfixed n).ge) hxlim hsRatio hT
  let Cm := b/cl+Cs
  have hb : 0<b := by dsimp only [b]; linarith [calibrated_band_start_pos hcu hAz]
  have hCm : 0≤Cm := by dsimp only [Cm]; positivity
  have HR : 0<Cs+Cm/T0 := by positivity
  have HB : 0≤1+Cm/T0 := by positivity
  have Hsmall : ∀ᶠn in atTop,Cm*(M n).xs^2 ≤ T0*c/2 := by
    have H := (hxlim.pow 2).const_mul Cm
    simp only [zero_pow (by norm_num : (2:ℕ)≠0),mul_zero] at H
    exact H.eventually (eventually_le_nhds (by positivity))
  have Hgap := hgap.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<4))
  refine ⟨c/2,Cs+Cm/T0,1+Cm/T0,by positivity,HR,HB,?_⟩
  filter_upwards [Hband,Hsmall,Hgap] with n hnBand hnSmall hnGap
  dsimp only at hnBand
  simp only [mul_one] at hnBand
  have hband : (calibratedBandStart cu Az+4)*(M n).xs≤1 ∧
      ∀u∈Icc (calibratedBandStart cu Az*(M n).xs)
        ((calibratedBandStart cu Az+4)*(M n).xs),
        (3*(starMassBandConstant cu Az/cu)/4)*(M n).xs ≤
          orderedPathS (dim n+1) (M n).bf (M n).hf u ∧
        orderedPathS (dim n+1) (M n).bf (M n).hf u≤Cs*(M n).xs ∧
        (M n).data.wallRadius (M n).alpha u≤
          ((calibratedBandStart cu Az+4)/cl)*(M n).xs ∧
        (M n).xs≤(M n).data.wallRadius (M n).alpha u := by
    refine ⟨hnBand.2.1,?_⟩
    intro u hu
    obtain ⟨hlo,hhi,_,hrhi,hxsR,_⟩ := hnBand.2.2.1 u hu
    exact ⟨hlo,hhi,hrhi,hxsR⟩
  have hsmall : Cm*(M n).xs^2 ≤ (M n).data.T*c/2 := by
    have H := mul_le_mul_of_nonneg_right (hT n) (by positivity : 0≤c/2)
    linarith only [hnSmall,H]
  have hgap' : (∫u in 0..(calibratedBandStart cu Az+4)*(M n).xs,
        |orderedPathS (dim n+1) (M n).bf (M n).hf u-
          scalarCovarianceResponse (M n).data.hTpos
            ((M n).data.scalarMassProfile (M n).alpha)
            (actualMixedClock (dim n+1) (M n).bf (M n).hf u)|) <
      4*(M n).xs^4 :=
    (div_lt_iff₀ (pow_pos (M n).hxs 4)).mp hnGap
  obtain ⟨q,hqlo,hqhi,hqres⟩ := (M n).critical_scalar_calibration_of_integrated_original_residual
    hcl hcu hAz (hfixed n) hCs hband hsmall hgap'
  have Hdiv : Cm/(M n).data.T≤Cm/T0 :=
    div_le_div_of_nonneg_left hCm hT0 (hT n)
  refine ⟨q,hqlo,?_,?_⟩
  · exact hqhi.trans (mul_le_mul_of_nonneg_right (add_le_add_right Hdiv Cs) (M n).hxs.le)
  · exact hqres.trans (mul_le_mul_of_nonneg_right (add_le_add_right Hdiv 1)
      (pow_nonneg (M n).hxs.le 3))

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
