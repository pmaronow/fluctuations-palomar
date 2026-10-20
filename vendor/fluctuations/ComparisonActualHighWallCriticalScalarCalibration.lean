module

public import ComparisonActualHighWallCalibratedBandProducerAlong
public import ComparisonActualHighWallScalarLimitData
public import ComparisonInitialIntegralGoodPoint
public import ComparisonNativeLocalTemperatureCalibration

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy NativeOverlapMinimum
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 14000000

namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem original_scalar_gap_intervalIntegrable
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {q : ℝ} (hq : q∈Icc (0:ℝ) 1) :
    IntervalIntegrable (fun u => orderedPathS (n+1) M.bf M.hf u-
      scalarCovarianceResponse M.data.hTpos (M.data.scalarMassProfile M.alpha)
        (actualMixedClock (n+1) M.bf M.hf u)) volume 0 q := by
  have hsub : uIcc (0:ℝ) q ⊆ Icc (0:ℝ) 1 := by
    rw [uIcc_of_le hq.1]
    exact Icc_subset_Icc le_rfl hq.2
  have hs : IntervalIntegrable (orderedPathS (n+1) M.bf M.hf) volume 0 q :=
    (M.mass_mean_monotone.mono hsub).intervalIntegrable
  have hK : MonotoneOn (actualMixedClock (n+1) M.bf M.hf) (Icc (0:ℝ) 1) := by
    intro u hu v hv huv
    exact add_le_add (M.data.hf_monotone M.alpha hu hv huv)
      (mul_le_mul (M.data.bf_monotone M.alpha hu hv huv)
        (M.mass_mean_monotone hu hv huv) (M.mass_mean_nonneg hu) (NNReal.coe_nonneg _))
  have hki : IntervalIntegrable (fun u => actualMixedClock (n+1) M.bf M.hf u/M.data.T)
      volume 0 q := (hK.mono hsub).intervalIntegrable.div_const M.data.T
  have he : IntervalIntegrable (fun u => scalarPlantedEnergy M.data.hTpos
      (M.data.scalarMassProfile M.alpha)
        (actualMixedClock (n+1) M.bf M.hf u/M.data.T)) volume 0 q := by
    rw [intervalIntegrable_iff,uIoc_of_le hq.1]
    apply Integrable.of_bound
      ((scalarPlantedEnergy_continuous M.data.hTpos
        (M.data.scalarMassProfile M.alpha)).comp_aestronglyMeasurable
          hki.1.aestronglyMeasurable) 1
    filter_upwards [] with u
    rw [Real.norm_eq_abs,abs_of_nonneg (scalarPlantedEnergy_bounds M.data.hTpos _ _).1]
    exact (scalarPlantedEnergy_bounds M.data.hTpos _ _).2
  exact hs.sub he

theorem critical_scalar_calibration_of_integrated_original_residual
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hfixed : M.xs = M.data.d) {Cs : ℝ} (hCs : 0 < Cs)
    (hband : let a := calibratedBandStart cu Az
      let b := a+4
      let c := 3*(starMassBandConstant cu Az/cu)/4
      b*M.xs ≤ 1 ∧
      ∀u∈Icc (a*M.xs) (b*M.xs),
        c*M.xs ≤ orderedPathS (n+1) M.bf M.hf u ∧
        orderedPathS (n+1) M.bf M.hf u ≤ Cs*M.xs ∧
        M.data.wallRadius M.alpha u ≤ (b/cl)*M.xs ∧
        M.xs ≤ M.data.wallRadius M.alpha u)
    (hsmall : ((calibratedBandStart cu Az+4)/cl+Cs)*M.xs^2 ≤
      M.data.T*(3*(starMassBandConstant cu Az/cu)/4)/2)
    (hgap : (∫u in 0..(calibratedBandStart cu Az+4)*M.xs,
      |orderedPathS (n+1) M.bf M.hf u-
        scalarCovarianceResponse M.data.hTpos (M.data.scalarMassProfile M.alpha)
          (actualMixedClock (n+1) M.bf M.hf u)|) < 4*M.xs^4) :
    let c := 3*(starMassBandConstant cu Az/cu)/4
    let Cm := (calibratedBandStart cu Az+4)/cl+Cs
    ∃q : ℝ,c/2*M.xs ≤ q ∧
      q ≤ (Cs+Cm/M.data.T)*M.xs ∧
      |scalarCovarianceResponse M.data.hTpos (M.data.scalarMassProfile M.alpha)
        (M.data.T*q)-q| ≤ (1+Cm/M.data.T)*M.xs^3 := by
  let a := calibratedBandStart cu Az
  let b := a+4
  let c := 3*(starMassBandConstant cu Az/cu)/4
  let Cm := b/cl+Cs
  have hA : 0 < starMassBandConstant cu Az := star_mass_band_constant_pos hcu hAz
  have ha : 0 < a := calibrated_band_start_pos hcu hAz
  have hab : a < b := by dsimp only [b]; linarith
  have hc : 0 < c := by dsimp only [c]; positivity
  have hCm : 0 ≤ Cm := by dsimp only [Cm,b]; positivity
  have ha1 : 1 ≤ a := by
    have H : 0 ≤ cu*Az := mul_nonneg hcu.le hAz
    dsimp only [a,calibratedBandStart,starMassBandConstant]
    nlinarith only [H,hcu]
  have hxs1 : M.xs ≤ 1 := by rw [hfixed]; exact M.data.hd1
  dsimp only at hband
  change b*M.xs ≤ 1 ∧ ∀u∈Icc (a*M.xs) (b*M.xs),
    c*M.xs ≤ orderedPathS (n+1) M.bf M.hf u ∧
    orderedPathS (n+1) M.bf M.hf u ≤ Cs*M.xs ∧
    M.data.wallRadius M.alpha u ≤ (b/cl)*M.xs ∧
    M.xs ≤ M.data.wallRadius M.alpha u at hband
  let f := fun u => orderedPathS (n+1) M.bf M.hf u-
    scalarCovarianceResponse M.data.hTpos (M.data.scalarMassProfile M.alpha)
      (actualMixedClock (n+1) M.bf M.hf u)
  have hfi' : IntervalIntegrable f volume 0 (b*M.xs) :=
    M.original_scalar_gap_intervalIntegrable ⟨(mul_pos (ha.trans hab) M.hxs).le,hband.1⟩
  have hgap' : (∫u in 0..b*M.xs, |f u|) < (b-a)*M.xs^4 := by
    have H : b-a=4 := by dsimp only [b]; ring
    rw [H]
    simpa only [b,a,f] using hgap
  obtain ⟨u,hu,hres⟩ := exists_abs_le_of_initial_integral_lt f M.hxs ha.le hab hfi' hgap'
  have hu01 : u∈Icc (0:ℝ) 1 :=
    ⟨((mul_pos ha M.hxs).trans hu.1).le,hu.2.le.trans hband.1⟩
  have huHigh : u∈Icc M.data.s 1 := by
    refine ⟨M.hsxs.trans ?_,hu01.2⟩
    simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right ha1 M.hxs.le).trans hu.1.le
  obtain ⟨hSlo,hShi,hRhi,hxsR⟩ := hband.2 u ⟨hu.1.le,hu.2.le⟩
  have hSu : 0 ≤ orderedPathS (n+1) M.bf M.hf u := M.mass_mean_nonneg hu01
  have hRu : 0 ≤ M.data.wallRadius M.alpha u := M.hxs.le.trans hxsR
  have hmismatch : |M.data.wallRadius M.alpha u-orderedPathS (n+1) M.bf M.hf u|
      ≤ Cm*M.xs := by
    have H := abs_sub_le (M.data.wallRadius M.alpha u) 0
      (orderedPathS (n+1) M.bf M.hf u)
    simp only [sub_zero,zero_sub,abs_neg,abs_of_nonneg hRu,abs_of_nonneg hSu] at H
    dsimp only [Cm]
    nlinarith only [H,hRhi,hShi]
  have hg : M.data.g (M.data.wallRadius M.alpha u) ≤ M.xs^2 := by
    have H : M.data.g (M.data.wallRadius M.alpha u) ≤ M.data.d^2 :=
      laplaceComparisonStrength_le M.data.d (sq_nonneg M.data.d) _
    simpa only [hfixed] using H
  have hclock : |actualMixedClock (n+1) M.bf M.hf u-
      M.data.T*orderedPathS (n+1) M.bf M.hf u| ≤ Cm*M.xs^3 := by
    rw [M.high_mass_clock_compensation huHigh,abs_mul,
      abs_of_pos (laplaceComparisonStrength_pos M.data.d
        (sq_pos_of_pos M.data.hd) _)]
    have H := mul_le_mul hg hmismatch (abs_nonneg _) (sq_nonneg M.xs)
    nlinarith only [H]
  refine ⟨actualMixedClock (n+1) M.bf M.hf u/M.data.T,?_⟩
  exact scalar_calibration_at_local_temperature
    (scalarCovarianceResponse M.data.hTpos (M.data.scalarMassProfile M.alpha))
    M.data.hTpos M.hxs hxs1 hCm hSlo hShi hclock hsmall
    (show |orderedPathS (n+1) M.bf M.hf u-
      scalarCovarianceResponse M.data.hTpos (M.data.scalarMassProfile M.alpha)
        (actualMixedClock (n+1) M.bf M.hf u)| ≤ 1*M.xs^3 by
      simpa only [one_mul,f] using hres)

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
