module

public import ComparisonActualHighWallStarSelectionDistinct
public import ComparisonSignedCavityActualCalibratedBandGeometry

@[expose] public section

noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy
set_option maxHeartbeats 5500000

namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem actual_closed_regular_mass_band_radius_bounds
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az)
    {W a b u : ℝ} (hW : 0<W) (hxs : M.xs≤W)
    (ha : NativeOverlapMinimum.starMassBandConstant cu Az≤a) (hsmall : b*W≤1)
    (hhigh : M.data.s≤a*W) (hu : u∈Icc (a*W) (b*W)) :
    (a/cu)*W≤M.data.wallRadius M.alpha u ∧ M.data.wallRadius M.alpha u≤(b/cl)*W := by
  have hA : 0<NativeOverlapMinimum.starMassBandConstant cu Az :=
    NativeOverlapMinimum.star_mass_band_constant_pos hcu hAz
  have ha0 : 0<a := hA.trans_le ha
  have hui : u∈Icc M.data.s 1 := ⟨hhigh.trans hu.1,hu.2.trans hsmall⟩
  have hR := M.data.wallRadius_bounds M.alpha u
  have hspec := M.data.wallRadius_spec M.alpha hui
  have hzR : M.z≤M.data.wallRadius M.alpha u := by
    by_contra H
    have halpha := M.alpha.val.property.2 (le_of_not_ge H)
    rw [hspec] at halpha
    have hreg := (M.regular M.z ⟨le_rfl,M.hz.2⟩).2
    have hZ := mul_le_mul_of_nonneg_left M.hzxs hcu.le
    have hxsW := mul_le_mul_of_nonneg_left hxs (mul_nonneg hcu.le hAz)
    have hAW := mul_le_mul_of_nonneg_right ha hW.le
    unfold NativeOverlapMinimum.starMassBandConstant at hAW
    nlinarith only [halpha,hreg,hZ,hxsW,hAW,hu.1,hW]
  have hr := M.regular (M.data.wallRadius M.alpha u) ⟨hzR,hR.2⟩
  rw [hspec] at hr
  constructor
  · have H : a*W/cu≤M.data.wallRadius M.alpha u :=
      (div_le_iff₀ hcu).mpr (by nlinarith only [hr.2,hu.1])
    simpa only [div_mul_eq_mul_div] using H
  · have H : M.data.wallRadius M.alpha u≤b*W/cl :=
      (le_div_iff₀ hcl).mpr (by nlinarith only [hr.1,hu.2])
    simpa only [div_mul_eq_mul_div] using H

theorem high_mass_clock_compensation
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {u : ℝ} (hu : u∈Icc M.data.s 1) :
    actualMixedClock (n+1) M.bf M.hf u-M.data.T*orderedPathS (n+1) M.bf M.hf u=
      M.data.g (M.data.wallRadius M.alpha u)*
        (M.data.wallRadius M.alpha u-orderedPathS (n+1) M.bf M.hf u) := by
  have hb : (M.bf u:ℝ)=M.data.T-M.data.g (M.data.wallRadius M.alpha u) := by
    rw [(M.data.clock_coe M.alpha ⟨M.data.hs.1.le.trans hu.1,hu.2⟩).1]
    dsimp only [ActualHighWallData.b]
    rw [wallChangedMatrix_on M.data.hr M.data.hs1 M.data.hc M.data.hk M.data.hkc
      M.data.hm M.data.hM M.data.g M.data.hg.continuous M.data.T M.data.epsilon
      M.data.theta M.alpha hu]
    have he : M.data.wallRadius M.alpha u=
        (constrainedQuantile M.data.hr M.data.hc M.data.hk M.data.hkc M.data.hm
          M.data.hM M.alpha ⟨u,hu⟩:ℝ) := by
      unfold ActualHighWallData.wallRadius comparisonCalibrationConstrainedRadius
      rw [IccExtend_of_mem _ _ hu]
      rfl
    rw [he]
  unfold actualMixedClock
  rw [hb,M.data.high_field_clock M.alpha hu]
  ring

theorem selected_high_mass_clock_calibration
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {u c W : ℝ} (hu : u∈Icc M.data.s 1) (hc : 0<c) (hW : 0<W)
    (hdW : M.data.d≤W) (hsmall : W^2≤M.data.T/2)
    (hmean : (3*c/4)*W≤orderedPathS (n+1) M.bf M.hf u)
    (hmismatch : |orderedPathS (n+1) M.bf M.hf u-M.data.wallRadius M.alpha u|≤c*W/4) :
    (3*M.data.T*c/8)*W≤actualMixedClock (n+1) M.bf M.hf u ∧
    |actualMixedClock (n+1) M.bf M.hf u-M.data.T*orderedPathS (n+1) M.bf M.hf u|≤
      (c/4)*W^3 := by
  have hg : M.data.g (M.data.wallRadius M.alpha u)≤W^2 :=
    (laplaceComparisonStrength_le M.data.d (sq_nonneg _) _).trans
      (pow_le_pow_left₀ M.data.hd.le hdW 2)
  have hb : M.data.T/2≤(M.bf u:ℝ) := by
    rw [(M.data.clock_coe M.alpha ⟨M.data.hs.1.le.trans hu.1,hu.2⟩).1]
    dsimp only [ActualHighWallData.b]
    rw [wallChangedMatrix_on M.data.hr M.data.hs1 M.data.hc M.data.hk M.data.hkc
      M.data.hm M.data.hM M.data.g M.data.hg.continuous M.data.T M.data.epsilon
      M.data.theta M.alpha hu]
    have he : (constrainedQuantile M.data.hr M.data.hc M.data.hk M.data.hkc M.data.hm
        M.data.hM M.alpha ⟨u,hu⟩:ℝ)=M.data.wallRadius M.alpha u := by
      unfold ActualHighWallData.wallRadius comparisonCalibrationConstrainedRadius
      rw [IccExtend_of_mem _ _ hu]
      rfl
    rw [he]
    linarith only [hg,hsmall]
  have hprod := mul_le_mul hb hmean
    (by positivity : 0≤(3*c/4)*W) (M.bf u).coe_nonneg
  refine ⟨?_,?_⟩
  · unfold actualMixedClock
    nlinarith only [hprod,(M.hf u).coe_nonneg]
  · rw [M.high_mass_clock_compensation hu,abs_mul,
      abs_of_pos (laplaceComparisonStrength_pos M.data.d (sq_pos_of_pos M.data.hd) _),abs_sub_comm]
    exact (mul_le_mul hg hmismatch (abs_nonneg _) (sq_nonneg W)).trans_eq (by ring)

theorem Potential.exists_thermal_good_star_clock_calibration
    {M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) {a z c C W : ℝ}
    (ha : M.data.s≤a) (haz : a<z) (hz : z≤1) (hc : 0<c) (hW : 0<W)
    (hdW : M.data.d≤W) (hsmallclock : W^2≤M.data.T/2)
    (htravelsmall : M.cavityCapTravel≤c*W/32)
    (haway : ∀u∈Ioo a z,M.data.rmin+M.cavityCapTravel<M.data.wallRadius M.alpha u)
    (hband : ∀u∈Ioo a z,c*W≤M.data.wallRadius M.alpha u ∧
      M.data.wallRadius M.alpha u≤C*W)
    (hsmallthermal : (∫u in Ioo a z,orderedPathB (n+1) M.bf M.hf u-
      (orderedPathS (n+1) M.bf M.hf u)^2)<
      ((c*W)^2/64)*((z-a)-M.data.N^(-delta)*comparisonSmallMass M.data.N M.data.E)) :
    ∃u∈Ioo a z,p.H (M.data.wallRadius M.alpha u)≤0 ∧
      orderedPathB (n+1) M.bf M.hf u-(orderedPathS (n+1) M.bf M.hf u)^2≤(c*W)^2/64 ∧
      |orderedPathS (n+1) M.bf M.hf u-M.data.wallRadius M.alpha u|≤c*W/4 ∧
      (3*c/4)*W≤orderedPathS (n+1) M.bf M.hf u ∧
      orderedPathS (n+1) M.bf M.hf u≤(C+c/4)*W ∧
      (3*M.data.T*c/8)*W≤actualMixedClock (n+1) M.bf M.hf u ∧
      |actualMixedClock (n+1) M.bf M.hf u-M.data.T*orderedPathS (n+1) M.bf M.hf u|≤
        (c/4)*W^3 := by
  obtain ⟨u,hu,hH,hthermal,hmis⟩ := p.exists_thermal_good_star_off_floor ha haz hz
    (by positivity : 0≤(c*W)^2/64) haway hsmallthermal
  have htravel2 := pow_le_pow_left₀ M.cavityCapTravel_nonneg htravelsmall 2
  have hsq : (orderedPathS (n+1) M.bf M.hf u-M.data.wallRadius M.alpha u)^2≤(c*W/4)^2 := by
    nlinarith only [hmis,htravel2,sq_nonneg (c*W)]
  have habs : |orderedPathS (n+1) M.bf M.hf u-M.data.wallRadius M.alpha u|≤c*W/4 := by
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity : 0≤c*W/4)).mp
    simpa only [sq_abs] using hsq
  have hmeanlo : (3*c/4)*W≤orderedPathS (n+1) M.bf M.hf u := by
    nlinarith only [(abs_le.mp habs).1,(hband u hu).1]
  have hmeanhi : orderedPathS (n+1) M.bf M.hf u≤(C+c/4)*W := by
    nlinarith only [(abs_le.mp habs).2,(hband u hu).2]
  have hclock := M.selected_high_mass_clock_calibration
    ⟨ha.trans hu.1.le,hu.2.le.trans hz⟩ hc hW hdW hsmallclock hmeanlo habs
  exact ⟨u,hu,hH,hthermal,habs,hmeanlo,hmeanhi,hclock.1,hclock.2⟩

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
