module

public import ComparisonActualHighWallStarMismatch
public import ComparisonSignedCavityActualStarSelection

@[expose] public section

noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy
set_option maxHeartbeats 6500000
attribute [local instance] Classical.propDecidable

namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem cavityCapTravel_nonneg
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    0 ≤ M.cavityCapTravel := by
  unfold cavityCapTravel
  exact mul_nonneg (div_nonneg M.data.hL.le (Real.rpow_pos_of_pos M.data.hN delta).le)
    (Real.log_nonneg ((le_div_iff₀ M.data.hU).mpr (by linarith)))

def Potential.starExtendedH
    {M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) : ℝ→ℝ := fun r=>p.H (projIcc M.data.rmin 1 M.data.hr r)

theorem Potential.starExtendedH_continuous
    {M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) : Continuous p.starExtendedH := by
  have hc : ContinuousOn p.H (Icc M.data.rmin 1) := by
    simpa only [uIcc_of_le M.data.hr] using p.hH.continuousOn
  exact (continuousOn_iff_continuous_domRestrict.mp hc).comp continuous_projIcc

def Potential.positiveMassMask
    {M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) : ℝ→ℝ :=
  (comparisonCalibrationFloor p.H (M.data.wallRadius M.alpha)).indicator (fun _=>1)

theorem Potential.positiveMassMask_extended
    {M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) : p.positiveMassMask=
      (comparisonCalibrationFloor p.starExtendedH (M.data.wallRadius M.alpha)).indicator (fun _=>1) := by
  funext u
  have he : p.starExtendedH (M.data.wallRadius M.alpha u)=p.H (M.data.wallRadius M.alpha u) := by
    dsimp only [starExtendedH]
    rw [projIcc_of_mem M.data.hr (M.data.wallRadius_bounds M.alpha u)]
  simp only [positiveMassMask,comparisonCalibrationFloor,indicator_apply,mem_ofPred_eq,he]

theorem Potential.positiveMassMask_zero_iff
    {M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) (u : ℝ) :
    p.positiveMassMask u=0 ↔ p.H (M.data.wallRadius M.alpha u)≤0 := by
  by_cases hp : 0<p.H (M.data.wallRadius M.alpha u)
  · simp [positiveMassMask,comparisonCalibrationFloor,hp,not_le_of_gt hp]
  · simp [positiveMassMask,comparisonCalibrationFloor,hp,le_of_not_gt hp]

theorem Potential.positiveMassMask_on_band
    {M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) {a z : ℝ} (ha : M.data.s≤a) (haz : a≤z) (hz : z≤1) :
    IntegrableOn p.positiveMassMask (Ioo a z) ∧
    (∫u in Ioo a z,p.positiveMassMask u)≤
      M.data.N^(-delta)*comparisonSmallMass M.data.N M.data.E := by
  have hfloor : ∀ᵐ r,r∈Icc M.data.rmin 1→0<p.starExtendedH r→
      deriv M.alpha.val.val r=comparisonFloor M.data.N delta
        (comparisonSmallMass M.data.N M.data.E) r := by
    filter_upwards [p.hfloor] with r hr hri hh
    have he : p.starExtendedH r=p.H r := by
      dsimp only [starExtendedH]
      rw [projIcc_of_mem M.data.hr hri]
    rw [he] at hh
    exact hr hri hh
  have H := comparison_calibration_native_floor_on_band M.data.hr M.data.hc M.data.hk
    M.data.hkc M.data.hm M.data.hM M.data.hN M.data.hU M.data.hrbounds.1.le
    M.alpha p.starExtendedH p.starExtendedH_continuous.measurable hfloor ha haz hz
  change IntervalIntegrable
    ((comparisonCalibrationFloor p.starExtendedH (M.data.wallRadius M.alpha)).indicator (fun _=>(1:ℝ)))
      volume a z ∧ _ at H
  rw [←p.positiveMassMask_extended] at H
  rw [intervalIntegral.integral_of_le haz,integral_Ioc_eq_integral_Ioo] at H
  have hmass := H.2
  change (∫u in Ioo a z,
    (comparisonCalibrationFloor p.starExtendedH (M.data.wallRadius M.alpha)).indicator (fun _=>(1:ℝ)) u)≤_ at hmass
  rw [←p.positiveMassMask_extended] at hmass
  exact ⟨H.1.1.mono_set Ioo_subset_Ioc_self,hmass⟩

theorem Potential.nonpositive_squared_mismatch_ae_mass
    {M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) :
    ∀ᵐu,u∈Icc M.data.s 1→M.data.rmin+M.cavityCapTravel<M.data.wallRadius M.alpha u→
      p.H (M.data.wallRadius M.alpha u)≤0→
      (orderedPathS (n+1) M.bf M.hf u-M.data.wallRadius M.alpha u)^2≤
        16*M.cavityCapTravel^2+2*(orderedPathB (n+1) M.bf M.hf u-
          (orderedPathS (n+1) M.bf M.hf u)^2) := by
  have H := ae_inverse_pullback
    (inverseIntegralConstraints_lipschitz M.data.hm M.data.hM M.alpha.property)
    (fun u (_ : u∈Icc M.data.s 1)=>M.data.wallRadius_bounds M.alpha u)
    (fun u hu=>M.data.wallRadius_spec M.alpha hu) p.nonpositive_squared_mismatch_ae
  filter_upwards [H] with u hu hui haway hh
  have H' := hu hui haway hh
  simpa only [radiusS,radiusB,M.data.wallRadius_spec M.alpha hui] using H'

theorem Potential.exists_thermal_good_star_off_floor
    {M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) {a z t : ℝ} (ha : M.data.s≤a) (haz : a<z) (hz : z≤1)
    (ht : 0≤t) (haway : ∀u∈Ioo a z,
      M.data.rmin+M.cavityCapTravel<M.data.wallRadius M.alpha u)
    (hsmall : (∫u in Ioo a z,orderedPathB (n+1) M.bf M.hf u-
      (orderedPathS (n+1) M.bf M.hf u)^2)<
      t*((z-a)-M.data.N^(-delta)*comparisonSmallMass M.data.N M.data.E)) :
    ∃u∈Ioo a z,p.H (M.data.wallRadius M.alpha u)≤0 ∧
      orderedPathB (n+1) M.bf M.hf u-(orderedPathS (n+1) M.bf M.hf u)^2≤t ∧
      (orderedPathS (n+1) M.bf M.hf u-M.data.wallRadius M.alpha u)^2≤
        16*M.cavityCapTravel^2+2*t := by
  let f := fun u=>orderedPathB (n+1) M.bf M.hf u-(orderedPathS (n+1) M.bf M.hf u)^2
  have hsub : Ioo a z⊆Icc M.data.s 1 := fun u hu=>⟨ha.trans hu.1.le,hu.2.le.trans hz⟩
  have hsubunit : Ioo a z⊆Icc (0:ℝ) 1 :=
    fun u hu=>⟨M.data.hs.1.le.trans (hsub hu).1,(hsub hu).2⟩
  have hiF : IntegrableOn f (Icc (0:ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp
      (physicalOrderedThermal_intervalIntegrable n M.bf M.hf
        (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha))
  have hf0 u (hu : u∈Ioo a z) : 0≤f u :=
    sub_nonneg.mpr (orderedPath_SK_bounds (n+1) (by omega) M.bf M.hf
      (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha)
      ⟨M.data.hs.1.trans_le (hsub hu).1,(hsub hu).2⟩).2.2.1
  obtain ⟨hm,hmass⟩ := p.positiveMassMask_on_band ha haz.le hz
  have hP : ∀ᵐu,u∈Ioo a z→p.H (M.data.wallRadius M.alpha u)≤0→
      (orderedPathS (n+1) M.bf M.hf u-M.data.wallRadius M.alpha u)^2≤
        16*M.cavityCapTravel^2+2*f u := by
    filter_upwards [p.nonpositive_squared_mismatch_ae_mass] with u hu hui hh
    exact hu (hsub hui) (haway u hui) hh
  have hbudget : (∫u in Ioo a z,f u)<t*((z-a)-(∫u in Ioo a z,p.positiveMassMask u)) :=
    hsmall.trans_le (mul_le_mul_of_nonneg_left (sub_le_sub_left hmass _) ht)
  obtain ⟨u,hu,hmask,hf,hp⟩ := exists_good_point_off_mask_ae haz ht
    (hiF.mono_set hsubunit) hm (Eventually.of_forall hf0)
    (Eventually.of_forall (fun u _=>by
      dsimp [positiveMassMask]
      by_cases h:u∈comparisonCalibrationFloor p.H (M.data.wallRadius M.alpha) <;> simp [h]))
    hP hbudget
  have hh := (p.positiveMassMask_zero_iff u).mp hmask
  exact ⟨u,hu,hh,hf,(hp hh).trans (by linarith only [hf])⟩

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
