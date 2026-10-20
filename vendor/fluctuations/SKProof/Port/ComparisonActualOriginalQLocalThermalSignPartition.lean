module

public import SKProof.Port.ComparisonActualOriginalQInitialFloorThermal
public import SKProof.Port.ComparisonActualOriginalQInnovation
public import ComparisonActualHighWallThetaZeroCapFamily
public import ComparisonShiftedNativeThermalGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}

theorem Potential.local_thermal_sign_partition
    (P : a.Potential) (A : Set ℝ) (hA : MeasurableSet A) (hAD : A⊆Ioo a.data.rmin 1) :
    (∫u in 0..1,A.indicator (fun _=>1) (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u)=
      (∫u in 0..1,(A∩(P.negativeSet∪P.contactSet)).indicator (fun _=>1)
        (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u)+
      (∫u in 0..1,(A∩P.positiveRadiusSet).indicator (fun _=>1)
        (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u) := by
  let m:=a.shiftedNativeModel
  change (∫u in 0..1,A.indicator (fun _=>1) (m.R u)*m.thermal u)=_
  have hn := m.thermal_mask_integrable _
    (hA.inter (P.negativeSet_open.measurableSet.union P.contactSet_measurable))
  have hp := m.thermal_mask_integrable _ (hA.inter P.positiveRadiusSet_measurable)
  rw [←intervalIntegral.integral_add hn hp]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [] with u hu
  by_cases ha : m.R u∈A
  ·
    have hr:=hAD ha
    have hri : m.R u∈Icc a.data.rmin 1:=Ioo_subset_Icc_self hr
    have hnon : (m.R u∈P.negativeSet∪P.contactSet) ↔ P.H (m.R u)≤0 := by
      constructor
      · rintro (h|h)
        · exact h.2.le
        · exact h.2.le
      · intro h
        rcases lt_or_eq_of_le h with hneg|hz
        · exact Or.inl ⟨hr,hneg⟩
        · exact Or.inr ⟨hri,hz⟩
    have hpos : (m.R u∈P.positiveRadiusSet) ↔ 0 < P.H (m.R u) :=
      ⟨fun h=>h.2,fun h=>⟨hri,h⟩⟩
    by_cases hH : 0 < P.H (m.R u)
    · have hp : m.R u∈A∩P.positiveRadiusSet := ⟨ha,hpos.mpr hH⟩
      have hn : m.R u∉A∩(P.negativeSet∪P.contactSet) :=
        fun h=>not_le_of_gt hH (hnon.mp h.2)
      simp only [indicator_of_mem ha,indicator_of_mem hp,indicator_of_notMem hn,
        one_mul,zero_mul,zero_add]
    · have hn : m.R u∈A∩(P.negativeSet∪P.contactSet) :=
        ⟨ha,hnon.mpr (le_of_not_gt hH)⟩
      have hp : m.R u∉A∩P.positiveRadiusSet := fun h=>hH (hpos.mp h.2)
      simp only [indicator_of_mem ha,indicator_of_mem hn,indicator_of_notMem hp,
        one_mul,zero_mul,add_zero]
  · have hn : m.R u∉A∩(P.negativeSet∪P.contactSet) := fun h=>ha h.1
    have hp : m.R u∉A∩P.positiveRadiusSet := fun h=>ha h.1
    simp only [indicator_of_notMem ha,indicator_of_notMem hn,indicator_of_notMem hp,zero_mul,add_zero]

theorem Potential.local_positive_thermal_le_initial_floor
    (P : a.Potential) (A : Set ℝ) (hA : MeasurableSet A) (hAD : A⊆Ioo a.data.rmin 1)
    (v : ℝ) (hv : v∈Icc (0:ℝ) 1) (hscale : ∀r∈A,a.alpha.val.val r ≤ v) :
    (∫u in 0..1,(A∩P.positiveRadiusSet).indicator (fun _=>1)
      (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u) ≤
      ∫u in 0..v,P.positiveMassMask u*a.shiftedNativeModel.thermal u := by
  let m:=a.shiftedNativeModel
  let f:=fun u=>P.positiveMassMask u*m.thermal u
  have hleft:=m.thermal_mask_integrable (A∩P.positiveRadiusSet) (hA.inter P.positiveRadiusSet_measurable)
  have hfloor:=m.thermal_mask_integrable P.positiveRadiusSet P.positiveRadiusSet_measurable
  change IntervalIntegrable f volume 0 1 at hfloor
  have hiL:=(intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hleft
  have hiF:=(intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hfloor
  have hsub : Ioc (0:ℝ) v⊆Icc (0:ℝ) 1:=fun u hu=>⟨hu.1.le,hu.2.trans hv.2⟩
  have hEq : (∫u in Icc (0:ℝ) 1,(Ioc (0:ℝ) v).indicator f u)=∫u in 0..v,f u := by
    rw [setIntegral_indicator measurableSet_Ioc,inter_eq_right.mpr hsub,←intervalIntegral.integral_of_le hv.1]
  rw [intervalIntegral.integral_of_le zero_le_one,←integral_Icc_eq_integral_Ioc,←hEq]
  apply integral_mono_ae hiL (hiF.indicator measurableSet_Ioc)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  by_cases hr : m.R u∈A∩P.positiveRadiusSet
  · have hr0 : a.data.rmin < m.R u := (hAD hr.1).1
    have hhigh : m.u0<u:=a.radius_high_mass hr0
    have hspec:=m.R_spec ⟨hhigh.le,hu.2⟩
    have huu : u∈Ioc (0:ℝ) v:=⟨m.hu.1.trans_lt hhigh,by
      rw [←hspec]
      exact hscale _ hr.1⟩
    have hp : P.positiveMassMask u=1:=indicator_of_mem hr.2 _
    simp only [indicator_of_mem hr,indicator_of_mem huu,f,hp,one_mul,le_refl]
  · rw [indicator_of_notMem hr,zero_mul]
    apply indicator_nonneg
    intro x hx
    exact mul_nonneg (show 0≤P.positiveMassMask x by
      unfold Potential.positiveMassMask
      exact indicator_nonneg (fun _ _=>zero_le_one) _)
      (a.actual_thermal_nonneg_on_unit (hsub hx))

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
