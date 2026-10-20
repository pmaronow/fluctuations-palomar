module

public import ComparisonActualHighWallCriticalWholeCapCover

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 6000000
attribute [local instance] Classical.propDecidable
namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualHighWallOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
variable {P : a.Potential}
theorem critical_local_finite_cap_thermal_cover {ι : Type*} [Fintype ι]
    (c : ι → ShiftedCapInterval a P)
    (A : Set ℝ) (hA : MeasurableSet A) :
    (∫u in 0..1,(A∩((⋃i,Ioo (c i).left (c i).right)∪P.contactSet)).indicator
      (fun _=>1) (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u) ≤
      (∫u in 0..1,(A∩P.contactSet).indicator (fun _=>1) (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u)+
      (∫u in 0..1,(criticalRelevantComparableCapUnion c A).indicator
        (fun _=>1) (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u)+
      (∑p : CriticalRelevantBroadSlice c A,
        ∫u in 0..1,(actualCriticalBroadSlice c p.val).indicator (fun _=>1) (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u)+
      (∫u in 0..min (8*a.criticalMassCoverBase) 1,a.shiftedNativeModel.thermal u) := by
  let full := A ∩ ((⋃i,Ioo (c i).left (c i).right) ∪ P.contactSet)
  let contact := A ∩ P.contactSet
  let comp := criticalRelevantComparableCapUnion c A
  let low : Set ℝ := {u |u ≤ min (8*a.criticalMassCoverBase) 1}
  let b := fun p : CriticalRelevantBroadSlice c A => fun u =>
    (actualCriticalBroadSlice c p.val).indicator (fun _=>1) (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u
  have hfull : MeasurableSet full := hA.inter
    ((MeasurableSet.iUnion (fun _=>measurableSet_Ioo)).union (P.contactSet_measurable))
  have hcontact : MeasurableSet contact := hA.inter (P.contactSet_measurable)
  have hcomp : MeasurableSet comp := MeasurableSet.iUnion (fun _=>measurableSet_Ioo)
  have hiF := a.shiftedNativeModel.thermal_mask_integrable full hfull
  have hiC := a.shiftedNativeModel.thermal_mask_integrable contact hcontact
  have hiComp := a.shiftedNativeModel.thermal_mask_integrable comp hcomp
  have hT : IntervalIntegrable a.shiftedNativeModel.thermal volume 0 1:=by
    simpa only [indicator_univ,one_mul] using
      a.shiftedNativeModel.thermal_mask_integrable univ MeasurableSet.univ
  have hiLow : IntervalIntegrable (fun u=>low.indicator (fun _=>(1:ℝ)) u*a.shiftedNativeModel.thermal u)
      volume 0 1:=intervalIntegrable_bounded_measurable_mul
        (measurable_const.indicator measurableSet_Iic) zero_le_one
        (fun u _=>by by_cases H:u∈low <;> simp [H]) hT
  have hiB p : IntervalIntegrable (b p) volume 0 1 :=
    a.shiftedNativeModel.thermal_mask_integrable _ measurableSet_Ioo
  have hiSum : IntervalIntegrable (fun u=>∑p,b p u) volume 0 1 := by
    have heq : (fun u=>∑p,b p u)=∑p,b p := by funext u; simp only [Finset.sum_apply]
    rw [heq]
    exact IntervalIntegrable.sum Finset.univ (fun p _=>hiB p)
  have hpoint : ∀ᵐu ∂volume.restrict (Ioc (0:ℝ) 1),
      full.indicator (fun _=>1) (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u ≤
        contact.indicator (fun _=>1) (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u+
        comp.indicator (fun _=>1) (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u+
        (∑p,b p u)+low.indicator (fun _=>1) u*a.shiftedNativeModel.thermal u := by
    have hc := critical_local_finite_cap_cover_ae c A
    rw [←restrict_Ioc_eq_restrict_Icc] at hc
    filter_upwards [ae_restrict_mem measurableSet_Ioc,hc] with u hu hc
    have hT := a.shiftedNativeModel.thermal_nonneg hu
    have hn (S : Set ℝ) : 0 ≤ S.indicator (fun _=>(1:ℝ)) (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u :=
      mul_nonneg (indicator_nonneg (fun _ _=>zero_le_one) _) hT
    have hbn p : 0 ≤ b p u := hn _
    have hsum : 0 ≤ ∑p,b p u := Finset.sum_nonneg (fun p _=>hbn p)
    have hnLow : 0≤low.indicator (fun _=>(1:ℝ)) u*a.shiftedNativeModel.thermal u:=
      mul_nonneg (indicator_nonneg (fun _ _=>zero_le_one) _) hT
    by_cases hf : a.shiftedNativeModel.R u ∈ full
    · simp only [indicator_of_mem hf,one_mul]
      rcases hc hf with hcontact | hcomp | ⟨p,hp⟩ | hlow
      · have hh : contact.indicator (fun _=>(1:ℝ)) (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u=a.shiftedNativeModel.thermal u := by
          rw [indicator_of_mem hcontact,one_mul]
        rw [hh]
        linarith [hn comp,hnLow]
      · have hh : comp.indicator (fun _=>(1:ℝ)) (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u=a.shiftedNativeModel.thermal u := by
          rw [indicator_of_mem hcomp,one_mul]
        rw [hh]
        linarith [hn contact,hnLow]
      · have hh : b p u=a.shiftedNativeModel.thermal u := by dsimp [b]; simp only [indicator_of_mem hp,one_mul]
        have hs := Finset.single_le_sum (s:=Finset.univ) (f:=fun p=>b p u)
          (fun p _=>hbn p) (Finset.mem_univ p)
        rw [hh] at hs
        linarith [hn contact,hn comp,hnLow]
      · have hh : low.indicator (fun _=>(1:ℝ)) u*a.shiftedNativeModel.thermal u=a.shiftedNativeModel.thermal u := by
          rw [indicator_of_mem (show u∈low from hlow),one_mul]
        rw [hh]
        linarith [hn contact,hn comp]
    · simp only [indicator_of_notMem hf,zero_mul]
      linarith [hn contact,hn comp,hnLow]
  have hb : (∫u in 0..1,full.indicator (fun _=>1) (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u) ≤
      ∫u in 0..1,contact.indicator (fun _=>1) (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u+
        comp.indicator (fun _=>1) (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u+(∑p,b p u)+
        low.indicator (fun _=>1) u*a.shiftedNativeModel.thermal u := by
    simp only [intervalIntegral.integral_of_le zero_le_one]
    exact integral_mono_ae ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hiF)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (((hiC.add hiComp).add hiSum).add hiLow)) hpoint
  rw [intervalIntegral.integral_add ((hiC.add hiComp).add hiSum) hiLow,
    intervalIntegral.integral_add (hiC.add hiComp) hiSum,
    intervalIntegral.integral_add hiC hiComp,
    intervalIntegral.integral_finsetSum (fun p _=>hiB p),
    ] at hb
  have hv : min (8*a.criticalMassCoverBase) 1∈Icc (0:ℝ) 1:=
    ⟨(lt_min (mul_pos (by norm_num) (criticalMassCoverBase_pos (a:=a))) zero_lt_one).le,min_le_right _ _⟩
  have heq : (fun u=>low.indicator (fun _=>(1:ℝ)) u*a.shiftedNativeModel.thermal u)=
      ({u |u ≤ min (8*a.criticalMassCoverBase) 1}).indicator a.shiftedNativeModel.thermal:=by
    funext u
    change low.indicator (fun _=>(1:ℝ)) u*a.shiftedNativeModel.thermal u=
      low.indicator a.shiftedNativeModel.thermal u
    by_cases H:u∈low
    · rw [indicator_of_mem H,indicator_of_mem H,one_mul]
    · rw [indicator_of_notMem H,indicator_of_notMem H,zero_mul]
  rw [heq,intervalIntegral.integral_indicator hv] at hb
  exact hb

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
