module

public import ComparisonActualHighOnlyConditionalFiniteRegions
public import ComparisonActualHighOnlyConditionalOpenRadiusError

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 22000000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
attribute [local instance] Classical.propDecidable
namespace ActualHighOnlyOverlapMinimum
variable {n:ℕ} {m delta cl cu Az C0 Ct D Bclock:ℝ}
variable {a:ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}

abbrev errorMaskIntegral (a:ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (S:Set ℝ):ℝ:=
  ∫u in 0..1,S.indicator (fun _=>(1:ℝ)) (a.R u)*a.comparisonErrorDensity u

theorem Potential.conditional_high_ordinary_union_budget_high_only (P:a.Potential)
    (F:Finset (ordConnectedSection P.negativeSet)) {B:ℝ}
    (hB:0 ≤ B) (hOrd:∀j:ConditionalHighOrdinaryDyad a,
      a.errorMaskIntegral (P.ordinaryGroup (P.capFamily F) (Ioo (0:ℝ) 1) 16 j.val) ≤ B) :
    a.errorMaskIntegral (P.conditionalHighOrdinaryUnion F) ≤
      (Fintype.card (ConditionalHighOrdinaryDyad a):ℝ)*B := by
  have H:=a.error_mask_integral_iUnion_le_high_only
    (fun j:ConditionalHighOrdinaryDyad a=>P.ordinaryGroup (P.capFamily F) (Ioo (0:ℝ) 1) 16 j.val)
    (fun j=>P.ordinaryGroup_measurable _ _ _ _)
  exact H.trans (by
    calc (∑j:ConditionalHighOrdinaryDyad a,a.errorMaskIntegral (P.ordinaryGroup (P.capFamily F) (Ioo (0:ℝ) 1) 16 j.val)) ≤
          ∑_j:ConditionalHighOrdinaryDyad a,B:=Finset.sum_le_sum (fun j _=>hOrd j)
         _=(Fintype.card (ConditionalHighOrdinaryDyad a):ℝ)*B:=by simp)

theorem Potential.conditional_initial_small_union_budget_high_only (P:a.Potential)
    (F:Finset (ordConnectedSection P.negativeSet)) {B:ℝ} (hB:0 ≤ B)
    (hInit:∀t:F,(P.capFamily F t).left=0 → a.alpha.val.val (P.capFamily F t).right ≤ 16*a.data.s →
      a.errorMaskIntegral (Ioo (P.capFamily F t).left (P.capFamily F t).right) ≤ B) :
    a.errorMaskIntegral (P.conditionalInitialSmallCapUnion F) ≤ B := by
  let J:={t:F // (P.capFamily F t).left=0 ∧ a.alpha.val.val (P.capFamily F t).right ≤ 16*a.data.s}
  have H:=a.error_mask_integral_iUnion_le_high_only
    (fun t:J=>Ioo (P.capFamily F t.val).left (P.capFamily F t.val).right) (fun _=>measurableSet_Ioo)
  have HC:Fintype.card J ≤ 1:=by
    have H1:=Fintype.card_le_of_injective
      (fun t:J=>(⟨t.val,t.property.1⟩:{t:F // (P.capFamily F t).left=0}))
      (by intro i j h;apply Subtype.ext;exact congrArg (fun t:{t:F // (P.capFamily F t).left=0}=>t.val) h)
    exact H1.trans (conditional_initial_cap_card_le_one (P.capFamily F) (P.capFamily_disjoint F))
  have HB:(∑t:J,a.errorMaskIntegral (Ioo (P.capFamily F t.val).left (P.capFamily F t.val).right)) ≤
      (Fintype.card J:ℝ)*B:=by
    calc _ ≤ ∑_t:J,B:=Finset.sum_le_sum (fun t _=>hInit t.val t.property.1 t.property.2)
         _=(Fintype.card J:ℝ)*B:=by simp
  exact H.trans (HB.trans (by
    have HH:(Fintype.card J:ℝ) ≤ 1:=by exact_mod_cast HC
    simpa only [one_mul] using mul_le_mul_of_nonneg_right HH hB))

theorem Potential.conditional_contact_budget_high_only (P:a.Potential)
    (F:Finset (ordConnectedSection P.negativeSet)) {B R O:ℝ}
    (hB:0 ≤ B) (hR:0 ≤ R) (hO:0 ≤ O)
    (hRaw:(∫u in 0..min (16*a.data.U) 1,a.comparisonErrorDensity u) ≤ R)
    (hWall:a.data.U ≤ a.data.s → a.errorMaskIntegral (P.conditionalWallSupport F) ≤ B)
    (hOrd:a.errorMaskIntegral (P.conditionalHighOrdinaryUnion F) ≤ O) :
    a.errorMaskIntegral (Ioo (0:ℝ) 1∩P.contactSet) ≤ R+B+O := by
  have hContact:MeasurableSet (Ioo (0:ℝ) 1∩P.contactSet):=measurableSet_Ioo.inter P.contactSet_measurable
  have hUnion:=P.conditionalHighOrdinaryUnion_measurable F
  by_cases hsU:a.data.s < a.data.U
  · let L:=a.conditionalLowRadiusRegion (min (16*a.data.U) 1)
    have hL:=a.conditionalLowRadiusRegion_measurable (min (16*a.data.U) 1)
    have HM:=a.error_mask_integral_mono_high_only _ _ hContact (hL.union hUnion)
      (P.conditional_contact_region_cover_U_high_only F hsU)
    have HU:=a.error_mask_integral_union_le_high_only L _ hL hUnion
    have HV:min (16*a.data.U) 1∈Icc (0:ℝ) 1:=⟨le_min (by have HU:=a.data.hU;positivity) zero_le_one,min_le_right _ _⟩
    have HL: a.errorMaskIntegral L ≤ R:=(a.error_low_radius_region_le_prefix_high_only HV).trans hRaw
    exact HM.trans (HU.trans (by linarith only [HL,hOrd,hB]))
  · have hUs:=le_of_not_gt hsU
    let V:Set ℝ:={r|a.alpha.val.val r=min (32*a.data.s) 1}
    have hV:MeasurableSet V:=measurableSet_eq_fun a.alpha.val.property.2.measurable measurable_const
    have hWallSet:=P.conditionalWallSupport_measurable F
    have HM:=a.error_mask_integral_mono_high_only _ _ hContact ((hWallSet.union hUnion).union hV)
      (P.conditional_contact_region_cover_wall_high_only F hUs)
    have H1:=a.error_mask_integral_union_le_high_only _ V (hWallSet.union hUnion) hV
    have H2:=a.error_mask_integral_union_le_high_only _ _ hWallSet hUnion
    have Hz:=a.error_profile_level_mask_zero_high_only (min (32*a.data.s) 1)
    exact HM.trans (H1.trans (by linarith only [H2,Hz,hWall hUs,hOrd,hR]))

theorem Potential.conditional_comparable_budget_high_only (P:a.Potential)
    (F:Finset (ordConnectedSection P.negativeSet)) {B R O:ℝ}
    (hB:0 ≤ B) (hR:0 ≤ R) (hO:0 ≤ O)
    (hRaw:(∫u in 0..min (16*a.data.U) 1,a.comparisonErrorDensity u) ≤ R)
    (hWall:a.data.U ≤ a.data.s → a.errorMaskIntegral (P.conditionalWallSupport F) ≤ B)
    (hOrd:a.errorMaskIntegral (P.conditionalHighOrdinaryUnion F) ≤ O) :
    a.errorMaskIntegral (relevantComparableCapUnion (P.capFamily F) (Ioo (0:ℝ) 1)) ≤ R+B+O := by
  have hComp:MeasurableSet (relevantComparableCapUnion (P.capFamily F) (Ioo (0:ℝ) 1)):=
    MeasurableSet.iUnion (fun _=>measurableSet_Ioo)
  have hUnion:=P.conditionalHighOrdinaryUnion_measurable F
  by_cases hsU:a.data.s < a.data.U
  · let L:=a.conditionalLowRadiusRegion (min (16*a.data.U) 1)
    have hL:=a.conditionalLowRadiusRegion_measurable (min (16*a.data.U) 1)
    have HM:=a.error_mask_integral_mono_high_only _ _ hComp (hL.union hUnion)
      (P.conditional_comparable_region_cover_U_high_only F hsU)
    have HU:=a.error_mask_integral_union_le_high_only L _ hL hUnion
    have HV:min (16*a.data.U) 1∈Icc (0:ℝ) 1:=⟨le_min (by have HU:=a.data.hU;positivity) zero_le_one,min_le_right _ _⟩
    have HL:a.errorMaskIntegral L ≤ R:=(a.error_low_radius_region_le_prefix_high_only HV).trans hRaw
    exact HM.trans (HU.trans (by linarith only [HL,hOrd,hB]))
  · have hUs:=le_of_not_gt hsU
    have hWallSet:=P.conditionalWallSupport_measurable F
    have HM:=a.error_mask_integral_mono_high_only _ _ hComp (hWallSet.union hUnion)
      (P.conditional_comparable_region_cover_wall_high_only F hUs)
    have HU:=a.error_mask_integral_union_le_high_only _ _ hWallSet hUnion
    exact HM.trans (HU.trans (by linarith only [hWall hUs,hOrd,hR]))

theorem Potential.conditional_small_budget_high_only (P:a.Potential)
    (F:Finset (ordConnectedSection P.negativeSet)) {B R:ℝ}
    (hB:0 ≤ B) (hR:0 ≤ R)
    (hRaw:(∫u in 0..min (16*a.data.U) 1,a.comparisonErrorDensity u) ≤ R)
    (hWall:a.data.U ≤ a.data.s → a.errorMaskIntegral (P.conditionalWallSupport F) ≤ B)
    (hInit:a.data.U ≤ a.data.s → ∀t:F,(P.capFamily F t).left=0 → a.alpha.val.val (P.capFamily F t).right ≤ 16*a.data.s →
      a.errorMaskIntegral (Ioo (P.capFamily F t).left (P.capFamily F t).right) ≤ B) :
    a.errorMaskIntegral (conditionalSmallCapUnion (P.capFamily F) (Ioo (0:ℝ) 1)) ≤ R+2*B := by
  have hSmall:MeasurableSet (conditionalSmallCapUnion (P.capFamily F) (Ioo (0:ℝ) 1)):=
    MeasurableSet.iUnion (fun _=>measurableSet_Ioo)
  by_cases hsU:a.data.s < a.data.U
  · have hL:=a.conditionalLowRadiusRegion_measurable (min (16*a.data.U) 1)
    have HM:=a.error_mask_integral_mono_high_only _ _ hSmall hL
      (P.conditional_small_region_cover_U_high_only F hsU)
    have HV:min (16*a.data.U) 1∈Icc (0:ℝ) 1:=⟨le_min (by have HU:=a.data.hU;positivity) zero_le_one,min_le_right _ _⟩
    have HL: a.errorMaskIntegral (a.conditionalLowRadiusRegion (min (16*a.data.U) 1)) ≤ R:=
      (a.error_low_radius_region_le_prefix_high_only HV).trans hRaw
    exact HM.trans (by linarith only [HL,hB])
  · have hUs:=le_of_not_gt hsU
    have hWallSet:=P.conditionalWallSupport_measurable F
    have hInitSet:=P.conditionalInitialSmallCapUnion_measurable F
    have HM:=a.error_mask_integral_mono_high_only _ _ hSmall (hWallSet.union hInitSet)
      (P.conditional_small_region_cover_wall_high_only F hUs)
    have HU:=a.error_mask_integral_union_le_high_only _ _ hWallSet hInitSet
    have HI:=P.conditional_initial_small_union_budget_high_only F hB (hInit hUs)
    exact HM.trans (HU.trans (by linarith only [hWall hUs,HI,hR]))

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
