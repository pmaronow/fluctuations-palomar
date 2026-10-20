module

public import ComparisonSignedCavitySecondLowInheritedCloneSumBudget
public import ComparisonSignedCavitySecondLowActualClassifiedRetainedCSource

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 30000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] nativeSecondLowSlotFintype
variable {n : ℕ} {pre mid tail : List PositiveMass}
variable {T : ClockTree (Spin n×Bool) (pre++(mid++tail))} {f c z : T.Slot}
variable {v : RestCoordinate n→ℝ} {q : ℕ→RestCoordinate n→ℝ} {x : RestCoordinate n→ℝ}

def nativeSecondLowClassifiedCloneConditional
    (E : NativeSecondLowClassifiedRetainedWholeCSource n pre mid tail T f c z v q x)
    (d : E.source.D.Slot) (cut : ℕ) (q' : ℕ→RestCoordinate n→ℝ)
    (Q : T.cavityLeft.Assignment→T.cavityLeft.Assignment→ℝ)
    (r : ((RestCoordinate n→ℝ)×(RestCoordinate n→ℝ))×(RestCoordinate n→ℝ)) : ℝ :=
  E.source.retainedCloneConditional d cut
    (fun j=>cumulativeIncrements (q' 0) (fun k=>q' (k+1)) (pre.length+j))
    (fun j=>cumulativeIncrements (q' 0) (fun k=>q' (k+1)) (pre.length+(mid.length+j)))
    Q (exteriorForestIRoot r) (exteriorForestStarRoot r)

theorem native_second_low_classified_clone_conditional_eq_forest
    (E : NativeSecondLowClassifiedRetainedWholeCSource n pre mid tail T f c z v q x)
    {a : ℝ} (ho : MassOrdered a (pre++(mid++tail)))
    (d : E.source.D.Slot) (cut : ℕ) (q' : ℕ→RestCoordinate n→ℝ)
    (Q : T.cavityLeft.Assignment→T.cavityLeft.Assignment→ℝ)
    (r : ((RestCoordinate n→ℝ)×(RestCoordinate n→ℝ))×(RestCoordinate n→ℝ)) :
    nativeSecondLowClassifiedCloneConditional E d cut q' Q r=
      nativeExteriorForestConditionalTest E.source.Ei E.source.Es
        (nativeCloneBlockAtSlot E.source.D d (cut-(pre.length+mid.length))).tree
        (restWeight n) (restFeature n)
        (fun j=>cumulativeIncrements (q' 0) (fun k=>q' (k+1)) (pre.length+j))
        (fun j=>cumulativeIncrements (q' 0) (fun k=>q' (k+1)) (pre.length+(mid.length+j)))
        (fun η ζ δ=>Q
          (E.source.read η ζ ((nativeCloneBlockAtSlot E.source.D d (cut-(pre.length+mid.length))).oldRestrict δ))
          (E.source.read η ζ ((nativeCloneBlockAtSlot E.source.D d (cut-(pre.length+mid.length))).newRestrict δ)))
        (exteriorForestIRoot r) (exteriorForestStarRoot r) := by
  dsimp only [nativeSecondLowClassifiedCloneConditional,
    NativeClassifiedWholeRetainedSource.retainedCloneConditional]
  rw [nativeExteriorForestConditionalTest_eq_joint]
  apply congrArg (fun F=>E.source.Ei.expect (restWeight n) (restFeature n) _ F _)
  funext η
  rw [expect_fork]
  apply congrArg (fun F=>E.source.Es.expect (restWeight n) (restFeature n) _ F _)
  funext ζ
  exact nativeRetainedCloneCutMean_eq_clone (restWeight_pos n) (restFeature n) E.source.D
    ho.suffix_end.suffix_end d (cut-(pre.length+mid.length)) _
    (fun δ δ'=>Q (E.source.read η ζ δ) (E.source.read η ζ δ')) _

theorem native_second_low_classified_clone_conditional_integrable
    (E : NativeSecondLowClassifiedRetainedWholeCSource n pre mid tail T f c z v q x)
    {a : ℝ} (ho : MassOrdered a (pre++(mid++tail)))
    (d : E.source.D.Slot) (cut : ℕ) (q' : ℕ→RestCoordinate n→ℝ)
    (Q : T.cavityLeft.Assignment→T.cavityLeft.Assignment→ℝ)
    (v' x' : RestCoordinate n→ℝ) :
    Integrable (nativeSecondLowClassifiedCloneConditional E d cut q' Q)
      (nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v' q' x') := by
  let C:=nativeCloneBlockAtSlot E.source.D d (cut-(pre.length+mid.length))
  let qi:=fun j=>cumulativeIncrements (q' 0) (fun k=>q' (k+1)) (pre.length+j)
  let qs:=fun j=>cumulativeIncrements (q' 0) (fun k=>q' (k+1)) (pre.length+(mid.length+j))
  let B:=fun y : (RestCoordinate n→ℝ)×(RestCoordinate n→ℝ)=>
    nativeExteriorForestConditionalTest E.source.Ei E.source.Es C.tree
      (restWeight n) (restFeature n) qi qs
      (fun η ζ δ=>Q (E.source.read η ζ (C.oldRestrict δ)) (E.source.read η ζ (C.newRestrict δ))) y.1 y.2
  have HB:=nativeExteriorForestConditionalTest_smooth_joint (restWeight_pos n) (restFeature n)
    E.source.Ei E.source.Es C.tree ho.suffix_end ho.suffix_end.suffix_end qi qs
    (fun η ζ δ=>Q (E.source.read η ζ (C.oldRestrict δ)) (E.source.read η ζ (C.newRestrict δ))) 0
  change BddSmooth 0 B at HB
  let :=nativeExteriorForestDisorderRootLaw_probability (restWeight_pos n) (restFeature n)
    pre mid tail ho v' q' x'
  have HE:nativeSecondLowClassifiedCloneConditional E d cut q' Q=
      fun r=>B (exteriorForestIRoot r,exteriorForestStarRoot r):=by
    funext r
    exact native_second_low_classified_clone_conditional_eq_forest E ho d cut q' Q r
  rw [HE]
  obtain ⟨K,_,Hbound⟩:=HB.bound
  apply Integrable.of_bound
    (HB.continuous.measurable.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)).aestronglyMeasurable K
  exact Eventually.of_forall fun r=>Hbound _

theorem native_second_low_classified_rest_clone_square_eq_original
    (E : NativeSecondLowClassifiedRetainedWholeCSource n pre mid tail T f c z v q x)
    {a : ℝ} (ho : MassOrdered a (pre++(mid++tail)))
    (d : E.source.D.Slot) (cut : ℕ) (hc : pre.length+mid.length < cut)
    (q' : ℕ→RestCoordinate n→ℝ) (P : T.cavityLeft.Assignment→ℝ) :
    (∫r,nativeSecondLowClassifiedCloneConditional E d cut q'
      (fun σ τ=>(P σ-P τ)^2) r
      ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q' 0)=
      nativeSecondLowRestCloneSquare n T (E.originalSlot d) cut q' P := by
  have HE:=E.source.retained_clone_whole_law (restWeight_pos n) ho d cut hc 0 q'
    (fun σ τ=>(P σ-P τ)^2) 0
  rw [←E.originalSlot_cavity] at HE
  exact HE.symm.trans (nativeRetainedCloneCut_rest_disorderLaw (restWeight_pos n)
    (restFeature n) T ho (E.originalSlot d) cut 0 q' (fun σ τ=>(P σ-P τ)^2) 0)

theorem native_second_low_classified_rest_clone_square_sum_eq_original
    (E : NativeSecondLowClassifiedRetainedWholeCSource n pre mid tail T f c z v q x)
    {a : ℝ} (ho : MassOrdered a (pre++(mid++tail)))
    (cut : ℕ) (hc : pre.length+mid.length < cut) (q' : ℕ→RestCoordinate n→ℝ)
    (Ps : E.source.D.Slot→T.cavityLeft.Assignment→ℝ) :
    (∑d:E.source.D.Slot,∫r,nativeSecondLowClassifiedCloneConditional E d cut q'
      (fun σ τ=>(Ps d σ-Ps d τ)^2) r
      ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q' 0)=
      ∑d:E.source.D.Slot,nativeSecondLowRestCloneSquare n T (E.originalSlot d) cut q' (Ps d) := by
  apply Finset.sum_congr rfl
  intro d _
  exact native_second_low_classified_rest_clone_square_eq_original E ho d cut hc q' (Ps d)

theorem native_second_low_classified_integral_sum_eq_sum_integral
    (E : NativeSecondLowClassifiedRetainedWholeCSource n pre mid tail T f c z v q x)
    {a : ℝ} (ho : MassOrdered a (pre++(mid++tail)))
    (cut : ℕ) (q' : ℕ→RestCoordinate n→ℝ)
    (Qs : E.source.D.Slot→T.cavityLeft.Assignment→T.cavityLeft.Assignment→ℝ)
    (v' x' : RestCoordinate n→ℝ) :
    (∫r,∑d:E.source.D.Slot,nativeSecondLowClassifiedCloneConditional E d cut q' (Qs d) r
      ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v' q' x')=
      ∑d:E.source.D.Slot,∫r,nativeSecondLowClassifiedCloneConditional E d cut q' (Qs d) r
        ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v' q' x' := by
  exact integral_finsetSum _ (fun d _=>native_second_low_classified_clone_conditional_integrable
    E ho d cut q' (Qs d) v' x')

theorem native_second_low_classified_integrated_square_sum_eq_original
    (E : NativeSecondLowClassifiedRetainedWholeCSource n pre mid tail T f c z v q x)
    {a : ℝ} (ho : MassOrdered a (pre++(mid++tail)))
    (cut : ℕ) (hc : pre.length+mid.length < cut) (q' : ℕ→RestCoordinate n→ℝ)
    (Ps : E.source.D.Slot→T.cavityLeft.Assignment→ℝ) :
    (∫r,∑d:E.source.D.Slot,nativeSecondLowClassifiedCloneConditional E d cut q'
      (fun σ τ=>(Ps d σ-Ps d τ)^2) r
      ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q' 0)=
      ∑d:E.source.D.Slot,nativeSecondLowRestCloneSquare n T (E.originalSlot d) cut q' (Ps d) :=
  (native_second_low_classified_integral_sum_eq_sum_integral E ho cut q'
    (fun d σ τ=>(Ps d σ-Ps d τ)^2) 0 0).trans
    (native_second_low_classified_rest_clone_square_sum_eq_original E ho cut hc q' Ps)

end OAI.SKFluctuations.Cavity
