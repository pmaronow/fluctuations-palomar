module

public import ComparisonSignedCavityDynamicExteriorTests
public import ComparisonSignedCavityTwoLevelStarIncomingProduct

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy

theorem native_two_level_star_incoming_product_eq_conditional (n j k : ℕ)
    {ias tas : List PositiveMass} (Ei : ClockTree (Spin n) ias)
    (Es D : ClockTree (Spin n) tas) (H : Ei.Assignment→Es.Assignment→ℝ)
    (e : Es.Slot) (s t : D.Slot) (qi qs : ℕ→RestCoordinate n→ℝ≥0)
    (center : ℝ) (xi xs : RestCoordinate n→ℝ) :
    nativeTwoLevelStarIncomingProduct n j k Ei Es D H e s t qi qs center xi xs=
      nativeExteriorForestConditionalTest Ei Es D (restWeight n) (restFeature n) qi qs
        (fun η ζ δ=>
          let Y:=nativeStarCenteredProjection n tas qs center xs
          (Y (D.atSlot δ t)-Y (D.atSlot δ s))*H η ζ*
            (deletedOverlap n (joinSpin (D.atSlot δ t,false)) (joinSpin (Es.atSlot ζ e,false))-
              deletedOverlap n (joinSpin (D.atSlot δ s,false)) (joinSpin (Es.atSlot ζ e,false)))*
            (Y (D.atSlot δ s)^j*Y (D.atSlot δ t)^k)) xi xs := by
  simp_rw [deleted_overlap_join_eq_scaled]
  unfold nativeTwoLevelStarIncomingProduct nativeExteriorForestConditionalTest
    nativeExteriorForestMean nativeTwoLevelWeightedAnchor nativeWeightedExteriorAnchor ClockTree.expect
  simp only [inner_smul_right,inner_sum,inner_sub_left,normalizedSpin_inner_eq_overlap,
    Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro δ _
  conv_lhs=>rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro η _
  apply Finset.sum_congr rfl
  intro ζ _
  ring

theorem native_two_level_star_incoming_product_smooth (n j k r : ℕ)
    {ias tas : List PositiveMass} (Ei : ClockTree (Spin n) ias)
    (Es D : ClockTree (Spin n) tas) {ai ast : ℝ}
    (hoi : MassOrdered ai ias) (hot : MassOrdered ast tas)
    (H : Ei.Assignment→Es.Assignment→ℝ) (e : Es.Slot) (s t : D.Slot)
    (qi qs : ℕ→RestCoordinate n→ℝ≥0) (center : ℝ) :
    BddSmooth r (fun z : (RestCoordinate n→ℝ)×(RestCoordinate n→ℝ)=>
      nativeTwoLevelStarIncomingProduct n j k Ei Es D H e s t qi qs center z.1 z.2) := by
  simp_rw [native_two_level_star_incoming_product_eq_conditional]
  apply native_dynamic_exterior_test_smooth r Ei Es D hoi hot
    (restWeight_pos n) (restFeature n) qi qs
  intro η ζ δ
  have HS:=(native_star_centered_projection_smooth n hot qs center (D.atSlot δ s) r).compCLM
    (ContinuousLinearMap.snd ℝ (RestCoordinate n→ℝ) (RestCoordinate n→ℝ))
  have HT:=(native_star_centered_projection_smooth n hot qs center (D.atSlot δ t) r).compCLM
    (ContinuousLinearMap.snd ℝ (RestCoordinate n→ℝ) (RestCoordinate n→ℝ))
  exact (((HT.sub HS).mul_const (H η ζ)).mul_const _).mul ((HS.pow j).mul (HT.pow k))

theorem integral_native_two_level_star_incoming_product (n j k : ℕ)
    (pre mid tail : List PositiveMass) {a : ℝ}
    (ho : MassOrdered a (pre++(mid++tail)))
    (Ei : ClockTree (Spin n) (mid++tail)) (Es D : ClockTree (Spin n) tail)
    (v : RestCoordinate n→ℝ) (q : ℕ→RestCoordinate n→ℝ) (x : RestCoordinate n→ℝ)
    (H : Ei.Assignment→Es.Assignment→ℝ) (e : Es.Slot) (s t : D.Slot) (center : ℝ) :
    let dq:=cumulativeIncrements (q 0) (fun l=>q (l+1))
    let qi:=fun l=>dq (pre.length+l)
    let qs:=fun l=>dq (pre.length+(mid.length+l))
    let B:=nativeTwoLevelStarIncomingProduct n j k Ei Es D H e s t qi qs center
    (∫z,B (exteriorForestIRoot z) (exteriorForestStarRoot z)
      ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x)=
      ∫y,prefixTest (clockSteps pre dq)
        (gaussianHierarchy (restWeight n) (restFeature n) (clockSteps mid qi++clockSteps tail qs))
        (fun xi=>prefixTest (clockSteps mid qi)
          (gaussianHierarchy (restWeight n) (restFeature n) (clockSteps tail qs)) (B xi) xi) (x+y)
        ∂Measure.pi (fun c=>gaussianReal 0 (Real.toNNReal (q 0 c-v c))) := by
  dsimp only
  apply integral_nativeExteriorForestDisorderRootLaw_dynamic (restWeight_pos n) (restFeature n)
    pre mid tail ho v q x
  exact native_two_level_star_incoming_product_smooth n j k 0 Ei Es D ho.suffix_end
    ho.suffix_end.suffix_end H e s t _ _ center

end OAI.SKFluctuations.Cavity
