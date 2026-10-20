module

public import ComparisonSignedCavityDynamicExteriorTests
public import ComparisonSignedCavityTwoLevelIncomingErrorProduct
public import ComparisonSignedCavityTwoLevelStarIncomingErrorProduct
public import ComparisonSignedCavityTwoLevelPowerErrorProduct

@[expose] public section

noncomputable section
set_option maxHeartbeats 14000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy

theorem native_two_level_incoming_error_product_eq_conditional (n j k : ℕ)
    {ias tas : List PositiveMass} (Ei : ClockTree (Spin n) ias)
    (Es D : ClockTree (Spin n) tas) (H : Ei.Assignment→Es.Assignment→ℝ)
    (e : Ei.Slot) (s t : D.Slot) (qi qs : ℕ→RestCoordinate n→ℝ≥0)
    (center : ℝ) (E : D.Assignment→ℝ) (xi xs : RestCoordinate n→ℝ) :
    nativeTwoLevelIncomingErrorProduct n j k Ei Es D H e s t qi qs center E xi xs=
      nativeExteriorForestConditionalTest Ei Es D (restWeight n) (restFeature n) qi qs
        (fun η ζ δ=>
          let Y:=nativeStarCenteredProjection n tas qs center xs
          (Y (D.atSlot δ t)-Y (D.atSlot δ s))*H η ζ*
            (deletedOverlap n (joinSpin (D.atSlot δ t,false)) (joinSpin (Ei.atSlot η e,false))-
              deletedOverlap n (joinSpin (D.atSlot δ s,false)) (joinSpin (Ei.atSlot η e,false)))*
            E δ*(Y (D.atSlot δ s)^j*Y (D.atSlot δ t)^k)) xi xs := by
  let Y:=nativeStarCenteredProjection n tas qs center xs
  let Z:=fun δ=>(Y (D.atSlot δ t)-Y (D.atSlot δ s))*E δ*(Y (D.atSlot δ s)^j*Y (D.atSlot δ t)^k)
  have HE:=native_two_level_weighted_target_difference n Ei Es D H e qi qs xi xs Z
    (fun δ=>D.atSlot δ t) (fun δ=>D.atSlot δ s)
  calc
    _=D.expect (restWeight n) (restFeature n) qs (fun δ=>Z δ*
        inner ℝ (WithLp.toLp 2 (normalizedSpin n (D.atSlot δ t))-
          WithLp.toLp 2 (normalizedSpin n (D.atSlot δ s)))
          (nativeTwoLevelWeightedAnchor n Ei Es H e qi qs xi xs)) xs := by
      unfold nativeTwoLevelIncomingErrorProduct ClockTree.expect
      apply Finset.sum_congr rfl
      intro δ _
      dsimp only [Z,Y]
      ring
    _=_:=by
      rw [←HE]
      apply congrArg (fun Q=>nativeExteriorForestConditionalTest Ei Es D (restWeight n) (restFeature n) qi qs Q xi xs)
      funext η ζ δ
      dsimp only [Z,Y]
      ring

theorem native_two_level_star_incoming_error_product_eq_conditional (n j k : ℕ)
    {ias tas : List PositiveMass} (Ei : ClockTree (Spin n) ias)
    (Es D : ClockTree (Spin n) tas) (H : Ei.Assignment→Es.Assignment→ℝ)
    (e : Es.Slot) (s t : D.Slot) (qi qs : ℕ→RestCoordinate n→ℝ≥0)
    (center : ℝ) (E : D.Assignment→ℝ) (xi xs : RestCoordinate n→ℝ) :
    nativeTwoLevelStarIncomingErrorProduct n j k Ei Es D H e s t qi qs center E xi xs=
      nativeExteriorForestConditionalTest Ei Es D (restWeight n) (restFeature n) qi qs
        (fun η ζ δ=>
          let Y:=nativeStarCenteredProjection n tas qs center xs
          (Y (D.atSlot δ t)-Y (D.atSlot δ s))*H η ζ*
            (deletedOverlap n (joinSpin (D.atSlot δ t,false)) (joinSpin (Es.atSlot ζ e,false))-
              deletedOverlap n (joinSpin (D.atSlot δ s,false)) (joinSpin (Es.atSlot ζ e,false)))*
            E δ*(Y (D.atSlot δ s)^j*Y (D.atSlot δ t)^k)) xi xs := by
  simp_rw [deleted_overlap_join_eq_scaled]
  unfold nativeTwoLevelStarIncomingErrorProduct nativeExteriorForestConditionalTest
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

end OAI.SKFluctuations.Cavity
