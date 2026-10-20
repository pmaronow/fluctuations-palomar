module

public import ComparisonSignedCavityDynamicExteriorRootLaw
public import ComparisonSignedCavityTwoLevelPowerProduct
public import ComparisonSignedCavityTwoLevelIncomingProduct

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

theorem native_dynamic_exterior_test_smooth (r : ℕ)
    {ias tas : List PositiveMass} (Ei : ClockTree S ias) (Es D : ClockTree S tas)
    {ai ast : ℝ} (hoi : MassOrdered ai ias) (hot : MassOrdered ast tas)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (qi qs : ℕ→ι→ℝ≥0)
    (J : ((ι→ℝ)×(ι→ℝ))→Ei.Assignment→Es.Assignment→D.Assignment→ℝ)
    (hJ : ∀η ζ δ,BddSmooth r (fun z=>J z η ζ δ)) :
    BddSmooth r (fun z : (ι→ℝ)×(ι→ℝ)=>
      nativeExteriorForestConditionalTest Ei Es D w φ qi qs (J z) z.1 z.2) := by
  simp_rw [nativeExteriorForestConditionalTest_eq_joint,ClockTree.expect_fork]
  unfold ClockTree.expect
  apply BddSmooth.sum Finset.univ
  intro η _
  apply BddSmooth.mul ((Ei.weight_smooth hw φ hoi qi η r).compCLM
    (ContinuousLinearMap.fst ℝ (ι→ℝ) (ι→ℝ)))
  apply BddSmooth.sum Finset.univ
  intro ζ _
  apply BddSmooth.mul ((Es.weight_smooth hw φ hot qs ζ r).compCLM
    (ContinuousLinearMap.snd ℝ (ι→ℝ) (ι→ℝ)))
  apply BddSmooth.sum Finset.univ
  intro δ _
  exact ((D.weight_smooth hw φ hot qs δ r).compCLM
    (ContinuousLinearMap.snd ℝ (ι→ℝ) (ι→ℝ))).mul (hJ η ζ δ)

theorem native_two_level_power_product_smooth (n j k r : ℕ)
    {ias tas : List PositiveMass} (Ei : ClockTree (Spin n) ias)
    (Es D : ClockTree (Spin n) tas) {ai ast : ℝ}
    (hoi : MassOrdered ai ias) (hot : MassOrdered ast tas)
    (Z : Ei.Assignment→Es.Assignment→D.Assignment→ℝ)
    (s t : D.Slot) (qi qs : ℕ→RestCoordinate n→ℝ≥0) (center : ℝ) :
    BddSmooth r (fun z : (RestCoordinate n→ℝ)×(RestCoordinate n→ℝ)=>
      nativeTwoLevelPowerProduct n j k Ei Es D Z s t qi qs center z.1 z.2) := by
  unfold nativeTwoLevelPowerProduct
  apply native_dynamic_exterior_test_smooth r Ei Es D hoi hot
    (restWeight_pos n) (restFeature n) qi qs
  intro η ζ δ
  have HS:=(native_star_centered_projection_smooth n hot qs center (D.atSlot δ s) r).compCLM
    (ContinuousLinearMap.snd ℝ (RestCoordinate n→ℝ) (RestCoordinate n→ℝ))
  have HT:=(native_star_centered_projection_smooth n hot qs center (D.atSlot δ t) r).compCLM
    (ContinuousLinearMap.snd ℝ (RestCoordinate n→ℝ) (RestCoordinate n→ℝ))
  exact (((HT.sub HS).pow 2).mul_const (Z η ζ δ)).mul ((HS.pow j).mul (HT.pow k))

theorem native_two_level_incoming_product_eq_conditional (n j k : ℕ)
    {ias tas : List PositiveMass} (Ei : ClockTree (Spin n) ias)
    (Es D : ClockTree (Spin n) tas) (H : Ei.Assignment→Es.Assignment→ℝ)
    (e : Ei.Slot) (s t : D.Slot) (qi qs : ℕ→RestCoordinate n→ℝ≥0)
    (center : ℝ) (xi xs : RestCoordinate n→ℝ) :
    nativeTwoLevelIncomingProduct n j k Ei Es D H e s t qi qs center xi xs=
      nativeExteriorForestConditionalTest Ei Es D (restWeight n) (restFeature n) qi qs
        (fun η ζ δ=>
          let Y:=nativeStarCenteredProjection n tas qs center xs
          (Y (D.atSlot δ t)-Y (D.atSlot δ s))*H η ζ*
            (deletedOverlap n (joinSpin (D.atSlot δ t,false)) (joinSpin (Ei.atSlot η e,false))-
              deletedOverlap n (joinSpin (D.atSlot δ s,false)) (joinSpin (Ei.atSlot η e,false)))*
            (Y (D.atSlot δ s)^j*Y (D.atSlot δ t)^k)) xi xs := by
  let Y:=nativeStarCenteredProjection n tas qs center xs
  let Z:=fun δ=>(Y (D.atSlot δ t)-Y (D.atSlot δ s))*(Y (D.atSlot δ s)^j*Y (D.atSlot δ t)^k)
  have HE:=native_two_level_weighted_target_difference n Ei Es D H e qi qs xi xs Z
    (fun δ=>D.atSlot δ t) (fun δ=>D.atSlot δ s)
  calc
    _=D.expect (restWeight n) (restFeature n) qs (fun δ=>Z δ*
        inner ℝ (WithLp.toLp 2 (normalizedSpin n (D.atSlot δ t))-
          WithLp.toLp 2 (normalizedSpin n (D.atSlot δ s)))
          (nativeTwoLevelWeightedAnchor n Ei Es H e qi qs xi xs)) xs := by
      unfold nativeTwoLevelIncomingProduct ClockTree.expect
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

theorem native_two_level_incoming_product_smooth (n j k r : ℕ)
    {ias tas : List PositiveMass} (Ei : ClockTree (Spin n) ias)
    (Es D : ClockTree (Spin n) tas) {ai ast : ℝ}
    (hoi : MassOrdered ai ias) (hot : MassOrdered ast tas)
    (H : Ei.Assignment→Es.Assignment→ℝ) (e : Ei.Slot) (s t : D.Slot)
    (qi qs : ℕ→RestCoordinate n→ℝ≥0) (center : ℝ) :
    BddSmooth r (fun z : (RestCoordinate n→ℝ)×(RestCoordinate n→ℝ)=>
      nativeTwoLevelIncomingProduct n j k Ei Es D H e s t qi qs center z.1 z.2) := by
  simp_rw [native_two_level_incoming_product_eq_conditional]
  apply native_dynamic_exterior_test_smooth r Ei Es D hoi hot
    (restWeight_pos n) (restFeature n) qi qs
  intro η ζ δ
  have HS:=(native_star_centered_projection_smooth n hot qs center (D.atSlot δ s) r).compCLM
    (ContinuousLinearMap.snd ℝ (RestCoordinate n→ℝ) (RestCoordinate n→ℝ))
  have HT:=(native_star_centered_projection_smooth n hot qs center (D.atSlot δ t) r).compCLM
    (ContinuousLinearMap.snd ℝ (RestCoordinate n→ℝ) (RestCoordinate n→ℝ))
  exact (((HT.sub HS).mul_const (H η ζ)).mul_const _).mul ((HS.pow j).mul (HT.pow k))

end OAI.SKFluctuations.Cavity
