module

public import ComparisonSignedCavityDynamicExteriorTests

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
  [MeasurableSpace S] [StandardBorelSpace S]

theorem integral_native_dynamic_exterior_test
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (pre mid tail : List PositiveMass) {a : ℝ}
    (ho : MassOrdered a (pre++(mid++tail)))
    (Ei : ClockTree S (mid++tail)) (Es D : ClockTree S tail)
    (v : ι→ℝ) (q : ℕ→ι→ℝ) (x : ι→ℝ)
    (J : ((ι→ℝ)×(ι→ℝ))→Ei.Assignment→Es.Assignment→D.Assignment→ℝ)
    (hJ : ∀η ζ δ,BddSmooth 0 (fun z=>J z η ζ δ)) :
    let dq:=cumulativeIncrements (q 0) (fun j=>q (j+1))
    let qi:=fun j=>dq (pre.length+j)
    let qs:=fun j=>dq (pre.length+(mid.length+j))
    let B:=fun xi xs=>nativeExteriorForestConditionalTest Ei Es D w φ qi qs (J (xi,xs)) xi xs
    (∫z,B (exteriorForestIRoot z) (exteriorForestStarRoot z)
      ∂nativeExteriorForestDisorderRootLaw w φ pre mid tail v q x)=
      ∫y,prefixTest (clockSteps pre dq)
        (gaussianHierarchy w φ (clockSteps mid qi++clockSteps tail qs))
        (fun xi=>prefixTest (clockSteps mid qi)
          (gaussianHierarchy w φ (clockSteps tail qs)) (B xi) xi) (x+y)
        ∂Measure.pi (fun i=>gaussianReal 0 (Real.toNNReal (q 0 i-v i))) := by
  dsimp only
  apply integral_nativeExteriorForestDisorderRootLaw_dynamic hw φ pre mid tail ho v q x
    (fun xi xs=>nativeExteriorForestConditionalTest Ei Es D w φ
      (fun j=>cumulativeIncrements (q 0) (fun j=>q (j+1)) (pre.length+j))
      (fun j=>cumulativeIncrements (q 0) (fun j=>q (j+1)) (pre.length+(mid.length+j)))
      (J (xi,xs)) xi xs)
  exact native_dynamic_exterior_test_smooth 0 Ei Es D ho.suffix_end
    ho.suffix_end.suffix_end hw φ _ _ J hJ

theorem integral_native_two_level_incoming_product (n j k : ℕ)
    (pre mid tail : List PositiveMass) {a : ℝ}
    (ho : MassOrdered a (pre++(mid++tail)))
    (Ei : ClockTree (Spin n) (mid++tail)) (Es D : ClockTree (Spin n) tail)
    (v : RestCoordinate n→ℝ) (q : ℕ→RestCoordinate n→ℝ) (x : RestCoordinate n→ℝ)
    (H : Ei.Assignment→Es.Assignment→ℝ) (e : Ei.Slot) (s t : D.Slot) (center : ℝ) :
    let dq:=cumulativeIncrements (q 0) (fun l=>q (l+1))
    let qi:=fun l=>dq (pre.length+l)
    let qs:=fun l=>dq (pre.length+(mid.length+l))
    let B:=nativeTwoLevelIncomingProduct n j k Ei Es D H e s t qi qs center
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
  exact native_two_level_incoming_product_smooth n j k 0 Ei Es D ho.suffix_end
    ho.suffix_end.suffix_end H e s t _ _ center

theorem integral_native_two_level_power_product (n j k : ℕ)
    (pre mid tail : List PositiveMass) {a : ℝ}
    (ho : MassOrdered a (pre++(mid++tail)))
    (Ei : ClockTree (Spin n) (mid++tail)) (Es D : ClockTree (Spin n) tail)
    (v : RestCoordinate n→ℝ) (q : ℕ→RestCoordinate n→ℝ) (x : RestCoordinate n→ℝ)
    (Z : Ei.Assignment→Es.Assignment→D.Assignment→ℝ) (s t : D.Slot) (center : ℝ) :
    let dq:=cumulativeIncrements (q 0) (fun l=>q (l+1))
    let qi:=fun l=>dq (pre.length+l)
    let qs:=fun l=>dq (pre.length+(mid.length+l))
    let B:=nativeTwoLevelPowerProduct n j k Ei Es D Z s t qi qs center
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
  exact native_two_level_power_product_smooth n j k 0 Ei Es D ho.suffix_end
    ho.suffix_end.suffix_end Z s t _ _ center

end OAI.SKFluctuations.Cavity
