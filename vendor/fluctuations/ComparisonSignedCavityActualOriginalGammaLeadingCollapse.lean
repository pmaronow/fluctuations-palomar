module

public import ComparisonSignedCavityActualOriginalGammaLowOrientation
public import ComparisonSignedCavityActualFullLeadingEndpoint

@[expose] public section

noncomputable section
set_option maxHeartbeats 22000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators Topology NNReal

theorem native_original_gamma_leading_eq_forward_row (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K S : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (hU : U ≤ as.length) (haz : T.splitIndex a z < U) :
    let Q:=fun σ=>P (T.cavityAssignment σ).1
    let A:=fun σ τ : Spin n×Bool=>
      restCenteredFixedForkKernel n b S (T.splitIndex a z) 0 σ.1 τ.1
    nativeCenteredLowGammaOriginalLeading n q U b h K S T P a z=
      nativeOriginalGammaLowForward n 0 (cutFullVariance n q U 1 1 b h K) 0 U K T Q a z A := by
  dsimp only
  let Q:=fun σ=>P (T.cavityAssignment σ).1
  let A:=fun σ τ : Spin n×Bool=>
    restCenteredFixedForkKernel n b S (T.splitIndex a z) 0 σ.1 τ.1
  have hA : ∀σ τ,A σ τ=A τ σ := by
    intro σ τ
    have HE : (∑i,spinValue (σ.1 i)*spinValue (τ.1 i))=
        ∑i,spinValue (τ.1 i)*spinValue (σ.1 i) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    simp only [A,restCenteredFixedForkKernel,HE]
  have HP (p : MarkedPlacement T) (r : MarkedPlacement p.tree) :
      (fun σ=>insertedRestTest P (restCenteredFixedForkKernel n b S (T.splitIndex a z)) p r
        (r.tree.cavityAssignment σ).1)=
      (fun σ=>Q (p.restrict (r.restrict σ))*A (p.spin (r.restrict σ)) (r.spin σ)) := by
    funext σ
    simp only [Q,A,insertedRestTest,restCenteredFixedForkKernel]
    rw [←r.restRestrict_actual,←p.restRestrict_actual,←p.restSpin_actual,←r.restSpin_actual]
  have Hpoint (p : MarkedPlacement T) (r : MarkedPlacement p.tree) :
      nativeLowScalarPairing r.tree U K (r.embed (p.embed a)) (r.embed (p.embed z))
        (r.embed p.mark) r.mark*
      r.tree.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 1 1 b h K)
        (fun σ=>Q (p.restrict (r.restrict σ))*A (p.spin (r.restrict σ)) (r.spin σ)) 0=
      fullScalarCutGamma r.tree U K (r.embed (p.embed z)) r.mark*
        nativeOriginalGammaWeightedExpectation n 0 (cutFullVariance n q U 1 1 b h K) 0 U K r.tree
          (fun σ=>Q (p.restrict (r.restrict σ))*A (p.spin (r.restrict σ)) (r.spin σ))
          (r.embed (p.embed a)) (r.embed p.mark)+
      fullScalarCutGamma r.tree U K (r.embed (p.embed z)) (r.embed p.mark)*
        nativeOriginalGammaWeightedExpectation n 0 (cutFullVariance n q U 1 1 b h K) 0 U K r.tree
          (fun σ=>Q (p.restrict (r.restrict σ))*A (p.spin (r.restrict σ)) (r.spin σ))
          (r.embed (p.embed a)) r.mark := by
    unfold nativeLowScalarPairing nativeOriginalGammaWeightedExpectation
    ring
  have HE : nativeCenteredLowGammaFixedForkOriginalLeading n q U b h K S T P a z=
      (nativeOriginalGammaLowForward n 0 (cutFullVariance n q U 1 1 b h K) 0 U K T Q a z A+
        nativeOriginalGammaLowReverse n 0 (cutFullVariance n q U 1 1 b h K) 0 U K T Q a z A)/2 := by
    unfold nativeCenteredLowGammaFixedForkOriginalLeading
    simp_rw [HP,Hpoint]
    simp only [mul_add,List.sum_map_add]
    rfl
  rw [native_original_leading_eq_fixed_target_fork n q U b h K S T ho P a z hU haz,HE]
  rw [←native_original_gamma_low_orientations_equal n 0 (cutFullVariance n q U 1 1 b h K) 0
    U K T ho Q a z A hA hU haz]
  ring

end OAI.SKFluctuations.Cavity
