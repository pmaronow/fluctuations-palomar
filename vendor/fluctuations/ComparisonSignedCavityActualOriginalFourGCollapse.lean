module

public import ComparisonSignedCavityActualOriginalLowOrientation
public import ComparisonSignedCavityActualOriginalGLowAllocation
public import ComparisonSignedCavityActualOriginalGPairMarginal

@[expose] public section

noncomputable section
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators Topology NNReal

theorem native_original_four_G_low_eq_two_forward_rows (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K S : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (hU : U ≤ as.length) (haz : T.splitIndex a z < U) :
    let Q:=fun σ=>P (T.cavityAssignment σ).1
    let A:=fun σ τ : Spin n×Bool=>
      restCenteredFixedForkKernel n b S (T.splitIndex a z) 0 σ.1 τ.1
    nativeOriginalGKernelLowAllocation n q U b h K S T P a z (restCenteredLowKernel n U b S)=
      nativeOriginalConnectedLowForward n 0 (cutFullVariance n q U 1 1 b h K) 0 U K b S T Q a z A+
      nativeOriginalConnectedLowForward n 0 (cutFullVariance n q U 1 1 b h K) 0 U K b S T Q z a A := by
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
  have HE : nativeOriginalGKernelLowAllocation n q U b h K S T P a z
      (restCenteredFixedForkKernel n b S (T.splitIndex a z))=
      (nativeOriginalConnectedLowForward n 0 (cutFullVariance n q U 1 1 b h K) 0 U K b S T Q a z A+
        nativeOriginalConnectedLowReverse n 0 (cutFullVariance n q U 1 1 b h K) 0 U K b S T Q a z A+
        nativeOriginalConnectedLowReverse n 0 (cutFullVariance n q U 1 1 b h K) 0 U K b S T Q z a A+
        nativeOriginalConnectedLowForward n 0 (cutFullVariance n q U 1 1 b h K) 0 U K b S T Q z a A)/2 := by
    unfold nativeOriginalGKernelLowAllocation
    simp_rw [native_original_high_pairing_eq_connected_response n 0
      (cutFullVariance n q U 1 1 b h K) 0 U K b S _ ho _ _ _ hU,HP]
    simp only [mul_add,List.sum_map_add]
    rfl
  rw [native_original_G_centered_low_allocation_eq_fixed_target_fork n q U b h K S T ho P a z hU haz,HE]
  rw [←native_original_connected_low_orientations_equal n 0 (cutFullVariance n q U 1 1 b h K) 0
      U K b S T ho Q a z A hA hU haz,
    ←native_original_connected_low_orientations_equal n 0 (cutFullVariance n q U 1 1 b h K) 0
      U K b S T ho Q z a A hA hU (by rwa [T.splitIndex_symm])]
  ring

end OAI.SKFluctuations.Cavity
