module

public import ComparisonSignedCavitySecondLowActualClassifiedRetainedCSource
public import ComparisonSignedCavitySecondLowUnweightedCCoupledPrefixSource

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false

theorem native_second_low_original_high_c_eq_classified_old_add_complete_coupled_prefix
    (n : ℕ) (pre mid tail : List PositiveMass)
    (T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (f c z : T.Slot)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    (ho : MassOrdered 0 (pre++(mid++tail))) (hU0 : 0 < U)
    (hU : U ≤ (pre++(mid++tail)).length)
    (Hfc : T.splitIndex f c < U) (Hcz : T.splitIndex c z < U)
    (E : NativeSecondLowClassifiedRetainedWholeCSource n pre mid tail T f c z 0 q 0)
    (P : T.cavityLeft.Assignment→ℝ) :
    nativeSecondLowUnweightedCRow n q U b h K T f c z P=
      partitionPoint 0 (pre++(mid++tail)) U*
        (∫r,nativeExteriorForestConditionalTest E.source.Ei E.source.Es E.source.D
          (restWeight n) (restFeature n)
          (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j))
          (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+(mid.length+j)))
          (fun η ζ δ=>(E.toWholeCSource ho).fullP P η ζ δ*
            (E.toWholeCSource ho).twoLow U b h K η ζ (E.source.D.atSlot δ E.source.target))
          (exteriorForestIRoot r) (exteriorForestStarRoot r)
          ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0)+
      nativeSecondLowUnweightedCCoupledPrefixSource n q U b h K T f c z P := by
  have HO:=(E.toWholeCSource ho).old_payload_whole_law P U b h K
  dsimp only [NativeSecondLowClassifiedRetainedWholeCSource.toWholeCSource] at HO
  rw [native_second_low_unweighted_c_eq_old_baseline_add_forest_replacement n q U b h K T ho
    hU0 hU f c z P,HO,
    native_second_low_original_unweighted_c_replacement_eq_coupled_prefix n q U b h K T ho
      hU0 hU f c z Hfc Hcz P]
  rfl

end OAI.SKFluctuations.Cavity
