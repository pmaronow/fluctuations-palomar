module

public import ComparisonSignedCavitySecondLowConditionalCFoldPrefixRegularity
public import ComparisonSignedCavitySecondLowActualClassifiedHighCSource
public import ComparisonSignedCavitySecondLowClassifiedDyadicSource
public import ComparisonSignedCavitySecondLowUnweightedCCoupledPrefixSource

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
set_option maxHeartbeats 50000000
set_option backward.isDefEq.respectTransparency false

theorem native_second_low_original_unweighted_c_replacement_eq_classified_complete_fold
    (n : ℕ) (pre mid tail : List PositiveMass)
    (T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (f c z : T.Slot)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    (ho : MassOrdered 0 (pre++(mid++tail))) (hstar : pre.length+mid.length < U)
    (hU : U ≤ (pre++(mid++tail)).length) (Hfc : T.splitIndex f c < U) (Hcz : T.splitIndex c z < U)
    (E : NativeSecondLowClassifiedHighWholeCSource n pre mid tail T f c z 0 q 0)
    (P : T.cavityLeft.Assignment→ℝ) :
    nativeSecondLowUnweightedCReplacementRow n q U b h K T f c z P=
      nativeSecondLowClassifiedCompleteCFold E.toRetainedCSource U q b h K P := by
  let cum:=cumulativeIncrements (q 0) (fun j=>q (j+1))
  let qi:=fun j=>cum (pre.length+j)
  let qs:=fun j=>cum (pre.length+(mid.length+j))
  let star:=pre.length+mid.length
  let astar:=partitionPoint 0 (pre++(mid++tail)) star
  let uD:=U-star
  let P0:=fun η ζ δ=>P (E.source.core.read η ζ δ)
  let Q:=fun sf sc sz=>restLowKernel n U b h (T.splitIndex f c) sf sc*
    restLowKernel n U b h (T.splitIndex c z) sc sz-
    (if T.splitIndex f c<U then K (T.splitIndex f c) else 0)*
      (if T.splitIndex c z<U then K (T.splitIndex c z) else 0)
  let B:=nativeExteriorCompleteCFold E.source.core.Ei E.source.core.Es E.source.core.D
    (restWeight n) (restFeature n) E.source.core.target uD astar qi qs P0 E.outsideF E.outsideZ Q
  have has : astar=partitionEnd (partitionEnd 0 pre) mid := by
    dsimp only [astar,star]
    rw [native_classified_star_mass_eq_nested_prefix,partitionPoint_eq_end_take,partitionPoint_eq_end_take]
    simp only [List.take_length]
  have hoD : MassOrdered astar tail := by rw [has];exact ho.suffix_end.suffix_end
  have huD : 0 < uD := by dsimp only [uD,star];omega
  have huDlen : uD ≤ tail.length := by simp only [List.length_append] at hU;dsimp only [uD,star];omega
  have hroot : uD=0 → 0 < astar := by omega
  have hB : BddSmooth 0 B := nativeExteriorCompleteCFold_smooth_joint E.source.core.Ei E.source.core.Es
    E.source.core.D E.source.core.target uD (restWeight_pos n) (restFeature n) ho.suffix_end hoD
    huDlen hroot qi qs P0 E.outsideF E.outsideZ Q
  have hBs : ∀xi,BddSmooth 0 (fun xs=>B (xi,xs)) := fun xi=>
    nativeExteriorCompleteCFold_smooth_star E.source.core.Ei E.source.core.Es E.source.core.D
      E.source.core.target uD (restWeight_pos n) (restFeature n) hoD huDlen hroot qi qs
      P0 E.outsideF E.outsideZ Q xi
  have hmass : partitionPoint (partitionEnd 0 pre) (mid++tail) mid.length=astar := by
    exact (native_classified_partitionPoint_append_shift 0 pre (mid++tail) mid.length).symm
  have hA : BddSmooth 0 (fun xi=>prefixTest (clockSteps mid qi)
      (gaussianHierarchy (restWeight n) (restFeature n) (clockSteps tail qs)) (fun xs=>B (xi,xs)) xi) := by
    have HA:=native_classified_conditional_c_fold_mid_prefix_smooth0 mid tail E.source.core.Ei E.source.core.Es
      E.source.core.D E.source.core.target (U-pre.length) (by omega) (by simp only [List.length_append] at hU ⊢;omega)
      (restWeight_pos n) (restFeature n) ho.suffix_end qi P0 E.outsideF E.outsideZ Q
    rw [hmass] at HA
    simpa only [Nat.sub_sub] using HA
  rw [native_second_low_original_unweighted_c_replacement_eq_coupled_prefix n q U b h K T ho
    (by omega) hU f c z Hfc Hcz P]
  unfold nativeSecondLowUnweightedCCoupledPrefixSource nativeSecondLowClassifiedCompleteCFold
  change (∫y,nativeSecondLowCCouplingFold (restWeight n) (restFeature n) T.cavityLeft
      (T.cavityLeftSlot c) U 0 cum P (.slot (T.cavityLeftSlot f)) (.slot (T.cavityLeftSlot z)) Q y
      ∂Measure.pi (fun i=>gaussianReal 0 (Real.toNNReal (q 0 i))))=
    ∫r,B (exteriorForestIRoot r,exteriorForestStarRoot r)
      ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0
  rw [←native_two_level_disorder_conditional_integral pre mid tail (restWeight_pos n) (restFeature n)
    ho 0 q 0 B hB hBs hA]
  simp only [Pi.zero_apply,sub_zero,zero_add]
  apply integral_congr_ae
  refine Eventually.of_forall fun y=>?_
  have HM (xi : RestCoordinate n→ℝ) : nativeClassifiedConditionalCFold E.source.core.Ei E.source.core.Es E.source.core.D
      E.source.core.target uD astar (restWeight n) (restFeature n) qi qs P0 E.outsideF E.outsideZ Q xi=
      fun xs=>B (xi,xs) := by
    funext xs
    rfl
  have HH:=E.c_coupling_fold_eq_conditional_prefix U hstar hU ho (by rwa [T.splitIndex_symm]) Hcz cum P Q y
  change nativeSecondLowCCouplingFold (restWeight n) (restFeature n) T.cavityLeft
      (T.cavityLeftSlot c) U 0 cum P (.slot (T.cavityLeftSlot f)) (.slot (T.cavityLeftSlot z)) Q y=
    prefixTest (clockSteps pre cum) (gaussianHierarchy (restWeight n) (restFeature n) (clockSteps (mid++tail) qi))
      (fun xi=>prefixTest (clockSteps mid qi) (gaussianHierarchy (restWeight n) (restFeature n) (clockSteps tail qs))
        (nativeClassifiedConditionalCFold E.source.core.Ei E.source.core.Es E.source.core.D E.source.core.target
          uD astar (restWeight n) (restFeature n) qi qs P0 E.outsideF E.outsideZ Q xi) xi) y at HH
  simp_rw [HM] at HH
  exact HH

end OAI.SKFluctuations.Cavity
