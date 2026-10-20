module

public import ComparisonActualGeneralTargetResponseCubicNumerics

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree Set Filter MeasureTheory ProbabilityTheory LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 12000000
set_option backward.isDefEq.respectTransparency false

theorem actual_general_target_response_precise_of_original_four_prices
    {n : ℕ} {as : List PositiveMass} {i star U : ℕ}
    (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    {Temp d cK D P O F Z T I : ℝ}
    (htotal : ∀u∈Icc (0:ℝ) 1,(hf u:ℝ)+(bf u:ℝ) ≤ Temp)
    (hd : 0 < d) (hcK : 0 < cK) (hP : 0 ≤ P)
    (ho : MassOrdered 0 as) (hi : i ≤ star) (hs : star < U) (hU : U ≤ as.length)
    (hstarK : cK*d ≤ nativeContinuumMixedClock n bf hf as star)
    (Hdefect :
      let K:=nativeContinuumMixedClock n bf hf as
      let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
      |1-(bf (partitionPoint 0 as star):ℝ)*chi^2| ≤ D)
    (depth : ℕ)
    (Hpair :
      let st:=nativeActualInitialState (S:=Spin n×Bool) as i star 0 (hi.trans (hs.le.trans hU))
      ∀j < depth,|actualGeneralFourPairSum bf hf U d
        (actualGeneralFourCenteredForest bf hf hs hU d j [st])| ≤ P)
    (Hother :
      let st:=nativeActualInitialState (S:=Spin n×Bool) as i star 0 (hi.trans (hs.le.trans hU))
      ∀j < depth,|actualGeneralFourOtherSourceErrorSum bf hf U d
        (actualGeneralFourCenteredForest bf hf hs hU d j [st])| ≤ O)
    (Hfirst :
      let st:=nativeActualInitialState (S:=Spin n×Bool) as i star 0 (hi.trans (hs.le.trans hU))
      ∀j < depth,|actualGeneralFourFirstHighErrorSum bf hf U d
        (actualGeneralFourCenteredForest bf hf hs hU d j [st])| ≤ F)
    (Hfrozen :
      let st:=nativeActualInitialState (S:=Spin n×Bool) as i star 0 (hi.trans (hs.le.trans hU))
      ∀j < depth,|actualGeneralFourFrozenChildSum bf hf hs hU d
        (actualGeneralFourCenteredForest bf hf hs hU d j [st])| ≤ Z)
    (Hterminal :
      let st:=nativeActualInitialState (S:=Spin n×Bool) as i star 0 (hi.trans (hs.le.trans hU))
      |((actualGeneralFourCenteredForest bf hf hs hU d depth [st]).map
        (actualGeneralFourStateResponse (n:=n) bf hf U d)).sum| ≤ T)
    (HinitialFrozen :
      let st:=nativeActualInitialState (S:=Spin n×Bool) as i star 0 (hi.trans (hs.le.trans hU))
      |actualGeneralFourStateResponse (n:=n) bf hf U d st.freeze| ≤ I) :
    |actualGeneralTargetLongitudinalResponse (n:=n) bf hf as i U| ≤
      (depth:ℝ)*((D*P+O)/(Real.exp (-4*Temp)*cK*d)+Z+F)+T+I := by
  dsimp only at Hdefect Hpair Hother Hfirst Hfrozen Hterminal HinitialFrozen ⊢
  let st:=nativeActualInitialState (S:=Spin n×Bool) as i star 0 (hi.trans (hs.le.trans hU))
  let den:=Real.exp (-4*Temp)*cK*d
  let levelBudget:=(D*P+O)/den+Z+F
  have hden : 0 < den := by dsimp only [den];positivity
  have Hprices : ∀j∈List.range depth,
      |((actualGeneralFourCenteredForest bf hf hs hU d j [st]).map
        (actualGeneralFourRecursionError bf hf hs hU d)).sum|≤levelBudget := by
    intro j hj
    let K:=nativeContinuumMixedClock n bf hf as
    let b:=fun l=>(bf (partitionPoint 0 as l):ℝ)
    let weight:=fun (Q : NativeActualResourceState (Spin n×Bool) as i star) tag=>
      nativeOriginalClockParentWeight d U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag)
    have HG : NativeActualResourceGenerated i star U [.initial] st.generation st.tree st.term:=
      .physical (.seed as hU 0 .initial (Or.inl rfl) (hi.trans (hs.le.trans hU)))
    have Hvalid : ∀Q∈[st],NativeActualResourceGenerated i star U [.initial]
        Q.generation Q.tree Q.term:=by
      intro Q hQ;obtain rfl:=List.mem_singleton.mp hQ;exact HG
    have HV:=nativeActualFourCenteredForest_valid (nativeOriginalHighRowGamma U K)
      hs (hs.le.trans hU) weight j [st] Hvalid
    have H:=actual_general_four_recursion_error_sum_first_high_abs_le (n:=n)
      bf hf hbf hhf htotal hd hcK ho hi hs hU hstarK _ HV
      (Hpair j (List.mem_range.mp hj)) (Hother j (List.mem_range.mp hj))
      (Hfirst j (List.mem_range.mp hj)) (Hfrozen j (List.mem_range.mp hj))
    have Hmul : |1-(bf (partitionPoint 0 as star):ℝ)*
        (scalarTerminal.schedule (scalarBoundaryClocks as
          (relocatedClock U 0 (nativeContinuumMixedClock n bf hf as)))).H 0 0^2| * P ≤ D*P :=
      mul_le_mul_of_nonneg_right Hdefect hP
    have Hdiv := div_le_div_of_nonneg_right (add_le_add_right Hmul O) hden.le
    dsimp only [levelBudget,den] at *
    have Hdiv' : (|1-(bf (partitionPoint 0 as star):ℝ)*
        (scalarTerminal.schedule (scalarBoundaryClocks as
          (relocatedClock U 0 (nativeContinuumMixedClock n bf hf as)))).H 0 0^2| * P+O)/
          (Real.exp (-4*Temp)*cK*d) ≤ (D*P+O)/(Real.exp (-4*Temp)*cK*d) := by
      simpa only [add_comm O] using Hdiv
    change |((actualGeneralFourCenteredForest bf hf hs hU d j [st]).map
      (actualGeneralFourRecursionError bf hf hs hU d)).sum| ≤ _ at H
    linarith only [H,Hdiv']
  have H:=actual_general_target_response_bound_of_level_prices (n:=n)
    bf hf hbf hhf as d i star U hi hs hU ho hd.ne'
    ((mul_pos hcK hd).trans_le hstarK) depth (fun _=>levelBudget) T I
    Hprices Hterminal HinitialFrozen
  simp only [List.map_const',List.length_range,List.sum_replicate,nsmul_eq_mul] at H
  simpa only [levelBudget,den] using H

end OAI.SKFluctuations.Cavity
