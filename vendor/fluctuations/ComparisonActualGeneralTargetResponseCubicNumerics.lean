module

public import ComparisonActualGeneralTargetFourReadout
public import ComparisonActualGeneralFourFirstHighIteration

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

 theorem actual_general_target_response_cubic_of_original_four_prices
    {n : ℕ} {as : List PositiveMass} {i star U : ℕ}
    (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    {Temp d cK q Cd Co Cf Cfr Ct Ci : ℝ}
    (htotal : ∀u∈Icc (0:ℝ) 1,(hf u:ℝ)+(bf u:ℝ) ≤ Temp)
    (hd : 0 < d) (hd1 : d ≤ 1) (hcK : 0 < cK) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hCd : 0 ≤ Cd) (_hCo : 0 ≤ Co) (_hCf : 0 ≤ Cf) (hCfr : 0 ≤ Cfr) (_hCt : 0 ≤ Ct) (hCi : 0 ≤ Ci)
    (ho : MassOrdered 0 as) (hi : i ≤ star) (hs : star < U) (hU : U ≤ as.length)
    (hstarK : cK*d ≤ nativeContinuumMixedClock n bf hf as star)
    (Hdefect :
      let K:=nativeContinuumMixedClock n bf hf as
      let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
      |1-(bf (partitionPoint 0 as star):ℝ)*chi^2| ≤ Cd*d^2)
    (depth : ℕ)
    (Hpair :
      let st:=nativeActualInitialState (S:=Spin n×Bool) as i star 0 (hi.trans (hs.le.trans hU))
      ∀j < depth,|actualGeneralFourPairSum bf hf U d
        (actualGeneralFourCenteredForest bf hf hs hU d j [st])| ≤ q*d^2)
    (Hother :
      let st:=nativeActualInitialState (S:=Spin n×Bool) as i star 0 (hi.trans (hs.le.trans hU))
      ∀j < depth,|actualGeneralFourOtherSourceErrorSum bf hf U d
        (actualGeneralFourCenteredForest bf hf hs hU d j [st])| ≤ Co*d^4)
    (Hfirst :
      let st:=nativeActualInitialState (S:=Spin n×Bool) as i star 0 (hi.trans (hs.le.trans hU))
      ∀j < depth,|actualGeneralFourFirstHighErrorSum bf hf U d
        (actualGeneralFourCenteredForest bf hf hs hU d j [st])| ≤ Cf*d^3)
    (Hfrozen :
      let st:=nativeActualInitialState (S:=Spin n×Bool) as i star 0 (hi.trans (hs.le.trans hU))
      ∀j < depth,|actualGeneralFourFrozenChildSum bf hf hs hU d
        (actualGeneralFourCenteredForest bf hf hs hU d j [st])| ≤ Cfr*d^5)
    (Hterminal :
      let st:=nativeActualInitialState (S:=Spin n×Bool) as i star 0 (hi.trans (hs.le.trans hU))
      |((actualGeneralFourCenteredForest bf hf hs hU d depth [st]).map
        (actualGeneralFourStateResponse bf hf U d)).sum| ≤ Ct*d^3)
    (HinitialFrozen :
      let st:=nativeActualInitialState (S:=Spin n×Bool) as i star 0 (hi.trans (hs.le.trans hU))
      |actualGeneralFourStateResponse bf hf U d st.freeze| ≤ Ci*d^5) :
    let den:=Real.exp (-4*Temp)*cK
    |actualGeneralTargetLongitudinalResponse (n:=n) bf hf as i U| ≤
      ((depth:ℝ)*((Cd+Co)/den+Cf+Cfr)+Ct+Ci)*d^3 := by
  dsimp only at Hdefect Hpair Hother Hfirst Hfrozen Hterminal HinitialFrozen ⊢
  let st:=nativeActualInitialState (S:=Spin n×Bool) as i star 0 (hi.trans (hs.le.trans hU))
  let den:=Real.exp (-4*Temp)*cK
  let defect:=|1-(bf (partitionPoint 0 as star):ℝ)*
    (scalarTerminal.schedule (scalarBoundaryClocks as
      (relocatedClock U 0 (nativeContinuumMixedClock n bf hf as)))).H 0 0^2|
  let Clevel:=(Cd+Co)/den+Cf+Cfr
  have hden : 0 < den:=by dsimp only [den];positivity
  have hD : 0 ≤ defect:=abs_nonneg _
  have HD : defect ≤ Cd*d^2:=Hdefect
  have Hd53 : d^5 ≤ d^3:=by
    have H2:=pow_le_pow_left₀ hd.le hd1 2
    norm_num only [one_pow] at H2
    have H:=mul_le_mul_of_nonneg_right H2 (pow_nonneg hd.le 3)
    nlinarith only [H]
  have Hnum : defect*(q*d^2)+Co*d^4 ≤ (Cd+Co)*d^4:=by
    have Hq:=mul_le_mul_of_nonneg_right hq1 (sq_nonneg d)
    have H1:=mul_le_mul HD Hq (mul_nonneg hq (sq_nonneg d)) (mul_nonneg hCd (sq_nonneg d))
    nlinarith only [H1]
  have Hnumerator : (defect*(q*d^2)+Co*d^4)/(den*d) ≤ (Cd+Co)/den*d^3:=by
    have H:=div_le_div_of_nonneg_right Hnum (mul_nonneg hden.le hd.le)
    apply H.trans_eq
    field_simp [hden.ne',hd.ne']
  have Hlevel : (defect*(q*d^2)+Co*d^4)/(den*d)+Cfr*d^5+Cf*d^3 ≤ Clevel*d^3:=by
    have HF:=mul_le_mul_of_nonneg_left Hd53 hCfr
    dsimp only [Clevel]
    nlinarith only [Hnumerator,HF]
  have HG : NativeActualResourceGenerated i star U [.initial] st.generation st.tree st.term:=
    .physical (.seed as hU 0 .initial (Or.inl rfl) (hi.trans (hs.le.trans hU)))
  have Hvalid : ∀Q∈[st],NativeActualResourceGenerated i star U [.initial] Q.generation Q.tree Q.term:=by
    intro Q hQ;obtain rfl:=List.mem_singleton.mp hQ;exact HG
  have Hprices : ∀j∈List.range depth,
      |((actualGeneralFourCenteredForest bf hf hs hU d j [st]).map
        (actualGeneralFourRecursionError bf hf hs hU d)).sum| ≤ Clevel*d^3:=by
    intro j hj
    let K:=nativeContinuumMixedClock n bf hf as
    let b:=fun l=>(bf (partitionPoint 0 as l):ℝ)
    let weight:=fun (Q : NativeActualResourceState (Spin n×Bool) as i star) tag=>
      nativeOriginalClockParentWeight d U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag)
    have HV:=nativeActualFourCenteredForest_valid (nativeOriginalHighRowGamma U K)
      hs (hs.le.trans hU) weight j [st] Hvalid
    have H:=actual_general_four_recursion_error_sum_first_high_abs_le (n:=n) bf hf hbf hhf htotal hd hcK
      ho hi hs hU hstarK _ HV
      (Hpair j (List.mem_range.mp hj)) (Hother j (List.mem_range.mp hj))
      (Hfirst j (List.mem_range.mp hj)) (Hfrozen j (List.mem_range.mp hj))
    exact H.trans Hlevel
  have H:=actual_general_target_response_bound_of_level_prices (n:=n) bf hf hbf hhf as d i star U
    hi hs hU ho hd.ne' ((mul_pos hcK hd).trans_le hstarK) depth (fun _=>Clevel*d^3)
    (Ct*d^3) (Ci*d^5) Hprices Hterminal HinitialFrozen
  simp only [List.map_const',List.length_range,List.sum_replicate,nsmul_eq_mul] at H
  apply H.trans
  have HF:=mul_le_mul_of_nonneg_left Hd53 hCi
  dsimp only [Clevel,den]
  nlinarith only [HF]

end OAI.SKFluctuations.Cavity
