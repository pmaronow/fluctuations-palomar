module

public import ComparisonActualGeneralTargetResponsePreciseNumerics

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree Set Filter MeasureTheory ProbabilityTheory LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 12000000
set_option backward.isDefEq.respectTransparency false

theorem actual_general_target_response_saved_Taylor_of_original_four_prices
    {n : ℕ} {as : List PositiveMass} {i star U : ℕ}
    (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    {Temp d cK Cd Q eps Cdi Di F Z T I : ℝ}
    (htotal : ∀u∈Icc (0:ℝ) 1,(hf u:ℝ)+(bf u:ℝ) ≤ Temp)
    (hd : 0 < d) (hcK : 0 < cK) (hQ : 0 ≤ Q)
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
        (actualGeneralFourCenteredForest bf hf hs hU d j [st])| ≤ Q*d^2)
    (Hother :
      let st:=nativeActualInitialState (S:=Spin n×Bool) as i star 0 (hi.trans (hs.le.trans hU))
      ∀j < depth,|actualGeneralFourOtherSourceErrorSum bf hf U d
        (actualGeneralFourCenteredForest bf hf hs hU d j [st])| ≤ eps*d^4+Cdi*Di*d^3)
    (Hfirst :
      let st:=nativeActualInitialState (S:=Spin n×Bool) as i star 0 (hi.trans (hs.le.trans hU))
      ∀j < depth,|actualGeneralFourFirstHighErrorSum bf hf U d
        (actualGeneralFourCenteredForest bf hf hs hU d j [st])| ≤ F*d^3)
    (Hfrozen :
      let st:=nativeActualInitialState (S:=Spin n×Bool) as i star 0 (hi.trans (hs.le.trans hU))
      ∀j < depth,|actualGeneralFourFrozenChildSum bf hf hs hU d
        (actualGeneralFourCenteredForest bf hf hs hU d j [st])| ≤ Z*d^5)
    (Hterminal :
      let st:=nativeActualInitialState (S:=Spin n×Bool) as i star 0 (hi.trans (hs.le.trans hU))
      |((actualGeneralFourCenteredForest bf hf hs hU d depth [st]).map
        (actualGeneralFourStateResponse (n:=n) bf hf U d)).sum| ≤ T*d^3)
    (HinitialFrozen :
      let st:=nativeActualInitialState (S:=Spin n×Bool) as i star 0 (hi.trans (hs.le.trans hU))
      |actualGeneralFourStateResponse (n:=n) bf hf U d st.freeze| ≤ I*d^5) :
    |actualGeneralTargetLongitudinalResponse (n:=n) bf hf as i U| ≤
      (depth:ℝ)*(d^2*Cdi*Di/(Real.exp (-4*Temp)*cK)+
        d^3*((Cd*Q+eps)/(Real.exp (-4*Temp)*cK)+F+Z*d^2))+
        T*d^3+I*d^5 := by
  have H:=actual_general_target_response_precise_of_original_four_prices
    bf hf hbf hhf htotal hd hcK (mul_nonneg hQ (sq_nonneg d))
    ho hi hs hU hstarK Hdefect depth Hpair Hother Hfirst Hfrozen Hterminal HinitialFrozen
  apply H.trans_eq
  have hden : Real.exp (-4*Temp)*cK ≠ 0 := by positivity
  field_simp [hd.ne',hden]
  ring

end OAI.SKFluctuations.Cavity
