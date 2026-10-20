module

public import ComparisonActualGeneralTargetResponseSavedTaylorNumerics

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree Set Filter MeasureTheory ProbabilityTheory LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 12000000

theorem actual_general_target_response_variable_saved_of_original_four_prices
    {n : ℕ} {as : List PositiveMass} {i star U : ℕ}
    (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    {Temp d cK Cd Q A B F Z T I : ℝ}
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
        (actualGeneralFourCenteredForest bf hf hs hU d j [st])| ≤ A*d^4+B*d^3)
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
      (depth:ℝ)*(d^2*B/(Real.exp (-4*Temp)*cK)+
        d^3*((Cd*Q+A)/(Real.exp (-4*Temp)*cK)+F+Z*d^2))+
        T*d^3+I*d^5 := by
  have Hother' :
      let st:=nativeActualInitialState (S:=Spin n×Bool) as i star 0 (hi.trans (hs.le.trans hU))
      ∀j < depth,|actualGeneralFourOtherSourceErrorSum bf hf U d
        (actualGeneralFourCenteredForest bf hf hs hU d j [st])| ≤ A*d^4+1*B*d^3 := by
    simpa only [one_mul] using Hother
  simpa only [one_mul,mul_one] using
    (actual_general_target_response_saved_Taylor_of_original_four_prices
      (Cdi:=1) (Di:=B) (eps:=A) bf hf hbf hhf htotal hd hcK hQ
      ho hi hs hU hstarK Hdefect depth Hpair Hother' Hfirst Hfrozen Hterminal HinitialFrozen)

theorem actual_general_initial_saved_forest_other_normal_form
    (d V VP rho base second linear power radius : ℝ) :
    d^4*(base+2*second)*(2*V)+d^3*linear*(2*V)+
      d^2*power*(2*VP*rho*d^2)+d^3*(power+radius)*(2*VP*rho*d) =
    (2*V*(base+2*second)+2*VP*rho*(2*power+radius))*d^4+
      (2*V*linear)*d^3 := by
  ring

end OAI.SKFluctuations.Cavity
