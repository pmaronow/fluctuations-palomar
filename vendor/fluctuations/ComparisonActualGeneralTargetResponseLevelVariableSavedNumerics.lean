module

public import ComparisonActualGeneralTargetResponseVariableSavedNumerics

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree Set Filter MeasureTheory ProbabilityTheory LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 12000000

theorem actual_general_target_response_level_variable_saved_of_original_four_prices
    {n : ℕ} {as : List PositiveMass} {i star U : ℕ}
    (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    {Temp d cK Cd Q T I : ℝ}
    (htotal : ∀u∈Icc (0:ℝ) 1,(hf u:ℝ)+(bf u:ℝ) ≤ Temp)
    (hd : 0 < d) (hcK : 0 < cK) (hQ : 0 ≤ Q)
    (ho : MassOrdered 0 as) (hi : i ≤ star) (hs : star < U) (hU : U ≤ as.length)
    (hstarK : cK*d ≤ nativeContinuumMixedClock n bf hf as star)
    (Hdefect :
      let K:=nativeContinuumMixedClock n bf hf as
      let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
      |1-(bf (partitionPoint 0 as star):ℝ)*chi^2| ≤ Cd*d^2)
    (depth : ℕ) (A B F Z : Fin depth→ℝ)
    (hA : ∀j,0 ≤ A j) (hB : ∀j,0 ≤ B j)
    (hF : ∀j,0 ≤ F j) (hZ : ∀j,0 ≤ Z j)
    (Hpair :
      let st:=nativeActualInitialState (S:=Spin n×Bool) as i star 0 (hi.trans (hs.le.trans hU))
      ∀j < depth,|actualGeneralFourPairSum bf hf U d
        (actualGeneralFourCenteredForest bf hf hs hU d j [st])| ≤ Q*d^2)
    (Hother :
      let st:=nativeActualInitialState (S:=Spin n×Bool) as i star 0 (hi.trans (hs.le.trans hU))
      ∀j : Fin depth,|actualGeneralFourOtherSourceErrorSum bf hf U d
        (actualGeneralFourCenteredForest bf hf hs hU d j.val [st])| ≤ A j*d^4+B j*d^3)
    (Hfirst :
      let st:=nativeActualInitialState (S:=Spin n×Bool) as i star 0 (hi.trans (hs.le.trans hU))
      ∀j : Fin depth,|actualGeneralFourFirstHighErrorSum bf hf U d
        (actualGeneralFourCenteredForest bf hf hs hU d j.val [st])| ≤ F j*d^3)
    (Hfrozen :
      let st:=nativeActualInitialState (S:=Spin n×Bool) as i star 0 (hi.trans (hs.le.trans hU))
      ∀j : Fin depth,|actualGeneralFourFrozenChildSum bf hf hs hU d
        (actualGeneralFourCenteredForest bf hf hs hU d j.val [st])| ≤ Z j*d^5)
    (Hterminal :
      let st:=nativeActualInitialState (S:=Spin n×Bool) as i star 0 (hi.trans (hs.le.trans hU))
      |((actualGeneralFourCenteredForest bf hf hs hU d depth [st]).map
        (actualGeneralFourStateResponse (n:=n) bf hf U d)).sum| ≤ T*d^3)
    (HinitialFrozen :
      let st:=nativeActualInitialState (S:=Spin n×Bool) as i star 0 (hi.trans (hs.le.trans hU))
      |actualGeneralFourStateResponse (n:=n) bf hf U d st.freeze| ≤ I*d^5) :
    |actualGeneralTargetLongitudinalResponse (n:=n) bf hf as i U| ≤
      (depth:ℝ)*(d^2*(∑j : Fin depth,B j)/(Real.exp (-4*Temp)*cK)+
        d^3*((Cd*Q+∑j : Fin depth,A j)/(Real.exp (-4*Temp)*cK)+
          (∑j : Fin depth,F j)+(∑j : Fin depth,Z j)*d^2))+
        T*d^3+I*d^5 := by
  have Hother' :
      let st:=nativeActualInitialState (S:=Spin n×Bool) as i star 0 (hi.trans (hs.le.trans hU))
      ∀j < depth,|actualGeneralFourOtherSourceErrorSum bf hf U d
        (actualGeneralFourCenteredForest bf hf hs hU d j [st])| ≤
          (∑k : Fin depth,A k)*d^4+(∑k : Fin depth,B k)*d^3 := by
    dsimp only
    intro j hj
    let k : Fin depth:=⟨j,hj⟩
    have hAj : A k ≤ ∑l : Fin depth,A l:=
      Finset.single_le_sum (fun l _=>hA l) (Finset.mem_univ k)
    have hBj : B k ≤ ∑l : Fin depth,B l:=
      Finset.single_le_sum (fun l _=>hB l) (Finset.mem_univ k)
    have H:=Hother k
    dsimp only [k] at H
    exact H.trans (add_le_add
      (mul_le_mul_of_nonneg_right hAj (pow_nonneg hd.le 4))
      (mul_le_mul_of_nonneg_right hBj (pow_nonneg hd.le 3)))
  have Hfirst' :
      let st:=nativeActualInitialState (S:=Spin n×Bool) as i star 0 (hi.trans (hs.le.trans hU))
      ∀j < depth,|actualGeneralFourFirstHighErrorSum bf hf U d
        (actualGeneralFourCenteredForest bf hf hs hU d j [st])| ≤
          (∑k : Fin depth,F k)*d^3 := by
    dsimp only
    intro j hj
    let k : Fin depth:=⟨j,hj⟩
    have hFj : F k ≤ ∑l : Fin depth,F l:=
      Finset.single_le_sum (fun l _=>hF l) (Finset.mem_univ k)
    exact (Hfirst k).trans (mul_le_mul_of_nonneg_right hFj (pow_nonneg hd.le 3))
  have Hfrozen' :
      let st:=nativeActualInitialState (S:=Spin n×Bool) as i star 0 (hi.trans (hs.le.trans hU))
      ∀j < depth,|actualGeneralFourFrozenChildSum bf hf hs hU d
        (actualGeneralFourCenteredForest bf hf hs hU d j [st])| ≤
          (∑k : Fin depth,Z k)*d^5 := by
    dsimp only
    intro j hj
    let k : Fin depth:=⟨j,hj⟩
    have hZj : Z k ≤ ∑l : Fin depth,Z l:=
      Finset.single_le_sum (fun l _=>hZ l) (Finset.mem_univ k)
    exact (Hfrozen k).trans (mul_le_mul_of_nonneg_right hZj (pow_nonneg hd.le 5))
  exact actual_general_target_response_variable_saved_of_original_four_prices
    bf hf hbf hhf htotal hd hcK hQ ho hi hs hU hstarK Hdefect depth
    Hpair Hother' Hfirst' Hfrozen' Hterminal HinitialFrozen

end OAI.SKFluctuations.Cavity
