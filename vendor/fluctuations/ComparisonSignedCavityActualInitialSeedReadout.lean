module

public import ComparisonSignedCavityActualInitialThermalResidual

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
open scoped NNReal

theorem actual_initial_seed_function_reindex
    {n i U : ℕ} (as bs : List PositiveMass) (hparts : bs=as)
    (star otherStar : ℕ) (hstar : otherStar=star)
    (hi : i ≤ star) (hs : star < U) (hU : U ≤ as.length)
    (hi' : i ≤ otherStar) (hs' : otherStar < U) (hU' : U ≤ bs.length)
    (F : (as : List PositiveMass)→(star : ℕ)→star<U→U ≤ as.length→
      List (NativeActualResourceState (Spin n×Bool) as i star)→ℝ)
    (B : ℝ)
    (H : F as star hs hU
      [nativeActualInitialState as i star 0 (hi.trans (hs.le.trans hU))] ≤ B) :
    F bs otherStar hs' hU'
      [nativeActualInitialState bs i otherStar 0 (hi'.trans (hs'.le.trans hU'))] ≤ B := by
  subst as
  subst star
  exact H

end OAI.SKFluctuations.Cavity
