module

public import ComparisonActualHighWallInitialForestAllLevelsSavedAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000

namespace ActualHighWallInitialForestSavedLevelConstants

def A {n level : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (P : ActualHighWallInitialForestSavedLevelConstants level) (eta cK : ℝ)
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (i : ℕ) : ℝ :=
  let V:=nativeActualWeightedFrontierCost nativeActualOriginalFourGCenteredBranches
    (Bclock/(Real.exp (-4*Bclock)*cK)) 3 2 level
  let VP:=nativeActualWeightedProfileFrontierCost nativeActualOriginalFourGCenteredBranches
    (Bclock/(Real.exp (-4*Bclock)*cK)) 3 2 level
  let rho:=((n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/256))
  let qsecond:=actualHighWallInitialFullB0Envelope (1+level) P.C P.CiU P.CiB P.CiM P.Cf P.Cr
    (originalHighWallInitialPairErrorScale M as i) M.data.d (n:ℝ) eta
  2*V*(P.Ca*(n:ℝ)^(-eta)+P.Cg*(n:ℝ)^(-eta)+P.Cd*((n+1:ℕ):ℝ)^(-m)+2*qsecond)+
    2*VP*rho*(2*(P.Ca+2*P.Cl+P.Cj+P.C4+P.CY)+P.Ch)

def B {n level : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (P : ActualHighWallInitialForestSavedLevelConstants level) (Ccut cK : ℝ)
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (i star : ℕ) : ℝ :=
  let V:=nativeActualWeightedFrontierCost nativeActualOriginalFourGCenteredBranches
    (Bclock/(Real.exp (-4*Bclock)*cK)) 3 2 level
  let Di:=nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ)
  let CB:=actualLowErrorComparisonConstant (2*max Bclock 0) (max Bclock 0)
  let Dstar:=(1+CB)*(nativeOriginalCutLowErrorRadius n M.bf M.hf as star+1/(n+1:ℕ))
  let I:=∫u in 0..Ccut*M.data.d,Real.sqrt (orderedPathB (n+1) M.bf M.hf u-
    (orderedPathS (n+1) M.bf M.hf u)^2)
  2*V*(P.CY*Di+(P.CY+P.Cgl+P.Cjl)*Dstar+P.CY*I)

def F {n level : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (P : ActualHighWallInitialForestSavedLevelConstants level)
    (_M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) : ℝ :=
  P.Cfirst*((n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/256))

theorem coefficients_nonneg {n level : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (P : ActualHighWallInitialForestSavedLevelConstants level) (eta Ccut cK : ℝ)
    (hcK : 0 < cK) (hCcut : 0 ≤ Ccut)
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (i star : ℕ) :
    0 ≤ P.A eta cK M as i ∧ 0 ≤ P.B Ccut cK M as i star ∧ 0 ≤ P.F M ∧ 0 ≤ P.Cfr := by
  have hBc : 0 ≤ Bclock:=M.data.hTpos.le.trans M.hT
  have hCW : 0 ≤ Bclock/(Real.exp (-4*Bclock)*cK):=by positivity
  have hV:=nativeActualWeightedFrontierCost_nonneg nativeActualOriginalFourGCenteredBranches hCW 3 2 level
  have hVP:=nativeActualWeightedProfileFrontierCost_nonneg nativeActualOriginalFourGCenteredBranches hCW 3 2 level
  have hN : 0 ≤ (n:ℝ)^(-eta):=Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hN1 : 0 ≤ ((n+1:ℕ):ℝ)^(-m):=Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hrho : 0 ≤ ((n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/256)):=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hq:=actual_high_wall_initial_full_B0_envelope_nonneg (1+level)
    P.C P.CiU P.CiB P.CiM P.Cf P.Cr _ M.data.d (n:ℝ) eta
    (fun a=>(P.hC a).1.le) (fun a=>(P.hC a).2.1.le)
    (fun a=>(P.hC a).2.2.1.le) (fun a=>(P.hC a).2.2.2.le)
    P.hCf.le P.hCr.le (original_high_wall_initial_pair_error_scale_nonneg M as i)
    M.data.hd.le (Nat.cast_nonneg _)
  have hDi : 0 ≤ nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ):=
    add_nonneg (Real.sqrt_nonneg _) (by positivity)
  have hDs : 0 ≤ nativeOriginalCutLowErrorRadius n M.bf M.hf as star+1/(n+1:ℕ):=
    add_nonneg (Real.sqrt_nonneg _) (by positivity)
  have hCB:=actualLowErrorComparisonConstant_nonneg (2*max Bclock 0) (le_max_right Bclock 0)
  have hI : 0 ≤ ∫u in 0..Ccut*M.data.d,Real.sqrt (orderedPathB (n+1) M.bf M.hf u-
      (orderedPathS (n+1) M.bf M.hf u)^2):=
    intervalIntegral.integral_nonneg (mul_nonneg hCcut M.data.hd.le) (fun _ _=>Real.sqrt_nonneg _)
  have hCa:=P.hCa.le
  have hCg:=P.hCg.le
  have hCd:=P.hCd.le
  have hCl:=P.hCl.le
  have hCj:=P.hCj.le
  have hC4:=P.hC4.le
  have hCY:=P.hCY.le
  have hCh:=P.hCh.le
  have hCgl:=P.hCgl.le
  have hCjl:=P.hCjl.le
  have hCfirst:=P.hCfirst.le
  refine ⟨?_,?_,?_,P.hCfr.le⟩
  · dsimp only [A];positivity
  · dsimp only [B];positivity
  · dsimp only [F];positivity

theorem saved_prices {n level : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (P : ActualHighWallInitialForestSavedLevelConstants level) (eta Ccut cK : ℝ)
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (i star U : ℕ) (hi : i < star)
    (hs : star < U) (hU : U ≤ as.length)
    (H : P.PriceOnGrid eta Ccut cK M as i star U hi hs hU) :
    let rows:=actualGeneralFourCenteredForest M.bf M.hf hs hU M.data.d level
      [nativeActualInitialState (S:=Spin n×Bool) as i star 0 (hi.le.trans (hs.le.trans hU))]
    |actualGeneralFourOtherSourceErrorSum M.bf M.hf U M.data.d rows| ≤
      P.A eta cK M as i*M.data.d^4+P.B Ccut cK M as i star*M.data.d^3 ∧
    |actualGeneralFourFirstHighErrorSum M.bf M.hf U M.data.d rows| ≤ P.F M*M.data.d^3 ∧
    |actualGeneralFourFrozenChildSum M.bf M.hf hs hU M.data.d rows| ≤ P.Cfr*M.data.d^5 := by
  dsimp only [PriceOnGrid,ActualHighWallInitialForestSavedLevelPricesOnGrid] at H
  dsimp only
  refine ⟨?_,?_,H.2.2⟩
  · convert H.1 using 1
    dsimp only [A,B]
    ring
  · simpa only [F] using H.2.1

end ActualHighWallInitialForestSavedLevelConstants
end OAI.SKFluctuations.Cavity
