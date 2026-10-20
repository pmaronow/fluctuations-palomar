module

public import ComparisonActualHighOnlyActualFourGaCurrent
public import ComparisonSignedCavityActualConstantSourceRatesOnCutsAlong
public import ComparisonActualHighOnlyAnalyticBasics
public import ComparisonActualHighOnlyResourcePhysicalFactories
public import ComparisonActualHighOnlyPullbackFourInterfaces
public import ComparisonActualHighOnlySourceProjectionAlong
public import ComparisonActualHighOnlyGaCurrentPrerequisites
public import ComparisonActualHighOnlyPullbackFourCutReadout
public import ComparisonActualHighOnlyActualConstantSourceGaCurrentAlong

@[expose] public section

noncomputable section
set_option linter.unusedVariables false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization ActualHighOnlyOverlapMinimum
set_option maxHeartbeats 26000000
variable {dim : ℕ → ℕ}

def ActualConstantSourceGaCurrentOnGivenCutsAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (eta C : ℝ)
    (M : (n:ℕ) → ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ → ℝ) (w : ℕ → ActualSlowWindowChoice) (high outer : ℕ → PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us → ∀ᶠj in atTop,
    let as:=finiteCutMasses us j
    let star:=retainedMassPrefixIndex (w n).star.val as
    let U:=retainedMassPrefixIndex (high n).val as
    ∃hs : star < U,∃hU : U ≤ as.length,
    ((nativeActualMinimumFourCenteredForest_high_only (M n) hs hU (W n) depth
      (nativeActualConstantSourceChildren_high_only (M n) as star U hs hU)).map
      (fun Q=>|nativeActualOriginalFourGaCurrentError_high_only (M n) U (W n) Q|)).sum ≤
      C*(dim n:ℝ)^(-eta)*(M n).xs^2

theorem ActualConstantSourceGaCurrentOnEveryFinalNetAlong_high_only.on_given_cuts
    {m delta cl cu Az C0 Ct D Bclock eta Cmass cK C cFirst A : ℝ} {depth : ℕ}
    {M : (n:ℕ) → ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    {W radius : ℕ → ℝ} {w : ℕ → ActualSlowWindowChoice} {high outer : ℕ → PositiveMass}
    (H : ActualConstantSourceGaCurrentOnEveryFinalNetAlong_high_only depth eta Cmass cK C M W w)
    (hxs : ∀n,(M n).xs ≤ W n) (hA : A ≤ Cmass)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry_high_only (M n) (W n) (w n)
      (high n) (outer n) (radius n) cFirst cK A) :
    ActualConstantSourceGaCurrentOnGivenCutsAlong_high_only depth eta C M W w high outer := by
  filter_upwards [H,Hcuts] with n hn hnCuts
  intro L us hus hret hmesh hstar hhigh houter
  filter_upwards [hn L us hus hret hmesh hstar] with j hj
  dsimp only at hj ⊢
  obtain ⟨Hs,HUV,HV,Hfirst,Hmass,_,Hrad,Hrad1,HRU,HRstar,Hrz,HK,_⟩:=
    hnCuts.finite_net_readout us hus hstar hhigh houter j
  refine ⟨Hs,HUV.le.trans HV,?_⟩
  exact hj _ Hs (HUV.le.trans HV) (radius n)
    (Hmass.trans (mul_le_mul_of_nonneg_right hA ((M n).hxs.trans_le (hxs n)).le))
    Hrad Hrad1 HRU HRstar Hrz HK

end OAI.SKFluctuations.Cavity
