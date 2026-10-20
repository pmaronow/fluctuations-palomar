module

public import SKProof.Port.ComparisonActualOriginalQActualGProjectedRowLaw
public import ComparisonSignedCavityActualResourceGaReadout
public import SKProof.Port.ComparisonActualOriginalQAnalyticBasics
public import SKProof.Port.ComparisonActualOriginalQResourcePhysicalFactories
public import SKProof.Port.ComparisonActualOriginalQPullbackFourInterfaces
public import SKProof.Port.ComparisonActualOriginalQSourceProjectionAlong
public import SKProof.Port.ComparisonActualOriginalQGaCurrentPrerequisites
public import SKProof.Port.ComparisonActualOriginalQCurrentGOriginalLawRestoration

@[expose] public section

noncomputable section
set_option linter.unusedVariables false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 24000000

def nativeActualResourceGa_original_q {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) : ℝ :=
  nativeActualResourceOriginalScalar_original_q M U P*
    nativeActualCoupledGProjectedResampling_original_q T P.live.test star U M
      (fun j=>Sum.elim (fun _=>(M.sweepBf (partitionPoint 0 as j):ℝ))
        (fun _=>(M.sweepHf (partitionPoint 0 as j):ℝ)))

def nativeActualResourceGaCurrent_original_q {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) : ℝ :=
  nativeActualResourceOriginalScalar_original_q M U P*
    nativeActualDecoupledGProjectedResampling_original_q T P.live.test star U M
      (fun j=>Sum.elim (fun _=>(M.sweepBf (partitionPoint 0 as j):ℝ))
        (fun _=>(M.sweepHf (partitionPoint 0 as j):ℝ)))

theorem actual_minimum_resource_Ga_eq_current_add_restoration_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k : ℕ} {seed : List NativeResourceMark} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P) (hi : i ≤ star)
    (hs : star < U) (ho : MassOrdered 0 as) :
    nativeActualResourceGa_original_q M U P=nativeActualResourceGaCurrent_original_q M U P+
      2*nativeActualResourceGaRestoration_original_q M U P := by
  unfold nativeActualResourceGa_original_q nativeActualResourceGaCurrent_original_q nativeActualResourceGaRestoration_original_q
  rw [native_actual_current_G_coupled_eq_decoupled_add_restoration_original_q hP hi hs ho M]
  ring

end OAI.SKFluctuations.Cavity
