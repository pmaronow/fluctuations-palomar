module

public import ComparisonActualHighOnlyActualGProjectedRowLaw
public import ComparisonSignedCavityActualResourceGaReadout
public import ComparisonActualHighOnlyAnalyticBasics
public import ComparisonActualHighOnlyResourcePhysicalFactories
public import ComparisonActualHighOnlyPullbackFourInterfaces
public import ComparisonActualHighOnlySourceProjectionAlong
public import ComparisonActualHighOnlyGaCurrentPrerequisites
public import ComparisonActualHighOnlyCurrentGOriginalLawRestoration

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

def nativeActualResourceGa_high_only {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) : ℝ :=
  nativeActualResourceOriginalScalar_high_only M U P*
    nativeActualCoupledGProjectedResampling_high_only T P.live.test star U M
      (fun j=>Sum.elim (fun _=>(M.bf (partitionPoint 0 as j):ℝ))
        (fun _=>(M.hf (partitionPoint 0 as j):ℝ)))

def nativeActualResourceGaCurrent_high_only {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) : ℝ :=
  nativeActualResourceOriginalScalar_high_only M U P*
    nativeActualDecoupledGProjectedResampling_high_only T P.live.test star U M
      (fun j=>Sum.elim (fun _=>(M.bf (partitionPoint 0 as j):ℝ))
        (fun _=>(M.hf (partitionPoint 0 as j):ℝ)))

theorem actual_minimum_resource_Ga_eq_current_add_restoration_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k : ℕ} {seed : List NativeResourceMark} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P) (hi : i ≤ star)
    (hs : star < U) (ho : MassOrdered 0 as) :
    nativeActualResourceGa_high_only M U P=nativeActualResourceGaCurrent_high_only M U P+
      2*nativeActualResourceGaRestoration_high_only M U P := by
  unfold nativeActualResourceGa_high_only nativeActualResourceGaCurrent_high_only nativeActualResourceGaRestoration_high_only
  rw [native_actual_current_G_coupled_eq_decoupled_add_restoration_high_only hP hi hs ho M]
  ring

end OAI.SKFluctuations.Cavity
