module

public import ComparisonActualGeneralCurrentGRestoration
public import ComparisonActualGeneralResourceJointLowRestorationReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators

def actualGeneralResourceGa {n : ℕ} (bf hf : ℝ→ℝ≥0)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) : ℝ :=
  actualGeneralResourceOriginalScalar bf hf U P*
    actualGeneralCoupledGProjectedResampling T P.live.test star U bf hf
      (fun j=>Sum.elim (fun _=>(bf (partitionPoint 0 as j):ℝ))
        (fun _=>(hf (partitionPoint 0 as j):ℝ)))

def actualGeneralResourceGaCurrent {n : ℕ} (bf hf : ℝ→ℝ≥0)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) : ℝ :=
  actualGeneralResourceOriginalScalar bf hf U P*
    actualGeneralDecoupledGProjectedResampling T P.live.test star U bf hf
      (fun j=>Sum.elim (fun _=>(bf (partitionPoint 0 as j):ℝ))
        (fun _=>(hf (partitionPoint 0 as j):ℝ)))

def actualGeneralResourceGaRestoration {n : ℕ} (bf hf : ℝ→ℝ≥0)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) : ℝ :=
  actualGeneralResourceOriginalScalar bf hf U P*
    actualGeneralGProjectedRestoration T P.live.test star U bf hf
      (fun j=>Sum.elim (fun _=>(bf (partitionPoint 0 as j):ℝ))
        (fun _=>(hf (partitionPoint 0 as j):ℝ)))

theorem actual_general_resource_Ga_eq_current_add_restoration
    {n : ℕ} (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k : ℕ} {seed : List NativeResourceMark} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P) (hi : i ≤ star)
    (hs : star < U) (ho : MassOrdered 0 as) :
    actualGeneralResourceGa bf hf U P=actualGeneralResourceGaCurrent bf hf U P+
      2*actualGeneralResourceGaRestoration bf hf U P := by
  unfold actualGeneralResourceGa actualGeneralResourceGaCurrent actualGeneralResourceGaRestoration
  rw [actual_general_current_G_coupled_eq_decoupled_add_restoration hP hi hs ho bf hf hbf hhf]
  ring

end OAI.SKFluctuations.Cavity
