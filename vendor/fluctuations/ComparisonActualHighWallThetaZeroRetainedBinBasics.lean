module

public import ComparisonActualHighWallThetaZeroRetainedRowsBasics
public import ComparisonActualHighWallSelectedCumulative
public import ComparisonActualHighWallConditionalAssembly

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
set_option autoImplicit false
set_option maxHeartbeats 14000000
attribute [local instance] Classical.propDecidable
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {Q : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}

def Potential.retainedBin (P : Q.Potential) {ι : Type*} (c : ι→ShiftedCapInterval Q P)
    (Dcuts : Finset ℝ) (ag zg : ℝ) (as : List PositiveMass) (bins : ℕ) (w : ℝ)
    (bb : Fin bins) : Finset (Fin ((sampleClockSteps Q.shiftedNativeModel.q 0 as).length+1)) :=
  NativeUnitHeight.bin
    (fun i=>physicalPathSecondMoment (n+1) (sampleClockSteps Q.shiftedNativeModel.q 0 as)
      (Q.shiftedNativeModel.q 0) i.val) (P.retainedRows c Dcuts ag zg as)
    (firstWholeUnitCell P.negativeSet (Q.shiftedNativeModel.rowRadius as)) bins w bb

theorem Potential.retainedBin_subset (P : Q.Potential) {ι : Type*}
    (c : ι→ShiftedCapInterval Q P) (Dcuts : Finset ℝ) (ag zg : ℝ)
    (as : List PositiveMass) (bins : ℕ) (w : ℝ) (bb : Fin bins) :
    P.retainedBin c Dcuts ag zg as bins w bb⊆P.retainedRows c Dcuts ag zg as := Finset.filter_subset _ _

theorem Potential.retainedBin_exists_coordinates (P : Q.Potential) {ι : Type*}
    (c : ι→ShiftedCapInterval Q P) (Dcuts : Finset ℝ) (ag zg : ℝ)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (bins : ℕ) (w : ℝ) (bb : Fin bins) :
    Nonempty (NativeConstructedCoordinates (sampleClockSteps Q.shiftedNativeModel.q 0 as)
      (P.retainedBin c Dcuts ag zg as bins w bb) (Q.shiftedNativeModel.rowRadius as) P.negativeSet) := by
  apply exists_nativeConstructedCoordinates _ (sampleClockSteps_ordered _ _ ho) _ _ _
    (Q.shiftedNativeModel.rowRadius_monotone as ho) P.negativeSet
  intro i hi
  exact ((P.retainedRows_mem c Dcuts ag zg as i).mp
    (P.retainedBin_subset c Dcuts ag zg as bins w bb hi)).2.2.1

def Potential.retainedBinCoordinates (P : Q.Potential) {ι : Type*}
    (c : ι→ShiftedCapInterval Q P) (Dcuts : Finset ℝ) (ag zg : ℝ)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (bins : ℕ) (w : ℝ) (bb : Fin bins) :
    NativeConstructedCoordinates (sampleClockSteps Q.shiftedNativeModel.q 0 as)
      (P.retainedBin c Dcuts ag zg as bins w bb) (Q.shiftedNativeModel.rowRadius as) P.negativeSet :=
  Classical.choice (P.retainedBin_exists_coordinates c Dcuts ag zg as ho bins w bb)

abbrev actualCDF (as : List PositiveMass) (ho : MassOrdered 0 as)
    (J : Finset (Fin ((sampleClockSteps Q.shiftedNativeModel.q 0 as).length+1))) :
    Icc (0:ℝ) 1→ᵇℝ := Q.shiftedNativeModel.selectedCDF as ho J

theorem actualCDF_finite_exists_uniform_subseq {β : Type*} [Fintype β]
    (as : ℕ→List PositiveMass) (ho : ∀j,MassOrdered 0 (as j))
    (J : ∀j,β→Finset (Fin ((sampleClockSteps Q.shiftedNativeModel.q 0 (as j)).length+1))) :
    ∃f : β→(Icc (0:ℝ) 1→ᵇℝ),∃φ : ℕ→ℕ,StrictMono φ ∧
      ∀b,Tendsto (fun j=>Q.actualCDF (as (φ j)) (ho (φ j)) (J (φ j) b)) atTop (𝓝 (f b)) :=
  Q.shiftedNativeModel.selectedCDF_finite_exists_uniform_subseq as ho J

theorem actualCDF_one (as : List PositiveMass) (ho : MassOrdered 0 as)
    (he : partitionEnd 0 as=1)
    (J : Finset (Fin ((sampleClockSteps Q.shiftedNativeModel.q 0 as).length+1)))
    (hhigh : ∀i∈J,Q.data.s ≤ partitionPoint 0 as i.val) :
    Q.actualCDF as ho J ⟨1,by simp⟩=
      physicalWindowMass (sampleClockSteps Q.shiftedNativeModel.q 0 as) 0 J :=
  Q.shiftedNativeModel.selectedCDF_one Q.data.hrbounds.1.le as ho he J hhigh

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
