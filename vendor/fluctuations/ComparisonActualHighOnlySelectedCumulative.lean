module

public import ComparisonActualHighWallSelectedCumulative
public import ComparisonActualHighOnlyOverlapMinimum

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable (a : ActualHighOnlyOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)

abbrev actualCDF (as : List PositiveMass) (ho : MassOrdered 0 as)
    (J : Finset (Fin ((sampleClockSteps a.shiftedNativeModel.q 0 as).length+1))) :
    Icc (0:ℝ) 1→ᵇℝ := a.shiftedNativeModel.selectedCDF as ho J

theorem actualCDF_finite_exists_uniform_subseq {β : Type*} [Fintype β]
    (as : ℕ→List PositiveMass) (ho : ∀j,MassOrdered 0 (as j))
    (J : ∀j,β→Finset (Fin ((sampleClockSteps a.shiftedNativeModel.q 0 (as j)).length+1))) :
    ∃f : β→(Icc (0:ℝ) 1→ᵇℝ),∃φ : ℕ→ℕ,StrictMono φ ∧
      ∀b,Tendsto (fun j=>a.actualCDF (as (φ j)) (ho (φ j)) (J (φ j) b)) atTop (𝓝 (f b)) :=
  a.shiftedNativeModel.selectedCDF_finite_exists_uniform_subseq as ho J

theorem actualCDF_one (as : List PositiveMass) (ho : MassOrdered 0 as)
    (he : partitionEnd 0 as=1)
    (J : Finset (Fin ((sampleClockSteps a.shiftedNativeModel.q 0 as).length+1)))
    (hhigh : ∀i∈J,a.data.s ≤ partitionPoint 0 as i.val) :
    a.actualCDF as ho J ⟨1,by simp⟩=
      physicalWindowMass (sampleClockSteps a.shiftedNativeModel.q 0 as) 0 J :=
  a.shiftedNativeModel.selectedCDF_one (le_refl (0:ℝ)) as ho he J hhigh

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
