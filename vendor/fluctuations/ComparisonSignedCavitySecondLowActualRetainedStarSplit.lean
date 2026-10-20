module

public import ComparisonSignedCavitySecondLowActualConstantResourceFactorGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators

theorem native_retained_positive_star_split
    (as : List PositiveMass) (ho : MassOrdered 0 as) (u : PositiveMass) (hu : u∈as) :
    let mid:=retainedMassBefore u.val as
    let tail:=retainedMassAfter u.val as
    as=mid++tail ∧ mid.length=retainedMassPrefixIndex u.val as ∧ 0 < mid.length := by
  let mid:=retainedMassBefore u.val as
  have Hmass:=retainedMass_endpoint as ho u hu
  change partitionEnd 0 mid=u.val at Hmass
  have Hnil : mid≠[]:=by
    intro H
    rw [H] at Hmass
    have Hzero : u.val=0:=by simpa only [partitionEnd] using Hmass.symm
    exact u.property.ne' Hzero
  exact ⟨(retainedMass_append u.val as).symm,rfl,List.length_pos_iff_ne_nil.mpr Hnil⟩

end OAI.SKFluctuations.Cavity
