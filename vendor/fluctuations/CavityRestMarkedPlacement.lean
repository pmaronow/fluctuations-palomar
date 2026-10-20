module

public import CavityAttachmentCoordinateProjection
public import CavityMarkedPrefixWeights

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S B : Type*}

namespace MarkedPlacement

def restPlacement {as : List PositiveMass} {T : ClockTree (S×B) as}
    (p : MarkedPlacement T) : MarkedPlacement T.cavityLeft where
  tree := p.tree.cavityLeft
  coeff := p.coeff
  restrict := p.restRestrict
  spin := p.restSpin
  embed := fun s=>cavityLeftSlot p.tree (p.embed ((cavityLeftSlot T).symm s))
  mark := cavityLeftSlot p.tree p.mark
  restrict_at := by
    intro σ s
    obtain ⟨s,rfl⟩:=(cavityLeftSlot T).surjective s
    simpa only [Equiv.symm_apply_apply] using p.restRestrict_at σ s
  spin_at := fun _=>rfl

theorem restPlacement_restrict_actual {as : List PositiveMass} {T : ClockTree (S×B) as}
    (p : MarkedPlacement T) (σ : p.tree.Assignment) :
    (T.cavityAssignment (p.restrict σ)).1=
      p.restPlacement.restrict (p.tree.cavityAssignment σ).1 := p.restRestrict_actual σ

theorem restPlacement_spin_actual {as : List PositiveMass} {T : ClockTree (S×B) as}
    (p : MarkedPlacement T) (σ : p.tree.Assignment) :
    (p.spin σ).1=p.restPlacement.spin (p.tree.cavityAssignment σ).1 := p.restSpin_actual σ

end MarkedPlacement

end OAI.SKFluctuations.Hierarchy.ClockTree
