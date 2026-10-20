module

public import ComparisonNativeMasterFullBand

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 3200000

theorem exists_nativeRawMasterRefinement (m : NativeBandModel) (hraw : NativeBandRawMaster m) :
    ∃s : NativeBandRefinement m,
      ∀ᶠ j in atTop,physicalRawRatio (m.n+1) m.l (s.steps j) 0 m.xs
        (Measure.pi fun a=>gaussianReal 0 (m.q 0 a)) id measurable_id ≤ m.Q := by
  obtain ⟨nodes,hbound,_,hQ⟩ := hraw [] (by simp)
  let s : NativeBandRefinement m := {
    as := fun j=>finiteCutMasses nodes j
    mesh := fun j=>((j+1:ℕ):ℝ)⁻¹
    ho := fun j=>finiteCutMasses_ordered nodes hbound j
    he := fun j=>finiteCutMasses_end nodes hbound j
    hm := fun j=>finiteCutMasses_mesh nodes hbound j
    hm0 := fun _=>by positivity
    hmesh := uniformMasses_mesh_tendsto }
  exact ⟨s,hQ⟩

theorem exists_nativeRawMasterRefinement_retaining (m : NativeBandModel) (hraw : NativeBandRawMaster m)
    (extra : List PositiveMass) (hextra : ∀u∈extra,u.val ≤ 1) :
    ∃s : NativeBandRefinement m,
      (∀j,∀u∈extra,u∈s.as j) ∧
      ∀ᶠ j in atTop,physicalRawRatio (m.n+1) m.l (s.steps j) 0 m.xs
        (Measure.pi fun a=>gaussianReal 0 (m.q 0 a)) id measurable_id ≤ m.Q := by
  obtain ⟨nodes,hbound,hretain,hQ⟩ := hraw extra hextra
  let s : NativeBandRefinement m := {
    as := fun j=>finiteCutMasses nodes j
    mesh := fun j=>((j+1:ℕ):ℝ)⁻¹
    ho := fun j=>finiteCutMasses_ordered nodes hbound j
    he := fun j=>finiteCutMasses_end nodes hbound j
    hm := fun j=>finiteCutMasses_mesh nodes hbound j
    hm0 := fun _=>by positivity
    hmesh := uniformMasses_mesh_tendsto }
  exact ⟨s,fun j u hu=>finiteCutMasses_nodes nodes j (hretain u hu),hQ⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
