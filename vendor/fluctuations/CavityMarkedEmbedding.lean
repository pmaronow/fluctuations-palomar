module

public import CavityAttachedTree

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type*}

 theorem markedAttach_embed_preserves {as : List PositiveMass} (T : ClockTree S as)
    (a : ℝ) (p : MarkedPlacement T) (hp : p ∈ T.markedAttach a) :
    Function.Injective p.embed ∧
      ∀ s t, p.tree.splitIndex (p.embed s) (p.embed t)=T.splitIndex s t := by
  induction T generalizing a with
  | leaf =>
    rcases List.mem_cons.mp hp with rfl|hp
    · exact ⟨fun _ _ h => h,fun _ _ => rfl⟩
    · obtain rfl := List.mem_singleton.mp hp
      exact ⟨Sum.inl_injective,fun _ _ => rfl⟩
  | step b T ih =>
    rcases List.mem_cons.mp hp with rfl|hp
    · exact ⟨Sum.inl_injective,fun _ _ => rfl⟩
    · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hp
      have H := ih b.val r hr
      exact ⟨H.1,fun s t => congrArg (1+·) (H.2 s t)⟩
  | fork T U ihT ihU =>
    rcases List.mem_cons.mp hp with rfl|hp
    · exact ⟨Sum.inl_injective,fun _ _ => rfl⟩
    · rcases List.mem_append.mp hp with hp|hp
      · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hp
        have H := ihT a r hr
        constructor
        · intro s t he
          rcases s with s|s <;> rcases t with t|t
          · exact congrArg Sum.inl (H.1 (Sum.inl.inj he))
          · cases he
          · cases he
          · exact congrArg Sum.inr (Sum.inr.inj he)
        · intro s t
          rcases s with s|s <;> rcases t with t|t
          · exact H.2 s t
          · rfl
          · rfl
          · rfl
      · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hp
        have H := ihU a r hr
        constructor
        · intro s t he
          rcases s with s|s <;> rcases t with t|t
          · exact congrArg Sum.inl (Sum.inl.inj he)
          · cases he
          · cases he
          · exact congrArg Sum.inr (H.1 (Sum.inr.inj he))
        · intro s t
          rcases s with s|s <;> rcases t with t|t
          · rfl
          · rfl
          · rfl
          · exact H.2 s t

end OAI.SKFluctuations.Hierarchy.ClockTree
