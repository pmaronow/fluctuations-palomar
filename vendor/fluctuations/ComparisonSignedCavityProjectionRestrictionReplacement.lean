module

public import ComparisonSignedCavityActualProjectionSpine

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S B : Type} {as : List PositiveMass}

theorem MarkedPlacement.restRestrict_replace_target {T : ClockTree (S×B) as}
    (p : MarkedPlacement T) (hinj : Function.Injective p.embed) (s : T.Slot)
    (σ : p.tree.cavityLeft.Assignment) (u : S) :
    p.restRestrict (nativeReplaceAtSlot p.tree.cavityLeft (p.tree.cavityLeftSlot (p.embed s)) σ u)=
      nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot s) (p.restRestrict σ) u := by
  classical
  apply T.cavityLeft.assignment_ext
  intro c
  obtain ⟨d,rfl⟩:=T.cavityLeftSlot.surjective c
  rw [p.restRestrict_at,nativeReplaceAtSlot_at,nativeReplaceAtSlot_at]
  have he : p.tree.cavityLeftSlot (p.embed d)=p.tree.cavityLeftSlot (p.embed s) ↔ d=s := by
    constructor
    · exact fun h=>hinj (p.tree.cavityLeftSlot.injective h)
    · exact fun h=>congrArg (fun e=>p.tree.cavityLeftSlot (p.embed e)) h
  have hf : T.cavityLeftSlot d=T.cavityLeftSlot s ↔ d=s := by
    constructor
    · exact fun h=>T.cavityLeftSlot.injective h
    · exact fun h=>congrArg T.cavityLeftSlot h
  rw [he,hf,p.restRestrict_at]

theorem NativeProjectionSpine.restRead_replace_target {A T : ClockTree (S×B) as}
    {base : NativeGeneratedTest A} {P : NativeGeneratedTest T} {star : ℕ}
    (h : NativeProjectionSpine base star P) (σ : T.cavityLeft.Assignment) (u : S) :
    h.restRead (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot P.target) σ u)=
      nativeReplaceAtSlot A.cavityLeft (A.cavityLeftSlot base.target) (h.restRead σ) u := by
  induction h with
  | base=>rfl
  | @projection T P h a hl ih=>
    dsimp only [NativeProjectionSpine.restRead,NativeGeneratedTest.addProjection]
    rw [(nativeFreshAtSlot T a P.target star).restRestrict_replace_target
      (nativeFreshAtSlot_old_splits T a P.target star).1]
    exact ih _

theorem nativeReplaceAtSlot_twice {X : Type} {as : List PositiveMass}
    (T : ClockTree X as) (s : T.Slot) (σ : T.Assignment) (u v : X) :
    nativeReplaceAtSlot T s (nativeReplaceAtSlot T s σ u) v=nativeReplaceAtSlot T s σ v := by
  classical
  apply T.assignment_ext
  intro c
  simp only [nativeReplaceAtSlot_at]
  split_ifs <;> rfl

theorem nativeReplaceAtSlot_original {X : Type} {as : List PositiveMass}
    (T : ClockTree X as) (s : T.Slot) (σ : T.Assignment) :
    nativeReplaceAtSlot T s σ (T.atSlot σ s)=σ := by
  classical
  apply T.assignment_ext
  intro c
  rw [nativeReplaceAtSlot_at]
  split_ifs with h
  · exact congrArg (T.atSlot σ) h.symm
  · rfl

theorem nativeReplaceAtSlot_restore {X : Type} {as : List PositiveMass}
    (T : ClockTree X as) (s : T.Slot) (σ : T.Assignment) (u : X) :
    nativeReplaceAtSlot T s (nativeReplaceAtSlot T s σ u) (T.atSlot σ s)=σ := by
  rw [nativeReplaceAtSlot_twice,nativeReplaceAtSlot_original]

end OAI.SKFluctuations.Hierarchy.ClockTree
