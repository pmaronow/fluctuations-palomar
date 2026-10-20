module

public import ComparisonSignedCavityProjectionSpineWordDiagram
public import ComparisonSignedCavityActualOriginalGeneratedGPolarization

@[expose] public section

noncomputable section
set_option maxHeartbeats 16000000
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type} {as : List PositiveMass}

theorem NativeProjectionSpine.fullRead_at {A T : ClockTree S as}
    {base : NativeGeneratedTest A} {P : NativeGeneratedTest T} {star : ℕ}
    (h : NativeProjectionSpine base star P) (σ : T.Assignment) (c : A.Slot) :
    A.atSlot (h.fullRead σ) c=T.atSlot σ (h.fullEmbed c) := by
  induction h with
  | base=>rfl
  | @projection T P h a hl ih=>
    exact (ih ((nativeFreshAtSlot T a P.target star).restrict σ)).trans
      ((nativeFreshAtSlot T a P.target star).restrict_at σ (h.fullEmbed c))

theorem NativeProjectionSpine.fullRead_target {A T : ClockTree S as}
    {base : NativeGeneratedTest A} {P : NativeGeneratedTest T} {star : ℕ}
    (h : NativeProjectionSpine base star P) (σ : T.Assignment) :
    A.atSlot (h.fullRead σ) base.target=T.atSlot σ P.target := by
  rw [h.fullRead_at,h.fullEmbed_target]

theorem NativeProjectionSpine.fullEmbed_injective {A T : ClockTree S as}
    {base : NativeGeneratedTest A} {P : NativeGeneratedTest T} {star : ℕ}
    (h : NativeProjectionSpine base star P) : Function.Injective h.fullEmbed := by
  induction h with
  | base=>exact Function.injective_id
  | @projection T P h a hl ih=>
    exact (nativeFreshAtSlot_old_splits T a P.target star).1.comp ih

theorem NativeProjectionSpine.fullRead_replace_target {A T : ClockTree S as}
    {base : NativeGeneratedTest A} {P : NativeGeneratedTest T} {star : ℕ}
    (h : NativeProjectionSpine base star P) (σ : T.Assignment) (u : S) :
    h.fullRead (nativeReplaceAtSlot T P.target σ u)=
      nativeReplaceAtSlot A base.target (h.fullRead σ) u := by
  apply A.assignment_ext
  intro c
  rw [h.fullRead_at,nativeReplaceAtSlot_at,nativeReplaceAtSlot_at,←h.fullEmbed_target,
    h.fullEmbed_injective.eq_iff,h.fullRead_at]

theorem NativeProjectionSpine.tooth_ne_target {A T : ClockTree S as}
    {base : NativeGeneratedTest A} {P : NativeGeneratedTest T} {star : ℕ}
    (h : NativeProjectionSpine base star P) {c : T.Slot} (hc : c∈h.toothSlots) : c ≠ P.target := by
  induction h with
  | base=>simp only [toothSlots,List.not_mem_nil] at hc
  | @projection T P h a hl ih=>
    simp only [toothSlots,List.mem_append,List.mem_map,List.mem_singleton] at hc
    rcases hc with ⟨d,hd,rfl⟩|rfl
    · exact (nativeFreshAtSlot_old_splits T a P.target star).1.ne (ih hd)
    · exact nativeFreshAtSlot_distinct T a P.target star P.target

theorem NativeProjectionSpine.full_value {A T : ClockTree S as}
    {base : NativeGeneratedTest A} {P : NativeGeneratedTest T} {star : ℕ}
    (h : NativeProjectionSpine base star P) (R : S→S→ℝ) (C : ℕ→ℝ) (σ : T.Assignment) :
    P.value R C σ=base.value R C (h.fullRead σ)*
      (h.toothSlots.map (fun c=>R (T.atSlot σ P.target) (T.atSlot σ c)-C star)).prod := by
  induction h with
  | base=>simp only [fullRead,toothSlots,List.map_nil,List.prod_nil,mul_one,id_eq]
  | @projection T P h a hl ih=>
    rw [P.addProjection_value a hl R C,ih]
    simp only [fullRead,toothSlots,List.map_append,List.map_map,List.prod_append,
      List.map_singleton,List.prod_singleton,Function.comp_def]
    simp only [NativeGeneratedTest.addProjection,
      ←(nativeFreshAtSlot T a P.target star).restrict_at,
      ←(nativeFreshAtSlot T a P.target star).spin_at]
    ring

theorem NativeProjectionSpine.full_value_replace_target {A T : ClockTree S as}
    {base : NativeGeneratedTest A} {P : NativeGeneratedTest T} {star : ℕ}
    (h : NativeProjectionSpine base star P) (R : S→S→ℝ) (C : ℕ→ℝ) (σ : T.Assignment) (u : S) :
    P.value R C (nativeReplaceAtSlot T P.target σ u)=
      base.value R C (nativeReplaceAtSlot A base.target (h.fullRead σ) u)*
        (h.toothSlots.map (fun c=>R u (T.atSlot σ c)-C star)).prod := by
  rw [h.full_value,h.fullRead_replace_target,nativeReplaceAtSlot_self]
  congr 1
  apply congrArg List.prod
  apply List.map_congr_left
  intro c hc
  rw [nativeReplaceAtSlot_at,ite_eq_right (h.tooth_ne_target hc)]

end OAI.SKFluctuations.Hierarchy.ClockTree
