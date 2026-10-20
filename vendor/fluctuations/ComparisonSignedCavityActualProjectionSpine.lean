module

public import ComparisonSignedCavityStarFieldTestFold

@[expose] public section

noncomputable section
set_option maxHeartbeats 14000000
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type} {as : List PositiveMass}

inductive NativeProjectionSpine {A : ClockTree S as} (base : NativeGeneratedTest A) (star : ℕ) :
    {T : ClockTree S as} → NativeGeneratedTest T → Type
  | base : NativeProjectionSpine base star base
  | projection {T : ClockTree S as} {P : NativeGeneratedTest T}
      (h : NativeProjectionSpine base star P) (a : ℝ) (hl : star≤as.length) :
      NativeProjectionSpine base star (P.addProjection a star)

def NativeProjectionSpine.toothCount {A T : ClockTree S as}
    {base : NativeGeneratedTest A} {P : NativeGeneratedTest T} {star : ℕ}
    (h : NativeProjectionSpine base star P) : ℕ :=
  match h with
  | .base=>0
  | .projection h _ _=>h.toothCount+1

def NativeActualProjectionDecomposition (i star U : ℕ) (T : ClockTree S as)
    (P : NativeResourceTerm i star T) : Prop :=
  ∃(A : ClockTree S as) (base : NativeResourceTerm i star A) (seed : List NativeResourceMark) (k : ℕ),
    NativeActualResourceGenerated i star U seed k A base ∧ base.live.test.teeth=[] ∧
      Nonempty (NativeProjectionSpine base.live.test star P.live.test)

theorem native_actual_projection_decomposition_reset
    {i star U k : ℕ} {seed : List NativeResourceMark} {T : ClockTree S as}
    {P : NativeResourceTerm i star T}
    (h : NativeActualResourceGenerated i star U seed k T P) (ht : P.live.test.teeth=[]) :
    NativeActualProjectionDecomposition i star U T P :=
  ⟨T,P,seed,k,h,ht,⟨.base⟩⟩

theorem NativePhysicalResourceGenerated.projectionDecomposition
    {i star U k : ℕ} {seed : List NativeResourceMark} {T : ClockTree S as}
    {P : NativeResourceTerm i star T}
    (h : NativePhysicalResourceGenerated i star U seed k T P) :
    NativeActualProjectionDecomposition i star U T P := by
  induction h with
  | constant as hU=>exact native_actual_projection_decomposition_reset (.physical (.constant as hU)) rfl
  | seed as hU a mark hm hl=>
    exact native_actual_projection_decomposition_reset (.physical (.seed as hU a mark hm hl)) rfl
  | freeze h ih=>exact native_actual_projection_decomposition_reset (.physical (.freeze h)) rfl
  | reweight h c ih=>exact ih
  | retarget h a ih=>exact native_actual_projection_decomposition_reset (.physical (.retarget h a)) rfl
  | projection h a hl ih=>
    obtain ⟨A,base,seed,k,hbase,ht,⟨spine⟩⟩:=ih
    exact ⟨A,base,seed,k,hbase,ht,⟨.projection spine a hl⟩⟩
  | switch h a c hs hh ih=>
    exact native_actual_projection_decomposition_reset (.physical (.switch h a c hs hh)) rfl
  | switchFreshHigh h a j hjU hj hs ih=>
    exact native_actual_projection_decomposition_reset (.physical (.switchFreshHigh h a j hjU hj hs)) rfl

theorem NativeActualResourceGenerated.projectionDecomposition
    {i star U k : ℕ} {seed : List NativeResourceMark} {T : ClockTree S as}
    {P : NativeResourceTerm i star T}
    (h : NativeActualResourceGenerated i star U seed k T P) :
    NativeActualProjectionDecomposition i star U T P := by
  induction h with
  | physical h=>exact h.projectionDecomposition
  | freeze h ih=>exact native_actual_projection_decomposition_reset (.freeze h) rfl
  | reweight h c ih=>exact ih
  | retarget h ih=>exact native_actual_projection_decomposition_reset (.retarget h) rfl
  | projection h hl ih=>
    obtain ⟨A,base,seed,k,hbase,ht,⟨spine⟩⟩:=ih
    exact ⟨A,base,seed,k,hbase,ht,⟨.projection spine 0 hl⟩⟩
  | markedSwitch h p hp hs hh ih=>
    exact native_actual_projection_decomposition_reset (.markedSwitch h p hp hs hh) rfl

variable {B : Type}

def NativeProjectionSpine.restRead {A : ClockTree (S×B) as}
    {base : NativeGeneratedTest A} {star : ℕ} :
    {T : ClockTree (S×B) as} → {P : NativeGeneratedTest T} →
      NativeProjectionSpine base star P → T.cavityLeft.Assignment → A.cavityLeft.Assignment
  | _,_,.base=>id
  | _,_,@NativeProjectionSpine.projection _ _ _ _ _ T P h a _=>
      fun σ=>h.restRead ((nativeFreshAtSlot T a P.target star).restRestrict σ)

theorem NativeProjectionSpine.restTargetRead {A T : ClockTree (S×B) as}
    {base : NativeGeneratedTest A} {P : NativeGeneratedTest T} {star : ℕ}
    (h : NativeProjectionSpine base star P) (σ : T.cavityLeft.Assignment) :
    A.cavityLeft.atSlot (h.restRead σ) (A.cavityLeftSlot base.target)=
      T.cavityLeft.atSlot σ (T.cavityLeftSlot P.target) := by
  induction h with
  | base=>rfl
  | @projection T P h a hl ih=>
    exact (ih ((nativeFreshAtSlot T a P.target star).restRestrict σ)).trans
      ((nativeFreshAtSlot T a P.target star).restRestrict_at σ P.target)

theorem NativeProjectionSpine.teeth_length {A T : ClockTree S as}
    {base : NativeGeneratedTest A} {P : NativeGeneratedTest T} {star : ℕ}
    (h : NativeProjectionSpine base star P) : P.teeth.length=base.teeth.length+h.toothCount := by
  induction h with
  | base=>simp only [toothCount,Nat.add_zero]
  | projection h a hl ih=>
    simp only [NativeGeneratedTest.addProjection,List.length_append,List.length_map,
      List.length_singleton,toothCount]
    omega

def nativeRestGeneratedTestValue (T : ClockTree (S×B) as) (P : NativeGeneratedTest T)
    (R : S → S → ℝ) (C : ℕ → ℝ) (σ : T.cavityLeft.Assignment) : ℝ :=
  (P.edges.map (fun e=>R (T.cavityLeft.atSlot σ (T.cavityLeftSlot e.1))
    (T.cavityLeft.atSlot σ (T.cavityLeftSlot e.2))-C (T.splitIndex e.1 e.2))).prod

theorem native_rest_generated_value_eq_full {T : ClockTree (S×B) as}
    (P : NativeGeneratedTest T) (R : S → S → ℝ) (C : ℕ → ℝ) (σ : T.Assignment) :
    nativeRestGeneratedTestValue T P R C (T.cavityAssignment σ).1=
      P.value (fun u v=>R u.1 v.1) C σ := by
  simp only [nativeRestGeneratedTestValue,NativeGeneratedTest.value,nativeGeneratedEdgeProduct,
    T.atSlot_cavityLeft]

variable [Nonempty B]

theorem native_rest_add_projection_value {T : ClockTree (S×B) as}
    (P : NativeGeneratedTest T) (a : ℝ) {star : ℕ} (hl : star≤as.length)
    (R : S → S → ℝ) (C : ℕ → ℝ)
    (σ : (nativeFreshAtSlot T a P.target star).tree.cavityLeft.Assignment) :
    let g:=nativeFreshAtSlot T a P.target star
    nativeRestGeneratedTestValue g.tree (P.addProjection a star) R C σ=
      nativeRestGeneratedTestValue T P R C (g.restRestrict σ)*
        (R (T.cavityLeft.atSlot (g.restRestrict σ) (T.cavityLeftSlot P.target)) (g.restSpin σ)-C star) := by
  let g:=nativeFreshAtSlot T a P.target star
  let τ:=g.tree.cavityAssignment.symm
    (σ,assignmentOfSlots g.tree.cavityRight (fun _=>Classical.choice ‹Nonempty B›))
  have ht : (g.tree.cavityAssignment τ).1=σ := by
    dsimp only [τ]
    rw [Equiv.apply_symm_apply]
  have H:=P.addProjection_value a hl (fun u v=>R u.1 v.1) C τ
  dsimp only at H
  rw [←native_rest_generated_value_eq_full,←native_rest_generated_value_eq_full,
    g.restRestrict_actual,g.restSpin_actual] at H
  rw [←T.atSlot_cavityLeft] at H
  rw [g.restRestrict_actual,ht] at H
  exact H

end OAI.SKFluctuations.Hierarchy.ClockTree
