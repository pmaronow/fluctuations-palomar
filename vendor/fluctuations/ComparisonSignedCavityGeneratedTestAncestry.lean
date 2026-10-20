module

public import ComparisonSignedCavityFreshGraft
public import CavityCutBlocks

@[expose] public section

noncomputable section
set_option maxHeartbeats 3000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type*} {as : List PositiveMass}

structure NativeGeneratedTest (T : ClockTree S as) where
  target : T.Slot
  exterior : List (T.Slot × T.Slot)
  teeth : List T.Slot
  incoming : List T.Slot

def NativeGeneratedTest.edges {T : ClockTree S as} (P : NativeGeneratedTest T) :
    List (T.Slot × T.Slot) :=
  P.exterior ++ P.teeth.map (fun c => (P.target,c)) ++
    P.incoming.map (fun c => (P.target,c))

structure NativeGeneratedTestAncestry {T : ClockTree S as}
    (i star : ℕ) (P : NativeGeneratedTest T) : Prop where
  exterior_departure : ∀ e ∈ P.exterior,
    T.splitIndex P.target e.1 ≤ star ∧ T.splitIndex P.target e.2 ≤ star
  exterior_cuts : ∀ e ∈ P.exterior,
    T.splitIndex e.1 e.2 = i ∨ T.splitIndex e.1 e.2 = star
  teeth_star : ∀ c ∈ P.teeth,T.splitIndex P.target c = star
  incoming_cuts : ∀ c ∈ P.incoming,
    T.splitIndex P.target c = i ∨ T.splitIndex P.target c = star
  incoming_degree : P.incoming.length ≤ 1

def NativeGeneratedTest.constant {T : ClockTree S as} (P : NativeGeneratedTest T) :
    NativeGeneratedTest T := ⟨P.target,[],[],[]⟩

def nativeGeneratedSeed (T : ClockTree S as) (a : ℝ) (s : T.Slot) (j : ℕ) :
    NativeGeneratedTest (nativeFreshAtSlot T a s j).tree :=
  ⟨(nativeFreshAtSlot T a s j).embed s,[],[],[(nativeFreshAtSlot T a s j).mark]⟩

def NativeGeneratedTest.addProjection {T : ClockTree S as}
    (P : NativeGeneratedTest T) (a : ℝ) (star : ℕ) :
    NativeGeneratedTest (nativeFreshAtSlot T a P.target star).tree :=
  let p := nativeFreshAtSlot T a P.target star
  ⟨p.embed P.target,P.exterior.map (fun e => (p.embed e.1,p.embed e.2)),
    P.teeth.map p.embed ++ [p.mark],P.incoming.map p.embed⟩

def NativeGeneratedTest.switchTarget {T : ClockTree S as}
    (P : NativeGeneratedTest T) (a : ℝ) (star : ℕ) (c : T.Slot) :
    NativeGeneratedTest (nativeFreshAtSlot T a P.target star).tree :=
  let p := nativeFreshAtSlot T a P.target star
  ⟨p.mark,P.edges.map (fun e => (p.embed e.1,p.embed e.2)),[],[p.embed c]⟩

theorem NativeGeneratedTestAncestry.edges_low {T : ClockTree S as}
    {i star : ℕ} {P : NativeGeneratedTest T} (hP : NativeGeneratedTestAncestry i star P)
    (e : T.Slot × T.Slot) (he : e ∈ P.edges) :
    T.splitIndex e.1 e.2 = i ∨ T.splitIndex e.1 e.2 = star := by
  simp only [NativeGeneratedTest.edges,List.mem_append,List.mem_map] at he
  rcases he with (he | ⟨c,hc,rfl⟩) | ⟨c,hc,rfl⟩
  · exact hP.exterior_cuts e he
  · exact Or.inr (hP.teeth_star c hc)
  · exact hP.incoming_cuts c hc

theorem NativeGeneratedTestAncestry.constant {T : ClockTree S as}
    (i star : ℕ) (P : NativeGeneratedTest T) :
    NativeGeneratedTestAncestry i star P.constant := by
  constructor <;> simp [NativeGeneratedTest.constant]

theorem nativeGeneratedSeed_ancestry (T : ClockTree S as) (a : ℝ)
    (s : T.Slot) {i star j : ℕ} (hj : j = i ∨ j = star) (hlen : j ≤ as.length) :
    NativeGeneratedTestAncestry i star (nativeGeneratedSeed T a s j) := by
  constructor
  · simp [nativeGeneratedSeed]
  · simp [nativeGeneratedSeed]
  · simp [nativeGeneratedSeed]
  · intro c hc
    have hc' : c = (nativeFreshAtSlot T a s j).mark := by
      simpa only [nativeGeneratedSeed,List.mem_singleton] using hc
    subst c
    have H : (nativeFreshAtSlot T a s j).tree.splitIndex
        ((nativeFreshAtSlot T a s j).embed s) (nativeFreshAtSlot T a s j).mark = j := by
      rw [splitIndex_symm,nativeFreshAtSlot_split,T.splitIndex_self,Nat.min_eq_left hlen]
    change (nativeFreshAtSlot T a s j).tree.splitIndex
      ((nativeFreshAtSlot T a s j).embed s) (nativeFreshAtSlot T a s j).mark = i ∨
      (nativeFreshAtSlot T a s j).tree.splitIndex
      ((nativeFreshAtSlot T a s j).embed s) (nativeFreshAtSlot T a s j).mark = star
    rw [H]
    exact hj
  · simp [nativeGeneratedSeed]

theorem NativeGeneratedTestAncestry.addProjection {T : ClockTree S as}
    {i star : ℕ} {P : NativeGeneratedTest T} (hP : NativeGeneratedTestAncestry i star P)
    (a : ℝ) (hlen : star ≤ as.length) :
    NativeGeneratedTestAncestry i star (P.addProjection a star) := by
  let p := nativeFreshAtSlot T a P.target star
  have hs := (nativeFreshAtSlot_old_splits T a P.target star).2
  constructor
  · intro e he
    rcases List.mem_map.mp he with ⟨d,hd,rfl⟩
    change p.tree.splitIndex (p.embed P.target) (p.embed d.1) ≤ star ∧
      p.tree.splitIndex (p.embed P.target) (p.embed d.2) ≤ star
    rw [hs,hs]
    exact hP.exterior_departure d hd
  · intro e he
    rcases List.mem_map.mp he with ⟨d,hd,rfl⟩
    change p.tree.splitIndex (p.embed d.1) (p.embed d.2) = i ∨
      p.tree.splitIndex (p.embed d.1) (p.embed d.2) = star
    rw [hs]
    exact hP.exterior_cuts d hd
  · intro c hc
    change c ∈ P.teeth.map p.embed ++ [p.mark] at hc
    rcases List.mem_append.mp hc with hc | hc
    · rcases List.mem_map.mp hc with ⟨d,hd,rfl⟩
      change p.tree.splitIndex (p.embed P.target) (p.embed d) = star
      rw [hs]
      exact hP.teeth_star d hd
    · have hc' : c = p.mark := List.mem_singleton.mp hc
      subst c
      change p.tree.splitIndex (p.embed P.target) p.mark = star
      rw [splitIndex_symm,nativeFreshAtSlot_split,T.splitIndex_self,Nat.min_eq_left hlen]
  · intro c hc
    rcases List.mem_map.mp hc with ⟨d,hd,rfl⟩
    change p.tree.splitIndex (p.embed P.target) (p.embed d) = i ∨
      p.tree.splitIndex (p.embed P.target) (p.embed d) = star
    rw [hs]
    exact hP.incoming_cuts d hd
  · simpa only [NativeGeneratedTest.addProjection,List.length_map] using hP.incoming_degree

theorem NativeGeneratedTestAncestry.switchTarget {T : ClockTree S as}
    {i star : ℕ} {P : NativeGeneratedTest T} (hP : NativeGeneratedTestAncestry i star P)
    (a : ℝ) (c : T.Slot) {U : ℕ} (hstar : star < U)
    (hhigh : U ≤ T.splitIndex P.target c) :
    NativeGeneratedTestAncestry i star (P.switchTarget a star c) := by
  let p := nativeFreshAtSlot T a P.target star
  have hs := (nativeFreshAtSlot_old_splits T a P.target star).2
  constructor
  · intro e he
    rcases List.mem_map.mp he with ⟨d,hd,rfl⟩
    change p.tree.splitIndex p.mark (p.embed d.1) ≤ star ∧
      p.tree.splitIndex p.mark (p.embed d.2) ≤ star
    rw [nativeFreshAtSlot_split,nativeFreshAtSlot_split]
    exact ⟨Nat.min_le_left _ _,Nat.min_le_left _ _⟩
  · intro e he
    rcases List.mem_map.mp he with ⟨d,hd,rfl⟩
    change p.tree.splitIndex (p.embed d.1) (p.embed d.2) = i ∨
      p.tree.splitIndex (p.embed d.1) (p.embed d.2) = star
    rw [hs]
    exact hP.edges_low d hd
  · simp [NativeGeneratedTest.switchTarget]
  · intro d hd
    have hd' : d = p.embed c := by
      simpa only [NativeGeneratedTest.switchTarget,List.mem_singleton] using hd
    subst d
    exact Or.inr (nativeFreshAtSlot_high_relative_star T a P.target c hstar hhigh)
  · simp [NativeGeneratedTest.switchTarget]

inductive NativeTestGenerated (i star : ℕ) :
    {as : List PositiveMass} → (T : ClockTree S as) → NativeGeneratedTest T → Prop
  | seed {as : List PositiveMass} (T : ClockTree S as) (a : ℝ) (s : T.Slot)
      (j : ℕ) (hj : j = i ∨ j = star) (hlen : j ≤ as.length) :
      NativeTestGenerated i star (nativeFreshAtSlot T a s j).tree
        (nativeGeneratedSeed T a s j)
  | constant {as : List PositiveMass} {T : ClockTree S as} {P : NativeGeneratedTest T}
      (h : NativeTestGenerated i star T P) : NativeTestGenerated i star T P.constant
  | projection {as : List PositiveMass} {T : ClockTree S as} {P : NativeGeneratedTest T}
      (h : NativeTestGenerated i star T P) (a : ℝ) (hlen : star ≤ as.length) :
      NativeTestGenerated i star (nativeFreshAtSlot T a P.target star).tree
        (P.addProjection a star)
  | switch {as : List PositiveMass} {T : ClockTree S as} {P : NativeGeneratedTest T}
      (h : NativeTestGenerated i star T P) (a : ℝ) (c : T.Slot)
      (U : ℕ) (hstar : star < U) (hhigh : U ≤ T.splitIndex P.target c) :
      NativeTestGenerated i star (nativeFreshAtSlot T a P.target star).tree
        (P.switchTarget a star c)

theorem NativeTestGenerated.ancestry {T : ClockTree S as} {i star : ℕ}
    {P : NativeGeneratedTest T} (h : NativeTestGenerated i star T P) :
    NativeGeneratedTestAncestry i star P := by
  induction h with
  | seed T a s j hj hlen => exact nativeGeneratedSeed_ancestry T a s hj hlen
  | constant _ => exact NativeGeneratedTestAncestry.constant _ _ _
  | projection _ a hlen ih => exact ih.addProjection a hlen
  | switch _ a c U hstar hhigh ih => exact ih.switchTarget a c hstar hhigh

theorem NativeTestGenerated.edges_boundary {T : ClockTree S as} {i star U : ℕ}
    {P : NativeGeneratedTest T} (h : NativeTestGenerated i star T P)
    (hi : i ≤ star) (hstar : star < U) (e : T.Slot × T.Slot) (he : e ∈ P.edges) :
    T.splitIndex e.1 e.2 < U := by
  rcases h.ancestry.edges_low e he with H | H
  · rw [H]; exact hi.trans_lt hstar
  · rw [H]; exact hstar

theorem NativeTestGenerated.exterior_leaves_departed {T : ClockTree S as}
    {i star : ℕ} {P : NativeGeneratedTest T} (h : NativeTestGenerated i star T P)
    (e : T.Slot × T.Slot) (he : e ∈ P.exterior) :
    T.splitIndex P.target e.1 ≤ star ∧ T.splitIndex P.target e.2 ≤ star :=
  h.ancestry.exterior_departure e he

def NativeGeneratedTest.observedOutside {T : ClockTree S as} (P : NativeGeneratedTest T) :
    List T.Slot := P.exterior.flatMap (fun e => [e.1,e.2]) ++ P.teeth ++ P.incoming

theorem NativeTestGenerated.target_unique_observed_block {T : ClockTree S as}
    {i star U : ℕ} {P : NativeGeneratedTest T} (h : NativeTestGenerated i star T P)
    (hi : i ≤ star) (hstar : star < U) (c : T.Slot) (hc : c ∈ P.observedOutside) :
    T.splitIndex P.target c < U := by
  simp only [NativeGeneratedTest.observedOutside,List.mem_append,List.mem_flatMap] at hc
  rcases hc with (⟨e,he,hc⟩ | hc) | hc
  · have hout := h.exterior_leaves_departed e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl
    · exact hout.1.trans_lt hstar
    · exact hout.2.trans_lt hstar
  · rw [h.ancestry.teeth_star c hc]
    exact hstar
  · rcases h.ancestry.incoming_cuts c hc with H | H
    · rw [H];exact hi.trans_lt hstar
    · rw [H];exact hstar

theorem nativeGeneratedSeed_degree (T : ClockTree S as) (a : ℝ) (s : T.Slot) (j : ℕ) :
    (nativeGeneratedSeed T a s j).edges.length = 1 := by
  simp [nativeGeneratedSeed,NativeGeneratedTest.edges]

theorem NativeGeneratedTest.addProjection_degree {T : ClockTree S as}
    (P : NativeGeneratedTest T) (a : ℝ) (star : ℕ) :
    (P.addProjection a star).edges.length = P.edges.length+1 := by
  simp only [NativeGeneratedTest.edges,NativeGeneratedTest.addProjection,
    List.length_append,List.length_map,List.length_singleton]
  omega

theorem NativeGeneratedTest.switchTarget_degree {T : ClockTree S as}
    (P : NativeGeneratedTest T) (a : ℝ) (star : ℕ) (c : T.Slot) :
    (P.switchTarget a star c).edges.length = P.edges.length+1 := by
  simp [NativeGeneratedTest.edges,NativeGeneratedTest.switchTarget,Nat.add_assoc]

def nativeGeneratedLeafCount : {as : List PositiveMass} → ClockTree S as → ℕ
  | _,.leaf => 1
  | _,.step _ T => nativeGeneratedLeafCount T
  | _,.fork T V => nativeGeneratedLeafCount T+nativeGeneratedLeafCount V

theorem nativeGeneratedLeafCount_single (as : List PositiveMass) :
    nativeGeneratedLeafCount (single (S:=S) as) = 1 := by
  induction as with
  | nil => rfl
  | cons b as ih => exact ih

theorem nativeGeneratedLeafCount_fresh (T : ClockTree S as) (a : ℝ)
    (s : T.Slot) (j : ℕ) :
    nativeGeneratedLeafCount (nativeFreshAtSlot T a s j).tree =
      nativeGeneratedLeafCount T+1 := by
  induction T generalizing a j with
  | leaf => simp only [nativeFreshAtSlot,MarkedPlacement.fresh,nativeGeneratedLeafCount,
      nativeGeneratedLeafCount_single]
  | step b T ih =>
    cases j with
    | zero => simp only [nativeFreshAtSlot,MarkedPlacement.fresh,nativeGeneratedLeafCount,
        nativeGeneratedLeafCount_single]
    | succ j => exact ih b.val s j
  | fork T V ihT ihV =>
    cases j with
    | zero => simp only [nativeFreshAtSlot,MarkedPlacement.fresh,nativeGeneratedLeafCount,
        nativeGeneratedLeafCount_single]
    | succ j => cases s with
      | inl s =>
        change nativeGeneratedLeafCount (nativeFreshAtSlot T a s (j+1)).tree+
          nativeGeneratedLeafCount V = nativeGeneratedLeafCount T+nativeGeneratedLeafCount V+1
        rw [ihT]
        omega
      | inr s =>
        change nativeGeneratedLeafCount T+
          nativeGeneratedLeafCount (nativeFreshAtSlot V a s (j+1)).tree =
            nativeGeneratedLeafCount T+nativeGeneratedLeafCount V+1
        rw [ihV]
        omega

theorem nativeGeneratedSwitch_retains_high_children {T : ClockTree S as}
    (P : NativeGeneratedTest T) (a : ℝ) (star : ℕ) (c d : T.Slot) :
    let p := nativeFreshAtSlot T a P.target star
    Function.Injective p.embed ∧
      p.tree.splitIndex (p.embed c) (p.embed d) = T.splitIndex c d :=
  ⟨(nativeFreshAtSlot_old_splits T a P.target star).1,
    (nativeFreshAtSlot_old_splits T a P.target star).2 c d⟩

theorem native_high_relative_exterior_split {T : ClockTree S as}
    (a c o : T.Slot) {star U : ℕ} (hstar : star < U)
    (hhigh : U ≤ T.splitIndex a c) (hout : T.splitIndex a o ≤ star) :
    T.splitIndex c o = T.splitIndex a o := by
  let j := T.splitIndex a o
  have hca : U ≤ T.splitIndex c a := by rwa [T.splitIndex_symm]
  have hjU : j < U := hout.trans_lt hstar
  have hl : j ≤ T.splitIndex c o :=
    T.splitIndex_cut_trans j c a o (hjU.le.trans hca) le_rfl
  have hu : T.splitIndex c o ≤ j := by
    by_contra H
    have hco : j+1 ≤ T.splitIndex c o := by omega
    have hac : j+1 ≤ T.splitIndex a c := (by omega : j+1 ≤ U).trans hhigh
    have HH := T.splitIndex_cut_trans (j+1) a c o hac hco
    change j+1 ≤ j at HH
    omega
  exact le_antisymm hu hl

theorem NativeTestGenerated.exterior_high_replacement_geometry
    {T : ClockTree S as} {i star U : ℕ} {P : NativeGeneratedTest T}
    (h : NativeTestGenerated i star T P) (hstar : star < U)
    (c : T.Slot) (hhigh : U ≤ T.splitIndex P.target c)
    (e : T.Slot × T.Slot) (he : e ∈ P.exterior) :
    T.splitIndex c e.1 = T.splitIndex P.target e.1 ∧
    T.splitIndex c e.2 = T.splitIndex P.target e.2 ∧
    T.splitIndex P.target e.1 < T.splitIndex P.target c ∧
    T.splitIndex P.target e.2 < T.splitIndex P.target c := by
  have hout := h.exterior_leaves_departed e he
  exact ⟨native_high_relative_exterior_split P.target c e.1 hstar hhigh hout.1,
    native_high_relative_exterior_split P.target c e.2 hstar hhigh hout.2,
    (hout.1.trans_lt hstar).trans_le hhigh,
    (hout.2.trans_lt hstar).trans_le hhigh⟩

theorem nativeGeneratedSwitch_low_high_geometry {T : ClockTree S as}
    (P : NativeGeneratedTest T) (a : ℝ) (c : T.Slot) {star U : ℕ}
    (hstar : star < U) (hhigh : U ≤ T.splitIndex P.target c) :
    let p := nativeFreshAtSlot T a P.target star
    p.tree.splitIndex p.mark (p.embed P.target) = star ∧
    p.tree.splitIndex p.mark (p.embed c) = star ∧
    p.tree.splitIndex p.mark (p.embed c) <
      p.tree.splitIndex (p.embed P.target) (p.embed c) := by
  dsimp only
  have hca : U ≤ T.splitIndex c P.target := by rwa [T.splitIndex_symm]
  have hUlen := T.splitIndex_cut_trans U P.target c P.target hhigh hca
  rw [T.splitIndex_self] at hUlen
  have hlen : star ≤ as.length := hstar.le.trans hUlen
  have hs : (nativeFreshAtSlot T a P.target star).tree.splitIndex
      (nativeFreshAtSlot T a P.target star).mark
      ((nativeFreshAtSlot T a P.target star).embed P.target) = star := by
    rw [nativeFreshAtSlot_split,T.splitIndex_self,Nat.min_eq_left hlen]
  have hc := nativeFreshAtSlot_high_relative_star T a P.target c hstar hhigh
  exact ⟨hs,hc,by
    rw [hc,(nativeFreshAtSlot_old_splits T a P.target star).2]
    exact hstar.trans_le hhigh⟩

theorem nativeGeneratedSwitch_retains_assignment {T : ClockTree S as}
    (P : NativeGeneratedTest T) (a : ℝ) (star : ℕ)
    (σ : (nativeFreshAtSlot T a P.target star).tree.Assignment) (c : T.Slot) :
    (nativeFreshAtSlot T a P.target star).tree.atSlot σ
      ((nativeFreshAtSlot T a P.target star).embed c) =
    T.atSlot ((nativeFreshAtSlot T a P.target star).restrict σ) c :=
  ((nativeFreshAtSlot T a P.target star).restrict_at σ c).symm

def nativeGeneratedEdgeProduct (T : ClockTree S as) (R : S → S → ℝ)
    (C : ℕ → ℝ) (es : List (T.Slot × T.Slot)) (σ : T.Assignment) : ℝ :=
  (es.map (fun e => R (T.atSlot σ e.1) (T.atSlot σ e.2)-C (T.splitIndex e.1 e.2))).prod

def NativeGeneratedTest.value {T : ClockTree S as} (P : NativeGeneratedTest T)
    (R : S → S → ℝ) (C : ℕ → ℝ) (σ : T.Assignment) : ℝ :=
  nativeGeneratedEdgeProduct T R C P.edges σ

theorem nativeGeneratedEdgeProduct_append (T : ClockTree S as) (R : S → S → ℝ)
    (C : ℕ → ℝ) (es fs : List (T.Slot × T.Slot)) (σ : T.Assignment) :
    nativeGeneratedEdgeProduct T R C (es ++ fs) σ =
      nativeGeneratedEdgeProduct T R C es σ * nativeGeneratedEdgeProduct T R C fs σ := by
  simp only [nativeGeneratedEdgeProduct,List.map_append,List.prod_append]

theorem nativeGeneratedEdgeProduct_graft_restrict {T : ClockTree S as}
    (a : ℝ) (s : T.Slot) (j : ℕ) (R : S → S → ℝ) (C : ℕ → ℝ)
    (es : List (T.Slot × T.Slot))
    (σ : (nativeFreshAtSlot T a s j).tree.Assignment) :
    let p := nativeFreshAtSlot T a s j
    nativeGeneratedEdgeProduct p.tree R C
      (es.map (fun e => (p.embed e.1,p.embed e.2))) σ =
    nativeGeneratedEdgeProduct T R C es (p.restrict σ) := by
  dsimp only
  unfold nativeGeneratedEdgeProduct
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro e he
  dsimp only [Function.comp_def]
  rw [(nativeFreshAtSlot_old_splits T a s j).2,
    ←(nativeFreshAtSlot T a s j).restrict_at σ e.1,
    ←(nativeFreshAtSlot T a s j).restrict_at σ e.2]

theorem NativeGeneratedTest.switchTarget_value {T : ClockTree S as}
    (P : NativeGeneratedTest T) (a : ℝ) (c : T.Slot) {star U : ℕ}
    (hstar : star < U) (hhigh : U ≤ T.splitIndex P.target c)
    (R : S → S → ℝ) (C : ℕ → ℝ)
    (σ : (nativeFreshAtSlot T a P.target star).tree.Assignment) :
    let p := nativeFreshAtSlot T a P.target star
    (P.switchTarget a star c).value R C σ =
      P.value R C (p.restrict σ)*
        (R (p.spin σ) (T.atSlot (p.restrict σ) c)-C star) := by
  dsimp only
  have he : (P.switchTarget a star c).edges =
      P.edges.map (fun e => ((nativeFreshAtSlot T a P.target star).embed e.1,
        (nativeFreshAtSlot T a P.target star).embed e.2)) ++
        [((nativeFreshAtSlot T a P.target star).mark,
          (nativeFreshAtSlot T a P.target star).embed c)] := by
    simp only [NativeGeneratedTest.edges,NativeGeneratedTest.switchTarget,
      List.map_nil,List.append_nil,List.map_singleton]
  change nativeGeneratedEdgeProduct _ R C (P.switchTarget a star c).edges σ = _
  rw [he,nativeGeneratedEdgeProduct_append,nativeGeneratedEdgeProduct_graft_restrict]
  simp only [nativeGeneratedEdgeProduct,List.map_singleton,List.prod_singleton]
  rw [nativeFreshAtSlot_high_relative_star T a P.target c hstar hhigh,
    ←(nativeFreshAtSlot T a P.target star).spin_at σ,
    ←(nativeFreshAtSlot T a P.target star).restrict_at σ c]
  rfl

theorem NativeGeneratedTest.addProjection_value {T : ClockTree S as}
    (P : NativeGeneratedTest T) (a : ℝ) {star : ℕ} (hlen : star ≤ as.length)
    (R : S → S → ℝ) (C : ℕ → ℝ)
    (σ : (nativeFreshAtSlot T a P.target star).tree.Assignment) :
    let p := nativeFreshAtSlot T a P.target star
    (P.addProjection a star).value R C σ =
      P.value R C (p.restrict σ)*
        (R (T.atSlot (p.restrict σ) P.target) (p.spin σ)-C star) := by
  dsimp only
  let p := nativeFreshAtSlot T a P.target star
  let lift := fun e : T.Slot × T.Slot => (p.embed e.1,p.embed e.2)
  have he : (P.addProjection a star).edges =
      P.exterior.map lift ++
        ((P.teeth.map (fun c => (P.target,c))).map lift ++ [(p.embed P.target,p.mark)]) ++
        (P.incoming.map (fun c => (P.target,c))).map lift := by
    simp only [NativeGeneratedTest.edges,NativeGeneratedTest.addProjection,
      List.map_append,List.map_map,List.map_singleton,Function.comp_def,lift,p]
  have hcut : p.tree.splitIndex (p.embed P.target) p.mark = star := by
    rw [splitIndex_symm,nativeFreshAtSlot_split,T.splitIndex_self,Nat.min_eq_left hlen]
  have hedge : nativeGeneratedEdgeProduct p.tree R C [(p.embed P.target,p.mark)] σ =
      R (T.atSlot (p.restrict σ) P.target) (p.spin σ)-C star := by
    simp only [nativeGeneratedEdgeProduct,List.map_singleton,List.prod_singleton]
    rw [hcut,←p.restrict_at σ P.target,←p.spin_at σ]
  change nativeGeneratedEdgeProduct p.tree R C (P.addProjection a star).edges σ = _
  rw [he]
  simp only [nativeGeneratedEdgeProduct_append]
  rw [hedge]
  have hH := nativeGeneratedEdgeProduct_graft_restrict a P.target star R C P.exterior σ
  have hT := nativeGeneratedEdgeProduct_graft_restrict a P.target star R C
    (P.teeth.map (fun c => (P.target,c))) σ
  have hI := nativeGeneratedEdgeProduct_graft_restrict a P.target star R C
    (P.incoming.map (fun c => (P.target,c))) σ
  change nativeGeneratedEdgeProduct p.tree R C (P.exterior.map lift) σ = _ at hH
  change nativeGeneratedEdgeProduct p.tree R C
    ((P.teeth.map (fun c => (P.target,c))).map lift) σ = _ at hT
  change nativeGeneratedEdgeProduct p.tree R C
    ((P.incoming.map (fun c => (P.target,c))).map lift) σ = _ at hI
  rw [hH,hT,hI]
  simp only [NativeGeneratedTest.value,NativeGeneratedTest.edges,nativeGeneratedEdgeProduct_append]
  ring

theorem NativeGeneratedTest.constant_value {T : ClockTree S as}
    (P : NativeGeneratedTest T) (R : S → S → ℝ) (C : ℕ → ℝ) (σ : T.Assignment) :
    P.constant.value R C σ = 1 := by
  simp [NativeGeneratedTest.value,NativeGeneratedTest.constant,
    NativeGeneratedTest.edges,nativeGeneratedEdgeProduct]

def NativeGeneratedTest.centeredPolynomial {T : ClockTree S as}
    (P : NativeGeneratedTest T) (mean : ℝ) : List (ℝ × NativeGeneratedTest T) :=
  [(1,P),(-mean,P.constant)]

theorem NativeGeneratedTest.centeredPolynomial_value {T : ClockTree S as}
    (P : NativeGeneratedTest T) (mean : ℝ) (R : S → S → ℝ)
    (C : ℕ → ℝ) (σ : T.Assignment) :
    ((P.centeredPolynomial mean).map (fun t => t.1*t.2.value R C σ)).sum =
      P.value R C σ-mean := by
  simp [NativeGeneratedTest.centeredPolynomial,NativeGeneratedTest.constant_value,sub_eq_add_neg]

theorem NativeTestGenerated.centeredPolynomial_generated {T : ClockTree S as}
    {i star : ℕ} {P : NativeGeneratedTest T} (h : NativeTestGenerated i star T P)
    (mean : ℝ) (t : ℝ × NativeGeneratedTest T) (ht : t ∈ P.centeredPolynomial mean) :
    NativeTestGenerated i star T t.2 := by
  simp only [NativeGeneratedTest.centeredPolynomial,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl | rfl
  · exact h
  · exact h.constant

def nativeGeneratedNonStarCount (T : ClockTree S as) (star : ℕ)
    (es : List (T.Slot × T.Slot)) : ℕ :=
  (es.map (fun e => if T.splitIndex e.1 e.2 = star then 0 else 1)).sum

theorem nativeGeneratedNonStarCount_append (T : ClockTree S as) (star : ℕ)
    (es fs : List (T.Slot × T.Slot)) :
    nativeGeneratedNonStarCount T star (es ++ fs) =
      nativeGeneratedNonStarCount T star es+nativeGeneratedNonStarCount T star fs := by
  simp only [nativeGeneratedNonStarCount,List.map_append,List.sum_append]

theorem nativeGeneratedNonStarCount_graft {T : ClockTree S as}
    (a : ℝ) (s : T.Slot) (j star : ℕ) (es : List (T.Slot × T.Slot)) :
    let p := nativeFreshAtSlot T a s j
    nativeGeneratedNonStarCount p.tree star
      (es.map (fun e => (p.embed e.1,p.embed e.2))) =
    nativeGeneratedNonStarCount T star es := by
  dsimp only
  unfold nativeGeneratedNonStarCount
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro e he
  dsimp only [Function.comp_def]
  rw [(nativeFreshAtSlot_old_splits T a s j).2]

theorem NativeGeneratedTest.switchTarget_nonStarCount {T : ClockTree S as}
    (P : NativeGeneratedTest T) (a : ℝ) (c : T.Slot) {star U : ℕ}
    (hstar : star < U) (hhigh : U ≤ T.splitIndex P.target c) :
    nativeGeneratedNonStarCount (nativeFreshAtSlot T a P.target star).tree star
      (P.switchTarget a star c).edges = nativeGeneratedNonStarCount T star P.edges := by
  simp only [NativeGeneratedTest.edges,NativeGeneratedTest.switchTarget,
    List.map_nil,List.append_nil,List.map_singleton]
  rw [nativeGeneratedNonStarCount_append,nativeGeneratedNonStarCount_graft]
  simp only [nativeGeneratedNonStarCount,List.map_singleton,List.sum_singleton,
    nativeFreshAtSlot_high_relative_star T a P.target c hstar hhigh,ite_true,Nat.add_zero]

theorem NativeGeneratedTest.addProjection_nonStarCount {T : ClockTree S as}
    (P : NativeGeneratedTest T) (a : ℝ) {star : ℕ} (hlen : star ≤ as.length) :
    nativeGeneratedNonStarCount (nativeFreshAtSlot T a P.target star).tree star
      (P.addProjection a star).edges = nativeGeneratedNonStarCount T star P.edges := by
  let p := nativeFreshAtSlot T a P.target star
  let lift := fun e : T.Slot × T.Slot => (p.embed e.1,p.embed e.2)
  have he : (P.addProjection a star).edges =
      P.exterior.map lift ++
        ((P.teeth.map (fun c => (P.target,c))).map lift ++ [(p.embed P.target,p.mark)]) ++
        (P.incoming.map (fun c => (P.target,c))).map lift := by
    simp only [NativeGeneratedTest.edges,NativeGeneratedTest.addProjection,
      List.map_append,List.map_map,List.map_singleton,Function.comp_def,lift,p]
  have hcut : p.tree.splitIndex (p.embed P.target) p.mark = star := by
    rw [splitIndex_symm,nativeFreshAtSlot_split,T.splitIndex_self,Nat.min_eq_left hlen]
  rw [he]
  simp only [nativeGeneratedNonStarCount_append]
  have hH := nativeGeneratedNonStarCount_graft a P.target star star P.exterior
  have hT := nativeGeneratedNonStarCount_graft a P.target star star
    (P.teeth.map (fun c => (P.target,c)))
  have hI := nativeGeneratedNonStarCount_graft a P.target star star
    (P.incoming.map (fun c => (P.target,c)))
  change nativeGeneratedNonStarCount p.tree star (P.exterior.map lift) = _ at hH
  change nativeGeneratedNonStarCount p.tree star
    ((P.teeth.map (fun c => (P.target,c))).map lift) = _ at hT
  change nativeGeneratedNonStarCount p.tree star
    ((P.incoming.map (fun c => (P.target,c))).map lift) = _ at hI
  rw [hH,hT,hI]
  have hcut' : (nativeFreshAtSlot T a P.target star).tree.splitIndex
      (p.embed P.target) p.mark = star := hcut
  simp only [nativeGeneratedNonStarCount,List.map_singleton,List.sum_singleton,hcut',ite_true,
    Nat.add_zero,NativeGeneratedTest.edges,List.map_append,List.sum_append]

theorem NativeTestGenerated.at_most_one_initial_edge {T : ClockTree S as}
    {i star : ℕ} {P : NativeGeneratedTest T} (h : NativeTestGenerated i star T P) :
    nativeGeneratedNonStarCount T star P.edges ≤ 1 := by
  induction h with
  | seed T a s j hj hlen =>
    simp only [nativeGeneratedSeed,NativeGeneratedTest.edges,List.map_nil,
      List.map_singleton,List.nil_append,nativeGeneratedNonStarCount,List.sum_singleton]
    split_ifs <;> omega
  | constant _ =>
    simp only [NativeGeneratedTest.constant,NativeGeneratedTest.edges,List.map_nil,
      List.nil_append,nativeGeneratedNonStarCount,List.sum_nil,Nat.zero_le]
  | projection _ a hlen ih =>
    rw [NativeGeneratedTest.addProjection_nonStarCount _ a hlen]
    exact ih
  | switch _ a c U hstar hhigh ih =>
    rw [NativeGeneratedTest.switchTarget_nonStarCount _ a c hstar hhigh]
    exact ih

variable {ι : Type*} [Fintype ι] [Nonempty ι] [Fintype S] [Nonempty S]

theorem NativeGeneratedTest.old_value_disorder_marginal {T : ClockTree S as}
    (P : NativeGeneratedTest T) {w : S → ℝ} (hw : ∀ σ,0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ]ℝ) (ho : MassOrdered 0 as) (star : ℕ)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (R : S → S → ℝ) (C : ℕ → ℝ) (x : ι → ℝ) :
    let p := nativeFreshAtSlot T 0 P.target star
    p.tree.disorderExpect w φ v q
      (fun σ => P.value R C (p.restrict σ)) x = T.disorderExpect w φ v q (P.value R C) x :=
  nativeFreshAtSlot_old_disorder_marginal hw φ T ho P.target star v q (P.value R C) x

end OAI.SKFluctuations.Hierarchy.ClockTree
