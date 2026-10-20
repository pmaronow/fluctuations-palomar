module

public import ComparisonSignedCavityGeneratedTestAncestry

@[expose] public section

noncomputable section
set_option maxHeartbeats 5000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type*} {as : List PositiveMass}

def NativeGeneratedTest.retarget {T : ClockTree S as}
    (P : NativeGeneratedTest T) (a : ℝ) (star : ℕ) :
    NativeGeneratedTest (nativeFreshAtSlot T a P.target star).tree :=
  let p := nativeFreshAtSlot T a P.target star
  ⟨p.mark,P.edges.map (fun e => (p.embed e.1,p.embed e.2)),[],[]⟩

def NativeGeneratedTest.retainOnFresh {T : ClockTree S as}
    (P : NativeGeneratedTest T) (a : ℝ) (j : ℕ) :
    NativeGeneratedTest (nativeFreshAtSlot T a P.target j).tree :=
  let p := nativeFreshAtSlot T a P.target j
  ⟨p.embed P.target,P.exterior.map (fun e => (p.embed e.1,p.embed e.2)),
    P.teeth.map p.embed,P.incoming.map p.embed⟩

theorem NativeGeneratedTest.retainOnFresh_edges {T : ClockTree S as}
    (P : NativeGeneratedTest T) (a : ℝ) (j : ℕ) :
    (P.retainOnFresh a j).edges = P.edges.map (fun e =>
      ((nativeFreshAtSlot T a P.target j).embed e.1,
        (nativeFreshAtSlot T a P.target j).embed e.2)) := by
  simp only [NativeGeneratedTest.edges,NativeGeneratedTest.retainOnFresh,
    List.map_append,List.map_map,Function.comp_def]

theorem NativeGeneratedTestAncestry.retainOnFresh {T : ClockTree S as}
    {i star : ℕ} {P : NativeGeneratedTest T}
    (hP : NativeGeneratedTestAncestry i star P) (a : ℝ) (j : ℕ) :
    NativeGeneratedTestAncestry i star (P.retainOnFresh a j) := by
  let p := nativeFreshAtSlot T a P.target j
  have hs := (nativeFreshAtSlot_old_splits T a P.target j).2
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
    rcases List.mem_map.mp hc with ⟨d,hd,rfl⟩
    change p.tree.splitIndex (p.embed P.target) (p.embed d) = star
    rw [hs]
    exact hP.teeth_star d hd
  · intro c hc
    rcases List.mem_map.mp hc with ⟨d,hd,rfl⟩
    change p.tree.splitIndex (p.embed P.target) (p.embed d) = i ∨
      p.tree.splitIndex (p.embed P.target) (p.embed d) = star
    rw [hs]
    exact hP.incoming_cuts d hd
  · simpa only [NativeGeneratedTest.retainOnFresh,List.length_map] using hP.incoming_degree

theorem nativeResourceFreshHighGeometry (T : ClockTree S as)
    (a : ℝ) (s : T.Slot) (j : ℕ) (hj : j ≤ as.length) :
    (nativeFreshAtSlot T a s j).tree.splitIndex
      ((nativeFreshAtSlot T a s j).embed s) (nativeFreshAtSlot T a s j).mark = j := by
  rw [splitIndex_symm,nativeFreshAtSlot_split,T.splitIndex_self,Nat.min_eq_left hj]

theorem NativeGeneratedTest.retarget_edges {T : ClockTree S as}
    (P : NativeGeneratedTest T) (a : ℝ) (star : ℕ) :
    (P.retarget a star).edges = P.edges.map (fun e =>
      ((nativeFreshAtSlot T a P.target star).embed e.1,
       (nativeFreshAtSlot T a P.target star).embed e.2)) := by
  simp [NativeGeneratedTest.retarget,NativeGeneratedTest.edges]

theorem NativeGeneratedTestAncestry.retarget {T : ClockTree S as}
    {i star : ℕ} {P : NativeGeneratedTest T}
    (hP : NativeGeneratedTestAncestry i star P) (a : ℝ) :
    NativeGeneratedTestAncestry i star (P.retarget a star) := by
  let p := nativeFreshAtSlot T a P.target star
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
    rw [(nativeFreshAtSlot_old_splits T a P.target star).2]
    exact hP.edges_low d hd
  · simp [NativeGeneratedTest.retarget]
  · simp [NativeGeneratedTest.retarget]
  · simp [NativeGeneratedTest.retarget]

theorem NativeGeneratedTest.retarget_value {T : ClockTree S as}
    (P : NativeGeneratedTest T) (a : ℝ) (star : ℕ)
    (R : S → S → ℝ) (C : ℕ → ℝ)
    (σ : (nativeFreshAtSlot T a P.target star).tree.Assignment) :
    (P.retarget a star).value R C σ =
      P.value R C ((nativeFreshAtSlot T a P.target star).restrict σ) := by
  change nativeGeneratedEdgeProduct _ R C (P.retarget a star).edges σ = _
  rw [P.retarget_edges]
  exact nativeGeneratedEdgeProduct_graft_restrict a P.target star R C P.edges σ

theorem NativeGeneratedTest.retainOnFresh_value {T : ClockTree S as}
    (P : NativeGeneratedTest T) (a : ℝ) (j : ℕ) (R : S → S → ℝ) (C : ℕ → ℝ)
    (σ : (nativeFreshAtSlot T a P.target j).tree.Assignment) :
    (P.retainOnFresh a j).value R C σ =
      P.value R C ((nativeFreshAtSlot T a P.target j).restrict σ) := by
  change nativeGeneratedEdgeProduct _ R C (P.retainOnFresh a j).edges σ = _
  rw [P.retainOnFresh_edges]
  exact nativeGeneratedEdgeProduct_graft_restrict a P.target j R C P.edges σ

theorem NativeGeneratedTest.retarget_nonStarCount {T : ClockTree S as}
    (P : NativeGeneratedTest T) (a : ℝ) (star : ℕ) :
    nativeGeneratedNonStarCount (nativeFreshAtSlot T a P.target star).tree star
      (P.retarget a star).edges = nativeGeneratedNonStarCount T star P.edges := by
  rw [P.retarget_edges]
  exact nativeGeneratedNonStarCount_graft a P.target star star P.edges

variable {ι : Type*} [Fintype ι] [Nonempty ι] [Fintype S] [Nonempty S]

theorem NativeGeneratedTest.retarget_disorder_marginal {T : ClockTree S as}
    (P : NativeGeneratedTest T) {w : S → ℝ} (hw : ∀ σ,0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ]ℝ) (ho : MassOrdered 0 as) (star : ℕ)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (R : S → S → ℝ) (C : ℕ → ℝ) (x : ι → ℝ) :
    (nativeFreshAtSlot T 0 P.target star).tree.disorderExpect w φ v q
      ((P.retarget 0 star).value R C) x =
        T.disorderExpect w φ v q (P.value R C) x := by
  have he : (P.retarget 0 star).value R C =
      fun σ => P.value R C ((nativeFreshAtSlot T 0 P.target star).restrict σ) :=
    funext (fun σ => P.retarget_value 0 star R C σ)
  rw [he]
  exact P.old_value_disorder_marginal hw φ ho star v q R C x

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type*} {as : List PositiveMass}

inductive NativeResourceMark where
  | initial
  | oldStar
  | markedStar (generation : ℕ)
  deriving DecidableEq, Repr

def NativeResourceMark.cut (i star : ℕ) : NativeResourceMark → ℕ
  | .initial => i
  | .oldStar => star
  | .markedStar _ => star

abbrev NativeResourceFactor (T : ClockTree S as) :=
  NativeResourceMark × (T.Slot × T.Slot)

structure NativeResourceMonomial (i star : ℕ) (T : ClockTree S as) where
  test : NativeGeneratedTest T
  factors : List (NativeResourceFactor T)
  realizes : (factors.map Prod.snd).Perm test.edges
  cuts : ∀ f ∈ factors,T.splitIndex f.2.1 f.2.2 = f.1.cut i star
  ancestry : NativeGeneratedTestAncestry i star test

def NativeResourceMonomial.tags {i star : ℕ} {T : ClockTree S as}
    (P : NativeResourceMonomial i star T) : List NativeResourceMark :=
  P.factors.map Prod.fst

def nativeResourceLiftFactor (T : ClockTree S as) (a : ℝ) (s : T.Slot)
    (j : ℕ) (f : NativeResourceFactor T) :
    NativeResourceFactor (nativeFreshAtSlot T a s j).tree :=
  (f.1,((nativeFreshAtSlot T a s j).embed f.2.1,
    (nativeFreshAtSlot T a s j).embed f.2.2))

theorem nativeResourceLiftFactor_cuts (T : ClockTree S as) (a : ℝ)
    (s : T.Slot) (j : ℕ) (f : NativeResourceFactor T) :
    (nativeFreshAtSlot T a s j).tree.splitIndex
      (nativeResourceLiftFactor T a s j f).2.1
      (nativeResourceLiftFactor T a s j f).2.2 = T.splitIndex f.2.1 f.2.2 :=
  (nativeFreshAtSlot_old_splits T a s j).2 _ _

theorem NativeGeneratedTest.addProjection_edges_perm {T : ClockTree S as}
    (P : NativeGeneratedTest T) (a : ℝ) (star : ℕ) :
    (P.addProjection a star).edges.Perm
      (P.edges.map (fun e => ((nativeFreshAtSlot T a P.target star).embed e.1,
        (nativeFreshAtSlot T a P.target star).embed e.2)) ++
        [((nativeFreshAtSlot T a P.target star).embed P.target,
          (nativeFreshAtSlot T a P.target star).mark)]) := by
  let p := nativeFreshAtSlot T a P.target star
  let E := P.exterior.map (fun e => (p.embed e.1,p.embed e.2))
  let D := P.teeth.map (fun c => (p.embed P.target,p.embed c))
  let I := P.incoming.map (fun c => (p.embed P.target,p.embed c))
  have h : ([((p.embed P.target),p.mark)] ++ I).Perm
      (I ++ [((p.embed P.target),p.mark)]) := List.perm_append_comm
  simpa only [NativeGeneratedTest.edges,NativeGeneratedTest.addProjection,
    List.map_append,List.map_map,List.map_singleton,Function.comp_def,
    List.append_assoc,E,D,I,p] using h.append_left (E ++ D)

def NativeResourceMonomial.constant {i star : ℕ} {T : ClockTree S as}
    (P : NativeResourceMonomial i star T) : NativeResourceMonomial i star T where
  test := P.test.constant
  factors := []
  realizes := by simp [NativeGeneratedTest.constant,NativeGeneratedTest.edges]
  cuts := by simp
  ancestry := NativeGeneratedTestAncestry.constant i star P.test

def nativeResourceConstant (T : ClockTree S as) (s : T.Slot) (i star : ℕ) :
    NativeResourceMonomial i star T where
  test := ⟨s,[],[],[]⟩
  factors := []
  realizes := by simp [NativeGeneratedTest.edges]
  cuts := by simp
  ancestry := by constructor <;> simp

def nativeResourceSeed (T : ClockTree S as) (a : ℝ) (s : T.Slot)
    (i star : ℕ) (mark : NativeResourceMark)
    (hmark : mark = .initial ∨ mark = .oldStar)
    (hlen : mark.cut i star ≤ as.length) :
    NativeResourceMonomial i star (nativeFreshAtSlot T a s (mark.cut i star)).tree where
  test := nativeGeneratedSeed T a s (mark.cut i star)
  factors := [(mark,((nativeFreshAtSlot T a s (mark.cut i star)).embed s,
    (nativeFreshAtSlot T a s (mark.cut i star)).mark))]
  realizes := by simp [nativeGeneratedSeed,NativeGeneratedTest.edges]
  cuts := by
    intro f hf
    have hf' := List.mem_singleton.mp hf
    subst f
    rw [splitIndex_symm,nativeFreshAtSlot_split,T.splitIndex_self,Nat.min_eq_left hlen]
  ancestry := nativeGeneratedSeed_ancestry T a s (by
    rcases hmark with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl) hlen

def NativeResourceMonomial.retarget {i star : ℕ} {T : ClockTree S as}
    (P : NativeResourceMonomial i star T) (a : ℝ) :
    NativeResourceMonomial i star (nativeFreshAtSlot T a P.test.target star).tree where
  test := P.test.retarget a star
  factors := P.factors.map (nativeResourceLiftFactor T a P.test.target star)
  realizes := by
    have h := P.realizes.map (fun e =>
      ((nativeFreshAtSlot T a P.test.target star).embed e.1,
       (nativeFreshAtSlot T a P.test.target star).embed e.2))
    simpa only [NativeGeneratedTest.retarget_edges,List.map_map,
      nativeResourceLiftFactor,Function.comp_def] using h
  cuts := by
    intro f hf
    rcases List.mem_map.mp hf with ⟨e,he,rfl⟩
    rw [nativeResourceLiftFactor_cuts]
    exact P.cuts e he
  ancestry := P.ancestry.retarget a

def NativeResourceMonomial.retainOnFresh {i star : ℕ} {T : ClockTree S as}
    (P : NativeResourceMonomial i star T) (a : ℝ) (j : ℕ) :
    NativeResourceMonomial i star (nativeFreshAtSlot T a P.test.target j).tree where
  test := P.test.retainOnFresh a j
  factors := P.factors.map (nativeResourceLiftFactor T a P.test.target j)
  realizes := by
    have h := P.realizes.map (fun e =>
      ((nativeFreshAtSlot T a P.test.target j).embed e.1,
        (nativeFreshAtSlot T a P.test.target j).embed e.2))
    simpa only [NativeGeneratedTest.retainOnFresh_edges,List.map_map,
      nativeResourceLiftFactor,Function.comp_def] using h
  cuts := by
    intro f hf
    rcases List.mem_map.mp hf with ⟨e,he,rfl⟩
    rw [nativeResourceLiftFactor_cuts]
    exact P.cuts e he
  ancestry := P.ancestry.retainOnFresh a j

def NativeResourceMonomial.projection {i star : ℕ} {T : ClockTree S as}
    (P : NativeResourceMonomial i star T) (a : ℝ) (k : ℕ)
    (hlen : star ≤ as.length) :
    NativeResourceMonomial i star (nativeFreshAtSlot T a P.test.target star).tree where
  test := P.test.addProjection a star
  factors := P.factors.map (nativeResourceLiftFactor T a P.test.target star) ++
    [(.markedStar k,((nativeFreshAtSlot T a P.test.target star).embed P.test.target,
      (nativeFreshAtSlot T a P.test.target star).mark))]
  realizes := by
    have h := (P.realizes.map (fun e =>
      ((nativeFreshAtSlot T a P.test.target star).embed e.1,
        (nativeFreshAtSlot T a P.test.target star).embed e.2))).append_right
      [((nativeFreshAtSlot T a P.test.target star).embed P.test.target,
        (nativeFreshAtSlot T a P.test.target star).mark)]
    have h' := h.trans (P.test.addProjection_edges_perm a star).symm
    simpa only [List.map_append,List.map_map,List.map_singleton,
      nativeResourceLiftFactor,Function.comp_def] using h'
  cuts := by
    intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · rcases List.mem_map.mp hf with ⟨e,he,rfl⟩
      rw [nativeResourceLiftFactor_cuts]
      exact P.cuts e he
    · have hf' := List.mem_singleton.mp hf
      subst f
      rw [splitIndex_symm,nativeFreshAtSlot_split,T.splitIndex_self,Nat.min_eq_left hlen]
      rfl
  ancestry := P.ancestry.addProjection a hlen

def NativeResourceMonomial.switch {i star U : ℕ} {T : ClockTree S as}
    (P : NativeResourceMonomial i star T) (a : ℝ) (k : ℕ)
    (c : T.Slot) (hstar : star < U) (hhigh : U ≤ T.splitIndex P.test.target c) :
    NativeResourceMonomial i star (nativeFreshAtSlot T a P.test.target star).tree where
  test := P.test.switchTarget a star c
  factors := P.factors.map (nativeResourceLiftFactor T a P.test.target star) ++
    [(.markedStar k,((nativeFreshAtSlot T a P.test.target star).mark,
      (nativeFreshAtSlot T a P.test.target star).embed c))]
  realizes := by
    have h := (P.realizes.map (fun e =>
      ((nativeFreshAtSlot T a P.test.target star).embed e.1,
        (nativeFreshAtSlot T a P.test.target star).embed e.2))).append_right
      [((nativeFreshAtSlot T a P.test.target star).mark,
        (nativeFreshAtSlot T a P.test.target star).embed c)]
    simpa only [NativeGeneratedTest.switchTarget,NativeGeneratedTest.edges,
      List.map_nil,List.append_nil,List.map_singleton,List.map_append,List.map_map,
      nativeResourceLiftFactor,Function.comp_def] using h
  cuts := by
    intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · rcases List.mem_map.mp hf with ⟨e,he,rfl⟩
      rw [nativeResourceLiftFactor_cuts]
      exact P.cuts e he
    · have hf' := List.mem_singleton.mp hf
      subst f
      exact nativeFreshAtSlot_high_relative_star T a P.test.target c hstar hhigh
  ancestry := P.ancestry.switchTarget a c hstar hhigh

def NativeResourceMonomial.switchFreshHigh {i star : ℕ} {T : ClockTree S as}
    (P : NativeResourceMonomial i star T) (a : ℝ) (k j U : ℕ)
    (hjU : U ≤ j) (hj : j ≤ as.length) (hstar : star < U) :
    NativeResourceMonomial i star
      (nativeFreshAtSlot (nativeFreshAtSlot T a P.test.target j).tree a
        ((nativeFreshAtSlot T a P.test.target j).embed P.test.target) star).tree :=
  (P.retainOnFresh a j).switch a k (nativeFreshAtSlot T a P.test.target j).mark hstar
    (by
      change U ≤ (nativeFreshAtSlot T a P.test.target j).tree.splitIndex
        ((nativeFreshAtSlot T a P.test.target j).embed P.test.target)
        (nativeFreshAtSlot T a P.test.target j).mark
      rw [nativeResourceFreshHighGeometry T a P.test.target j hj]
      exact hjU)

theorem NativeResourceMonomial.factor_product_eq {i star : ℕ} {T : ClockTree S as}
    (P : NativeResourceMonomial i star T) (R : S → S → ℝ) (C : ℕ → ℝ)
    (σ : T.Assignment) :
    (P.factors.map (fun f => R (T.atSlot σ f.2.1) (T.atSlot σ f.2.2)-
      C (T.splitIndex f.2.1 f.2.2))).prod = P.test.value R C σ := by
  have h := (P.realizes.map (fun e => R (T.atSlot σ e.1) (T.atSlot σ e.2)-
    C (T.splitIndex e.1 e.2))).prod_eq
  simpa only [List.map_map,Function.comp_def,NativeGeneratedTest.value,
    nativeGeneratedEdgeProduct] using h

@[simp] theorem NativeResourceMonomial.constant_tags {i star : ℕ} {T : ClockTree S as}
    (P : NativeResourceMonomial i star T) : P.constant.tags = [] := rfl

@[simp] theorem NativeResourceMonomial.retarget_tags {i star : ℕ} {T : ClockTree S as}
    (P : NativeResourceMonomial i star T) (a : ℝ) : (P.retarget a).tags = P.tags := by
  simp only [NativeResourceMonomial.retarget,NativeResourceMonomial.tags,
    List.map_map,nativeResourceLiftFactor,Function.comp_def]

@[simp] theorem NativeResourceMonomial.retainOnFresh_tags {i star : ℕ} {T : ClockTree S as}
    (P : NativeResourceMonomial i star T) (a : ℝ) (j : ℕ) :
    (P.retainOnFresh a j).tags = P.tags := by
  simp only [NativeResourceMonomial.retainOnFresh,NativeResourceMonomial.tags,
    List.map_map,nativeResourceLiftFactor,Function.comp_def]

@[simp] theorem NativeResourceMonomial.projection_tags {i star : ℕ} {T : ClockTree S as}
    (P : NativeResourceMonomial i star T) (a : ℝ) (k : ℕ) (hlen : star ≤ as.length) :
    (P.projection a k hlen).tags = P.tags ++ [.markedStar k] := by
  simp only [NativeResourceMonomial.projection,NativeResourceMonomial.tags,
    List.map_append,List.map_map,List.map_singleton,nativeResourceLiftFactor,Function.comp_def]

@[simp] theorem NativeResourceMonomial.switch_tags {i star U : ℕ} {T : ClockTree S as}
    (P : NativeResourceMonomial i star T) (a : ℝ) (k : ℕ) (c : T.Slot)
    (hstar : star < U) (hhigh : U ≤ T.splitIndex P.test.target c) :
    (P.switch a k c hstar hhigh).tags = P.tags ++ [.markedStar k] := by
  simp only [NativeResourceMonomial.switch,NativeResourceMonomial.tags,
    List.map_append,List.map_map,List.map_singleton,nativeResourceLiftFactor,Function.comp_def]

@[simp] theorem NativeResourceMonomial.switchFreshHigh_tags {i star : ℕ} {T : ClockTree S as}
    (P : NativeResourceMonomial i star T) (a : ℝ) (k j U : ℕ)
    (hjU : U ≤ j) (hj : j ≤ as.length) (hstar : star < U) :
    (P.switchFreshHigh a k j U hjU hj hstar).tags = P.tags ++ [.markedStar k] := by
  have hh : U ≤ (nativeFreshAtSlot T a P.test.target j).tree.splitIndex
      (P.retainOnFresh a j).test.target (nativeFreshAtSlot T a P.test.target j).mark := by
    change U ≤ (nativeFreshAtSlot T a P.test.target j).tree.splitIndex
      ((nativeFreshAtSlot T a P.test.target j).embed P.test.target)
      (nativeFreshAtSlot T a P.test.target j).mark
    rw [nativeResourceFreshHighGeometry T a P.test.target j hj]
    exact hjU
  exact ((P.retainOnFresh a j).switch_tags a k
    (nativeFreshAtSlot T a P.test.target j).mark hstar hh).trans
      (congrArg (fun rs => rs ++ [.markedStar k]) (P.retainOnFresh_tags a j))

structure NativeFrozenResource (S : Type*) (as : List PositiveMass) (i star : ℕ) where
  tree : ClockTree S as
  monomial : NativeResourceMonomial i star tree

structure NativeResourceTerm (i star : ℕ) (T : ClockTree S as) where
  live : NativeResourceMonomial i star T
  frozen : List (NativeFrozenResource S as i star)
  coefficient : ℝ

def NativeResourceTerm.ofLive {i star : ℕ} {T : ClockTree S as}
    (P : NativeResourceMonomial i star T) : NativeResourceTerm i star T := ⟨P,[],1⟩

def NativeResourceTerm.freeze {i star : ℕ} {T : ClockTree S as}
    (P : NativeResourceTerm i star T) : NativeResourceTerm i star T :=
  ⟨P.live.constant,P.frozen ++ [⟨T,P.live⟩],-P.coefficient⟩

def NativeResourceTerm.centered {i star : ℕ} {T : ClockTree S as}
    (P : NativeResourceTerm i star T) : List (NativeResourceTerm i star T) := [P,P.freeze]

def NativeResourceTerm.reweight {i star : ℕ} {T : ClockTree S as}
    (P : NativeResourceTerm i star T) (c : ℝ) : NativeResourceTerm i star T :=
  ⟨P.live,P.frozen,c*P.coefficient⟩

def NativeResourceTerm.retarget {i star : ℕ} {T : ClockTree S as}
    (P : NativeResourceTerm i star T) (a : ℝ) :
    NativeResourceTerm i star (nativeFreshAtSlot T a P.live.test.target star).tree :=
  ⟨P.live.retarget a,P.frozen,P.coefficient⟩

def NativeResourceTerm.projection {i star : ℕ} {T : ClockTree S as}
    (P : NativeResourceTerm i star T) (a : ℝ) (k : ℕ) (hlen : star ≤ as.length) :
    NativeResourceTerm i star (nativeFreshAtSlot T a P.live.test.target star).tree :=
  ⟨P.live.projection a k hlen,P.frozen,P.coefficient⟩

def NativeResourceTerm.switch {i star U : ℕ} {T : ClockTree S as}
    (P : NativeResourceTerm i star T) (a : ℝ) (k : ℕ) (c : T.Slot)
    (hstar : star < U) (hhigh : U ≤ T.splitIndex P.live.test.target c) :
    NativeResourceTerm i star (nativeFreshAtSlot T a P.live.test.target star).tree :=
  ⟨P.live.switch a k c hstar hhigh,P.frozen,P.coefficient⟩

def NativeResourceTerm.switchFreshHigh {i star : ℕ} {T : ClockTree S as}
    (P : NativeResourceTerm i star T) (a : ℝ) (k j U : ℕ)
    (hjU : U ≤ j) (hj : j ≤ as.length) (hstar : star < U) :
    NativeResourceTerm i star
      (nativeFreshAtSlot (nativeFreshAtSlot T a P.live.test.target j).tree a
        ((nativeFreshAtSlot T a P.live.test.target j).embed P.live.test.target) star).tree :=
  ⟨P.live.switchFreshHigh a k j U hjU hj hstar,P.frozen,P.coefficient⟩

def NativeResourceTerm.resources {i star : ℕ} {T : ClockTree S as}
    (P : NativeResourceTerm i star T) : List NativeResourceMark :=
  P.frozen.flatMap (fun F => F.monomial.tags) ++ P.live.tags

@[simp] theorem NativeResourceTerm.freeze_resources {i star : ℕ} {T : ClockTree S as}
    (P : NativeResourceTerm i star T) : P.freeze.resources = P.resources := by
  simp [NativeResourceTerm.freeze,NativeResourceTerm.resources]

@[simp] theorem NativeResourceTerm.reweight_resources {i star : ℕ} {T : ClockTree S as}
    (P : NativeResourceTerm i star T) (c : ℝ) :
    (P.reweight c).resources = P.resources := rfl

@[simp] theorem NativeResourceTerm.retarget_resources {i star : ℕ} {T : ClockTree S as}
    (P : NativeResourceTerm i star T) (a : ℝ) :
    (P.retarget a).resources = P.resources := by
  simp only [NativeResourceTerm.retarget,NativeResourceTerm.resources,
    NativeResourceMonomial.retarget_tags]

@[simp] theorem NativeResourceTerm.projection_resources {i star : ℕ} {T : ClockTree S as}
    (P : NativeResourceTerm i star T) (a : ℝ) (k : ℕ) (hlen : star ≤ as.length) :
    (P.projection a k hlen).resources = P.resources ++ [.markedStar k] := by
  simp only [NativeResourceTerm.projection,NativeResourceTerm.resources,
    NativeResourceMonomial.projection_tags,List.append_assoc]

@[simp] theorem NativeResourceTerm.switch_resources {i star U : ℕ} {T : ClockTree S as}
    (P : NativeResourceTerm i star T) (a : ℝ) (k : ℕ) (c : T.Slot)
    (hstar : star < U) (hhigh : U ≤ T.splitIndex P.live.test.target c) :
    (P.switch a k c hstar hhigh).resources = P.resources ++ [.markedStar k] := by
  simp only [NativeResourceTerm.switch,NativeResourceTerm.resources,
    NativeResourceMonomial.switch_tags,List.append_assoc]

@[simp] theorem NativeResourceTerm.switchFreshHigh_resources {i star : ℕ} {T : ClockTree S as}
    (P : NativeResourceTerm i star T) (a : ℝ) (k j U : ℕ)
    (hjU : U ≤ j) (hj : j ≤ as.length) (hstar : star < U) :
    (P.switchFreshHigh a k j U hjU hj hstar).resources = P.resources ++ [.markedStar k] := by
  simp only [NativeResourceTerm.switchFreshHigh,NativeResourceTerm.resources,
    NativeResourceMonomial.switchFreshHigh_tags,List.append_assoc]

variable {ι : Type*} [Fintype ι] [Fintype S] [Nonempty S]

def NativeFrozenResource.mean {i star : ℕ} (F : NativeFrozenResource S as i star)
    (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ]ℝ) (v : ι → ℝ)
    (q : ℕ → ι → ℝ) (R : S → S → ℝ) (C : ℕ → ℝ) (x : ι → ℝ) : ℝ :=
  F.tree.disorderExpect w φ v q (F.monomial.test.value R C) x

def NativeResourceTerm.scalar {i star : ℕ} {T : ClockTree S as}
    (P : NativeResourceTerm i star T) (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ]ℝ) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (R : S → S → ℝ) (C : ℕ → ℝ) (x : ι → ℝ) : ℝ :=
  P.coefficient*(P.frozen.map (fun F => F.mean w φ v q R C x)).prod

def NativeResourceTerm.value {i star : ℕ} {T : ClockTree S as}
    (P : NativeResourceTerm i star T) (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ]ℝ) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (R : S → S → ℝ) (C : ℕ → ℝ) (x : ι → ℝ) (σ : T.Assignment) : ℝ :=
  P.scalar w φ v q R C x*P.live.test.value R C σ

omit [Nonempty S] in
theorem NativeResourceTerm.retarget_value {i star : ℕ} {T : ClockTree S as}
    (P : NativeResourceTerm i star T) (a : ℝ) (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ]ℝ) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (R : S → S → ℝ) (C : ℕ → ℝ) (x : ι → ℝ)
    (σ : (nativeFreshAtSlot T a P.live.test.target star).tree.Assignment) :
    (P.retarget a).value w φ v q R C x σ =
      P.value w φ v q R C x
        ((nativeFreshAtSlot T a P.live.test.target star).restrict σ) := by
  change P.scalar w φ v q R C x*(P.live.test.retarget a star).value R C σ = _
  rw [P.live.test.retarget_value]
  rfl

theorem NativeResourceTerm.retarget_disorder_marginal [Nonempty ι]
    {i star : ℕ} {T : ClockTree S as}
    (P : NativeResourceTerm i star T) {w : S → ℝ} (hw : ∀ σ,0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ]ℝ) (ho : MassOrdered 0 as)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (R : S → S → ℝ)
    (C : ℕ → ℝ) (x : ι → ℝ) :
    (nativeFreshAtSlot T 0 P.live.test.target star).tree.disorderExpect w φ v q
      ((P.retarget 0).value w φ v q R C x) x =
        T.disorderExpect w φ v q (P.value w φ v q R C x) x := by
  have he : (P.retarget 0).value w φ v q R C x =
      fun σ => P.value w φ v q R C x
        ((nativeFreshAtSlot T 0 P.live.test.target star).restrict σ) :=
    funext (fun σ => P.retarget_value 0 w φ v q R C x σ)
  rw [he]
  exact nativeFreshAtSlot_old_disorder_marginal hw φ T ho P.live.test.target star
    v q (P.value w φ v q R C x) x

theorem NativeResourceTerm.freeze_value {i star : ℕ} {T : ClockTree S as}
    (P : NativeResourceTerm i star T) {w : S → ℝ} (hw : ∀ σ,0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ]ℝ) (ho : MassOrdered 0 as)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (R : S → S → ℝ)
    (C : ℕ → ℝ) (x : ι → ℝ) (σ : T.Assignment) :
    P.freeze.value w φ v q R C x σ =
      -T.disorderExpect w φ v q (P.value w φ v q R C x) x := by
  rw [show P.value w φ v q R C x =
      (fun τ => P.scalar w φ v q R C x*P.live.test.value R C τ) from rfl,
    T.disorderExpect_const_mul hw φ ho]
  simp only [NativeResourceTerm.freeze,NativeResourceTerm.value,
    NativeResourceTerm.scalar,List.map_append,List.prod_append,List.map_singleton,
    List.prod_singleton,NativeFrozenResource.mean,NativeResourceMonomial.constant,
    NativeGeneratedTest.constant_value]
  ring

theorem NativeResourceTerm.centered_value {i star : ℕ} {T : ClockTree S as}
    (P : NativeResourceTerm i star T) {w : S → ℝ} (hw : ∀ σ,0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ]ℝ) (ho : MassOrdered 0 as)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (R : S → S → ℝ)
    (C : ℕ → ℝ) (x : ι → ℝ) (σ : T.Assignment) :
    (P.centered.map (fun t => t.value w φ v q R C x σ)).sum =
      P.value w φ v q R C x σ-
        T.disorderExpect w φ v q (P.value w φ v q R C x) x := by
  simp only [NativeResourceTerm.centered,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,add_zero,P.freeze_value hw φ ho v q R C x σ,
    sub_eq_add_neg]

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type*} {as : List PositiveMass}

inductive NativeResourceGenerated (i star : ℕ) :
    List NativeResourceMark → ℕ → {as : List PositiveMass} →
      (T : ClockTree S as) → NativeResourceTerm i star T → Prop
  | constant {as : List PositiveMass} (T : ClockTree S as) (s : T.Slot) :
      NativeResourceGenerated i star [] 0 T
        (.ofLive (nativeResourceConstant T s i star))
  | seed {as : List PositiveMass} (T : ClockTree S as) (a : ℝ) (s : T.Slot) (mark : NativeResourceMark)
      (hmark : mark = .initial ∨ mark = .oldStar) (hlen : mark.cut i star ≤ as.length) :
      NativeResourceGenerated i star [mark] 0
        (nativeFreshAtSlot T a s (mark.cut i star)).tree
        (.ofLive (nativeResourceSeed T a s i star mark hmark hlen))
  | freeze {as : List PositiveMass} {seed : List NativeResourceMark} {k : ℕ} {T : ClockTree S as}
      {P : NativeResourceTerm i star T} (h : NativeResourceGenerated i star seed k T P) :
      NativeResourceGenerated i star seed k T P.freeze
  | reweight {as : List PositiveMass} {seed : List NativeResourceMark} {k : ℕ} {T : ClockTree S as}
      {P : NativeResourceTerm i star T} (h : NativeResourceGenerated i star seed k T P)
      (c : ℝ) : NativeResourceGenerated i star seed k T (P.reweight c)
  | retarget {as : List PositiveMass} {seed : List NativeResourceMark} {k : ℕ} {T : ClockTree S as}
      {P : NativeResourceTerm i star T} (h : NativeResourceGenerated i star seed k T P)
      (a : ℝ) : NativeResourceGenerated i star seed k
        (nativeFreshAtSlot T a P.live.test.target star).tree (P.retarget a)
  | projection {as : List PositiveMass} {seed : List NativeResourceMark} {k : ℕ} {T : ClockTree S as}
      {P : NativeResourceTerm i star T} (h : NativeResourceGenerated i star seed k T P)
      (a : ℝ) (hlen : star ≤ as.length) : NativeResourceGenerated i star seed (k+1)
        (nativeFreshAtSlot T a P.live.test.target star).tree (P.projection a k hlen)
  | switch {as : List PositiveMass} {seed : List NativeResourceMark} {k U : ℕ} {T : ClockTree S as}
      {P : NativeResourceTerm i star T} (h : NativeResourceGenerated i star seed k T P)
      (a : ℝ) (c : T.Slot) (hstar : star < U)
      (hhigh : U ≤ T.splitIndex P.live.test.target c) :
      NativeResourceGenerated i star seed (k+1)
        (nativeFreshAtSlot T a P.live.test.target star).tree (P.switch a k c hstar hhigh)
  | switchFreshHigh {as : List PositiveMass} {seed : List NativeResourceMark} {k : ℕ}
      {T : ClockTree S as} {P : NativeResourceTerm i star T}
      (h : NativeResourceGenerated i star seed k T P) (a : ℝ) (j U : ℕ)
      (hjU : U ≤ j) (hj : j ≤ as.length) (hstar : star < U) :
      NativeResourceGenerated i star seed (k+1)
        (nativeFreshAtSlot (nativeFreshAtSlot T a P.live.test.target j).tree a
          ((nativeFreshAtSlot T a P.live.test.target j).embed P.live.test.target) star).tree
        (P.switchFreshHigh a k j U hjU hj hstar)

theorem NativeResourceGenerated.resource_word {i star : ℕ} {seed : List NativeResourceMark}
    {k : ℕ} {T : ClockTree S as} {P : NativeResourceTerm i star T}
    (h : NativeResourceGenerated i star seed k T P) :
    P.resources = seed ++ (List.range k).map NativeResourceMark.markedStar := by
  induction h with
  | constant T s =>
    simp [NativeResourceTerm.ofLive,NativeResourceTerm.resources,
      nativeResourceConstant,NativeResourceMonomial.tags]
  | seed T a s mark hmark hlen =>
    simp [NativeResourceTerm.ofLive,NativeResourceTerm.resources,
      nativeResourceSeed,NativeResourceMonomial.tags]
  | freeze _ ih => simpa only [NativeResourceTerm.freeze_resources] using ih
  | reweight _ c ih => simpa only [NativeResourceTerm.reweight_resources] using ih
  | retarget _ a ih => simpa only [NativeResourceTerm.retarget_resources] using ih
  | projection _ a hlen ih =>
    rw [NativeResourceTerm.projection_resources,ih]
    simp only [List.range_succ,List.map_append,List.map_singleton,List.append_assoc]
  | switch _ a c hstar hhigh ih =>
    rw [NativeResourceTerm.switch_resources,ih]
    simp only [List.range_succ,List.map_append,List.map_singleton,List.append_assoc]
  | switchFreshHigh _ a j U hjU hj hstar ih =>
    rw [NativeResourceTerm.switchFreshHigh_resources,ih]
    simp only [List.range_succ,List.map_append,List.map_singleton,List.append_assoc]

theorem NativeResourceGenerated.centered_generated {i star : ℕ}
    {seed : List NativeResourceMark} {k : ℕ} {T : ClockTree S as}
    {P : NativeResourceTerm i star T} (h : NativeResourceGenerated i star seed k T P)
    (Q : NativeResourceTerm i star T) (hQ : Q ∈ P.centered) :
    NativeResourceGenerated i star seed k T Q := by
  simp only [NativeResourceTerm.centered,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl
  · exact h
  · exact h.freeze

def NativeResourceMark.initialWeight : NativeResourceMark → ℕ
  | .initial => 1
  | _ => 0

def NativeResourceMark.markedWeight : NativeResourceMark → ℕ
  | .markedStar _ => 1
  | _ => 0

def nativeInitialResourceCount (rs : List NativeResourceMark) : ℕ :=
  (rs.map NativeResourceMark.initialWeight).sum

def nativeMarkedResourceCount (rs : List NativeResourceMark) : ℕ :=
  (rs.map NativeResourceMark.markedWeight).sum

theorem nativeMarkedResourceCount_range (k : ℕ) :
    nativeMarkedResourceCount ((List.range k).map NativeResourceMark.markedStar) = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [List.range_succ,List.map_append,List.map_singleton,
      nativeMarkedResourceCount,List.sum_append,List.map_map,Function.comp_def,
      List.sum_singleton,NativeResourceMark.markedWeight] at *
    omega

theorem NativeResourceGenerated.seed_counts {i star : ℕ} {seed : List NativeResourceMark}
    {k : ℕ} {T : ClockTree S as} {P : NativeResourceTerm i star T}
    (h : NativeResourceGenerated i star seed k T P) :
    nativeInitialResourceCount seed ≤ 1 ∧ nativeMarkedResourceCount seed = 0 := by
  induction h with
  | constant T s => simp [nativeInitialResourceCount,nativeMarkedResourceCount]
  | seed T a s mark hmark hlen =>
    rcases hmark with rfl | rfl <;>
      simp [nativeInitialResourceCount,nativeMarkedResourceCount,
        NativeResourceMark.initialWeight,NativeResourceMark.markedWeight]
  | freeze _ ih => exact ih
  | reweight _ c ih => exact ih
  | retarget _ a ih => exact ih
  | projection _ a hlen ih => exact ih
  | switch _ a c hstar hhigh ih => exact ih
  | switchFreshHigh _ a j U hjU hj hstar ih => exact ih

theorem NativeResourceGenerated.at_most_one_initial_across_expectations
    {i star : ℕ} {seed : List NativeResourceMark} {k : ℕ} {T : ClockTree S as}
    {P : NativeResourceTerm i star T} (h : NativeResourceGenerated i star seed k T P) :
    nativeInitialResourceCount P.resources ≤ 1 := by
  rw [h.resource_word]
  simpa [nativeInitialResourceCount,List.map_append,List.sum_append,List.map_map,
    Function.comp_def,NativeResourceMark.initialWeight] using h.seed_counts.1

theorem NativeResourceGenerated.exact_marked_depth {i star : ℕ}
    {seed : List NativeResourceMark} {k : ℕ} {T : ClockTree S as}
    {P : NativeResourceTerm i star T} (h : NativeResourceGenerated i star seed k T P) :
    nativeMarkedResourceCount P.resources = k := by
  rw [h.resource_word]
  simp only [nativeMarkedResourceCount,List.map_append,List.sum_append]
  change nativeMarkedResourceCount seed +
    nativeMarkedResourceCount ((List.range k).map NativeResourceMark.markedStar) = k
  rw [h.seed_counts.2,nativeMarkedResourceCount_range,zero_add]

theorem NativeResourceGenerated.total_factor_depth {i star : ℕ}
    {seed : List NativeResourceMark} {k : ℕ} {T : ClockTree S as}
    {P : NativeResourceTerm i star T} (h : NativeResourceGenerated i star seed k T P) :
    P.resources.length = seed.length+k := by
  rw [h.resource_word]
  simp only [List.length_append,List.length_map,List.length_range]

def NativeResourceMark.savedScale (x W ε : ℝ) : NativeResourceMark → ℝ
  | .initial => x
  | .oldStar => W
  | .markedStar _ => ε*W

def nativeResourceScale (x W ε : ℝ) (rs : List NativeResourceMark) : ℝ :=
  (rs.map (NativeResourceMark.savedScale x W ε)).prod

theorem nativeResourceScale_marked_range (x W ε : ℝ) (k : ℕ) :
    nativeResourceScale x W ε ((List.range k).map NativeResourceMark.markedStar) =
      (ε*W)^k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [List.range_succ,List.map_append,List.map_singleton,nativeResourceScale,
      List.prod_append,List.map_map,Function.comp_def,List.prod_singleton,
      NativeResourceMark.savedScale] at *
    rw [ih,pow_succ]

theorem NativeResourceGenerated.saved_scale {i star : ℕ} {seed : List NativeResourceMark}
    {k : ℕ} {T : ClockTree S as} {P : NativeResourceTerm i star T}
    (h : NativeResourceGenerated i star seed k T P) (x W ε : ℝ) :
    nativeResourceScale x W ε P.resources = nativeResourceScale x W ε seed*(ε*W)^k := by
  rw [h.resource_word]
  simp only [nativeResourceScale,List.map_append,List.prod_append]
  rw [show ((((List.range k).map NativeResourceMark.markedStar).map
    (NativeResourceMark.savedScale x W ε)).prod) = (ε*W)^k from
      nativeResourceScale_marked_range x W ε k]

theorem NativeResourceGenerated.normalized_saved_scale {i star : ℕ}
    {seed : List NativeResourceMark} {k : ℕ} {T : ClockTree S as}
    {P : NativeResourceTerm i star T} (h : NativeResourceGenerated i star seed k T P)
    (x W ε : ℝ) (hW : W ≠ 0) :
    (W⁻¹)^k*nativeResourceScale x W ε P.resources =
      nativeResourceScale x W ε seed*ε^k := by
  rw [h.saved_scale x W ε]
  calc
    _ = nativeResourceScale x W ε seed*ε^k*((W⁻¹)^k*W^k) := by
      rw [mul_pow]
      ring
    _ = _ := by rw [←mul_pow,inv_mul_cancel₀ hW,one_pow,mul_one]

end OAI.SKFluctuations.Hierarchy.ClockTree
