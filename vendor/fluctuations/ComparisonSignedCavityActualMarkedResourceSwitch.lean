module

public import ComparisonSignedCavityForestFrozenResourcesLaw
public import ComparisonSignedCavityGeneratedHighVariation

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type} {as : List PositiveMass}

def NativeGeneratedTest.retainOnMarked {T : ClockTree S as}
    (P : NativeGeneratedTest T) (p : MarkedPlacement T) :
    NativeGeneratedTest p.tree :=
  ⟨p.embed P.target,P.exterior.map (fun e => (p.embed e.1,p.embed e.2)),
    P.teeth.map p.embed,P.incoming.map p.embed⟩

theorem NativeGeneratedTest.retainOnMarked_edges {T : ClockTree S as}
    (P : NativeGeneratedTest T) (p : MarkedPlacement T) :
    (P.retainOnMarked p).edges = P.edges.map (fun e =>
      (p.embed e.1,
        p.embed e.2)) := by
  simp only [NativeGeneratedTest.edges,NativeGeneratedTest.retainOnMarked,
    List.map_append,List.map_map,Function.comp_def]

theorem NativeGeneratedTestAncestry.retainOnMarked {T : ClockTree S as}
    {i star : ℕ} {P : NativeGeneratedTest T}
    (hP : NativeGeneratedTestAncestry i star P) (a : ℝ) (p : MarkedPlacement T) (hp : p∈T.markedAttach a) :
    NativeGeneratedTestAncestry i star (P.retainOnMarked p) := by
  have hs := (T.markedAttach_embed_preserves a p hp).2
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
  · simpa only [NativeGeneratedTest.retainOnMarked,List.length_map] using hP.incoming_degree

def nativeResourceMarkedLiftFactor {T : ClockTree S as} (p : MarkedPlacement T)
    (f : NativeResourceFactor T) : NativeResourceFactor p.tree :=
  (f.1,(p.embed f.2.1,p.embed f.2.2))

def NativeResourceMonomial.retainOnMarked {i star : ℕ} {T : ClockTree S as}
    (P : NativeResourceMonomial i star T) (a : ℝ) (p : MarkedPlacement T) (hp : p∈T.markedAttach a) :
    NativeResourceMonomial i star p.tree where
  test := P.test.retainOnMarked p
  factors := P.factors.map (nativeResourceMarkedLiftFactor p)
  realizes := by
    have h := P.realizes.map (fun e =>
      (p.embed e.1,
        p.embed e.2))
    simpa only [NativeGeneratedTest.retainOnMarked_edges,List.map_map,
      nativeResourceMarkedLiftFactor,Function.comp_def] using h
  cuts := by
    intro f hf
    rcases List.mem_map.mp hf with ⟨e,he,rfl⟩
    change p.tree.splitIndex (p.embed e.2.1) (p.embed e.2.2)=e.1.cut i star
    rw [(T.markedAttach_embed_preserves a p hp).2]
    exact P.cuts e he
  ancestry := P.ancestry.retainOnMarked a p hp

def NativeResourceTerm.retainOnMarked {i star : ℕ} {T : ClockTree S as}
    (P : NativeResourceTerm i star T) (a : ℝ) (p : MarkedPlacement T) (hp : p∈T.markedAttach a) :
    NativeResourceTerm i star p.tree :=
  ⟨P.live.retainOnMarked a p hp,P.frozen,P.coefficient⟩

def NativeResourceTerm.markedHighSwitch {i star U : ℕ} {T : ClockTree S as}
    (P : NativeResourceTerm i star T) (a : ℝ) (k : ℕ)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach a)
    (hs : star < U) (hh : U≤p.tree.splitIndex (p.embed P.live.test.target) p.mark) :
    NativeResourceTerm i star (nativeFreshAtSlot p.tree 0 (p.embed P.live.test.target) star).tree :=
  (P.retainOnMarked a p hp).switch 0 k p.mark hs hh

theorem NativeResourceMonomial.retainOnMarked_tags {i star : ℕ} {T : ClockTree S as}
    (P : NativeResourceMonomial i star T) (a : ℝ) (p : MarkedPlacement T) (hp : p∈T.markedAttach a) :
    (P.retainOnMarked a p hp).tags=P.tags := by
  simp only [NativeResourceMonomial.retainOnMarked,NativeResourceMonomial.tags,List.map_map,
    nativeResourceMarkedLiftFactor,Function.comp_def]

theorem NativeResourceTerm.retainOnMarked_resources {i star : ℕ} {T : ClockTree S as}
    (P : NativeResourceTerm i star T) (a : ℝ) (p : MarkedPlacement T) (hp : p∈T.markedAttach a) :
    (P.retainOnMarked a p hp).resources=P.resources := by
  simp only [NativeResourceTerm.retainOnMarked,NativeResourceTerm.resources,
    NativeResourceMonomial.retainOnMarked_tags]

theorem NativeResourceTerm.markedHighSwitch_resources {i star U : ℕ} {T : ClockTree S as}
    (P : NativeResourceTerm i star T) (a : ℝ) (k : ℕ)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach a)
    (hs : star < U) (hh : U≤p.tree.splitIndex (p.embed P.live.test.target) p.mark) :
    (P.markedHighSwitch a k p hp hs hh).resources=P.resources++[.markedStar k] := by
  calc
    _=(P.retainOnMarked a p hp).resources++[.markedStar k]:=
      (P.retainOnMarked a p hp).switch_resources 0 k p.mark hs hh
    _=P.resources++[.markedStar k]:=by rw [P.retainOnMarked_resources a p hp]

theorem NativeGeneratedTest.retainOnMarked_value {T : ClockTree S as}
    (P : NativeGeneratedTest T) (a : ℝ) (p : MarkedPlacement T) (hp : p∈T.markedAttach a)
    (R : S → S → ℝ) (C : ℕ → ℝ) (σ : p.tree.Assignment) :
    (P.retainOnMarked p).value R C σ=P.value R C (p.restrict σ) := by
  unfold NativeGeneratedTest.value
  rw [P.retainOnMarked_edges]
  unfold nativeGeneratedEdgeProduct
  simp only [List.map_map,Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro e he
  rw [(T.markedAttach_embed_preserves a p hp).2,←p.restrict_at,←p.restrict_at]

variable {ι : Type} [Fintype ι] [Fintype S] [Nonempty S]

omit [Nonempty S] in
theorem NativeResourceTerm.retainOnMarked_value {i star : ℕ} {T : ClockTree S as}
    (P : NativeResourceTerm i star T) (a : ℝ) (p : MarkedPlacement T) (hp : p∈T.markedAttach a)
    (w : S → ℝ) (φ : S → (ι → ℝ)→L[ℝ]ℝ) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (R : S → S → ℝ) (C : ℕ → ℝ) (x : ι → ℝ) (σ : p.tree.Assignment) :
    (P.retainOnMarked a p hp).value w φ v q R C x σ=P.value w φ v q R C x (p.restrict σ) := by
  change P.scalar w φ v q R C x*(P.live.test.retainOnMarked p).value R C σ=_
  rw [P.live.test.retainOnMarked_value a p hp]
  rfl

omit [Nonempty S] in
theorem NativeResourceTerm.markedHighSwitch_value {i star U : ℕ} {T : ClockTree S as}
    (P : NativeResourceTerm i star T) (a : ℝ) (k : ℕ)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach a)
    (hs : star < U) (hh : U≤p.tree.splitIndex (p.embed P.live.test.target) p.mark)
    (w : S → ℝ) (φ : S → (ι → ℝ)→L[ℝ]ℝ) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (R : S → S → ℝ) (C : ℕ → ℝ) (x : ι → ℝ)
    (σ : (nativeFreshAtSlot p.tree 0 (p.embed P.live.test.target) star).tree.Assignment) :
    let g:=nativeFreshAtSlot p.tree 0 (p.embed P.live.test.target) star
    (P.markedHighSwitch a k p hp hs hh).value w φ v q R C x σ=
      P.value w φ v q R C x (p.restrict (g.restrict σ))*
        (R (g.spin σ) (p.spin (g.restrict σ))-C star) := by
  dsimp only
  change P.scalar w φ v q R C x*
    ((P.live.test.retainOnMarked p).switchTarget 0 star p.mark).value R C σ=_
  rw [(P.live.test.retainOnMarked p).switchTarget_value 0 p.mark hs hh R C σ,
    P.live.test.retainOnMarked_value a p hp,←p.spin_at]
  dsimp only [NativeGeneratedTest.retainOnMarked]
  change P.scalar w φ v q R C x*(_*_)=(P.scalar w φ v q R C x*_)*_
  ring

end OAI.SKFluctuations.Hierarchy.ClockTree
