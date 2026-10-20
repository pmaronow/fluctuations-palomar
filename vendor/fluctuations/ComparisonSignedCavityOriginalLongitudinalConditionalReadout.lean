module

public import ComparisonSignedCavityOriginalLongitudinalWordDiagram
public import ComparisonSignedCavityFullStarFieldFreshDisorderFold
public import ComparisonSignedCavityGWordConditionalSum
public import ComparisonSignedCavityActualAuxiliaryGammaTransport

@[expose] public section

noncomputable section
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
open scoped NNReal

def nativeOriginalConditionalLongitudinalDiagramValue {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (star U : ℕ) (K b C : ℕ→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (A : (Spin n×Bool)→(Spin n×Bool)→ℝ) (D : NativeObservedDiagram T) : ℝ :=
  match D.marks with
  | [f,e,c]=>nativeStarFieldDisorderMean (fullWeight n) (fullFeature n) D.tree (D.embed s) star v q
      (fun y σ=>nativeOriginalHighGAtom D.tree U K b C (D.embed s) c e f σ*
        nativeStarPairFactor (fullWeight n) (fullFeature n) as star
          (cumulativeIncrements (q 0) (fun j=>q (j+1))) A y (T.atSlot (D.read σ) s)) x
  | _=>0

def nativeOriginalConditionalLongitudinalPair {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (star U : ℕ) (K b C : ℕ→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (A : (Spin n×Bool)→(Spin n×Bool)→ℝ) : ℝ :=
  nativeObservedHighWordSum (NativeObservedDiagram.identity T) s star 3
    (nativeOriginalConditionalLongitudinalDiagramValue T s star U K b C v q x A)

theorem native_original_longitudinal_pair_diagram_fresh_eq_conditional
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (s : T.Slot) (star U : ℕ) (hstar : star ≤ as.length)
    (K b C : ℕ→ℝ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (A : (Spin n×Bool)→(Spin n×Bool)→ℝ)
    (D : NativeObservedDiagram T) (f e c : D.tree.Slot) (hm : D.marks=[f,e,c]) :
    nativeOriginalLongitudinalPairDiagramValue T s U K b C v q x A (D.fresh s star 0)=
      nativeOriginalConditionalLongitudinalDiagramValue T s star U K b C v q x A D := by
  let g:=nativeFreshAtSlot D.tree 0 (D.embed s) star
  have HR : nativeOriginalLongitudinalPairDiagramValue T s U K b C v q x A (D.fresh s star 0)=
      g.tree.disorderExpect (fullWeight n) (fullFeature n) v q
        (fun σ=>nativeOriginalHighGAtom D.tree U K b C (D.embed s) c e f (g.restrict σ)*
          A (T.atSlot (D.read (g.restrict σ)) s) (g.spin σ)) x := by
    simp only [nativeOriginalLongitudinalPairDiagramValue,NativeObservedDiagram.fresh,hm,
      List.map_cons,List.map_nil,List.nil_append,List.cons_append]
    apply congrArg (fun J=>g.tree.disorderExpect (fullWeight n) (fullFeature n) v q J x)
    funext σ
    rw [native_original_G_atom_marked_readout D.tree ho U K b C (D.embed s) c e f g
      (nativeFreshAtSlot_mem D.tree 0 (D.embed s) star)]
    rw [g.spin_at]
    ring
  rw [HR]
  simpa only [nativeOriginalConditionalLongitudinalDiagramValue,hm] using
    native_full_fresh_disorder_selector_factor D.tree (D.embed s) star hstar 0
      (fullWeight_pos n) (fullFeature n) ho v q
      (nativeOriginalHighGAtom D.tree U K b C (D.embed s) c e f)
      (fun σ=>T.atSlot (D.read σ) s) A x

theorem native_original_longitudinal_pair_eq_conditional_insertion
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (s : T.Slot) (star U : ℕ)
    (hs : star < U) (hU : U ≤ as.length) (K b C : ℕ→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (A : (Spin n×Bool)→(Spin n×Bool)→ℝ) :
    let g:=nativeFreshAtSlot T 0 s star
    nativeOriginalLongitudinalPairing n v q x U K b C g.tree
      (fun σ=>A (T.atSlot (g.restrict σ) s) (g.spin σ)) (g.embed s)=
      nativeOriginalConditionalLongitudinalPair T s star U K b C v q x A := by
  dsimp only
  rw [native_original_longitudinal_pair_eq_word_before_fresh T ho s star U hs hU]
  unfold nativeOriginalConditionalLongitudinalPair nativeObservedHighWordSum
  apply congrArg List.sum
  apply List.map_congr_left
  intro z hz
  apply congrArg (fun t=>z.1*t)
  have HL : z.2.marks.length=3:=by
    simpa only [NativeObservedDiagram.identity,List.length_nil,Nat.add_zero] using
      native_observed_high_words_marks_length (NativeObservedDiagram.identity T) s star 3 z hz
  obtain ⟨f,e,c,hm⟩ : ∃f e c,z.2.marks=[f,e,c]:=by
    cases hm : z.2.marks with
    | nil=>simp only [hm,List.length_nil] at HL;omega
    | cons f es=>
      cases es with
      | nil=>simp only [hm,List.length_cons,List.length_nil] at HL;omega
      | cons e cs=>
        cases cs with
        | nil=>simp only [hm,List.length_cons,List.length_nil] at HL;omega
        | cons c ds=>
          cases ds with
          | nil=>exact ⟨f,e,c,rfl⟩
          | cons d tail=>simp only [hm,List.length_cons] at HL;omega
  exact native_original_longitudinal_pair_diagram_fresh_eq_conditional T ho s star U
    (hs.le.trans hU) K b C v q x A z.2 f e c hm

end OAI.SKFluctuations.Cavity
