module

public import ComparisonSignedCavityOriginalGWordDiagram
public import ComparisonSignedCavityProjectionSpineFullValue

@[expose] public section

noncomputable section
set_option maxHeartbeats 30000000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree

def nativeOriginalGSpineDiagramValue {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (base : NativeGeneratedTest T)
    (star U : ℕ) (K b C : ℕ→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (A R : (Spin n×Bool)→(Spin n×Bool)→ℝ) (D : NativeObservedDiagram T) : ℝ :=
  match D.marks with
  | f::e::c::rest=>match rest.reverse with
    | t::teeth=>D.tree.disorderExpect (fullWeight n) (fullFeature n) v q
        (fun σ=>(A (D.tree.atSlot σ c) (D.tree.atSlot σ t)-
          A (T.atSlot (D.read σ) base.target) (D.tree.atSlot σ t))*
          (base.value R C (D.read σ)*
            (teeth.map (fun d=>R (T.atSlot (D.read σ) base.target) (D.tree.atSlot σ d)-C star)).prod-
          base.value R C (nativeReplaceAtSlot T base.target (D.read σ) (D.tree.atSlot σ c))*
            (teeth.map (fun d=>R (D.tree.atSlot σ c) (D.tree.atSlot σ d)-C star)).prod)*
          nativeOriginalHighGAtom D.tree U K b C (D.embed base.target) c e f σ) x
    | []=>0
  | _=>0

theorem native_original_G_spine_localized_eq_word
    {n : ℕ} {as : List PositiveMass} {B T : ClockTree (Spin n×Bool) as}
    {base : NativeGeneratedTest B} {P : NativeGeneratedTest T} {star : ℕ}
    (h : NativeProjectionSpine base star P) (U : ℕ) (K b C : ℕ→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (A R : (Spin n×Bool)→(Spin n×Bool)→ℝ) :
    nativeActualOriginalGProjectedLocalizedResampling T P.target star U K b C v q x A (P.value R C)=
      nativeObservedHighWordSum (h.literalDiagram.fresh base.target star 0) base.target star 3
        (nativeOriginalGSpineDiagramValue B base star U K b C v q x A R) := by
  have HD : h.literalDiagram.fresh base.target star 0=
      (show NativeObservedDiagram B from
      { tree:=(nativeFreshAtSlot T 0 P.target star).tree
        embed:=fun d=>(nativeFreshAtSlot T 0 P.target star).embed (h.fullEmbed d)
        marks:=h.toothSlots.map (nativeFreshAtSlot T 0 P.target star).embed++
          [(nativeFreshAtSlot T 0 P.target star).mark]
        read:=fun σ=>h.fullRead ((nativeFreshAtSlot T 0 P.target star).restrict σ) }) :=
    congrArg (fun s : T.Slot => (show NativeObservedDiagram B from
      { tree:=(nativeFreshAtSlot T 0 s star).tree
        embed:=fun d=>(nativeFreshAtSlot T 0 s star).embed (h.fullEmbed d)
        marks:=h.toothSlots.map (nativeFreshAtSlot T 0 s star).embed++
          [(nativeFreshAtSlot T 0 s star).mark]
        read:=fun σ=>h.fullRead ((nativeFreshAtSlot T 0 s star).restrict σ) })) h.fullEmbed_target
  rw [HD]
  unfold nativeActualOriginalGProjectedLocalizedResampling nativeOriginalLocalizedHighPairing
  simp only [native_observed_high_word_sum_succ,native_observed_high_word_sum_zero,
    NativeObservedDiagram.observe,
    h.fullEmbed_target,List.map_append,List.map_cons,List.map_nil,List.map_map,Function.comp_def,
    nativeOriginalGSpineDiagramValue,List.reverse_append,List.reverse_cons,List.reverse_nil,
    List.nil_append,List.cons_append,List.map_reverse,List.prod_reverse]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro r hr
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro z hz
  congr 1
  apply congrArg (fun J=>z.tree.disorderExpect (fullWeight n) (fullFeature n) v q J x)
  funext σ
  rw [h.full_value,h.full_value_replace_target]
  simp only [h.fullRead_target,p.spin_at,p.restrict_at,r.restrict_at,z.restrict_at,
    (nativeFreshAtSlot T 0 P.target star).spin_at,(nativeFreshAtSlot T 0 P.target star).restrict_at]

theorem native_original_G_spine_resampling_eq_reset_word
    {n : ℕ} {as : List PositiveMass} {B T : ClockTree (Spin n×Bool) as}
    {base : NativeGeneratedTest B} {P : NativeGeneratedTest T} {star : ℕ}
    (h : NativeProjectionSpine base star P) (ho : MassOrdered 0 as)
    (U : ℕ) (hs : star < U) (hU : U ≤ as.length) (K b C : ℕ→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (A R : (Spin n×Bool)→(Spin n×Bool)→ℝ) :
    nativeActualOriginalGProjectedResampling T P.target star U K b C v q x A (P.value R C)=
      nativeObservedHighWordSum (NativeObservedDiagram.identity B) base.target star 3
        (fun D=>nativeOriginalGSpineDiagramValue B base star U K b C v q x A R
          ((h.graftDiagram D).fresh base.target star 0)) := by
  rw [native_original_G_projected_resampling_eq_three_high_rows T ho P.target star U hs hU,
    native_original_G_spine_localized_eq_word h,
    native_observed_high_word_sum_fresh 3 _ base.target star (hs.le.trans hU) 0,
    h.high_word_sum_literal]

end OAI.SKFluctuations.Cavity
