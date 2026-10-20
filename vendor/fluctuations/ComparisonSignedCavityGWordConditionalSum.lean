module

public import ComparisonSignedCavityGWordConditionalFold
public import ComparisonSignedCavityDecoupledGSpineWord

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
namespace OAI.SKFluctuations.Hierarchy.ClockTree

theorem native_observed_high_words_marks_length {S : Type} {as : List PositiveMass}
    {T : ClockTree S as} (D : NativeObservedDiagram T) (s : T.Slot) (star k : ℕ)
    (z : ℝ×NativeObservedDiagram T) (hz : z∈nativeObservedHighWords D s star k) :
    z.2.marks.length=k+D.marks.length := by
  induction k generalizing D z with
  | zero=>
    simp only [nativeObservedHighWords,List.mem_singleton] at hz
    subst z
    simp only [Nat.zero_add]
  | succ k ih=>
    simp only [nativeObservedHighWords,List.mem_flatMap,List.mem_map] at hz
    obtain ⟨w,hw,v,hv,rfl⟩:=hz
    have H:=ih w.2 v hv
    obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hw
    simpa only [NativeObservedDiagram.observe,List.length_cons,List.length_map,Nat.add_assoc,
      Nat.add_comm,Nat.add_left_comm] using H

end OAI.SKFluctuations.Hierarchy.ClockTree
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree

theorem native_decoupled_G_spine_resampling_eq_conditional_word
    {n : ℕ} {as : List PositiveMass} {B T : ClockTree (Spin n×Bool) as}
    {base : NativeGeneratedTest B} {P : NativeGeneratedTest T} {star : ℕ}
    (spine : NativeProjectionSpine base star P) (ho : MassOrdered 0 as)
    (U : ℕ) (hs : star < U) (hU : U ≤ as.length)
    (q : ℕ→RestCoordinate n→ℝ) (b h K C : ℕ→ℝ) (hKC : ∀j,K j=h j+b j*C j)
    (A R : Spin n→Spin n→ℝ) :
    nativeActualOriginalGProjectedResampling T P.target star U K b C 0
      (cutFullVariance n q U 0 0 b h K) 0 (fun u v=>A u.1 v.1)
      (P.value (fun u v=>R u.1 v.1) C)=
      nativeObservedHighWordSum (NativeObservedDiagram.identity B) base.target star 3
        (fun D=>nativeObservedGScalar (spine.graftDiagram D) base.target U K*
          nativeStarFieldDisorderMean (restWeight n) (restFeature n) D.tree.cavityLeft
            (D.tree.cavityLeftSlot (D.embed base.target)) star 0 q
            (nativeGWordProjectedPayload B base D star U spine.toothCount q b h K C A R) 0) := by
  rw [native_decoupled_G_spine_resampling_eq_rest_word spine ho U hs hU q b h K C hKC]
  unfold nativeObservedHighWordSum
  apply congrArg List.sum
  apply List.map_congr_left
  intro z hz
  apply congrArg (fun v=>z.1*v)
  apply native_rest_G_spine_word_conditional_fold spine z.2
    (by simpa only [NativeObservedDiagram.identity,List.length_nil,Nat.add_zero] using
      native_observed_high_words_marks_length (NativeObservedDiagram.identity B) base.target star 3 z hz)
    ho U (hs.le.trans hU)

end OAI.SKFluctuations.Cavity
