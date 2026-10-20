module

public import ComparisonSignedCavityGWordSupport

@[expose] public section

noncomputable section
set_option maxHeartbeats 22000000
set_option backward.isDefEq.respectTransparency false
open Classical
namespace OAI.SKFluctuations.Hierarchy.ClockTree

theorem native_three_mark_G_support_iff {S : Type} {as : List PositiveMass}
    {T : ClockTree S as} (s : T.Slot) (U : ℕ)
    (p : MarkedPlacement T) (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
    (z : MarkedPlacement r.tree) (hz : z∈r.tree.markedAttach 0) :
    nativeObservedGSupport ((((NativeObservedDiagram.identity T).observe p).observe r).observe z) s U ↔
      U≤p.tree.splitIndex (p.embed s) p.mark ∧
      U≤r.tree.splitIndex (r.embed (p.embed s)) r.mark ∧
      U≤z.tree.splitIndex (z.embed (r.embed (p.embed s))) z.mark ∧
      z.embed r.mark≠z.mark ∧ p.embed s≠p.mark := by
  simp only [nativeObservedGSupport,NativeObservedDiagram.observe,NativeObservedDiagram.identity,
    id_eq,List.map_cons,List.map_nil,ne_eq,
    (r.tree.markedAttach_embed_preserves 0 z hz).2,
    (p.tree.markedAttach_embed_preserves 0 r hr).2,
    (r.tree.markedAttach_embed_preserves 0 z hz).1.eq_iff,
    (p.tree.markedAttach_embed_preserves 0 r hr).1.eq_iff]

end OAI.SKFluctuations.Hierarchy.ClockTree
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree

theorem native_G_spine_word_zero_of_not_support
    {n : ℕ} {as : List PositiveMass} {B T : ClockTree (Spin n×Bool) as}
    {base : NativeGeneratedTest B} {P : NativeGeneratedTest T} {star : ℕ}
    (spine : NativeProjectionSpine base star P) (D : NativeObservedDiagram B)
    (ho : MassOrdered 0 as) (U : ℕ) (hU : U≤as.length) (hk : 3≤D.marks.length)
    (q : ℕ→RestCoordinate n→ℝ) (b h K C : ℕ→ℝ) (A R : Spin n→Spin n→ℝ)
    (hs : ¬nativeObservedGSupport D base.target U) :
    nativeObservedGScalar (spine.graftDiagram D) base.target U K*
      nativeStarFieldDisorderMean (restWeight n) (restFeature n) D.tree.cavityLeft
        (D.tree.cavityLeftSlot (D.embed base.target)) star 0 q
        (nativeGWordProjectedPayload B base D star U spine.toothCount q b h K C A R) 0=0 := by
  by_cases hE : U≤nativeObservedErrorIndex D
  · rw [native_observed_G_scalar_zero_of_not_support (spine.graftDiagram D) ho base.target U K hU
      (by rw [spine.graft_marks_length_all];omega)
      (by rw [spine.graft_error_index D (by omega)];exact hE)
      (by rw [spine.graft_G_support D hk];exact hs),zero_mul]
  · have Hpayload : nativeGWordProjectedPayload B base D star U spine.toothCount q b h K C A R=
        fun _ _=>0 := by
      funext y σ
      simp only [nativeGWordProjectedPayload,nativeGWordOldPayload,nativeGWordNewPayload,
        nativeGWordError,restHighKernel,lt_of_not_ge hE,ite_true,mul_zero,zero_mul,sub_self]
    rw [Hpayload]
    have Hzero:=native_star_field_disorder_mean_const_mul D.tree.cavityLeft
      (D.tree.cavityLeftSlot (D.embed base.target)) star (restWeight n) (restFeature n) 0 q
      0 (fun _ _=>0) 0
    simp only [zero_mul] at Hzero
    rw [Hzero,mul_zero]

theorem native_actual_triple_spine_G_value_zero_of_not_support
    {n : ℕ} {pre mid tail : List PositiveMass}
    {B T : ClockTree (Spin n×Bool) (pre++(mid++tail))}
    {base : NativeGeneratedTest B} {P : NativeGeneratedTest T}
    (spine : NativeProjectionSpine base (pre.length+mid.length) P)
    {m delta cl cu Az C0 Ct D₀ Bclock : ℝ}
    (M : LaplaceWindowFormalization.NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D₀ Bclock)
    (ho : MassOrdered 0 (pre++(mid++tail))) (U : ℕ) (hU : U≤(pre++(mid++tail)).length)
    (p : MarkedPlacement B) (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
    (z : MarkedPlacement r.tree) (hz : z∈r.tree.markedAttach 0) (q : ℕ→RestCoordinate n→ℝ)
    (hs : ¬(U≤p.tree.splitIndex (p.embed base.target) p.mark ∧
      U≤r.tree.splitIndex (r.embed (p.embed base.target)) r.mark ∧
      U≤z.tree.splitIndex (z.embed (r.embed (p.embed base.target))) z.mark ∧
      z.embed r.mark≠z.mark ∧ p.embed base.target≠p.mark)) :
    nativeActualTripleSpineGValue spine M U p r z q=0 := by
  apply native_G_spine_word_zero_of_not_support spine _ ho U hU (by
    simp only [NativeObservedDiagram.observe,NativeObservedDiagram.identity,
      List.length_cons,List.length_map,List.length_nil];omega)
  rwa [native_three_mark_G_support_iff base.target U p r hr z hz]

end OAI.SKFluctuations.Cavity
