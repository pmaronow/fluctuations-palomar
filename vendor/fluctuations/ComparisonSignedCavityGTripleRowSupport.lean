module

public import ComparisonSignedCavityGWordSupportValue
public import ComparisonSignedCavityGTripleRowAlgebra
public import ComparisonSignedCavityGWordConditionalSum
public import ComparisonSignedCavityHighRowsSupportReduction

@[expose] public section

noncomputable section
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
open Classical
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type} {as : List PositiveMass}

theorem native_observed_high_word_sum_three (T : ClockTree S as) (s : T.Slot) (star : ℕ)
    (F : NativeObservedDiagram T→ℝ) :
    nativeObservedHighWordSum (NativeObservedDiagram.identity T) s star 3 F=
      ((nativeHighMarkedRows T s star 0).map (fun p=>p.coeff*
        ((nativeHighMarkedRows p.tree (p.embed s) star 0).map (fun r=>r.coeff*
          ((nativeHighMarkedRows r.tree (r.embed (p.embed s)) star 0).map (fun z=>z.coeff*
            F ((((NativeObservedDiagram.identity T).observe p).observe r).observe z))).sum)).sum)).sum := by
  rw [native_observed_high_word_sum_succ]
  simp_rw [native_observed_high_word_sum_succ,native_observed_high_word_sum_zero]
  rfl

theorem native_three_high_nested_full_of_support (T : ClockTree S as) (s : T.Slot) (star : ℕ)
    (F : (p : MarkedPlacement T)→(r : MarkedPlacement p.tree)→MarkedPlacement r.tree→ℝ)
    (hF : ∀p∈T.markedAttach 0,∀r∈p.tree.markedAttach 0,∀z∈r.tree.markedAttach 0,
      ¬(star<p.tree.splitIndex (p.embed s) p.mark ∧
        star<r.tree.splitIndex (r.embed (p.embed s)) r.mark ∧
        star<z.tree.splitIndex (z.embed (r.embed (p.embed s))) z.mark) → F p r z=0) :
    ((nativeHighMarkedRows T s star 0).map (fun p=>p.coeff*
      ((nativeHighMarkedRows p.tree (p.embed s) star 0).map (fun r=>r.coeff*
        ((nativeHighMarkedRows r.tree (r.embed (p.embed s)) star 0).map (fun z=>z.coeff*F p r z)).sum)).sum)).sum=
      ((T.markedAttach 0).map (fun p=>p.coeff*
        ((p.tree.markedAttach 0).map (fun r=>r.coeff*
          ((r.tree.markedAttach 0).map (fun z=>z.coeff*F p r z)).sum)).sum)).sum := by
  have HI (p : MarkedPlacement T) (hp : p∈T.markedAttach 0) :=
    native_two_high_nested_full_of_support p.tree (p.embed s) (p.embed s) star 0 (F p)
      (by intro r hr z hz hlow;exact hF p hp r hr z hz (fun HH=>hlow HH.2.1))
      (by intro r hr z hz hlow;exact hF p hp r hr z hz (fun HH=>hlow HH.2.2))
  calc
    _=((nativeHighMarkedRows T s star 0).map (fun p=>p.coeff*
        ((p.tree.markedAttach 0).map (fun r=>r.coeff*
          ((r.tree.markedAttach 0).map (fun z=>z.coeff*F p r z)).sum)).sum)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro p hp
      rw [HI p ((mem_nativeHighMarkedRows T s star 0 p).mp hp).1]
    _=_:=by
      apply native_high_row_sum_eq_full_of_support
      intro p hp hlow
      have HE : ((p.tree.markedAttach 0).map (fun r=>r.coeff*
          ((r.tree.markedAttach 0).map (fun z=>z.coeff*F p r z)).sum)).sum=0 := by
        apply List.sum_eq_zero
        intro a ha
        obtain ⟨r,hr,rfl⟩:=List.mem_map.mp ha
        have HZ : ((r.tree.markedAttach 0).map (fun z=>z.coeff*F p r z)).sum=0 := by
          apply List.sum_eq_zero
          intro a ha
          obtain ⟨z,hz,rfl⟩:=List.mem_map.mp ha
          rw [hF p hp r hr z hz (fun HH=>hlow HH.1),mul_zero]
        rw [HZ,mul_zero]
      rw [HE,mul_zero]

end OAI.SKFluctuations.Hierarchy.ClockTree
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem native_actual_triple_spine_G_high_sum_eq_row
    {n : ℕ} {pre mid tail : List PositiveMass}
    {B T : ClockTree (Spin n×Bool) (pre++(mid++tail))}
    {base : NativeGeneratedTest B} {P : NativeGeneratedTest T}
    (spine : NativeProjectionSpine base (pre.length+mid.length) P)
    {m delta cl cu Az C0 Ct D₀ Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D₀ Bclock)
    (ho : MassOrdered 0 (pre++(mid++tail))) (U : ℕ)
    (hs : pre.length+mid.length<U) (hU : U≤(pre++(mid++tail)).length)
    (V : ℝ) (hV : V≤M.R (partitionPoint 0 (pre++(mid++tail)) U))
    (q : ℕ→RestCoordinate n→ℝ) :
    ((nativeHighMarkedRows B base.target (pre.length+mid.length) 0).map (fun p=>p.coeff*
      ((nativeHighMarkedRows p.tree (p.embed base.target) (pre.length+mid.length) 0).map (fun r=>r.coeff*
        ((nativeHighMarkedRows r.tree (r.embed (p.embed base.target)) (pre.length+mid.length) 0).map
          (fun z=>z.coeff*nativeActualTripleSpineGValue spine M U p r z q)).sum)).sum)).sum=
      nativeActualTripleSpineGRow spine M U V q := by
  rw [native_three_high_nested_full_of_support B base.target (pre.length+mid.length)
    (fun p r z=>nativeActualTripleSpineGValue spine M U p r z q) (by
      intro p hp r hr z hz hlow
      apply native_actual_triple_spine_G_value_zero_of_not_support spine M ho U hU p r hr z hz q
      intro HH
      exact hlow ⟨hs.trans_le HH.1,hs.trans_le HH.2.1,hs.trans_le HH.2.2.1⟩)]
  unfold nativeActualTripleSpineGRow
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  apply congrArg (fun a=>p.coeff*a)
  apply congrArg List.sum
  apply List.map_congr_left
  intro r hr
  apply congrArg (fun a=>r.coeff*a)
  apply congrArg List.sum
  apply List.map_congr_left
  intro z hz
  apply congrArg (fun a=>z.coeff*a)
  by_cases H : U≤p.tree.splitIndex (p.embed base.target) p.mark ∧
      U≤r.tree.splitIndex (r.embed (p.embed base.target)) r.mark ∧
      U≤z.tree.splitIndex (z.embed (r.embed (p.embed base.target))) z.mark ∧
      z.embed r.mark≠z.mark ∧ p.embed base.target≠p.mark
  · have HR:=comparisonSweepQuantile_monotone M.context.hc M.context.hk M.context.hkc
      M.context.hm M.context.hM M.alpha (partitionPoint_mono _ ho H.1)
    rw [ite_eq_left ⟨H.1,H.2.1,H.2.2.1,H.2.2.2.1,H.2.2.2.2,hV.trans HR⟩]
  · rw [native_actual_triple_spine_G_value_zero_of_not_support spine M ho U hU p r hr z hz q H]
    simp only [ite_self]

end OAI.SKFluctuations.Cavity
