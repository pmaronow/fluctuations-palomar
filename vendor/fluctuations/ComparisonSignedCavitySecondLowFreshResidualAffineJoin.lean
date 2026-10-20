module

public import ComparisonSignedCavitySecondLowFreshResidualWordSource

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators
set_option maxHeartbeats 40000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

def nativeSecondLowOldThreeFreshObservedDiagram {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (z : T.Slot) (star : ℕ)
    (p : MarkedPlacement T) (r : MarkedPlacement p.tree) (e : MarkedPlacement r.tree) :
    NativeObservedDiagram T :=
  ((((NativeObservedDiagram.identity T).observe p).observe r).observe e).fresh z star 0

theorem native_second_low_old_three_fresh_rest_read {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (z : T.Slot) (star : ℕ)
    (p : MarkedPlacement T) (r : MarkedPlacement p.tree) (e : MarkedPlacement r.tree)
    (τ : (nativeFreshAtSlot e.tree 0 (e.embed (r.embed (p.embed z))) star).tree.cavityLeft.Assignment) :
    (nativeSecondLowOldThreeFreshObservedDiagram T z star p r e).restRead τ=
      p.restRestrict (r.restRestrict (e.restRestrict
        ((nativeFreshAtSlot e.tree 0 (e.embed (r.embed (p.embed z))) star).restRestrict τ))) := by
  apply T.cavityLeft.assignment_ext
  intro c
  obtain ⟨d,rfl⟩:=T.cavityLeftSlot.surjective c
  rw [NativeObservedDiagram.restRead_at,p.restRestrict_at,r.restRestrict_at,e.restRestrict_at,
    (nativeFreshAtSlot e.tree 0 (e.embed (r.embed (p.embed z))) star).restRestrict_at]
  rfl

theorem native_second_low_old_three_fresh_value_eq_complete_atom
    (n degree : ℕ) {as : List PositiveMass} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as) (star U : ℕ)
    (a z : T.Slot) (G : ActualNaturalBoundaryShape n degree T)
    (forms : Fin degree→NativeSourceFactorForm) (q : ℕ→RestCoordinate n→ℝ) (K : ℕ→ℝ)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
    (e : MarkedPlacement r.tree) (he : e∈r.tree.markedAttach 0) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    nativeSecondLowObservedFreshDiagramResidualValue n q U b h K
      (G.canonicalMinimumSource M forms).restProduct a
      (nativeSecondLowOldThreeFreshObservedDiagram T z star p r e)=
      fullScalarCutGamma p.tree U K (p.embed a) p.mark*
        fullScalarCutGamma e.tree U K (e.embed r.mark) e.mark*
        nativeSecondLowCanonicalObservedFreshLowDifferenceAtom n degree M r.tree star U
          r.mark (r.embed (p.embed z)) (r.embed p.mark)
          ((G.retainOnMarked 0 p hp).retainOnMarked 0 r hr) forms q e := by
  dsimp only
  let g:=nativeFreshAtSlot e.tree 0 (e.embed (r.embed (p.embed z))) star
  have HR : (nativeSecondLowOldThreeFreshObservedDiagram T z star p r e).restRead=
      fun τ=>p.restRestrict (r.restRestrict (e.restRestrict (g.restRestrict τ))) := by
    funext τ
    exact native_second_low_old_three_fresh_rest_read T z star p r e τ
  simp only [nativeSecondLowOldThreeFreshObservedDiagram,NativeObservedDiagram.observe,
    NativeObservedDiagram.fresh,NativeObservedDiagram.identity,id_eq,g] at HR
  unfold nativeSecondLowObservedFreshDiagramResidualValue
  simp only [nativeSecondLowOldThreeFreshObservedDiagram,NativeObservedDiagram.observe,
    NativeObservedDiagram.fresh,NativeObservedDiagram.identity,List.map_cons,List.map_nil,
    List.cons_append,List.nil_append,id_eq]
  rw [fullScalarCutGamma_marked_preserves e.tree ho U K _ _ g (nativeFreshAtSlot_mem e.tree 0 _ star),
    fullScalarCutGamma_marked_preserves e.tree ho U K _ _ g (nativeFreshAtSlot_mem e.tree 0 _ star),
    fullScalarCutGamma_double_preserves p.tree ho U K (p.embed a) p.mark r hr e he]
  congr 2
  funext τ
  rw [HR,((G.retainOnMarked 0 p hp).retained_canonical_restProduct M forms 0 r hr),
    G.retained_canonical_restProduct M forms 0 p hp]
  rw [(nativeFreshAtSlot_old_splits e.tree 0 (e.embed (r.embed (p.embed z))) star).2,
    e.tree.splitIndex_symm]
  simp only [MarkedPlacement.restSpin,
    ←(nativeFreshAtSlot e.tree 0 (e.embed (r.embed (p.embed z))) star).restRestrict_at,
    ←e.restRestrict_at,(nativeFreshAtSlot e.tree 0 (e.embed (r.embed (p.embed z))) star).tree.splitIndex_symm]

def nativeSecondLowCanonicalRetainedFreshLowDifferenceHighSource
    (n degree : ℕ) {as : List PositiveMass} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (T : ClockTree (Spin n×Bool) as) (star U : ℕ) (a v z : T.Slot)
    (G : ActualNaturalBoundaryShape n degree T) (forms : Fin degree→NativeSourceFactorForm)
    (q : ℕ→RestCoordinate n→ℝ) (K : ℕ→ℝ) : ℝ :=
  ((nativeHighMarkedRows T a (U-1) 0).attach.map (fun p=>p.val.coeff*
    fullScalarCutGamma p.val.tree U K (p.val.embed a) p.val.mark*
    ((nativeHighMarkedRows p.val.tree (p.val.embed v) (U-1) 0).attach.map (fun r=>r.val.coeff*
      nativeSecondLowCanonicalObservedFreshLowDifferenceRow n degree M r.val.tree star U
        r.val.mark (r.val.embed (p.val.embed z)) (r.val.embed p.val.mark)
        ((G.retainOnMarked 0 p.val ((mem_nativeHighMarkedRows T a (U-1) 0 p.val).mp p.property).1).retainOnMarked
          0 r.val ((mem_nativeHighMarkedRows p.val.tree (p.val.embed v) (U-1) 0 r.val).mp r.property).1)
        forms q K)).sum)).sum

theorem native_second_low_commuted_word_eq_retained_fresh_low_difference_source
    (n degree : ℕ) {as : List PositiveMass} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as) (star U : ℕ)
    (hU0 : 0<U) (hU : U≤as.length) (a v z : T.Slot)
    (G : ActualNaturalBoundaryShape n degree T) (forms : Fin degree→NativeSourceFactorForm)
    (q : ℕ→RestCoordinate n→ℝ) (K : ℕ→ℝ) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    ((nativeSecondLowObservedHighWord (NativeObservedDiagram.identity T) (U-1) [a,v,v]).map
      (fun w=>w.1*nativeSecondLowObservedFreshDiagramResidualValue n q U b h K
        (G.canonicalMinimumSource M forms).restProduct a (w.2.fresh z star 0))).sum=
      nativeSecondLowCanonicalRetainedFreshLowDifferenceHighSource n degree M T star U a v z G forms q K := by
  dsimp only
  have Hmiddle (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
      (r : MarkedPlacement p.tree) (hr : r∈nativeHighMarkedRows p.tree (p.embed v) (U-1) 0) :
      ((nativeHighMarkedRows r.tree (r.embed (p.embed v)) (U-1) 0).map (fun e=>e.coeff*
        nativeSecondLowObservedFreshDiagramResidualValue n q U
          (fun j=>(M.bf (partitionPoint 0 as j):ℝ)) (fun j=>(M.hf (partitionPoint 0 as j):ℝ)) K
          (G.canonicalMinimumSource M forms).restProduct a
          (nativeSecondLowOldThreeFreshObservedDiagram T z star p r e))).sum=
        fullScalarCutGamma p.tree U K (p.embed a) p.mark*
          nativeSecondLowCanonicalObservedFreshLowDifferenceRow n degree M r.tree star U
            r.mark (r.embed (p.embed z)) (r.embed p.mark)
            ((G.retainOnMarked 0 p hp).retainOnMarked 0 r
              ((mem_nativeHighMarkedRows p.tree (p.embed v) (U-1) 0 r).mp hr).1) forms q K := by
    obtain ⟨hr',Hr⟩:=(mem_nativeHighMarkedRows p.tree (p.embed v) (U-1) 0 r).mp hr
    have HrU : U ≤ r.tree.splitIndex (r.embed (p.embed v)) r.mark:=by omega
    have Hsame:=native_second_low_high_rows_eq_of_same_cut r.tree U hU0 hU (r.embed (p.embed v)) r.mark HrU
    have Hrow : nativeSecondLowCanonicalObservedFreshLowDifferenceRow n degree M r.tree star U
        r.mark (r.embed (p.embed z)) (r.embed p.mark) ((G.retainOnMarked 0 p hp).retainOnMarked 0 r hr') forms q K=
      ((nativeHighMarkedRows r.tree r.mark (U-1) 0).map (fun e=>e.coeff*fullScalarCutGamma e.tree U K
        (e.embed r.mark) e.mark*nativeSecondLowCanonicalObservedFreshLowDifferenceAtom n degree M r.tree star U
          r.mark (r.embed (p.embed z)) (r.embed p.mark) ((G.retainOnMarked 0 p hp).retainOnMarked 0 r hr') forms q e)).sum := by
      unfold nativeSecondLowCanonicalObservedFreshLowDifferenceRow
      symm
      apply native_high_row_sum_eq_full_of_support
      intro e _ he
      rw [fullScalarCutGamma_cross_zero e.tree ho U K (e.embed r.mark) e.mark hU (by omega)]
      ring
    rw [Hrow,←Hsame,←List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro e he
    rw [native_second_low_old_three_fresh_value_eq_complete_atom n degree M T ho star U a z G forms q K
      p hp r hr' e ((mem_nativeHighMarkedRows r.tree (r.embed (p.embed v)) (U-1) 0 e).mp he).1]
    ring
  rw [native_second_low_observed_high_word_eval_fold (NativeObservedDiagram.identity T) (U-1)
    (fun E=>nativeSecondLowObservedFreshDiagramResidualValue n q U
      (fun j=>(M.bf (partitionPoint 0 as j):ℝ)) (fun j=>(M.hf (partitionPoint 0 as j):ℝ)) K
      (G.canonicalMinimumSource M forms).restProduct a (E.fresh z star 0)) [a,v,v]]
  change ((nativeHighMarkedRows T a (U-1) 0).map (fun p=>p.coeff*
    ((nativeHighMarkedRows p.tree (p.embed v) (U-1) 0).map (fun r=>r.coeff*
      ((nativeHighMarkedRows r.tree (r.embed (p.embed v)) (U-1) 0).map (fun e=>e.coeff*
        nativeSecondLowObservedFreshDiagramResidualValue n q U
          (fun j=>(M.bf (partitionPoint 0 as j):ℝ)) (fun j=>(M.hf (partitionPoint 0 as j):ℝ)) K
          (G.canonicalMinimumSource M forms).restProduct a
          (nativeSecondLowOldThreeFreshObservedDiagram T z star p r e))).sum)).sum)).sum=_
  unfold nativeSecondLowCanonicalRetainedFreshLowDifferenceHighSource
  conv_lhs=>rw [←List.attach_map_val]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  rw [mul_assoc]
  apply congrArg (fun x : ℝ=>p.val.coeff*x)
  conv_lhs=>rw [←List.attach_map_val]
  conv_rhs=>rw [←List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro r _
  rw [Hmiddle p.val ((mem_nativeHighMarkedRows T a (U-1) 0 p.val).mp p.property).1 r.val r.property]
  ring

theorem native_second_low_actual_canonical_fresh_residual_eq_retained_low_difference_source
    (n degree : ℕ) {as : List PositiveMass} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as) (star U : ℕ)
    (hstar : star<U) (hU : U≤as.length) (a v z : T.Slot)
    (G : ActualNaturalBoundaryShape n degree T) (forms : Fin degree→NativeSourceFactorForm)
    (q : ℕ→RestCoordinate n→ℝ) (K : ℕ→ℝ) :
    let g:=nativeFreshAtSlot T 0 z star
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    nativeSecondLowCanonicalObservedResidualSource n q U b h K g.tree
      (fun old=>(G.canonicalMinimumSource M forms).restProduct (g.restRestrict old))
      (g.embed a) (g.embed v) g.mark=
        nativeSecondLowCanonicalRetainedFreshLowDifferenceHighSource n degree M T star U a v z G forms q K := by
  dsimp only
  rw [native_second_low_actual_fresh_residual_eq_commuted_observed_word n q U star _ _ K T ho hstar hU
    (G.canonicalMinimumSource M forms).restProduct a v z]
  exact native_second_low_commuted_word_eq_retained_fresh_low_difference_source n degree M T ho star U
    (by omega) hU a v z G forms q K

def nativeSecondLowCanonicalRetainedObservedAffineHighSource
    (n degree : ℕ) {as : List PositiveMass} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (T : ClockTree (Spin n×Bool) as) (star U : ℕ) (a v z : T.Slot)
    (G : ActualNaturalBoundaryShape n degree T) (forms : Fin degree→NativeSourceFactorForm)
    (q : ℕ→RestCoordinate n→ℝ) (K : ℕ→ℝ) : ℝ :=
  ((nativeHighMarkedRows T a (U-1) 0).attach.map (fun p=>p.val.coeff*
    fullScalarCutGamma p.val.tree U K (p.val.embed a) p.val.mark*
    ((nativeHighMarkedRows p.val.tree (p.val.embed v) (U-1) 0).attach.map (fun r=>r.val.coeff*
      nativeCanonicalObservedFreshAffineHighRow n degree M r.val.tree star U
        r.val.mark (r.val.embed (p.val.embed z)) (r.val.embed p.val.mark) false
        ((G.retainOnMarked 0 p.val ((mem_nativeHighMarkedRows T a (U-1) 0 p.val).mp p.property).1).retainOnMarked
          0 r.val ((mem_nativeHighMarkedRows p.val.tree (p.val.embed v) (U-1) 0 r.val).mp r.property).1)
        forms q K)).sum)).sum

private theorem second_low_join_sum_neg {α : Type} (L : List α) (F : α→ℝ) :
    (L.map (fun x=>-F x)).sum=-(L.map F).sum := by
  induction L with
  | nil=>simp
  | cons x L ih=>simp only [List.map_cons,List.sum_cons,ih,neg_add]

theorem native_second_low_retained_low_difference_source_eq_negative_affine_high_source
    (n degree : ℕ) {as : List PositiveMass} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as) (star U : ℕ)
    (hstar : star<U) (hU : U≤as.length) (a v z : T.Slot) (Hav : T.splitIndex a v<U)
    (G : ActualNaturalBoundaryShape n degree T) (forms : Fin degree→NativeSourceFactorForm)
    (q : ℕ→RestCoordinate n→ℝ) (K : ℕ→ℝ) :
    nativeSecondLowCanonicalRetainedFreshLowDifferenceHighSource n degree M T star U a v z G forms q K=
      -nativeSecondLowCanonicalRetainedObservedAffineHighSource n degree M T star U a v z G forms q K := by
  have Hrow (p : {p // p∈nativeHighMarkedRows T a (U-1) 0})
      (r : {r // r∈nativeHighMarkedRows p.val.tree (p.val.embed v) (U-1) 0}) :
      nativeSecondLowCanonicalObservedFreshLowDifferenceRow n degree M r.val.tree star U
        r.val.mark (r.val.embed (p.val.embed z)) (r.val.embed p.val.mark)
        ((G.retainOnMarked 0 p.val ((mem_nativeHighMarkedRows T a (U-1) 0 p.val).mp p.property).1).retainOnMarked
          0 r.val ((mem_nativeHighMarkedRows p.val.tree (p.val.embed v) (U-1) 0 r.val).mp r.property).1)
        forms q K=
      -nativeCanonicalObservedFreshAffineHighRow n degree M r.val.tree star U
        r.val.mark (r.val.embed (p.val.embed z)) (r.val.embed p.val.mark) false
        ((G.retainOnMarked 0 p.val ((mem_nativeHighMarkedRows T a (U-1) 0 p.val).mp p.property).1).retainOnMarked
          0 r.val ((mem_nativeHighMarkedRows p.val.tree (p.val.embed v) (U-1) 0 r.val).mp r.property).1)
        forms q K := by
    obtain ⟨hp,Hp⟩:=(mem_nativeHighMarkedRows T a (U-1) 0 p.val).mp p.property
    obtain ⟨hr,Hr⟩:=(mem_nativeHighMarkedRows p.val.tree (p.val.embed v) (U-1) 0 r.val).mp r.property
    have Hpv : p.val.tree.splitIndex p.val.mark (p.val.embed v)=T.splitIndex a v:=by
      rw [p.val.tree.splitIndex_symm]
      exact (native_second_low_high_mark_low_split T U v a p.val hp (by omega)
        (by rw [T.splitIndex_symm];exact Hav)).trans (T.splitIndex_symm _ _)
    have Hcf : r.val.tree.splitIndex r.val.mark (r.val.embed p.val.mark)<U:=by
      rw [r.val.tree.splitIndex_symm,native_second_low_high_mark_low_split p.val.tree U p.val.mark
        (p.val.embed v) r.val hr (by omega) (by rw [Hpv];exact Hav),Hpv]
      exact Hav
    rw [native_second_low_canonical_observed_fresh_low_difference_eq_negative_affine_row n degree M r.val.tree
      star U r.val.mark (r.val.embed (p.val.embed z)) (r.val.embed p.val.mark) hstar Hcf,
      native_canonical_observed_fresh_affine_row_eq_high n degree M r.val.tree ho star U hU]
  unfold nativeSecondLowCanonicalRetainedFreshLowDifferenceHighSource nativeSecondLowCanonicalRetainedObservedAffineHighSource
  simp_rw [Hrow,mul_neg,second_low_join_sum_neg]
  simp_rw [mul_neg,second_low_join_sum_neg]

theorem native_second_low_actual_canonical_fresh_residual_eq_negative_retained_affine_high_source
    (n degree : ℕ) {as : List PositiveMass} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as) (star U : ℕ)
    (hstar : star<U) (hU : U≤as.length) (a v z : T.Slot) (Hav : T.splitIndex a v<U)
    (G : ActualNaturalBoundaryShape n degree T) (forms : Fin degree→NativeSourceFactorForm)
    (q : ℕ→RestCoordinate n→ℝ) (K : ℕ→ℝ) :
    let g:=nativeFreshAtSlot T 0 z star
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    nativeSecondLowCanonicalObservedResidualSource n q U b h K g.tree
      (fun old=>(G.canonicalMinimumSource M forms).restProduct (g.restRestrict old))
      (g.embed a) (g.embed v) g.mark=
        -nativeSecondLowCanonicalRetainedObservedAffineHighSource n degree M T star U a v z G forms q K := by
  dsimp only
  rw [native_second_low_actual_canonical_fresh_residual_eq_retained_low_difference_source n degree M T ho
    star U hstar hU a v z G forms q K]
  exact native_second_low_retained_low_difference_source_eq_negative_affine_high_source n degree M T ho
    star U hstar hU a v z Hav G forms q K

end OAI.SKFluctuations.Cavity
