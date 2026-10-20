module

public import ComparisonSignedCavityCanonicalOldLowMoment
public import ComparisonSignedCavityCanonicalMarkedOldProduct
public import ComparisonSignedCavityOriginalFreshAffineIdentity
public import ComparisonSignedCavityActualFreshAffineRow
public import ComparisonSignedCavityOriginalAffineObservedRow
public import ComparisonSignedCavitySecondLowInheritedFreshAffineSource
public import ComparisonSignedCavitySecondLowFreshResidualAffineJoin
public import ComparisonActualHighOnlyOriginalTargetB0

@[expose] public section
noncomputable section
set_option maxHeartbeats 80000000
set_option linter.unusedVariables false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal ENNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization ActualHighOnlyOverlapMinimum
attribute [local instance] Classical.propDecidable
attribute [local instance] nativeSecondLowSlotFintype
namespace ActualNaturalBoundaryShape
variable {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
def canonicalLowRestFactor_high_only {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (i j : T.Slot) (σ : T.cavityLeft.Assignment) : ℝ :=
  let u:=partitionPoint 0 as (T.splitIndex i j)
  fullBoundaryAffineFactor n (M.hf u) (M.bf u)
    (T.cavityLeft.atSlot σ (T.cavityLeftSlot j),false)
    (T.cavityLeft.atSlot σ (T.cavityLeftSlot i),false)

theorem canonical_cons_restProduct_high_only {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNaturalBoundaryShape n a T) (f : Fin a→NativeSourceFactorForm)
    (i j : T.Slot) (hij : i≠j) (σ : T.cavityLeft.Assignment) :
    ((G.consLowShape i j hij).canonicalHighOnlySource M (Fin.cases .row f)).restProduct σ=
      canonicalLowRestFactor_high_only M i j σ*(G.canonicalHighOnlySource M f).restProduct σ := by
  unfold restProduct
  rw [Fin.prod_univ_succ]
  rfl

end ActualNaturalBoundaryShape

def nativeOriginalFreshAffineResidual_high_only (n : ℕ) {as : List PositiveMass}
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (T : ClockTree (Spin n×Bool) as) (s e b : T.Slot) (star : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (Z : T.cavityLeft.Assignment→ℝ) : ℝ :=
  let g:=nativeFreshAtSlot T 0 b star
  g.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
    (fun σ=>Z (g.restRestrict σ)*
      (ActualNaturalBoundaryShape.canonicalLowRestFactor_high_only M g.mark (g.embed s) σ-
        ActualNaturalBoundaryShape.canonicalLowRestFactor_high_only M g.mark (g.embed e) σ)) 0

theorem canonical_low_rest_factor_eq_restLowKernel_high_only (n : ℕ) {as : List PositiveMass}
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (T : ClockTree (Spin n×Bool) as) (U : ℕ) (i j : T.Slot)
    (hlow : T.splitIndex i j < U) (σ : T.cavityLeft.Assignment) :
    ActualNaturalBoundaryShape.canonicalLowRestFactor_high_only M i j σ=
      restLowKernel n U (fun l=>(M.bf (partitionPoint 0 as l):ℝ))
        (fun l=>(M.hf (partitionPoint 0 as l):ℝ)) (T.splitIndex i j)
        (T.cavityLeft.atSlot σ (T.cavityLeftSlot j)) (T.cavityLeft.atSlot σ (T.cavityLeftSlot i)) := by
  simp [ActualNaturalBoundaryShape.canonicalLowRestFactor_high_only,restLowKernel,hlow,
    fullBoundaryAffineFactor,deletedOverlap,joinSpin]

def nativeCanonicalObservedFreshAffineHighRow_high_only (n a : ℕ) {as : List PositiveMass}
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (T : ClockTree (Spin n×Bool) as) (star U : ℕ) (c b fslot : T.Slot) (useNew : Bool)
    (G : ActualNaturalBoundaryShape n a T) (forms : Fin a→NativeSourceFactorForm)
    (q : ℕ→RestCoordinate n→ℝ) (K : ℕ→ℝ) : ℝ :=
  ((T.markedAttach 0).map fun p=>p.coeff*
    (if U≤p.tree.splitIndex (p.embed c) p.mark then
      fullScalarCutGamma p.tree U K (p.embed c) p.mark*
        nativeOriginalFreshAffineResidual_high_only n M p.tree (p.embed c) p.mark (p.embed b) star q
          (fun σ=>ActualNaturalBoundaryShape.canonicalLowRestFactor_high_only M
            (nativeObservedRemainingTarget c p useNew) (p.embed fslot) σ*
            (G.canonicalHighOnlySource M forms).restProduct (p.restRestrict σ)) else 0)).sum

def nativeCanonicalObservedFreshAffineRow_high_only (n a : ℕ) {as : List PositiveMass}
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (T : ClockTree (Spin n×Bool) as) (star U : ℕ) (c b fslot : T.Slot) (useNew : Bool)
    (G : ActualNaturalBoundaryShape n a T) (forms : Fin a→NativeSourceFactorForm)
    (q : ℕ→RestCoordinate n→ℝ) (K : ℕ→ℝ) : ℝ :=
  ((T.markedAttach 0).map fun p=>p.coeff*
    (fullScalarCutGamma p.tree U K (p.embed c) p.mark*
      nativeOriginalFreshAffineResidual_high_only n M p.tree (p.embed c) p.mark (p.embed b) star q
        (fun σ=>ActualNaturalBoundaryShape.canonicalLowRestFactor_high_only M
          (nativeObservedRemainingTarget c p useNew) (p.embed fslot) σ*
          (G.canonicalHighOnlySource M forms).restProduct (p.restRestrict σ)))).sum

theorem native_canonical_observed_fresh_affine_row_eq_high_high_only
    (n a : ℕ) {as : List PositiveMass} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as) (star U : ℕ) (hU : U≤as.length)
    (c b fslot : T.Slot) (useNew : Bool)
    (G : ActualNaturalBoundaryShape n a T) (forms : Fin a→NativeSourceFactorForm)
    (q : ℕ→RestCoordinate n→ℝ) (K : ℕ→ℝ) :
    nativeCanonicalObservedFreshAffineRow_high_only n a M T star U c b fslot useNew G forms q K=
      nativeCanonicalObservedFreshAffineHighRow_high_only n a M T star U c b fslot useNew G forms q K := by
  unfold nativeCanonicalObservedFreshAffineRow_high_only nativeCanonicalObservedFreshAffineHighRow_high_only
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  by_cases hhigh : U≤p.tree.splitIndex (p.embed c) p.mark
  · simp only [hhigh,↓reduceIte]
  · have hzero:=fullScalarCutGamma_cross_zero p.tree ho U K (p.embed c) p.mark hU (by omega)
    simp only [hhigh,↓reduceIte,hzero,zero_mul,mul_zero]

def nativeSecondLowCanonicalObservedFreshLowDifferenceAtom_high_only
    (n a : ℕ) {as : List PositiveMass} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (T : ClockTree (Spin n×Bool) as) (star U : ℕ) (c bslot fslot : T.Slot)
    (G : ActualNaturalBoundaryShape n a T) (forms : Fin a→NativeSourceFactorForm)
    (q : ℕ→RestCoordinate n→ℝ) (p : MarkedPlacement T) : ℝ :=
  let g:=nativeFreshAtSlot p.tree 0 (p.embed bslot) star
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  g.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
    (fun τ=>(G.canonicalHighOnlySource M forms).restProduct (p.restRestrict (g.restRestrict τ))*
      restLowKernel n U b h (p.tree.splitIndex (p.embed c) (p.embed fslot))
        (p.tree.cavityLeft.atSlot (g.restRestrict τ) (p.tree.cavityLeftSlot (p.embed fslot)))
        (p.tree.cavityLeft.atSlot (g.restRestrict τ) (p.tree.cavityLeftSlot (p.embed c)))*
      (restLowKernel n U b h (g.tree.splitIndex g.mark (g.embed p.mark))
          (p.restSpin (g.restRestrict τ)) (g.restSpin τ)-
        restLowKernel n U b h (g.tree.splitIndex g.mark (g.embed (p.embed c)))
          (p.tree.cavityLeft.atSlot (g.restRestrict τ) (p.tree.cavityLeftSlot (p.embed c))) (g.restSpin τ))) 0

def nativeSecondLowCanonicalObservedFreshLowDifferenceRow_high_only
    (n a : ℕ) {as : List PositiveMass} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (T : ClockTree (Spin n×Bool) as) (star U : ℕ) (c bslot fslot : T.Slot)
    (G : ActualNaturalBoundaryShape n a T) (forms : Fin a→NativeSourceFactorForm)
    (q : ℕ→RestCoordinate n→ℝ) (K : ℕ→ℝ) : ℝ :=
  ((T.markedAttach 0).map (fun p=>p.coeff*fullScalarCutGamma p.tree U K (p.embed c) p.mark*
    nativeSecondLowCanonicalObservedFreshLowDifferenceAtom_high_only n a M T star U c bslot fslot G forms q p)).sum

private theorem low_b0_second_low_fresh_expect_neg (n : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n) as) (q : ℕ→RestCoordinate n→ℝ) (F : T.Assignment→ℝ) :
    T.disorderExpect (restWeight n) (restFeature n) 0 q (fun τ=>-F τ) 0=
      -T.disorderExpect (restWeight n) (restFeature n) 0 q F 0 := by
  unfold ClockTree.disorderExpect
  simp only [mul_neg,Finset.sum_neg_distrib]

theorem native_second_low_canonical_observed_fresh_low_difference_atom_eq_negative_affine_high_only
    (n a : ℕ) {as : List PositiveMass} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (T : ClockTree (Spin n×Bool) as) (star U : ℕ) (c bslot fslot : T.Slot)
    (hstar : star<U) (Hcf : T.splitIndex c fslot<U)
    (G : ActualNaturalBoundaryShape n a T) (forms : Fin a→NativeSourceFactorForm)
    (q : ℕ→RestCoordinate n→ℝ) (p : MarkedPlacement T) (hp : p∈T.markedAttach 0) :
    nativeSecondLowCanonicalObservedFreshLowDifferenceAtom_high_only n a M T star U c bslot fslot G forms q p=
      -nativeOriginalFreshAffineResidual_high_only n M p.tree (p.embed c) p.mark (p.embed bslot) star q
        (fun σ=>ActualNaturalBoundaryShape.canonicalLowRestFactor_high_only M (p.embed c) (p.embed fslot) σ*
          (G.canonicalHighOnlySource M forms).restProduct (p.restRestrict σ)) := by
  let g:=nativeFreshAtSlot p.tree 0 (p.embed bslot) star
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  have Hcfp : p.tree.splitIndex (p.embed c) (p.embed fslot)<U:=by
    rw [(T.markedAttach_embed_preserves 0 p hp).2]
    exact Hcf
  have Hgc : g.tree.splitIndex g.mark (g.embed (p.embed c))<U:=
    nativeFreshAtSlot_outside_old_blocks p.tree 0 (p.embed bslot) hstar (p.embed c)
  have Hge : g.tree.splitIndex g.mark (g.embed p.mark)<U:=
    nativeFreshAtSlot_outside_old_blocks p.tree 0 (p.embed bslot) hstar p.mark
  unfold nativeSecondLowCanonicalObservedFreshLowDifferenceAtom_high_only nativeOriginalFreshAffineResidual_high_only
  dsimp only
  rw [←low_b0_second_low_fresh_expect_neg]
  congr 1
  funext τ
  rw [canonical_low_rest_factor_eq_restLowKernel_high_only n M p.tree U (p.embed c) (p.embed fslot) Hcfp,
    canonical_low_rest_factor_eq_restLowKernel_high_only n M g.tree U g.mark (g.embed (p.embed c)) Hgc,
    canonical_low_rest_factor_eq_restLowKernel_high_only n M g.tree U g.mark (g.embed p.mark) Hge]
  simp only [←g.restRestrict_at,MarkedPlacement.restSpin]
  ring

private theorem low_b0_second_low_fresh_sum_neg {α : Type} (L : List α) (F : α→ℝ) :
    (L.map (fun x=>-F x)).sum=-(L.map F).sum := by
  induction L with
  | nil=>simp
  | cons x L ih=>simp only [List.map_cons,List.sum_cons,ih,neg_add]

theorem native_second_low_canonical_observed_fresh_low_difference_eq_negative_affine_row_high_only
    (n a : ℕ) {as : List PositiveMass} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (T : ClockTree (Spin n×Bool) as) (star U : ℕ) (c bslot fslot : T.Slot)
    (hstar : star<U) (Hcf : T.splitIndex c fslot<U)
    (G : ActualNaturalBoundaryShape n a T) (forms : Fin a→NativeSourceFactorForm)
    (q : ℕ→RestCoordinate n→ℝ) (K : ℕ→ℝ) :
    nativeSecondLowCanonicalObservedFreshLowDifferenceRow_high_only n a M T star U c bslot fslot G forms q K=
      -nativeCanonicalObservedFreshAffineRow_high_only n a M T star U c bslot fslot false G forms q K := by
  unfold nativeSecondLowCanonicalObservedFreshLowDifferenceRow_high_only nativeCanonicalObservedFreshAffineRow_high_only
  rw [←low_b0_second_low_fresh_sum_neg]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  rw [native_second_low_canonical_observed_fresh_low_difference_atom_eq_negative_affine_high_only n a M T
    star U c bslot fslot hstar Hcf G forms q p hp]
  simp only [nativeObservedRemainingTarget,Bool.false_eq_true,ite_false]
  ring

theorem native_second_low_old_three_fresh_value_eq_complete_atom_high_only
    (n degree : ℕ) {as : List PositiveMass} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as) (star U : ℕ)
    (a z : T.Slot) (G : ActualNaturalBoundaryShape n degree T)
    (forms : Fin degree→NativeSourceFactorForm) (q : ℕ→RestCoordinate n→ℝ) (K : ℕ→ℝ)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
    (e : MarkedPlacement r.tree) (he : e∈r.tree.markedAttach 0) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    nativeSecondLowObservedFreshDiagramResidualValue n q U b h K
      (G.canonicalHighOnlySource M forms).restProduct a
      (nativeSecondLowOldThreeFreshObservedDiagram T z star p r e)=
      fullScalarCutGamma p.tree U K (p.embed a) p.mark*
        fullScalarCutGamma e.tree U K (e.embed r.mark) e.mark*
        nativeSecondLowCanonicalObservedFreshLowDifferenceAtom_high_only n degree M r.tree star U
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
  rw [HR,((G.retainOnMarked 0 p hp).retained_canonical_restProduct_high_only M forms 0 r hr),
    G.retained_canonical_restProduct_high_only M forms 0 p hp]
  rw [(nativeFreshAtSlot_old_splits e.tree 0 (e.embed (r.embed (p.embed z))) star).2,
    e.tree.splitIndex_symm]
  simp only [MarkedPlacement.restSpin,
    ←(nativeFreshAtSlot e.tree 0 (e.embed (r.embed (p.embed z))) star).restRestrict_at,
    ←e.restRestrict_at,(nativeFreshAtSlot e.tree 0 (e.embed (r.embed (p.embed z))) star).tree.splitIndex_symm]

def nativeSecondLowCanonicalRetainedFreshLowDifferenceHighSource_high_only
    (n degree : ℕ) {as : List PositiveMass} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (T : ClockTree (Spin n×Bool) as) (star U : ℕ) (a v z : T.Slot)
    (G : ActualNaturalBoundaryShape n degree T) (forms : Fin degree→NativeSourceFactorForm)
    (q : ℕ→RestCoordinate n→ℝ) (K : ℕ→ℝ) : ℝ :=
  ((nativeHighMarkedRows T a (U-1) 0).attach.map (fun p=>p.val.coeff*
    fullScalarCutGamma p.val.tree U K (p.val.embed a) p.val.mark*
    ((nativeHighMarkedRows p.val.tree (p.val.embed v) (U-1) 0).attach.map (fun r=>r.val.coeff*
      nativeSecondLowCanonicalObservedFreshLowDifferenceRow_high_only n degree M r.val.tree star U
        r.val.mark (r.val.embed (p.val.embed z)) (r.val.embed p.val.mark)
        ((G.retainOnMarked 0 p.val ((mem_nativeHighMarkedRows T a (U-1) 0 p.val).mp p.property).1).retainOnMarked
          0 r.val ((mem_nativeHighMarkedRows p.val.tree (p.val.embed v) (U-1) 0 r.val).mp r.property).1)
        forms q K)).sum)).sum

theorem native_second_low_commuted_word_eq_retained_fresh_low_difference_source_high_only
    (n degree : ℕ) {as : List PositiveMass} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as) (star U : ℕ)
    (hU0 : 0<U) (hU : U≤as.length) (a v z : T.Slot)
    (G : ActualNaturalBoundaryShape n degree T) (forms : Fin degree→NativeSourceFactorForm)
    (q : ℕ→RestCoordinate n→ℝ) (K : ℕ→ℝ) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    ((nativeSecondLowObservedHighWord (NativeObservedDiagram.identity T) (U-1) [a,v,v]).map
      (fun w=>w.1*nativeSecondLowObservedFreshDiagramResidualValue n q U b h K
        (G.canonicalHighOnlySource M forms).restProduct a (w.2.fresh z star 0))).sum=
      nativeSecondLowCanonicalRetainedFreshLowDifferenceHighSource_high_only n degree M T star U a v z G forms q K := by
  dsimp only
  have Hmiddle (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
      (r : MarkedPlacement p.tree) (hr : r∈nativeHighMarkedRows p.tree (p.embed v) (U-1) 0) :
      ((nativeHighMarkedRows r.tree (r.embed (p.embed v)) (U-1) 0).map (fun e=>e.coeff*
        nativeSecondLowObservedFreshDiagramResidualValue n q U
          (fun j=>(M.bf (partitionPoint 0 as j):ℝ)) (fun j=>(M.hf (partitionPoint 0 as j):ℝ)) K
          (G.canonicalHighOnlySource M forms).restProduct a
          (nativeSecondLowOldThreeFreshObservedDiagram T z star p r e))).sum=
        fullScalarCutGamma p.tree U K (p.embed a) p.mark*
          nativeSecondLowCanonicalObservedFreshLowDifferenceRow_high_only n degree M r.tree star U
            r.mark (r.embed (p.embed z)) (r.embed p.mark)
            ((G.retainOnMarked 0 p hp).retainOnMarked 0 r
              ((mem_nativeHighMarkedRows p.tree (p.embed v) (U-1) 0 r).mp hr).1) forms q K := by
    obtain ⟨hr',Hr⟩:=(mem_nativeHighMarkedRows p.tree (p.embed v) (U-1) 0 r).mp hr
    have HrU : U ≤ r.tree.splitIndex (r.embed (p.embed v)) r.mark:=by omega
    have Hsame:=native_second_low_high_rows_eq_of_same_cut r.tree U hU0 hU (r.embed (p.embed v)) r.mark HrU
    have Hrow : nativeSecondLowCanonicalObservedFreshLowDifferenceRow_high_only n degree M r.tree star U
        r.mark (r.embed (p.embed z)) (r.embed p.mark) ((G.retainOnMarked 0 p hp).retainOnMarked 0 r hr') forms q K=
      ((nativeHighMarkedRows r.tree r.mark (U-1) 0).map (fun e=>e.coeff*fullScalarCutGamma e.tree U K
        (e.embed r.mark) e.mark*nativeSecondLowCanonicalObservedFreshLowDifferenceAtom_high_only n degree M r.tree star U
          r.mark (r.embed (p.embed z)) (r.embed p.mark) ((G.retainOnMarked 0 p hp).retainOnMarked 0 r hr') forms q e)).sum := by
      unfold nativeSecondLowCanonicalObservedFreshLowDifferenceRow_high_only
      symm
      apply native_high_row_sum_eq_full_of_support
      intro e _ he
      rw [fullScalarCutGamma_cross_zero e.tree ho U K (e.embed r.mark) e.mark hU (by omega)]
      ring
    rw [Hrow,←Hsame,←List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro e he
    rw [native_second_low_old_three_fresh_value_eq_complete_atom_high_only n degree M T ho star U a z G forms q K
      p hp r hr' e ((mem_nativeHighMarkedRows r.tree (r.embed (p.embed v)) (U-1) 0 e).mp he).1]
    ring
  rw [native_second_low_observed_high_word_eval_fold (NativeObservedDiagram.identity T) (U-1)
    (fun E=>nativeSecondLowObservedFreshDiagramResidualValue n q U
      (fun j=>(M.bf (partitionPoint 0 as j):ℝ)) (fun j=>(M.hf (partitionPoint 0 as j):ℝ)) K
      (G.canonicalHighOnlySource M forms).restProduct a (E.fresh z star 0)) [a,v,v]]
  change ((nativeHighMarkedRows T a (U-1) 0).map (fun p=>p.coeff*
    ((nativeHighMarkedRows p.tree (p.embed v) (U-1) 0).map (fun r=>r.coeff*
      ((nativeHighMarkedRows r.tree (r.embed (p.embed v)) (U-1) 0).map (fun e=>e.coeff*
        nativeSecondLowObservedFreshDiagramResidualValue n q U
          (fun j=>(M.bf (partitionPoint 0 as j):ℝ)) (fun j=>(M.hf (partitionPoint 0 as j):ℝ)) K
          (G.canonicalHighOnlySource M forms).restProduct a
          (nativeSecondLowOldThreeFreshObservedDiagram T z star p r e))).sum)).sum)).sum=_
  unfold nativeSecondLowCanonicalRetainedFreshLowDifferenceHighSource_high_only
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

theorem native_second_low_actual_canonical_fresh_residual_eq_retained_low_difference_source_high_only
    (n degree : ℕ) {as : List PositiveMass} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as) (star U : ℕ)
    (hstar : star<U) (hU : U≤as.length) (a v z : T.Slot)
    (G : ActualNaturalBoundaryShape n degree T) (forms : Fin degree→NativeSourceFactorForm)
    (q : ℕ→RestCoordinate n→ℝ) (K : ℕ→ℝ) :
    let g:=nativeFreshAtSlot T 0 z star
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    nativeSecondLowCanonicalObservedResidualSource n q U b h K g.tree
      (fun old=>(G.canonicalHighOnlySource M forms).restProduct (g.restRestrict old))
      (g.embed a) (g.embed v) g.mark=
        nativeSecondLowCanonicalRetainedFreshLowDifferenceHighSource_high_only n degree M T star U a v z G forms q K := by
  dsimp only
  rw [native_second_low_actual_fresh_residual_eq_commuted_observed_word n q U star _ _ K T ho hstar hU
    (G.canonicalHighOnlySource M forms).restProduct a v z]
  exact native_second_low_commuted_word_eq_retained_fresh_low_difference_source_high_only n degree M T ho star U
    (by omega) hU a v z G forms q K

end OAI.SKFluctuations.Cavity
