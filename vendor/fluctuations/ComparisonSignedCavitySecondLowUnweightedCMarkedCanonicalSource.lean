module

public import ComparisonSignedCavitySecondLowUnweightedCForestSource
public import ComparisonSignedCavitySecondLowUnweightedCCanonicalSource

@[expose] public section

noncomputable section
set_option maxHeartbeats 5000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal ENNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

 theorem native_unweighted_c_canonical_row_eq_LOW
    (n U : ℕ) {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (f c : T.Slot) (hlow : T.splitIndex f c<U) (τ : T.cavityLeft.Assignment) :
    ActualNaturalBoundaryShape.canonicalLowRestFactor M f c τ=
      restLowKernel n U (fun j=>(M.bf (partitionPoint 0 as j):ℝ))
        (fun j=>(M.hf (partitionPoint 0 as j):ℝ)) (T.splitIndex f c)
        (T.cavityLeft.atSlot τ (T.cavityLeftSlot f)) (T.cavityLeft.atSlot τ (T.cavityLeftSlot c)) := by
  simp only [ActualNaturalBoundaryShape.canonicalLowRestFactor,fullBoundaryAffineFactor,
    restLowKernel,hlow,ite_true,deletedOverlap,joinSpin,Fin.lastCases_castSucc]
  congr 3
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

 theorem native_second_low_unweighted_c_complete_marked_canonical_source
    (n U : ℕ) {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (hU : U≤as.length) (f c z : T.Slot)
    (Hfc : T.splitIndex f c<U) (Hcz : T.splitIndex c z<U)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {a : ℕ} (G : ActualNaturalBoundaryShape n a T) (forms : Fin a→NativeSourceFactorForm)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (hh : U≤p.tree.splitIndex (p.embed c) p.mark) (K : ℕ→ℝ)
    (τ : p.tree.cavityLeft.Assignment) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let Hf:=native_second_low_high_c_preserves_LOW T U c f p hp hh Hfc
    let Hz:=native_second_low_high_c_preserves_LOW T U c z p hp hh (by rwa [T.splitIndex_symm])
    let hfn:=native_second_low_low_slots_ne p.tree U hU (p.embed f) p.mark (Hf.trans_lt Hfc)
    let hzn:=native_second_low_low_slots_ne p.tree U hU (p.embed z) p.mark
      (Hz.trans_lt (by rwa [T.splitIndex_symm]))
    let hfo:=fun H=>native_second_low_low_slots_ne T U hU f c Hfc ((T.markedAttach_embed_preserves 0 p hp).1 H)
    let hzo:=fun H=>native_second_low_low_slots_ne T U hU z c (by rwa [T.splitIndex_symm])
      ((T.markedAttach_embed_preserves 0 p hp).1 H)
    let GN:=G.retainOnMarked 0 p hp
    nativeSecondLowUnweightedCPayload n U b h K T f c z (G.canonicalMinimumSource M forms).restProduct p τ-
      nativeSecondLowUnweightedCOldPayload n U b h K T f c z (G.canonicalMinimumSource M forms).restProduct (p.restRestrict τ)=
      ((GN.consTwoLowC (p.embed f) p.mark (p.embed z) hfn hzn).canonicalMinimumSource M
        (ActualNaturalBoundaryShape.twoLowCForms forms)).restProduct τ-
      ((GN.consTwoLowC (p.embed f) (p.embed c) (p.embed z) hfo hzo).canonicalMinimumSource M
        (ActualNaturalBoundaryShape.twoLowCForms forms)).restProduct τ := by
  dsimp only
  have Hf:=native_second_low_high_c_preserves_LOW T U c f p hp hh Hfc
  have Hz:=native_second_low_high_c_preserves_LOW T U c z p hp hh (by rwa [T.splitIndex_symm])
  rw [(G.retainOnMarked 0 p hp).consTwoLowC_complete_old_difference M forms]
  rw [G.retained_canonical_restProduct M forms 0 p hp]
  rw [native_unweighted_c_canonical_row_eq_LOW n U p.tree M (p.embed f) p.mark (Hf.trans_lt Hfc),
    native_unweighted_c_canonical_row_eq_LOW n U p.tree M (p.embed z) p.mark
      (Hz.trans_lt (by rwa [T.splitIndex_symm])),
    native_unweighted_c_canonical_row_eq_LOW n U p.tree M (p.embed f) (p.embed c)
      (by rw [(T.markedAttach_embed_preserves 0 p hp).2];exact Hfc),
    native_unweighted_c_canonical_row_eq_LOW n U p.tree M (p.embed z) (p.embed c)
      (by rw [(T.markedAttach_embed_preserves 0 p hp).2,T.splitIndex_symm];exact Hcz)]
  simp only [Hf,Hz,(T.markedAttach_embed_preserves 0 p hp).2,T.splitIndex_symm z c,
    ←p.restRestrict_at]
  unfold nativeSecondLowUnweightedCPayload nativeSecondLowUnweightedCOldPayload
  have Hsymm (σ τ : Spin n) :
      restLowKernel n U (fun j=>(M.bf (partitionPoint 0 as j):ℝ))
        (fun j=>(M.hf (partitionPoint 0 as j):ℝ)) (T.splitIndex c z) σ τ=
      restLowKernel n U (fun j=>(M.bf (partitionPoint 0 as j):ℝ))
        (fun j=>(M.hf (partitionPoint 0 as j):ℝ)) (T.splitIndex c z) τ σ:=by
    simp only [restLowKernel,mul_comm]
  simp only [MarkedPlacement.restSpin]
  rw [Hsymm (T.cavityLeft.atSlot (p.restRestrict τ) (T.cavityLeftSlot z))
      (p.tree.cavityLeft.atSlot τ (p.tree.cavityLeftSlot p.mark)),
    Hsymm (T.cavityLeft.atSlot (p.restRestrict τ) (T.cavityLeftSlot z))
      (T.cavityLeft.atSlot (p.restRestrict τ) (T.cavityLeftSlot c))]
  ring

end OAI.SKFluctuations.Cavity
