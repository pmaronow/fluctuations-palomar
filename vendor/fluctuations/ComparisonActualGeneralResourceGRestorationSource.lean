module

public import ComparisonActualGeneralResourceGaReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000

theorem actual_general_resource_G_restoration_eq_canonical_source
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k : ℕ} {seed : List NativeResourceMark} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P) (hi : i ≤ star) (hs : star < U)
    (ho : MassOrdered 0 as) (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    (q : ℕ→RestCoordinate n→ℝ) :
    let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
    let S:=fun j=>orderedPathS (n+1) bf hf (partitionPoint 0 as j)
    let K:=fun j=>h j+b j*S j
    let G:=nativeActualResourceCanonicalShape P.live hi (hs.trans_le hP.highCut_le_length)
    actualGeneralGProjectedRestoration T P.live.test star U bf hf q=
      nativeOriginalGProjectedDisplacementRestoration T P.live.test.target star U q b h K S
        (fun u v=>deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false)))
        (G.canonicalPhysicalSource bf hf (fun _=>NativeSourceFactorForm.centered)).restProduct := by
  dsimp only
  let G:=nativeActualResourceCanonicalShape P.live hi (hs.trans_le hP.highCut_le_length)
  let R:=fun u v=>deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false))
  let C:=nativePhysicalResourceCenter n bf hf as
  have HP : (G.canonicalPhysicalSource bf hf (fun _=>NativeSourceFactorForm.centered)).restProduct=
      nativeRestGeneratedTestValue T P.live.test R C := by
    funext sigma
    exact actual_general_resource_canonical_rest_product_eq_live P.live hi
      (hs.trans_le hP.highCut_le_length) bf hf sigma
  rw [HP]
  have HCfun : C=fun j=>orderedPathS (n+1) bf hf (partitionPoint 0 as j):=by
    funext j
    exact (native_ordered_source_center_eq_completed n bf hf hbf hhf (partitionPoint_mem as ho j)).symm
  unfold actualGeneralGProjectedRestoration
  dsimp only
  change nativeOriginalGProjectedDisplacementRestoration T P.live.test.target star U q _ _ _ C R
    (nativeRestGeneratedTestValue T P.live.test R C)=_
  rw [HCfun]

end OAI.SKFluctuations.Cavity
