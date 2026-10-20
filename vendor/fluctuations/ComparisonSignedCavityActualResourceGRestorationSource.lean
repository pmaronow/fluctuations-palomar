module

public import ComparisonSignedCavityActualResourceCanonicalShape
public import ComparisonSignedCavityActualCurrentGRestorationCanonical

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000

theorem native_actual_resource_G_restoration_eq_canonical_source
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k : ℕ} {seed : List NativeResourceMark} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P) (hi : i ≤ star)
    (hs : star < U) (ho : MassOrdered 0 as)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (q : ℕ→RestCoordinate n→ℝ) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
    let K:=fun j=>h j+b j*S j
    let G:=nativeActualResourceCanonicalShape P.live hi (hs.trans_le hP.highCut_le_length)
    nativeActualGProjectedRestoration T P.live.test star U M q=
      nativeOriginalGProjectedDisplacementRestoration T P.live.test.target star U q b h K S
        (fun u v=>deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false)))
        (G.canonicalMinimumSource M (fun _=>NativeSourceFactorForm.centered)).restProduct := by
  have H:=native_actual_current_G_restoration_eq_canonical_source hP hi hs ho M q
  dsimp only at H ⊢
  have HE :
      ((nativeGeneratedCompleteShape n P.live.test P.live.ancestry hi
        (hs.trans_le hP.highCut_le_length)).canonicalMinimumSource M
        (fun _=>NativeSourceFactorForm.centered)).restProduct=
      ((nativeActualResourceCanonicalShape P.live hi
        (hs.trans_le hP.highCut_le_length)).canonicalMinimumSource M
        (fun _=>NativeSourceFactorForm.centered)).restProduct := by
    funext σ
    rw [native_generated_complete_canonical_rest_product,
      native_actual_resource_canonical_rest_product_eq_live]
    rfl
  rw [HE] at H
  exact H

end OAI.SKFluctuations.Cavity
