module

public import ComparisonSignedCavityActualFourLongitudinalRestorationReadout
public import ComparisonSignedCavityActualFourGaRestorationProfile

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000

theorem actual_minimum_four_longitudinal_restoration_forest_profile_le
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star U : ℕ} (ho : MassOrdered 0 as)
    (hs : star < U) (hU : U ≤ as.length)
    {Temp Cf W cK B : ℝ} (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    (HS : NativeActualSmallSourceClocks M Temp Cf) (hxs : M.xs ≤ 1)
    (hW : 0 < W) (hcK : 0 < cK) (hB : 0 ≤ B)
    (hK : cK*W ≤ nativeContinuumMixedClock n M.bf M.hf as star)
    (right : Bool) (depth : ℕ) (st : NativeActualResourceState (Spin n×Bool) as i star)
    {r : ℕ} (hr : st.tree.leaves ≤ r)
    (f2 R : ℕ→ℝ) (hf2 : ∀j,0 ≤ f2 j) (hR : ∀j,0 ≤ R j)
    (hf2lo : ∀j,j < U → f2 j=0) (hRlo : ∀j,j < U → R j=0)
    (Hrows : ∀Q∈nativeActualMinimumFourCenteredForest M hs hU W depth [st],
      |nativeActualOriginalFourLongitudinalError M U W Q right| ≤
        |Q.term.coefficient| *B*(Q.tree.forkCost f2+edgeBudget 0 as f2+
          W*(Q.tree.forkCost R+edgeBudget 0 as R))) :
    ((nativeActualMinimumFourCenteredForest M hs hU W depth [st]).map
      (fun Q=>|nativeActualOriginalFourLongitudinalError M U W Q right|)).sum ≤
      2*|st.term.coefficient| *B*
        nativeActualWeightedProfileFrontierCost nativeActualOriginalFourGCenteredBranches
          ((Temp+2*Cf)/(Real.exp (-4*(Temp+2*Cf))*cK)) 3 r depth*
        (st.tree.forkCost f2+edgeBudget 0 as f2+W*(st.tree.forkCost R+edgeBudget 0 as R)) := by
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let Γ:=nativeOriginalHighRowGamma (n:=n) (as:=as) U K
  let weight:=fun (Q : NativeActualResourceState (Spin n×Bool) as i star) tag=>
    nativeOriginalClockParentWeight W U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag)
  let rows:=nativeActualMinimumFourCenteredForest M hs hU W depth [st]
  let Cw:=(Temp+2*Cf)/(Real.exp (-4*(Temp+2*Cf))*cK)
  have hCw : 0 ≤ Cw:=by dsimp only [Cw];positivity
  have HW Q tag : |weight Q tag| ≤ Cw:=
    actual_continuum_four_G_weight_bound_of_small_source_clocks M hCf HS hxs hW hcK as ho hs hU hK Q tag
  have Hf:=nativeActualFourCenteredForest_wholeProfile_le ho Γ
    (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one ho U K Q p) hs (hs.le.trans hU) weight
    hCw HW depth [st] r (by intro Q hQ;obtain rfl:=List.mem_singleton.mp hQ;exact hr)
    f2 hf2 hf2lo
  have HR:=nativeActualFourCenteredForest_wholeProfile_le ho Γ
    (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one ho U K Q p) hs (hs.le.trans hU) weight
    hCw HW depth [st] r (by intro Q hQ;obtain rfl:=List.mem_singleton.mp hQ;exact hr)
    R hR hRlo
  have Hsum : (rows.map (fun Q=>|nativeActualOriginalFourLongitudinalError M U W Q right|)).sum ≤
      B*((rows.map (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost f2+edgeBudget 0 as f2))).sum+
        W*(rows.map (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost R+edgeBudget 0 as R))).sum) := by
    apply (List.sum_le_sum Hrows).trans_eq
    simp only [←List.sum_map_mul_left,←List.sum_map_add]
    congr 1
    apply List.map_congr_left
    intro Q hQ
    ring
  have H:=mul_le_mul_of_nonneg_left (add_le_add Hf (mul_le_mul_of_nonneg_left HR hW.le)) hB
  apply Hsum.trans
  convert H using 1 <;> simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
    rows,nativeActualMinimumFourCenteredForest,Cw] <;> ring

end OAI.SKFluctuations.Cavity
