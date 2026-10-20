module

public import ComparisonSignedCavityOriginalGErrorPairProfile
public import ComparisonSignedCavityInheritedErrorTransport

@[expose] public section

noncomputable section
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree Set LaplaceWindowFormalization
open scoped BigOperators NNReal

theorem actual_minimum_inherited_original_target_G_density
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (Temp Cf : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    (hsource : NativeActualSmallSourceClocks M Temp Cf) (hxs : M.xs ≤ 1)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (i U : ℕ)
    (hi : i < U) (hU : U ≤ as.length) (A : ℝ) (hA : 0 ≤ A)
    (P : (nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i).tree.Assignment→ℝ)
    (hP :
      let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
      let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
      let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
      let K:=fun j=>h j+b j*S j
      let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
      (nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i).tree.disorderExpect
        (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 1 1 b h K) (fun σ=>(P σ)^2) 0 ≤ A^2) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
    let K:=fun j=>h j+b j*S j
    let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i
    abs (nativeOriginalLongitudinalPairing n 0 (cutFullVariance n q U 1 1 b h K) 0 U K b S
      g.tree P (g.embed (singleSlot as))) ≤
      A*forkVariation 2 3*actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
        edgeBudget 0 as (fun j=>if j<U then 0 else nativeOriginalCutLowErrorRadius n M.bf M.hf as j+1/(n+1:ℕ)) := by
  dsimp only at hP ⊢
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=cutFullVariance n q U 1 1 b h K
  let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i
  let f:=fun j=>if j<U then 0 else nativeWholeLawErrorRadius n as qfull (cutTSlope n U 0 b h K) j
  let Ccmp:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp
  let R:=fun j=>if j<U then 0 else nativeOriginalCutLowErrorRadius n M.bf M.hf as j+1/(n+1:ℕ)
  have hleaves : g.tree.leaves ≤ 2:=by
    have H:=(single (S:=Spin n×Bool) as).markedAttach_leaves 0 g
      (nativeFreshAtSlot_mem _ _ _ _)
    simpa only [single_leaves_exact] using H
  have H:=native_original_longitudinal_abs_le_high_profile g.tree ho U hU b h K S
    (fun _=>rfl) qfull P (g.embed (singleSlot as)) A hA hP 2 hleaves
  dsimp only at H
  have Hfork : g.tree.forkCost f=0:=native_initial_seed_high_forkCost as 0 hi f
    (by intro j hj;exact ite_eq_left hj)
  change _ ≤ A*forkVariation 2 3*(g.tree.forkCost f+edgeBudget 0 as f) at H
  rw [Hfork,zero_add] at H
  have HR : edgeBudget 0 as f ≤ Ccmp*edgeBudget 0 as R:=by
    have Hpoint (j : ℕ) (hj : j ≤ as.length) : f j ≤ Ccmp*R j:=by
      have HE:=actual_minimum_inherited_current_high_error_radius_le_original M Temp Cf hTemp hCf
        hsource hxs ho U (by norm_num : (1:ℝ)∈Icc (0:ℝ) 1)
        (by norm_num : (1:ℝ)∈Icc (0:ℝ) 1) j hj
      dsimp only [f,R,Ccmp]
      by_cases hjU : j<U
      · simp only [hjU,ite_true,mul_zero,le_refl]
      · simpa only [nativeOriginalHighErrorEnvelope,hjU,ite_false] using HE
    have HH:=actual_low_edgeBudget_mono ho Hpoint
    have HE : edgeBudget 0 as (fun j=>Ccmp*R j)=Ccmp*edgeBudget 0 as R:=by
      simpa only [zero_mul,add_zero] using actual_low_edgeBudget_linear as 0 Ccmp 0 R (fun _=>0)
    rw [HE] at HH
    exact HH
  exact H.trans ((mul_le_mul_of_nonneg_left HR (mul_nonneg hA (forkVariation_nonneg 2 3))).trans_eq (by ring))

end OAI.SKFluctuations.Cavity
