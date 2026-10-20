module

public import ComparisonSignedCavityActualTargetGCutDensity
public import SKProof.Port.ComparisonActualOriginalQPullbackFourProducers
public import SKProof.Port.ComparisonActualOriginalQTargetGCutEnvelope
public import ComparisonSignedCavityOriginalLongitudinalCutProfile
public import ComparisonSignedCavityActualTargetGOriginalReadout

@[expose] public section

noncomputable section
set_option linter.unusedVariables false
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree Set Classical LaplaceWindowFormalization
open scoped NNReal
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

def nativeActualTargetCutCoefficient_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (V : ℕ) : ℝ :=
  (3/2:ℝ)*(errorJetVariation 5 0 0*(6:ℝ))*nativeContinuumMixedClock n M.sweepBf M.sweepHf as (V-1)

theorem actual_minimum_inherited_target_G_cut_density_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (Temp Cf : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf)
    (hsource : ActualOriginalQSmallSourceClocks M Temp Cf) (hxs : M.xs≤1)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (i U V : ℕ)
    (hi : i<U) (hUV : U≤V) (hV : V≤as.length) (A : ℝ) (hA : 0≤A)
    (hP :
      let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
      let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
      let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
      let K:=fun j=>h j+b j*S j
      let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
      let T:=single (S:=Spin n×Bool) as
      let g:=nativeFreshAtSlot T 0 (singleSlot as) i
      g.tree.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 1 1 b h K)
        (fun σ=>(deletedOverlap n (joinSpin (T.atSlot (g.restrict σ) (singleSlot as)))
          (joinSpin (g.spin σ))-S i)^2) 0≤A^2) :
    abs (nativeActualTargetLongitudinalResponse_original_q M as i U-nativeActualTargetLongitudinalResponse_original_q M as i V)≤
      A*forkVariation 2 3*actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
        (edgeBudget 0 as (fun j=>if j<U then 0 else if j<V then
            nativeOriginalCutLowErrorRadius n M.sweepBf M.sweepHf as j+1/(n+1:ℕ) else 0)+
         nativeActualTargetCutCoefficient_original_q M as V*
           edgeBudget 0 as (fun j=>if j<V then 0 else
             nativeOriginalCutLowErrorRadius n M.sweepBf M.sweepHf as j+1/(n+1:ℕ))) := by
  dsimp only at hP
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=cutFullVariance n q U 1 1 b h K
  let T:=single (S:=Spin n×Bool) as
  let g:=nativeFreshAtSlot T 0 (singleSlot as) i
  let P:=fun σ=>deletedOverlap n (joinSpin (T.atSlot (g.restrict σ) (singleSlot as)))
    (joinSpin (g.spin σ))-S i
  let coef:=nativeActualTargetCutCoefficient_original_q M as V
  let f:=fun j=>if j<U then 0 else
    if j<V then nativeWholeLawErrorRadius n as qfull (cutTSlope n U 0 b h K) j
    else coef*nativeWholeLawErrorRadius n as qfull (cutTSlope n V 0 b h K) j
  let Cmp:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp
  let lo:=fun j=>if j<U then 0 else if j<V then
    nativeOriginalCutLowErrorRadius n M.sweepBf M.sweepHf as j+1/(n+1:ℕ) else 0
  let hiR:=fun j=>if j<V then 0 else nativeOriginalCutLowErrorRadius n M.sweepBf M.sweepHf as j+1/(n+1:ℕ)
  have hKm : Monotone K:=native_continuum_mixed_clock_monotone n M.sweepBf M.sweepHf
    M.inherited_bf_monotone M.inherited_hf_monotone as ho
  have hK0 : ∀j,0≤K j:=native_continuum_mixed_clock_nonneg n M.sweepBf M.sweepHf
    M.inherited_bf_monotone M.inherited_hf_monotone as ho
  have hc : 0≤coef:=mul_nonneg (mul_nonneg (by norm_num)
    (mul_nonneg (errorJetVariation_nonneg 5 0 0) (by norm_num))) (hK0 _)
  have hleaves : g.tree.leaves≤2:=by
    have H:=(single (S:=Spin n×Bool) as).markedAttach_leaves 0 g
      (nativeFreshAtSlot_mem _ _ _ _)
    simpa only [single_leaves_exact] using H
  have H:=native_original_longitudinal_cut_difference_abs_le_profile g.tree ho 2 hleaves
    U V (Nat.zero_le i |>.trans_lt hi) hUV hV b h K S (fun _=>rfl) hKm hK0 qfull
    P (g.embed (singleSlot as)) A hA hP
  dsimp only at H
  norm_num only [Nat.reduceAdd,Nat.cast_ofNat,show (5:ℝ)+1=6 by norm_num] at H
  have HQ:=native_original_full_endpoint_revelation_cut_independent n q U V b h K
  have HRV : nativeActualTargetLongitudinalResponse_original_q M as i V=
      nativeOriginalLongitudinalPairing n 0 qfull 0 V K b S g.tree P (g.embed (singleSlot as)):=by
    unfold nativeActualTargetLongitudinalResponse_original_q
    dsimp only
    change nativeOriginalLongitudinalPairing n 0 (cutFullVariance n q V 1 1 b h K) 0 V K b S
      g.tree P (g.embed (singleSlot as))=_
    rw [←HQ]
  change abs (nativeActualTargetLongitudinalResponse_original_q M as i U-
      nativeOriginalLongitudinalPairing n 0 qfull 0 V K b S g.tree P (g.embed (singleSlot as)))≤
    A*forkVariation 2 3*(g.tree.forkCost f+edgeBudget 0 as f) at H
  rw [←HRV] at H
  have Hfork : g.tree.forkCost f=0:=native_initial_seed_high_forkCost as 0 hi f
    (by intro j hj;exact ite_eq_left hj)
  rw [Hfork,zero_add] at H
  have Hedge : edgeBudget 0 as f≤Cmp*(edgeBudget 0 as lo+coef*edgeBudget 0 as hiR):=by
    have Hpoint (j : ℕ) (hj : j≤as.length) : f j≤Cmp*(lo j+coef*hiR j):=by
      have HU:=actual_minimum_inherited_current_high_error_radius_le_original_original_q M Temp Cf hTemp hCf
        hsource hxs ho U (by norm_num : (1:ℝ)∈Icc (0:ℝ) 1)
        (by norm_num : (1:ℝ)∈Icc (0:ℝ) 1) j hj
      change nativeWholeLawErrorRadius n as qfull (cutTSlope n U 0 b h K) j≤_ at HU
      have HV:=actual_minimum_inherited_current_high_error_radius_le_original_original_q M Temp Cf hTemp hCf
        hsource hxs ho V (by norm_num : (1:ℝ)∈Icc (0:ℝ) 1)
        (by norm_num : (1:ℝ)∈Icc (0:ℝ) 1) j hj
      change nativeWholeLawErrorRadius n as (cutFullVariance n q V 1 1 b h K) (cutTSlope n V 0 b h K) j≤_ at HV
      rw [←HQ] at HV
      dsimp only [f,lo,hiR]
      by_cases hjU : j<U
      · have hjV : j<V:=hjU.trans_le hUV
        simp only [hjU,hjV,ite_true,mul_zero,add_zero,le_refl]
      · by_cases hjV : j<V
        · simpa only [nativeOriginalHighErrorEnvelope,hjU,hjV,ite_false,ite_true,mul_zero,add_zero,Cmp] using HU
        · simp only [hjU,hjV,ite_false,zero_add]
          have HH : nativeWholeLawErrorRadius n as qfull (cutTSlope n V 0 b h K) j≤
              Cmp*(nativeOriginalCutLowErrorRadius n M.sweepBf M.sweepHf as j+1/(n+1:ℕ)):=by
            simpa only [nativeOriginalHighErrorEnvelope,hjV,ite_false] using HV
          exact (mul_le_mul_of_nonneg_left HH hc).trans_eq (by ring)
    have HB:=actual_low_edgeBudget_mono ho Hpoint
    have HL : edgeBudget 0 as (fun j=>Cmp*(lo j+coef*hiR j))=
        Cmp*(edgeBudget 0 as lo+coef*edgeBudget 0 as hiR):=by
      have H1:=actual_low_edgeBudget_linear as 0 Cmp 0 (fun j=>lo j+coef*hiR j) (fun _=>0)
      have H2:=actual_low_edgeBudget_linear as 0 1 coef lo hiR
      simp only [zero_mul,add_zero] at H1
      simp only [one_mul] at H2
      rw [H1,H2]
    rw [HL] at HB
    exact HB
  exact H.trans ((mul_le_mul_of_nonneg_left Hedge
    (mul_nonneg hA (forkVariation_nonneg 2 3))).trans_eq (by ring))

end OAI.SKFluctuations.Cavity
