module

public import ComparisonActualGeneralTargetRawRestorationReadout
public import ComparisonActualHighWallSecondLowFreshRawCubicAlong
public import ComparisonActualHighWallUnifiedResourceJointHigh
public import ComparisonActualHighWallResourceJointLowRestoration
public import ComparisonActualHighWallResourceLongitudinalFromMinimum
public import ComparisonActualHighWallJointLowCubicPrice
public import ComparisonActualHighWallContinuumClockMass
public import ComparisonSignedCavitySecondLowGeneratedFullB0Geometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 42000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_high_wall_original_target_restoration_profile_along
    (dOrder : ℕ) (hd : 0< dOrder) (p : ℝ) (hp : 2< p) (hOrder : p/(p-2)≤ (dOrder:ℝ))
    (Bclock Cmass Ccut Rmacro F Cx : ℝ) {eta : ℝ}
    (hCm : 0≤ Cmass) (hCcut : 0≤ Ccut) (hCx : 0< Cx) (heta : 0< eta)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0< m) (hdelta : 0< delta) (hroom : delta< 3*m) (hgap : 2*eta< 6*m)
    (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az) (hC0 : 0< C0) (hCt : 0≤ Ct)
    (hmacro : 0< Rmacro) (hRhalf : Rmacro≤ 1/2)
    (hFmass : 1+2*cu≤ F) (hFradius : 1+1/Rmacro≤ F)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop) :
    ∃C : ℝ,0< C ∧ ∀ᶠn in atTop,
      ∀M : ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock,
      M.xs=M.data.d→∀(L : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val≤ 1)→(∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹≤ M.xs→∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      ∀(mid tail : List PositiveMass),as=mid++tail→0< mid.length→
      ∀(U : ℕ),mid.length< U→U≤ as.length→
      partitionPoint 0 as mid.length≤ Cmass*M.data.d→partitionPoint 0 as U≤ Ccut*M.data.d→
      M.data.d≤ Rmacro/2→4*M.data.d≤ M.data.wallRadius M.alpha (partitionPoint 0 as U)→
      M.z≤ min (M.data.wallRadius M.alpha (partitionPoint 0 as U)/8) (Rmacro/4)→
      M.data.wallRadius M.alpha (partitionPoint 0 as 0)≤
        min (M.data.wallRadius M.alpha (partitionPoint 0 as U)/8) (Rmacro/4)→
      M.data.wallRadius M.alpha (partitionPoint 0 as mid.length)≤
        min (M.data.wallRadius M.alpha (partitionPoint 0 as U)/8) (Rmacro/4)→
      ∀sourceMass : ℝ,∀hsourceMass : 0< sourceMass,
      Cx*M.xs≤ sourceMass→partitionPoint 0 as U=sourceMass→
      (∀j≤ nativeDyadicCutDepth sourceMass,nativeDyadicMassCut sourceMass hsourceMass j∈us)→
      let g:=nativeFreshAtSlot (single (S:=Spin (dim n)×Bool) as) 0 (singleSlot as) mid.length
      let R:=M.data.highErrorEnvelope M.alpha as U
      actualGeneralTargetRawRestorationBudget (n:=dim n) M.bf M.hf as mid.length U≤
        C*(M.data.d^3+M.data.d*(g.tree.forkCost (fun l=> (R l)^(4/p))+edgeBudget 0 as (fun l=> (R l)^(4/p))+
          M.data.d*(g.tree.forkCost R+edgeBudget 0 as R))) := by
  obtain ⟨Cb,hCb,HB⟩:=eventually_actual_high_wall_second_low_fresh_raw_cubic_price_along (D:=D)
    0 1 Bclock Cmass Ccut Rmacro F Cx hCx heta hCm hCcut hm hdelta hroom hgap hcl hcu hAz hC0 hCt
    hmacro hRhalf hFmass hFradius dim hdim
  obtain ⟨Cj,hCj,HJ⟩:=eventually_actual_high_wall_resource_joint_HIGH_restoration_from_minimum .lowTwoHigh (D:=D)
    0 dOrder 2 hd p hp hOrder Bclock Cmass Ccut hCm hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨C4,hC4,H4⟩:=eventually_actual_high_wall_resource_joint_HIGH_restoration_from_minimum .fourGLow (D:=D)
    0 dOrder 2 hd p hp hOrder Bclock Cmass Ccut hCm hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cq,hCq,HQ⟩:=eventually_actual_high_wall_resource_joint_LOW_restoration_from_minimum (D:=D)
    0 2 Bclock Cmass Ccut hCm hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cl,hCl,HL⟩:=eventually_actual_high_wall_resource_longitudinal_restoration_from_minimum (D:=D)
    0 dOrder 2 hd p hp hOrder Bclock Cmass Ccut hCm hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨CK,hCK,HK⟩:=eventually_actual_high_wall_continuum_clock_mass_upper (D:=D)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨CD,hCD,HD⟩:=eventually_actual_high_wall_original_low_error_radius_bigO (D:=D)
    Bclock Cmass hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  let CB:=actualLowErrorComparisonConstant (2*max Bclock 0) (max Bclock 0)
  have hCB : 0≤ CB:=actualLowErrorComparisonConstant_nonneg _ (le_max_right _ _)
  let C:=Cb+Cj+C4+Cq*CB*(CD+1)+2*CK*(1+Cmass)*Cl+1
  refine ⟨C,by dsimp only [C];positivity,?_⟩
  filter_upwards [HB,hdim.eventually HJ,hdim.eventually H4,hdim.eventually HQ,
    hdim.eventually HL,hdim.eventually HK,hdim.eventually HD,
    hdim.eventually (eventually_actual_high_wall_site_le_square (D:=D) (Bclock:=Bclock) hm hC0)]
      with n hnB hnJ hn4 hnQ hnL hnK hnD hnSite
  intro M hwork L us hus hret hmesh
  filter_upwards [hnB M hwork L us hus hret hmesh,hnJ M hwork L us hus hret hmesh,
    hn4 M hwork L us hus hret hmesh,hnQ M hwork L us hus hret hmesh,
    hnL M hwork L us hus hret hmesh,hnD M hwork L us hus hret hmesh]
      with jGrid hjB hjJ hj4 hjQ hjL hjD
  dsimp only at hjB hjJ hj4 hjQ hjL hjD ⊢
  intro mid tail hparts hmid U hs hU hmass hcut hsmall hhigh hz hri hrs
    sourceMass hsourceMass hsource hsourceeq hnodes
  let as:=mid++tail
  let T:=single (S:=Spin (dim n)×Bool) as
  let s:=singleSlot (S:=Spin (dim n)×Bool) as
  let g:=nativeFreshAtSlot T 0 s mid.length
  let P:=actualGeneralTargetFreshConstantResource (n:=dim n) as mid.length
  let R:=M.data.highErrorEnvelope M.alpha as U
  let profile:=g.tree.forkCost (fun l=> (R l)^(4/p))+edgeBudget 0 as (fun l=> (R l)^(4/p))+
    M.data.d*(g.tree.forkCost R+edgeBudget 0 as R)
  let K:=nativeContinuumMixedClock (dim n) M.bf M.hf as
  have hdpos : 0< M.data.d:=M.data.hd
  have ho : MassOrdered 0 as:=by dsimp only [as];rw [←hparts];exact finiteCutMasses_ordered us hus jGrid
  have hU' : U≤ as.length:=by simpa only [as,hparts] using hU
  have hmass' : partitionPoint 0 as mid.length≤ Cmass*M.data.d:=by simpa only [as,hparts] using hmass
  have hcut' : partitionPoint 0 as U≤ Ccut*M.data.d:=by simpa only [as,hparts] using hcut
  have hzero : partitionPoint 0 as 0≤ Cmass*M.data.d:=by
    simpa only [partitionPoint,partitionValues_zero,id_eq] using mul_nonneg hCm hdpos.le
  have hg : g.tree.leaves≤ 2:=by
    have H:=T.markedAttach_leaves 0 g (nativeFreshAtSlot_mem T 0 s mid.length)
    simpa only [T,single_leaves_exact] using H
  have Hsplit : g.tree.splitIndex (g.embed s) g.mark=mid.length:=by
    rw [g.tree.splitIndex_symm,nativeFreshAtSlot_split,T.splitIndex_self,Nat.min_eq_left (hs.le.trans hU')]
  have hP : NativeActualResourceGenerated 0 mid.length U [] 0 g.tree P:=
    actual_general_target_fresh_constant_resource_generated as mid.length U hU'
  have hcoef : P.coefficient=1:=rfl
  have hR l : 0≤ R l:=M.data.highErrorEnvelope_nonneg M.alpha as U l
  have hprofile : 0≤ profile:=add_nonneg (add_nonneg (g.tree.forkCost_nonneg (fun l=> Real.rpow_nonneg (hR l) _))
    (edgeBudget_nonneg ho (fun l=> Real.rpow_nonneg (hR l) _)))
    (mul_nonneg hdpos.le (add_nonneg (g.tree.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)))
  have hdyadic:=native_second_low_coarse_readout_from_retained_nodes sourceMass hsourceMass us hus hnodes jGrid U hU hsourceeq
  rw [hparts] at hjJ hj4 hjQ hjL hjD hdyadic
  have Hj:=hjJ 0 mid.length U 0 [] g.tree P hP (Nat.zero_le _) hs hU' hg (by simp) hzero hmass' hcut'
    (g.embed s) g.mark (by rw [Hsplit];exact hs)
  have H4p:=hj4 0 mid.length U 0 [] g.tree P hP (Nat.zero_le _) hs hU' hg (by simp) hzero hmass' hcut'
    (g.embed s) g.mark (by rw [Hsplit];exact hs)
  have Hq:=hjQ 0 mid.length U 0 [] g.tree P hP (Nat.zero_le _) hs hU' hg (by simp) hzero hmass' hcut'
    (g.embed s) g.mark (by rw [Hsplit];exact hs)
  have Hl (a : g.tree.Slot):=hjL 0 mid.length U 0 [] g.tree P hP (Nat.zero_le _) hs hU' hg (by simp)
    hzero hmass' hcut' a
  simp only [pow_zero,one_mul,hcoef,abs_one,nativeResourceScale,List.map_nil,List.prod_nil,mul_one] at Hj H4p Hq
  have Hld (a : g.tree.Slot) : |actualGeneralResourceLongitudinalRestoration M.bf M.hf U P a|≤ Cl*profile:=by
    simpa only [pow_zero,one_mul,hcoef,abs_one,nativeResourceScale,List.map_nil,List.prod_nil,mul_one,profile,R,as,g,T,s] using Hl a
  have Hlow:=hjD mid.length (hs.le.trans hU') hmass'
  have Hsite : 1/(dim n+1:ℕ)≤ M.data.d:=by
    have H:=hnSite M hwork
    have H' : 3*(1/((dim n+1:ℕ):ℝ))≤ M.data.d^2:=by convert H using 1;ring
    have HN : (0:ℝ)≤ 1/(dim n+1:ℕ):=by positivity
    have Hds : M.data.d^2≤ M.data.d:=by nlinarith only [hdpos.le,M.data.hd1]
    linarith only [H',HN,Hds]
  have Hrad : actualLowErrorComparisonConstant (2*M.data.T) M.data.T*
      (nativeOriginalCutLowErrorRadius (dim n) M.bf M.hf as mid.length+1/(dim n+1:ℕ))≤ CB*(CD+1)*M.data.d:=by
    have Hfactor:=actual_wall_low_error_comparison_constant_le (B:=max Bclock 0)
      M.data.hTpos.le (M.hT.trans (le_max_left Bclock 0))
    have Hsum : nativeOriginalCutLowErrorRadius (dim n) M.bf M.hf as mid.length+1/(dim n+1:ℕ)≤ (CD+1)*M.data.d:=by
      nlinarith only [Hlow,Hsite]
    exact (mul_le_mul Hfactor Hsum (add_nonneg (Real.sqrt_nonneg _) (by positivity)) hCB).trans_eq (by ring)
  rw [Hsplit] at Hq
  have Hq' : |actualGeneralTargetRawJointLowPart (n:=dim n) M.bf M.hf as mid.length U|≤ Cq*CB*(CD+1)*M.data.d^3:=by
    apply Hq.trans
    have HB:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right Hrad (sq_nonneg M.data.d)) hCq.le
    convert HB using 1 <;> ring
  have HK : K mid.length≤ CK*(1+Cmass)*M.data.d:=by
    have H:=hnK M hwork as ho mid.length
    rw [hwork] at H
    change K mid.length≤ CK*(M.data.d+partitionPoint 0 as mid.length) at H
    nlinarith only [H,mul_le_mul_of_nonneg_left hmass' hCK.le]
  have HK0 : 0≤ K mid.length:=native_continuum_mixed_clock_nonneg (dim n) M.bf M.hf
    (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) as ho mid.length
  have Hchi:=actual_general_continuum_chi_mem_unit_on_any_grid (n:=dim n) M.bf M.hf
    (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) as ho U (by omega) hU'
  have Hlp : |actualGeneralTargetRawLongitudinalPart (n:=dim n) M.bf M.hf as mid.length U|≤
      2*CK*(1+Cmass)*Cl*M.data.d*profile:=by
    unfold actualGeneralTargetRawLongitudinalPart
    dsimp only
    rw [abs_mul,abs_of_nonneg (mul_nonneg Hchi.1 HK0)]
    have Hcoeff:=mul_le_mul Hchi.2 HK HK0 (by norm_num : (0:ℝ)≤ 1)
    simp only [one_mul] at Hcoeff
    have Hsum:=(abs_add_le _ _).trans (add_le_add (Hld (g.embed s)) (Hld g.mark))
    have HH:=mul_le_mul Hcoeff Hsum (abs_nonneg _) (by positivity : 0≤ CK*(1+Cmass)*M.data.d)
    convert HH using 1;ring
  let G0:=emptyNaturalBoundaryShape (dim n) T
  have Hbfresh:=hjB [] mid tail hparts T G0 Fin.elim0 ∅ s U hU' M.data.d sourceMass hsourceMass hmid
    (by simpa only [List.length_nil,Nat.zero_add] using hs)
    (native_single_persistentLowForks 0 (0+mid.length) U hU')
    (by exact (ClockTree.single_leaves_exact (S:=Spin (dim n)×Bool) as).le)
    hcut (by rw [hwork]) le_rfl hsmall (fun e=> e.elim0) (fun e=> e.elim0)
    (by simpa only [List.length_nil,hparts,as] using hzero)
    (by simpa only [List.length_nil,Nat.zero_add] using hmass) hhigh hz (fun e=> e.elim0) hri
    (by simpa only [List.length_nil,Nat.zero_add] using hrs) hsource hdyadic
  have HE : (G0.canonicalHighWallSource M Fin.elim0).restProduct=(fun _=> 1):=by
    funext sigma
    simp only [ActualNaturalBoundaryShape.restProduct,Finset.univ_eq_empty,Finset.prod_empty]
  rw [HE] at Hbfresh
  have Hsf : sourceMonomialScale M.data.d M.data.d (∅ : Finset (Fin 0))=1:=by
    rw [←source_factor_scale_product];exact Fin.prod_univ_zero _
  have Hb' : |actualGeneralTargetRawFreshB0Part (n:=dim n) M.bf M.hf as mid.length U|≤ Cb*M.data.d^3:=by
    rw [Hsf,mul_one] at Hbfresh
    unfold actualGeneralTargetRawFreshB0Part
    dsimp only
    have HKfun : nativeContinuumMixedClock (dim n) M.bf M.hf as=
        (fun j=>(M.hf (partitionPoint 0 as j):ℝ)+(M.bf (partitionPoint 0 as j):ℝ)*
          orderedPathS (dim n+1) M.bf M.hf (partitionPoint 0 as j)):=rfl
    rw [HKfun]
    simpa only [List.length_nil,Nat.zero_add,List.nil_append,hparts,as,T,s] using Hbfresh
  have Hj' : |actualGeneralTargetRawJointHighPart (n:=dim n) M.bf M.hf .lowTwoHigh as mid.length U|≤ Cj*M.data.d*profile:=Hj
  have H4' : |actualGeneralTargetRawJointHighPart (n:=dim n) M.bf M.hf .fourGLow as mid.length U|≤ C4*M.data.d*profile:=H4p
  rw [hparts]
  change _≤ C*(M.data.d^3+M.data.d*profile)
  unfold actualGeneralTargetRawRestorationBudget
  have Hsum:=add_le_add (add_le_add (add_le_add (add_le_add Hb' Hj') Hq') Hlp) H4'
  apply Hsum.trans
  dsimp only [C]
  have HD3 : 0≤ M.data.d^3:=pow_nonneg hdpos.le 3
  have HP : 0≤ M.data.d*profile:=mul_nonneg hdpos.le hprofile
  nlinarith only [mul_nonneg hCb.le HP,mul_nonneg hCj.le HD3,mul_nonneg hC4.le HD3,
    mul_nonneg (mul_nonneg (mul_nonneg hCq.le hCB) (by positivity : 0≤ CD+1)) HP,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤ 2) hCK.le)
      (by positivity : 0≤ 1+Cmass)) hCl.le) HD3,HD3,HP]

end OAI.SKFluctuations.Cavity
