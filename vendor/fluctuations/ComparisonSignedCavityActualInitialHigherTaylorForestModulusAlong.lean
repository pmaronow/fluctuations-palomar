module

public import ComparisonSignedCavityActualFourHigherTaylorProfile
public import ComparisonSignedCavityInitialInheritedFreshResourceThirdLowSavingAlong
public import ComparisonSignedCavityActualFreshResourceHighTaylorFromMinimum
public import ComparisonSignedCavityActualOriginalHighProfileHistory
public import ComparisonSignedCavityActualExpansionInitialTerminal
public import ComparisonSignedCavityActualFourForestTaylorProfile
public import ComparisonSignedCavityActualConstantChildHighProfile
public import ComparisonSignedCavityActualConstantJointFourReadout
public import ComparisonNativeActualInheritedHighTailPowers

@[expose] public section

noncomputable section
set_option autoImplicit false
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 26000000
set_option backward.isDefEq.respectTransparency false

theorem actual_inherited_initial_higher_Taylor_forest_modulus_along
    (depth : ℕ) (Bclock Temp Cf Cmass Cinitial Ccut cK : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCinitial : 0 ≤ Cinitial) (hCcut : 0 < Ccut) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D Cs c Tstar Lwin Cwindow : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2 ≤ Cs*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (Hshell : ∀ᶠn in atTop,∃(Tbase epsilon shell : ℝ) (ts : List ComparisonHistoryTerm),
      (∀u,(M n).b u=historyMatrixClock Tbase epsilon shell ts u) ∧
      (∀u,(M n).h u=historyFieldClock ts u))
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cwindow (w n)) :
    ∃Ci : ℝ,0 < Ci ∧ ∃err : ℕ→ℝ,(∀n,0 ≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧ ∀ᶠn in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        ∀(i V U : ℕ) (hi : i ≤ star) (hs : star<U) (hU : U ≤ as.length),
        2*c*W n ≤ partitionPoint 0 as U → partitionPoint 0 as U ≤ Ccut*W n →
        0 < V → i < V → V ≤ star → partitionPoint 0 as V ≤ Cinitial*(M n).xs →
        partitionPoint 0 as i ≤ Cmass*(M n).xs →
        partitionPoint 0 as star ≤ Cmass*W n →
        cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as star →
        ∀seedMass : ℝ,
        ((nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth
          [nativeActualInitialState as i star seedMass (hi.trans (hs.le.trans hU))]).map
          (fun Q=>|nativeActualOriginalFourHigherTaylorError (M n) U (W n) Q|)).sum ≤
            Ci*(M n).xs^2*actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
              (nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as i+1/(dim n+1:ℕ))+
              err n*(M n).xs^3 := by
  let eta:=actualMassSavingExponent m delta
  let degree:=1+depth
  let rBound:=2+6*depth
  obtain ⟨p,dOrder,hp,hdOrder,hOrder,htheta1,htheta2,hdeficit⟩:=
    exists_native_high_profile_holder_orders (actualMassSavingExponent_pos hm hdelta)
  obtain ⟨CH,hCH,HH⟩:=eventually_actual_minimum_inherited_fresh_resource_HIGH_parts_from_minimum
    (D:=D) degree dOrder (rBound+1) hdOrder p hp hOrder Bclock Temp Cf Cmass Ccut
    hTemp hCf hCmass hCcut.le hm hdelta hroom hcl hcu hAz hC0 hCt
  have Hclock : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1:=by
    filter_upwards [Hshell] with n hn
    rcases hn with ⟨Tbase,epsilon,shell,ts,hb,hh⟩
    exact NativePullbackClockRegularity.of_shell_history
      (M n).context.hc (M n).context.hk (M n).context.hkc (M n).context.hm (M n).context.hM
      (M n).alpha Tbase epsilon shell ts (M n).b (M n).h hb hh le_rfl zero_le_one le_rfl
  obtain ⟨CiLow,hCiLow,eLow,heLow,hELow,HLow⟩:=actual_inherited_initial_fresh_resource_third_LOW_saving_along
    degree (rBound+1) Bclock Temp Cf Cmass Cinitial Ccut hTemp hCf hCmass hCinitial hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs dim hdim M W hcanonical hWlim Hsource hsmall Hclock w hw
  have Htail:=eventually_actual_shell_history_original_high_envelope_powers
    (D:=D) (Cs:=Cs) Bclock Temp Cf hTemp hm hdelta hroom hcl hcu hAz hC0 hCt
    hCs hc hcouter
  let Cd:=Real.exp (-4*(Temp+2*Cf))*cK
  let Cw:=(Temp+2*Cf)/Cd
  let Vp:=nativeActualWeightedProfileFrontierCost nativeActualOriginalFourGCenteredBranches Cw 3 2 depth
  let Vv:=nativeActualWeightedFrontierCost nativeActualOriginalFourGCenteredBranches Cw 3 2 depth
  have hVv : 0 ≤ Vv:=nativeActualWeightedFrontierCost_nonneg _ (by dsimp only [Cw,Cd];positivity) _ _ _
  have hCd : 0 < Cd:=by dsimp only [Cd];positivity
  have hCw : 0 ≤ Cw:=by dsimp only [Cw];positivity
  have hVp : 0 ≤ Vp:=nativeActualWeightedProfileFrontierCost_nonneg _ hCw _ _ _
  let err:=fun n=>(8*CH/Cd*Vp)*((dim n+1:ℕ):ℝ)^(-eta/256)+(2*Vv/Cd)*eLow n
  have Hpow:=(tendsto_rpow_neg_atTop (show 0 < eta/256 from div_pos
    (actualMassSavingExponent_pos hm hdelta) (by norm_num))).comp
    (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
  have Herr : Tendsto err atTop (𝓝 0):=by
    have HH:=(Hpow.const_mul (8*CH/Cd*Vp)).add (hELow.const_mul (2*Vv/Cd))
    simpa only [err,Function.comp_def,mul_zero,add_zero,neg_div] using HH
  have hErr n : 0 ≤ err n:=by
    have HL:=heLow n
    dsimp only [err]
    positivity
  refine ⟨2*Vv/Cd*CiLow+1,by positivity,err,hErr,Herr,?_⟩
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hdim.eventually HH,hdim.eventually Htail,HLow,Hsource,hsmall,Hshell,HW1] with
    n hnH hnTail hnLow hsource hnSmall hnShell hW1
  rcases hnShell with ⟨Tbase,epsilon,shell,ts,hb,hh⟩
  have hxW : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hxs1:=hxW.trans hW1
  have hW : 0 < W n:=(M n).hxs.trans_le hxW
  have hx : 0 < (M n).xs:=(M n).hxs
  intro L us hus hret hmesh hstar
  filter_upwards [hnH (M n) hsource hxs1 L us hus hret hmesh,
    hnLow L us hus hret hmesh hstar,
    hnTail (M n) Tbase epsilon shell ts hb hh hnSmall (by simpa only [←hcanonical] using hW1) us hus]
    with jGrid hgridH hgridLow hgridTail
  dsimp only at hgridH hgridLow hgridTail ⊢
  intro i V U hi hs hU hcutlo hcut hV hiV hVstar hcutI hmi hmassstar hstarK seedMass
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
  let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
  let Γ:=nativeOriginalHighRowGamma (n:=dim n) (as:=as) U K
  let weight:=fun (Q : NativeActualResourceState (Spin (dim n)×Bool) as i star) tag=>
    nativeOriginalClockParentWeight (W n) U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag)
  let root:=nativeActualInitialState (S:=Spin (dim n)×Bool) as i star seedMass (hi.trans (hs.le.trans hU))
  let children:=[root]
  let rows:=nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth children
  let R:=nativeOriginalHighErrorEnvelope (dim n) U (M n).bf (M n).hf as (4*Cf+2*Temp) Temp
  let f:=fun j=>(R j)^(4/p)
  let BH:=4*CH/Cd
  let initialError:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
    (nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as i+1/(dim n+1:ℕ))
  let lowPrice:=CiLow*(M n).xs*initialError+eLow n*(M n).xs^2
  let BL:=(M n).xs/Cd*lowPrice
  have hInitialError:0 ≤ initialError:=by
    dsimp only [initialError,nativeOriginalCutLowErrorRadius]
    exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp) (by positivity)
  have hLowPrice:0 ≤ lowPrice:=by
    have HL:=heLow n
    dsimp only [lowPrice];positivity
  have hBL:0 ≤ BL:=by dsimp only [BL];positivity
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hR j : 0 ≤ R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hRlo j (hj : j<U) : R j=0:=by simp only [R,nativeOriginalHighErrorEnvelope,hj,ite_true]
  have hf j : 0 ≤ f j:=Real.rpow_nonneg (hR j) _
  have hflo j (hj : j<U) : f j=0:=by dsimp only [f];rw [hRlo j hj,Real.zero_rpow (by positivity : 4/p≠0)]
  have hBH : 0 ≤ BH:=by dsimp only [BH];positivity
  have HW Q tag : |weight Q tag| ≤ Cw:=
    actual_continuum_four_G_weight_bound_of_small_source_clocks (M n) hCf hsource hxs1 hW hcK as ho hs hU hstarK Q tag
  have Hroot : NativeActualResourceGenerated i star U [.initial] root.generation root.tree root.term:=
    .physical (.seed as hU seedMass .initial (Or.inl rfl) (hi.trans (hs.le.trans hU)))
  have Hleaves Q (hQ : Q∈children) : Q.tree.leaves ≤ 2:=by
    have HQ : Q=root:=List.mem_singleton.mp hQ
    subst Q
    exact nativeActualInitialState_leaves_le as i star seedMass (hi.trans (hs.le.trans hU))
  have Hvalid Q (hQ : Q∈rows) := nativeActualFourCenteredForest_valid Γ hs (hs.le.trans hU) weight depth children
    (fun P hP=>by have HP : P=root:=List.mem_singleton.mp hP;subst P;exact Hroot) Q hQ
  have Hgen Q (hQ : Q∈rows) := nativeActualFourCenteredForest_generation_bound Γ hs (hs.le.trans hU) weight depth children
    0 (fun P hP=>by have HP : P=root:=List.mem_singleton.mp hP;subst P;rfl) Q hQ
  have Hleaf Q (hQ : Q∈rows) :=nativeActualFourCenteredForest_leaves_bound Γ hs (hs.le.trans hU) weight depth children
    2 Hleaves Q hQ
  have Hrow Q (hQ : Q∈rows) : |nativeActualOriginalFourHigherTaylorError (M n) U (W n) Q| ≤
      |Q.term.coefficient| *((BH*(M n).xs)*(Q.tree.forkCost f+edgeBudget 0 as f+
        W n*(Q.tree.forkCost R+edgeBudget 0 as R))+BL):=by
    have HV:=Hvalid Q hQ
    have HG:=Hgen Q hQ
    have HT:=Hleaf Q hQ
    have HD : 1+Q.generation ≤ degree:=by dsimp only [degree];omega
    let g:=nativeFreshAtSlot Q.tree 0 Q.term.live.test.target star
    have hg : g.tree.leaves ≤ rBound+1:=by
      have HH:=Q.tree.markedAttach_leaves 0 g (nativeFreshAtSlot_mem Q.tree 0 Q.term.live.test.target star)
      dsimp only [rBound]
      omega
    let cost:=Q.tree.forkCost f+edgeBudget 0 as f+W n*(Q.tree.forkCost R+edgeBudget 0 as R)
    have hcost : 0 ≤ cost:=by
      have HF:=add_nonneg (Q.tree.forkCost_nonneg hf) (edgeBudget_nonneg ho hf)
      have HR:=add_nonneg (Q.tree.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
      dsimp only [cost];positivity
    have Hhigh0 l t hl ht part:=hgridH i star U Q.generation [.initial] Q.tree Q.term HV hi hs hU
      (by dsimp only [rBound];omega) (by simpa using HD) (M n).xs (W n) le_rfl hxW hW1 hmi hmassstar hcut l t hl ht part
    have Hhigh1 l t hl ht part:=hgridH i star U Q.generation [.initial] g.tree (Q.term.retarget 0) HV.retarget hi hs hU
      hg (by simpa using HD) (M n).xs (W n) le_rfl hxW hW1 hmi hmassstar hcut l t hl ht part
    simp only [nativeResourceScale,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
      NativeResourceMark.savedScale,mul_one] at Hhigh0 Hhigh1
    have Hforkf:=nativeFreshAtSlot_high_forkCost Q.tree 0 Q.term.live.test.target hs f hflo
    have HforkR:=nativeFreshAtSlot_high_forkCost Q.tree 0 Q.term.live.test.target hs R hRlo
    change ∀l t,l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → ∀part : Fin 3,
      |((W n)⁻¹)^Q.generation*nativeActualOriginalFreshResourceHigherHighPart (M n) U (Q.term.retarget 0) part l t| ≤
      |Q.term.coefficient| *(M n).xs*(CH*W n*(g.tree.forkCost f+edgeBudget 0 as f+W n*(g.tree.forkCost R+edgeBudget 0 as R))) at Hhigh1
    rw [show g.tree.forkCost f=Q.tree.forkCost f from Hforkf,show g.tree.forkCost R=Q.tree.forkCost R from HforkR] at Hhigh1
    have Hlow0 l t hl ht:=hgridLow i V U Q.generation [.initial] Q.tree Q.term HV hU
      (by dsimp only [rBound];omega) (by simpa using HD) hV hiV hVstar hs hcutI hmi hmassstar hcut l t hl ht
    have Hlow1 l t hl ht:=hgridLow i V U Q.generation [.initial] g.tree (Q.term.retarget 0) HV.retarget hU
      hg (by simpa using HD) hV hiV hVstar hs hcutI hmi hmassstar hcut l t hl ht
    simp only [nativeResourceScale,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
      NativeResourceMark.savedScale,mul_one,NativeResourceTerm.retarget] at Hlow0 Hlow1
    let B:=2*CH*(M n).xs*cost+(M n).xs/2*lowPrice
    have hB:0 ≤ B:=by dsimp only [B];positivity
    have H0:=actual_minimum_normalized_fresh_resource_Taylor_abs_le (M n) U Q.generation Q.term ho hW
      (H:=|Q.term.coefficient| *((M n).xs*CH*W n*cost)) (L:=|Q.term.coefficient| *(M n).xs*W n*lowPrice)
      (by positivity) (by positivity)
      (by
        intro l t hl ht part
        convert Hhigh0 l t hl ht part using 1
        all_goals try dsimp only [cost]
        all_goals ring)
      (by
        intro l t hl ht
        convert Hlow0 l t hl ht using 1
        all_goals try dsimp only [lowPrice,initialError,as,NativeResourceTerm.retarget]
        all_goals ring)
    have H1:=actual_minimum_normalized_fresh_resource_Taylor_abs_le (M n) U Q.generation (Q.term.retarget 0) ho hW
      (H:=|Q.term.coefficient| *((M n).xs*CH*W n*cost)) (L:=|Q.term.coefficient| *(M n).xs*W n*lowPrice)
      (by positivity) (by positivity)
      (by
        intro l t hl ht part
        convert Hhigh1 l t hl ht part using 1
        all_goals try dsimp only [cost]
        all_goals ring)
      (by
        intro l t hl ht
        convert Hlow1 l t hl ht using 1
        all_goals try dsimp only [lowPrice,initialError,as,NativeResourceTerm.retarget]
        all_goals ring)
    have Herror:=actual_minimum_four_higher_Taylor_error_abs_le (M n) hCf hsource hxs1 Q ho hs hU hW hcK hB hstarK
      (by apply H0.trans_eq;dsimp only [B];ring)
      (by apply H1.trans_eq;dsimp only [B];ring)
    apply Herror.trans_eq
    dsimp only [BH,BL,B,cost,Cd]
    ring
  have Hsum:=nativeActualFourCenteredForest_profile_and_constant_sum_le ho Γ
    (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one ho U K Q p) hs (hs.le.trans hU) weight
    hCw HW hW.le (show 0 ≤ BH*(M n).xs by positivity) hBL depth children 2 Hleaves f R hf hR hflo hRlo
    (nativeActualOriginalFourHigherTaylorError (M n) U (W n)) Hrow
  have Hfamily (ff : ℕ→ℝ) (hfflo : ∀j,j<U→ff j=0) :
      (children.map (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost ff+edgeBudget 0 as ff))).sum = edgeBudget 0 as ff:=by
    have Hfork:=nativeActualInitialState_high_forkCost_zero (S:=Spin (dim n)×Bool)
      as i star U hi hs (hi.trans (hs.le.trans hU)) seedMass ff hfflo
    simp only [children,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    change |(1:ℝ)| *(root.tree.forkCost ff+edgeBudget 0 as ff)=_
    rw [show root.tree.forkCost ff=0 from Hfork]
    norm_num
  rw [Hfamily f hflo,Hfamily R hRlo] at Hsum
  have Hcoeff:(children.map (fun Q=>|Q.term.coefficient|)).sum=1:=by
    simp only [children,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    change |(1:ℝ)|=1
    norm_num
  rw [Hcoeff] at Hsum
  have Hrate : edgeBudget 0 as f+W n*edgeBudget 0 as R ≤
      ((dim n+1:ℕ):ℝ)^(-eta/256)*(M n).xs^2:=by
    have HReq : R=nativeOriginalHighTailEnvelope (dim n) U (M n).bf (M n).hf as
        (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp):=by funext j;rfl
    rw [show f=(fun j=>(R j)^(4/p)) from rfl,HReq]
    have H:=hgridTail U hU (by simpa only [hcanonical] using hcutlo) (4/p) htheta1 htheta2.le hdeficit
    simpa only [←hcanonical,NativeOverlapContext.N,eta,neg_div] using H
  apply Hsum.trans
  have Hfinal:=add_le_add_right (mul_le_mul_of_nonneg_left Hrate (show 0 ≤ 2*(BH*(M n).xs)*Vp by positivity)) (2*BL*Vv*1)
  have Hfinal' : 2*(BH*(M n).xs)*Vp*(edgeBudget 0 as f+W n*edgeBudget 0 as R)+2*BL*Vv*1 ≤
      2*(BH*(M n).xs)*Vp*(((dim n+1:ℕ):ℝ)^(-eta/256)*(M n).xs^2)+2*BL*Vv*1:=by
    convert Hfinal using 1 <;> ring
  apply Hfinal'.trans
  have Hinitial:=mul_le_mul_of_nonneg_right (show 2*Vv/Cd*CiLow ≤ 2*Vv/Cd*CiLow+1 by linarith)
    (show 0 ≤ (M n).xs^2*initialError by positivity)
  have Htotal:=add_le_add_right Hinitial (err n*(M n).xs^3)
  convert Htotal using 1 <;> dsimp only [err,BH,BL,lowPrice,initialError,as] <;> ring

end OAI.SKFluctuations.Cavity
