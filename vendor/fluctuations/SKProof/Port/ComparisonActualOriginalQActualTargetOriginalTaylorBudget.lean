module

public import SKProof.Port.ComparisonActualOriginalQPullbackFourProducers
public import SKProof.Port.ComparisonActualOriginalQTargetHighTailPowers
public import SKProof.Port.ComparisonActualOriginalQOriginalTargetReadout
public import SKProof.Port.ComparisonActualOriginalQOriginalTargetB0
public import SKProof.Port.ComparisonActualOriginalQOriginalTaylorProfiles
public import SKProof.Port.ComparisonActualOriginalQGaCurrentPrerequisites
public import SKProof.Port.ComparisonActualOriginalQCavityCategoryReduction
public import SKProof.Port.ComparisonActualOriginalQActualTargetHighTaylorRate
public import SKProof.Port.ComparisonActualOriginalQActualTargetJointRestorationRates
public import SKProof.Port.ComparisonActualOriginalQActualTargetLongitudinalRestorationRate

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option linter.unusedVariables false
open OAI.SKFluctuations.LaplaceWindowFormalization.ActualThetaZeroOverlapMinimum
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 30000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_regular_target_original_Taylor_integral_budget_original_q
    (Bclock Temp Cf Ccut : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct)
    (hCs : 0≤Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1)≤c) :
    ∃C : ℝ,0<C ∧ ∀ᶠn in atTop,
      ∀(M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (_hclock : NativePullbackClockRegularity M.alpha.val.val M.b M.h M.data.rmin 1),
        M.data.s≤1/4 → M.data.s≤M.xs → 64*M.data.s≤c*M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf →
        M.xs^2≤Cs*laplaceComparisonStrength M.data.d M.lam M.xs → M.directTestWorkingScale≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(i U : ℕ) (x : ℝ),i<U → U≤as.length → M.xs≤x → x≤M.directTestWorkingScale →
          Ccut*x≤1 → 2*c*x≤partitionPoint 0 as U → partitionPoint 0 as U≤Ccut*x →
          |nativeActualTargetOriginalTaylorPart_original_q M as i U|≤
            C*(x^2*(nativeOriginalCutLowErrorRadius n M.sweepBf M.sweepHf as i+1/(n+1:ℕ))+
              x*(∫u in 0..Ccut*x,Real.sqrt (orderedPathB (n+1) M.sweepBf M.sweepHf u-
                (orderedPathS (n+1) M.sweepBf M.sweepHf u)^2))+
              M.data.N^(-(actualMassSavingExponent m delta/256))*x^3) := by
  obtain ⟨CB,hCB,HB⟩:=eventually_actual_minimum_inherited_second_low_sole_root_target_B0_integral_budget_original_q
    (D:=D) Bclock Temp Cf Ccut hTemp hCf hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨CH,hCH,HH⟩:=eventually_actual_regular_target_constant_fresh_HIGH_parts_rate_original_q
    (D:=D) Bclock Temp Cf Ccut hTemp hCf hCcut hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  obtain ⟨CL,hCL,HL⟩:=eventually_actual_minimum_inherited_target_third_LOW_integral_budget_original_q
    (D:=D) Bclock Temp Cf Ccut hTemp hCf hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨C2,hC2,H2⟩:=eventually_actual_regular_target_constant_fresh_C_two_HIGH_rate_original_q
    (D:=D) Bclock Temp Cf Ccut hTemp hCf hCcut hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  obtain ⟨C4,hC4,H4⟩:=eventually_actual_regular_target_constant_fresh_FOUR_G_LOW_rate_original_q
    (D:=D) Bclock Temp Cf Ccut hTemp hCf hCcut hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  obtain ⟨Cq,hCq,Hq⟩:=eventually_actual_minimum_inherited_constant_low_restoration_ledger_original_q
    (D:=D) 2 Bclock Temp Cf Ccut hTemp hCf hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨CR,hCR,HR⟩:=eventually_actual_regular_target_constant_longitudinal_restoration_rate_original_q
    (D:=D) Bclock Temp Cf Ccut hTemp hCf hCcut hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  obtain ⟨CK,hCK,HK⟩:=eventually_actual_inherited_continuum_clock_mass_upper_original_q
    (D:=D) Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cerr:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp
  have hCe : 0≤Cerr:=actualLowErrorComparisonConstant_nonneg _ hTemp
  let CQ:=24*absJetVariation 4 2*(Cq*(1+Ccut))^2
  have hCQ : 0≤CQ:=by dsimp only [CQ];have :=absJetVariation_nonneg 4 2;positivity
  let C:=CB*Cerr+CL*Cerr+CQ*Cerr+2*CH+C2+C4+2*CK*(1+Ccut)*CR+1
  have hC : 0<C:=by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [HB,HH,HL,H2,H4,Hq,HR,HK] with n hnB hnH hnL hn2 hn4 hnq hnR hnK
  intro M hclock hs0 hsxs hs64 HS hsmall hW1 L us hus hret hmesh
  have hxs1:=M.canonical_direct_test_band_ge_scale.trans hW1
  filter_upwards [hnB M hs0 hsxs HS hxs1 L us hus hret hmesh,
    hnH M hclock hs0 hsxs hs64 HS hsmall hW1 L us hus hret hmesh,
    hnL M hs0 hsxs HS hxs1 L us hus hret hmesh,
    hn2 M hclock hs0 hsxs hs64 HS hsmall hW1 L us hus hret hmesh,
    hn4 M hclock hs0 hsxs hs64 HS hsmall hW1 L us hus hret hmesh,
    hnq M hs0 hsxs HS hxs1 L us hus hret hmesh,
    hnR M hclock hs0 hsxs hs64 HS hsmall hW1 L us hus hret hmesh]
      with jGrid hB hH hL h2 h4 hq hR
  dsimp only at hB hH hL h2 h4 hq hR ⊢
  intro i U x hi hU hxsx hxW hcut1 hcutlo hcut
  let as:=finiteCutMasses us jGrid
  let T:=single (S:=Spin n×Bool) as
  let s:=singleSlot (S:=Spin n×Bool) as
  let g:=nativeFreshAtSlot T 0 s i
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  let di:=nativeOriginalCutLowErrorRadius n M.sweepBf M.sweepHf as i+1/(n+1:ℕ)
  let I:=(∫u in 0..Ccut*x,Real.sqrt (orderedPathB (n+1) M.sweepBf M.sweepHf u-(orderedPathS (n+1) M.sweepBf M.sweepHf u)^2))
  let save:=M.data.N^(-(actualMassSavingExponent m delta/256))
  have hx : 0<x:=M.hxs.trans_le hxsx
  have hx1 : x≤1:=hxW.trans hW1
  have hdi : 0≤di:=add_nonneg (Real.sqrt_nonneg _) (by positivity)
  have hI : 0≤I:=intervalIntegral.integral_nonneg (mul_nonneg hCcut hx.le) (fun _ _=>Real.sqrt_nonneg _)
  have hsave : 0≤ save:=Real.rpow_nonneg M.data.hN.le _
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hg : g.tree.leaves≤2:=by
    have H:=T.markedAttach_leaves 0 g (nativeFreshAtSlot_mem _ _ _ _)
    simpa only [T,single_leaves_exact] using H
  have hsplit : g.tree.splitIndex (g.embed s) g.mark=i:=by
    rw [g.tree.splitIndex_symm,nativeFreshAtSlot_split,T.splitIndex_self,Nat.min_eq_left (hi.le.trans hU)]
  have haz : g.tree.splitIndex (g.embed s) g.mark<U:=hsplit.trans_lt hi
  have HBi:=hB i U x hU hi hxsx hxW hcut
  rw [min_eq_left hcut1] at HBi
  have HLi (l t : ℝ) (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1):=
    hL i U x hi hU hxsx hx1 hcut1 hcut l t hl ht
  have HHi (l t : ℝ) (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1) (part : Fin 3):=
    hH i U hi hU x hxsx hxW hcutlo hcut 0 (g.embed s) g.mark l t hl ht part
  have H2i:=h2 i U hi hU x hxsx hxW hcutlo hcut 0 (g.embed s) g.mark haz
  have H4i:=h4 i U hi hU x hxsx hxW hcutlo hcut 0 (g.embed s) g.mark
  have HQi:=hq U g.tree hU hg x hxsx hcut (g.embed s) g.mark haz
  rw [hsplit] at HQi
  have HQi' : |nativeCenteredLowGammaLowRestoration n q U b h K S g.tree (fun _=>1) (g.embed s) g.mark|≤
      CQ*x^2*Cerr*di:=by
    apply HQi.trans_eq
    dsimp only [CQ,Cerr,di]
    ring!
  have HRi (a : g.tree.Slot):=hR i U x hi hU hxsx hxW hcutlo hcut a
  have HKi : K i≤CK*(1+Ccut)*x:=by
    have HH:=hnK M hs0 hsxs HS (partitionPoint 0 as i) (partitionPoint_mem as ho i)
    change K i≤CK*(M.xs+partitionPoint 0 as i) at HH
    have Hmass:=(partitionPoint_mono as ho hi.le).trans hcut
    nlinarith only [HH,hCK,hxsx,Hmass]
  have Hchi:=actual_minimum_continuum_chi_mem_unit_on_any_grid_original_q M as ho U (by omega) hU
  have HK0:=native_continuum_mixed_clock_nonneg n M.sweepBf M.sweepHf M.inherited_bf_monotone M.inherited_hf_monotone as ho i
  have HRsum : |chi*K i*(nativeOriginalLongitudinalRestoration n q U b h K S g.tree (fun _=>1) (g.embed s)+
      nativeOriginalLongitudinalRestoration n q U b h K S g.tree (fun _=>1) g.mark)|≤
      (2*CK*(1+Ccut)*CR)*save*x^3:=by
    have HBsum:=(abs_add_le _ _).trans (add_le_add (HRi (g.embed s)) (HRi g.mark))
    have Hcoef:=mul_le_mul Hchi.2 HKi HK0 (by norm_num : (0:ℝ)≤1)
    simp only [one_mul] at Hcoef
    rw [abs_mul,abs_of_nonneg (mul_nonneg Hchi.1 HK0)]
    apply (mul_le_mul Hcoef HBsum (abs_nonneg _) (by positivity)).trans_eq
    dsimp only [save]
    ring
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepBf u:ℝ)≤M.sweepBf v from M.inherited_bf_monotone hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepHf u:ℝ)≤M.sweepHf v from M.inherited_hf_monotone hu hv huv) as ho
  have HTay:=native_actual_taylor_remainder_abs_le_HIGH_LOW n q U b h K g.tree ho (fun _=>1) (g.embed s) g.mark
    (fun j z=>by cases z <;> exact NNReal.coe_nonneg _)
    (fun z=>by cases z <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _)
    (native_continuum_mixed_clock_nonneg n M.sweepBf M.sweepHf M.inherited_bf_monotone M.inherited_hf_monotone as ho)
    hbm hhm (native_continuum_mixed_clock_monotone n M.sweepBf M.sweepHf M.inherited_bf_monotone M.inherited_hf_monotone as ho)
    (CH*save*x^3) (CL*x^2*Cerr*di+CL*x*Cerr*I) (by positivity) (by positivity) HHi HLi
  have HBsource : (1/2:ℝ)*nativeRetainedCenteredCoefficient n q U b h K g.tree (fun _=>1) [g.embed s,g.mark] 2 0=
      nativeSecondLowJointLedger n q U b h K g.tree (fun _=>1) [g.embed s,g.mark]/2:=by
    rw [native_second_low_centered_eq_scalar_subtraction n q U b h K g.tree ho (fun _=>1)
      (g.embed s) g.mark hU haz,←native_second_low_joint_ledger_eq_scalar_subtraction n q U b h K g.tree ho (fun _=>1) [g.embed s,g.mark]]
    ring
  have Habs : |nativeActualOriginalForwardTaylorError n q U b h K S g.tree (fun _=>1) (g.embed s) g.mark|≤
      |nativeSecondLowJointLedger n q U b h K g.tree (fun _=>1) [g.embed s,g.mark]/2|+
      |nativeActualTaylorRemainder n q U b h K g.tree (fun _=>1) (g.embed s) g.mark|+
      |nativeCenteredLowGammaHighSecondRemainder n q U b h K S g.tree (fun _=>1) (g.embed s) g.mark|+
      |nativeCenteredLowGammaLowRestoration n q U b h K S g.tree (fun _=>1) (g.embed s) g.mark|+
      |chi*K i*(nativeOriginalLongitudinalRestoration n q U b h K S g.tree (fun _=>1) (g.embed s)+
        nativeOriginalLongitudinalRestoration n q U b h K S g.tree (fun _=>1) g.mark)|+
      |nativeOriginalGKernelLowRestoration n q U b h K S g.tree (fun _=>1) (g.embed s) g.mark (restCenteredLowKernel n U b S)|:=by
    unfold nativeActualOriginalForwardTaylorError nativeActualHigherAllocatedRemainder
    rw [HBsource,hsplit]
    exact (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add
      ((abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)) le_rfl)) le_rfl)
  have Htotal:=add_le_add (add_le_add (add_le_add (add_le_add (add_le_add HBi HTay) H2i) HQi') HRsum) H4i
  have Hbound : |nativeActualOriginalForwardTaylorError n q U b h K S g.tree (fun _=>1) (g.embed s) g.mark|≤
      C*(x^2*di+x*I+save*x^3):=by
    have Hnumeric : CB*x^2*Cerr*di+CB*x*Cerr*I+
        (2*(CH*save*x^3)+(CL*x^2*Cerr*di+CL*x*Cerr*I)/2)+
        C2*save*x^3+CQ*x^2*Cerr*di+(2*CK*(1+Ccut)*CR)*save*x^3+C4*save*x^3≤
        C*(x^2*di+x*I+save*x^3):=by
      let A:=CB*Cerr+CL*Cerr+CQ*Cerr
      let B:=2*CH+C2+C4+2*CK*(1+Ccut)*CR
      have hA : 0≤A:=by dsimp only [A];positivity
      have hB : 0≤B:=by dsimp only [B];positivity
      have Hp1 : 0≤(B+1)*(x^2*di+x*I):=by positivity
      have Hp2 : 0≤(A+1)*(save*x^3):=by positivity
      have Hp3 : 0≤CL*Cerr*(x^2*di+x*I)/2+CQ*Cerr*x*I:=by positivity
      dsimp only [C,A,B] at Hp1 Hp2 Hp3 ⊢
      nlinarith only [Hp1,Hp2,Hp3]
    exact Habs.trans (Htotal.trans Hnumeric)
  have HScenter : S=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as:=by
    funext j
    exact native_ordered_source_center_eq_completed n M.sweepBf M.sweepHf M.inherited_bf_monotone
      M.inherited_hf_monotone (partitionPoint_mem as ho j)
  rw [HScenter] at Hbound
  exact Hbound

end OAI.SKFluctuations.Cavity
