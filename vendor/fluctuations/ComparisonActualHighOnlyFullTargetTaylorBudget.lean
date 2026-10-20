module

public import ComparisonActualHighOnlyFreshTargetHighBudget
public import ComparisonSignedCavityActualTaylorHighLowBudget

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 42000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
theorem eventually_actual_high_only_target_original_Taylor_full_thermal_budget
    (Bclock Temp Cf Ccut : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0<C ∧ ∀ᶠn in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf →
        M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(i U : ℕ) (x : ℝ),i<U → U≤as.length → M.xs≤x → x≤M.canonicalDirectTestBandScale → x≤1 →
          Ccut*x≤1 → partitionPoint 0 as U≤Ccut*x →
          |nativeActualTargetOriginalTaylorPart_high_only M as i U|≤
            C*(x^2*(nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ))+
              x*((∫u in 0..1,Real.sqrt (orderedPathB (n+1) M.bf M.hf u-
                (orderedPathS (n+1) M.bf M.hf u)^2))+3/(n+1:ℕ))) := by
  obtain ⟨CB,hCB,HB⟩:=eventually_actual_minimum_inherited_second_low_sole_root_target_B0_integral_budget_high_only
    (D:=D) Bclock Temp Cf Ccut hTemp hCf hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨CH,hCH,HH⟩:=eventually_actual_regular_target_constant_fresh_HIGH_parts_whole_budget_high_only
    (D:=D) Bclock Temp Cf Ccut hTemp hCf hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨CL,hCL,HL⟩:=eventually_actual_minimum_inherited_target_third_LOW_integral_budget_high_only
    (D:=D) Bclock Temp Cf Ccut hTemp hCf hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨C2,hC2,H2⟩:=eventually_actual_regular_target_constant_fresh_C_two_HIGH_whole_budget_high_only
    (D:=D) Bclock Temp Cf Ccut hTemp hCf hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨C4,hC4,H4⟩:=eventually_actual_regular_target_constant_fresh_FOUR_G_LOW_whole_budget_high_only
    (D:=D) Bclock Temp Cf Ccut hTemp hCf hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cq,hCq,Hq⟩:=eventually_actual_minimum_inherited_constant_low_restoration_ledger_high_only
    (D:=D) 2 Bclock Temp Cf Ccut hTemp hCf hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨CR,hCR,HR⟩:=eventually_actual_regular_target_constant_longitudinal_restoration_whole_budget_high_only
    (D:=D) Bclock Temp Cf Ccut hTemp hCf hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨CK,hCK,HK⟩:=eventually_actual_inherited_continuum_clock_mass_upper_high_only
    (D:=D) Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cerr:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp
  have hCe : 0≤Cerr:=actualLowErrorComparisonConstant_nonneg _ hTemp
  let CQ:=24*absJetVariation 4 2*(Cq*(1+Ccut))^2
  have hCQ : 0≤CQ:=by dsimp only [CQ];have :=absJetVariation_nonneg 4 2;positivity
  let C:=(CB+CL+CQ+2*CH+C2+C4+2*CK*(1+Ccut)*CR)*Cerr+1
  have hC : 0<C:=by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [HB,HH,HL,H2,H4,Hq,HR,HK] with n hnB hnH hnL hn2 hn4 hnq hnR hnK
  intro M hs0 hsxs HS hxs1 L us hus hret hmesh
  filter_upwards [hnB M hs0 hsxs HS hxs1 L us hus hret hmesh,
    hnH M hs0 hsxs HS hxs1 L us hus hret hmesh,
    hnL M hs0 hsxs HS hxs1 L us hus hret hmesh,
    hn2 M hs0 hsxs HS hxs1 L us hus hret hmesh,
    hn4 M hs0 hsxs HS hxs1 L us hus hret hmesh,
    hnq M hs0 hsxs HS hxs1 L us hus hret hmesh,
    hnR M hs0 hsxs HS hxs1 L us hus hret hmesh,
    actual_original_high_l1_density_on_all_final_nets_high_only M]
      with jGrid hB hH hL h2 h4 hq hR hTail
  dsimp only at hB hH hL h2 h4 hq hR ⊢
  intro i U x hi hU hxsx hxW hx1 hcut1 hcut
  let as:=finiteCutMasses us jGrid
  let T:=single (S:=Spin n×Bool) as
  let s:=singleSlot (S:=Spin n×Bool) as
  let g:=nativeFreshAtSlot T 0 s i
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  let di:=nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ)
  let I:=(∫u in 0..1,Real.sqrt (orderedPathB (n+1) M.bf M.hf u-(orderedPathS (n+1) M.bf M.hf u)^2))+3/(n+1:ℕ)
  have hx : 0<x:=M.hxs.trans_le hxsx
  have hdi : 0≤di:=add_nonneg (Real.sqrt_nonneg _) (by positivity)
  have hI : 0≤I:=add_nonneg (intervalIntegral.integral_nonneg zero_le_one (fun _ _=>Real.sqrt_nonneg _)) (by positivity)
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hg : g.tree.leaves≤2:=by
    have H:=T.markedAttach_leaves 0 g (nativeFreshAtSlot_mem _ _ _ _)
    simpa only [T,single_leaves_exact] using H
  have hsplit : g.tree.splitIndex (g.embed s) g.mark=i:=by
    rw [g.tree.splitIndex_symm,nativeFreshAtSlot_split,T.splitIndex_self,Nat.min_eq_left (hi.le.trans hU)]
  have haz : g.tree.splitIndex (g.embed s) g.mark<U:=hsplit.trans_lt hi
  have HIlo : (∫u in 0..Ccut*x,Real.sqrt (orderedPathB (n+1) M.bf M.hf u-
      (orderedPathS (n+1) M.bf M.hf u)^2))≤I:=by
    apply (intervalIntegral.integral_mono_interval le_rfl (mul_nonneg hCcut hx.le) hcut1
      (ae_of_all _ (fun _=>Real.sqrt_nonneg _))
      (native_intervalIntegrable_sqrt_of_intervalIntegrable (high_only_original_thermal_intervalIntegrable M))).trans
    exact le_add_of_nonneg_right (by positivity)
  have HBi0:=hB i U x hU hi hxsx hxW hcut
  rw [min_eq_left hcut1] at HBi0
  have HBi := HBi0.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left HIlo (show 0≤CB*x*Cerr by positivity)))
  let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp
  have Hhigh : edgeBudget 0 as R≤Cerr*I:=by
    have Heq : R=(fun j=>Cerr*(if j<U then 0 else nativeOriginalCutLowErrorRadius n M.bf M.hf as j+1/(n+1:ℕ))+0*(0:ℝ)):=by
      funext j
      dsimp only [R,nativeOriginalHighErrorEnvelope,Cerr]
      split_ifs <;> simp
    rw [Heq,actual_low_edgeBudget_linear]
    simp only [zero_mul,add_zero]
    apply mul_le_mul_of_nonneg_left _ hCe
    have HT:=hTail us hus U hU
    have HTmono:=intervalIntegral.integral_mono_interval (partitionPoint_mem as ho U).1
      (partitionPoint_mem as ho U).2 le_rfl (ae_of_all _ (fun _=>Real.sqrt_nonneg _))
      (native_intervalIntegrable_sqrt_of_intervalIntegrable (high_only_original_thermal_intervalIntegrable M))
    exact HT.trans (add_le_add HTmono le_rfl)
  have HLi (l t : ℝ) (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1):=
    (hL i U x hi hU hxsx hx1 hcut1 hcut l t hl ht).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left HIlo (show 0≤CL*x*Cerr by positivity)))
  have HHi (l t : ℝ) (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1) (part : Fin 3):=
    (hH i U hi hU x hxsx hx1 hcut 0 (g.embed s) g.mark l t hl ht part).trans
      (mul_le_mul_of_nonneg_left Hhigh (show 0≤CH*x by positivity))
  have H2i:=(h2 i U hi hU x hxsx hx1 hcut 0 (g.embed s) g.mark haz).trans
    (mul_le_mul_of_nonneg_left Hhigh (show 0≤C2*x by positivity))
  have H4i:=(h4 i U hi hU x hxsx hx1 hcut 0 (g.embed s) g.mark).trans
    (mul_le_mul_of_nonneg_left Hhigh (show 0≤C4*x by positivity))
  have HQi:=hq U g.tree hU hg x hxsx hcut (g.embed s) g.mark haz
  rw [hsplit] at HQi
  have HQi' : |nativeCenteredLowGammaLowRestoration n q U b h K S g.tree (fun _=>1) (g.embed s) g.mark|≤
      CQ*x^2*Cerr*di:=by
    apply HQi.trans_eq
    dsimp only [CQ,Cerr,di]
    ring!
  have HRi (a : g.tree.Slot):=(hR i U x hi hU hxsx hx1 hcut a).trans
    (mul_le_mul_of_nonneg_left Hhigh hCR.le)
  have HKi : K i≤CK*(1+Ccut)*x:=by
    have HH:=hnK M hs0 hsxs HS (partitionPoint 0 as i) (partitionPoint_mem as ho i)
    change K i≤CK*(M.xs+partitionPoint 0 as i) at HH
    have Hmass:=(partitionPoint_mono as ho hi.le).trans hcut
    nlinarith only [HH,hCK,hxsx,Hmass]
  have Hchi:=actual_minimum_continuum_chi_mem_unit_on_any_grid_high_only M as ho U (by omega) hU
  have HK0:=native_continuum_mixed_clock_nonneg n M.bf M.hf M.bf_monotone M.hf_monotone as ho i
  have HRsum : |chi*K i*(nativeOriginalLongitudinalRestoration n q U b h K S g.tree (fun _=>1) (g.embed s)+
      nativeOriginalLongitudinalRestoration n q U b h K S g.tree (fun _=>1) g.mark)|≤
      (2*CK*(1+Ccut)*CR)*Cerr*x*I:=by
    have HBsum:=(abs_add_le _ _).trans (add_le_add (HRi (g.embed s)) (HRi g.mark))
    have Hcoef:=mul_le_mul Hchi.2 HKi HK0 (by norm_num : (0:ℝ)≤1)
    simp only [one_mul] at Hcoef
    rw [abs_mul,abs_of_nonneg (mul_nonneg Hchi.1 HK0)]
    apply (mul_le_mul Hcoef HBsum (abs_nonneg _) (by positivity)).trans_eq
    ring
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.bf u:ℝ)≤M.bf v from M.bf_monotone hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.hf u:ℝ)≤M.hf v from M.hf_monotone hu hv huv) as ho
  have HTay:=native_actual_taylor_remainder_abs_le_HIGH_LOW n q U b h K g.tree ho (fun _=>1) (g.embed s) g.mark
    (fun j z=>by cases z <;> exact NNReal.coe_nonneg _)
    (fun z=>by cases z <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _)
    (native_continuum_mixed_clock_nonneg n M.bf M.hf M.bf_monotone M.hf_monotone as ho)
    hbm hhm (native_continuum_mixed_clock_monotone n M.bf M.hf M.bf_monotone M.hf_monotone as ho)
    (CH*x*Cerr*I) (CL*x^2*Cerr*di+CL*x*Cerr*I) (by positivity) (by positivity)
    (fun l t hl ht part=>by simpa only [mul_assoc] using HHi l t hl ht part) HLi
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
      C*(x^2*di+x*I):=by
    have Hnumeric : CB*x^2*Cerr*di+CB*x*Cerr*I+
        (2*(CH*x*Cerr*I)+(CL*x^2*Cerr*di+CL*x*Cerr*I)/2)+
        C2*x*Cerr*I+CQ*x^2*Cerr*di+(2*CK*(1+Ccut)*CR)*Cerr*x*I+C4*x*Cerr*I≤
        C*(x^2*di+x*I):=by
      have Hp1 : 0≤(2*CH+C2+C4+2*CK*(1+Ccut)*CR)*Cerr*x^2*di:=by positivity
      have Hp2 : 0≤CQ*Cerr*x*I:=by positivity
      have Hp3 : 0≤CL*Cerr*(x^2*di+x*I)/2:=by positivity
      have Hp4 : 0≤x^2*di+x*I:=by positivity
      dsimp only [C] at ⊢
      nlinarith only [Hp1,Hp2,Hp3,Hp4]
    exact Habs.trans (Htotal.trans (by convert Hnumeric using 1 <;> dsimp only [Cerr,di] <;> ring))
  have HScenter : S=nativePhysicalResourceCenter n M.bf M.hf as:=by
    funext j
    exact native_ordered_source_center_eq_completed n M.bf M.hf M.bf_monotone
      M.hf_monotone (partitionPoint_mem as ho j)
  rw [HScenter] at Hbound
  exact Hbound

end OAI.SKFluctuations.Cavity
