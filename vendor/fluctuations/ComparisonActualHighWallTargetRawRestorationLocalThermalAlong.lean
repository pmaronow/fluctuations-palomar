module

public import ComparisonActualHighWallTargetRawB0LocalThermalAlong
public import ComparisonActualHighWallUnifiedResourceJointHigh
public import ComparisonActualHighWallResourceJointLowRestoration
public import ComparisonActualHighWallResourceLongitudinalFromMinimum
public import ComparisonActualHighWallJointLowCubicPrice
public import ComparisonActualHighWallContinuumClockMass

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 48000000
set_option backward.isDefEq.respectTransparency false

private theorem wall_raw_restoration_local_profile_algebra
    {a b c d e X Y Z : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (he : 0 ≤ e) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hZ : 0 ≤ Z) :
    a*X+a*Y+b*Z+c*X+d*Z+e*Z ≤ (a+b+c+d+e+1)*(X+Y+Z) := by
  nlinarith only [mul_nonneg ha hZ,mul_nonneg hb hX,mul_nonneg hb hY,
    mul_nonneg hc hY,mul_nonneg hc hZ,mul_nonneg hd hX,mul_nonneg hd hY,
    mul_nonneg he hX,mul_nonneg he hY,hX,hY,hZ]

theorem eventually_actual_high_wall_original_target_raw_restoration_local_thermal_profile_along
    (dOrder : ℕ) (hd : 0 < dOrder) (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Cmass Ccut : ℝ) (hCm : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn in atTop,
      ∀M : ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock,
      M.xs=M.data.d → ∀(L : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs → ∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      ∀(i U : ℕ),i < U → U ≤ as.length →
        partitionPoint 0 as i ≤ Cmass*M.data.d → partitionPoint 0 as U ≤ Ccut*M.data.d →
      let g:=nativeFreshAtSlot (single (S:=Spin (dim n)×Bool) as) 0 (singleSlot as) i
      let R:=M.data.highErrorEnvelope M.alpha as U
      actualGeneralTargetRawRestorationBudget (n:=dim n) M.bf M.hf as i U ≤
        C*(M.data.d^2*(nativeOriginalCutLowErrorRadius (dim n) M.bf M.hf as i+1/(dim n+1:ℕ))+
          M.data.d*(∫u in 0..min (Ccut*M.data.d) 1,Real.sqrt (orderedPathB (dim n+1) M.bf M.hf u-
            (orderedPathS (dim n+1) M.bf M.hf u)^2))+
          M.data.d*(g.tree.forkCost (fun l=>(R l)^(4/p))+edgeBudget 0 as (fun l=>(R l)^(4/p))+
            M.data.d*(g.tree.forkCost R+edgeBudget 0 as R))) := by
  obtain ⟨Cb,hCb,HB⟩:=eventually_actual_high_wall_original_target_raw_B0_uniform_local_thermal_budget_along
    (D:=D) Bclock Ccut hCcut hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim
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
  let CB:=actualLowErrorComparisonConstant (2*max Bclock 0) (max Bclock 0)
  have hCB : 0≤ CB:=actualLowErrorComparisonConstant_nonneg _ (le_max_right _ _)
  let C:=Cb+Cj+C4+Cq*CB+2*CK*(1+Cmass)*Cl+1
  refine ⟨C,by dsimp only [C];positivity,?_⟩
  filter_upwards [HB,hdim.eventually HJ,hdim.eventually H4,hdim.eventually HQ,
    hdim.eventually HL,hdim.eventually HK] with n hnB hnJ hn4 hnQ hnL hnK
  intro M hwork L us hus hret hmesh
  filter_upwards [hnB M hwork L us hus hret hmesh,hnJ M hwork L us hus hret hmesh,
    hn4 M hwork L us hus hret hmesh,hnQ M hwork L us hus hret hmesh,
    hnL M hwork L us hus hret hmesh]
      with jGrid hjB hjJ hj4 hjQ hjL
  dsimp only at hjB hjJ hj4 hjQ hjL ⊢
  intro i U hs hU hmass hcut
  let as:=finiteCutMasses us jGrid
  let T:=single (S:=Spin (dim n)×Bool) as
  let s:=singleSlot (S:=Spin (dim n)×Bool) as
  let g:=nativeFreshAtSlot T 0 s i
  let P:=actualGeneralTargetFreshConstantResource (n:=dim n) as i
  let R:=M.data.highErrorEnvelope M.alpha as U
  let profile:=g.tree.forkCost (fun l=> (R l)^(4/p))+edgeBudget 0 as (fun l=> (R l)^(4/p))+
    M.data.d*(g.tree.forkCost R+edgeBudget 0 as R)
  let K:=nativeContinuumMixedClock (dim n) M.bf M.hf as
  have hdpos : 0< M.data.d:=M.data.hd
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hU' : U≤ as.length:=by simpa only [as] using hU
  have hmass' : partitionPoint 0 as i≤ Cmass*M.data.d:=by simpa only [as] using hmass
  have hcut' : partitionPoint 0 as U≤ Ccut*M.data.d:=by simpa only [as] using hcut
  have hzero : partitionPoint 0 as 0≤ Cmass*M.data.d:=by
    simpa only [partitionPoint,partitionValues_zero,id_eq] using mul_nonneg hCm hdpos.le
  have hg : g.tree.leaves≤ 2:=by
    have H:=T.markedAttach_leaves 0 g (nativeFreshAtSlot_mem T 0 s i)
    simpa only [T,single_leaves_exact] using H
  have Hsplit : g.tree.splitIndex (g.embed s) g.mark=i:=by
    rw [g.tree.splitIndex_symm,nativeFreshAtSlot_split,T.splitIndex_self,Nat.min_eq_left (hs.le.trans hU')]
  have hP : NativeActualResourceGenerated 0 i U [] 0 g.tree P:=
    actual_general_target_fresh_constant_resource_generated as i U hU'
  have hcoef : P.coefficient=1:=rfl
  have hR l : 0≤ R l:=M.data.highErrorEnvelope_nonneg M.alpha as U l
  have hprofile : 0≤ profile:=add_nonneg (add_nonneg (g.tree.forkCost_nonneg (fun l=> Real.rpow_nonneg (hR l) _))
    (edgeBudget_nonneg ho (fun l=> Real.rpow_nonneg (hR l) _)))
    (mul_nonneg hdpos.le (add_nonneg (g.tree.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)))
  have Hj:=hjJ 0 i U 0 [] g.tree P hP (Nat.zero_le _) hs hU' hg (by simp) hzero hmass' hcut'
    (g.embed s) g.mark (by rw [Hsplit];exact hs)
  have H4p:=hj4 0 i U 0 [] g.tree P hP (Nat.zero_le _) hs hU' hg (by simp) hzero hmass' hcut'
    (g.embed s) g.mark (by rw [Hsplit];exact hs)
  have Hq:=hjQ 0 i U 0 [] g.tree P hP (Nat.zero_le _) hs hU' hg (by simp) hzero hmass' hcut'
    (g.embed s) g.mark (by rw [Hsplit];exact hs)
  have Hl (a : g.tree.Slot):=hjL 0 i U 0 [] g.tree P hP (Nat.zero_le _) hs hU' hg (by simp)
    hzero hmass' hcut' a
  simp only [pow_zero,one_mul,hcoef,abs_one,nativeResourceScale,List.map_nil,List.prod_nil,mul_one] at Hj H4p Hq
  have Hld (a : g.tree.Slot) : |actualGeneralResourceLongitudinalRestoration M.bf M.hf U P a|≤ Cl*profile:=by
    simpa only [pow_zero,one_mul,hcoef,abs_one,nativeResourceScale,List.map_nil,List.prod_nil,mul_one,profile,R,as,g,T,s] using Hl a
  let di:=nativeOriginalCutLowErrorRadius (dim n) M.bf M.hf as i+1/(dim n+1:ℕ)
  let density:=(∫u in 0..min (Ccut*M.data.d) 1,Real.sqrt (orderedPathB (dim n+1) M.bf M.hf u-
    (orderedPathS (dim n+1) M.bf M.hf u)^2))
  have hdi : 0 ≤ di:=add_nonneg (Real.sqrt_nonneg _) (by positivity)
  have hdensity : 0 ≤ density:=by
    apply intervalIntegral.integral_nonneg (le_min (mul_nonneg hCcut hdpos.le) zero_le_one)
    intro u _
    exact Real.sqrt_nonneg _
  have Hrad : actualLowErrorComparisonConstant (2*M.data.T) M.data.T*di ≤ CB*di:=
    mul_le_mul_of_nonneg_right (actual_wall_low_error_comparison_constant_le
      (M.data.hepsilon.1.trans M.data.hepsilon.2).le (M.hT.trans (le_max_left Bclock 0))) hdi
  rw [Hsplit] at Hq
  have Hq' : |actualGeneralTargetRawJointLowPart (n:=dim n) M.bf M.hf as i U| ≤ Cq*CB*M.data.d^2*di:=by
    apply Hq.trans
    have HH:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right Hrad (sq_nonneg M.data.d)) hCq.le
    convert HH using 1 <;> ring
  have HK : K i≤ CK*(1+Cmass)*M.data.d:=by
    have H:=hnK M hwork as ho i
    rw [hwork] at H
    change K i≤ CK*(M.data.d+partitionPoint 0 as i) at H
    nlinarith only [H,mul_le_mul_of_nonneg_left hmass' hCK.le]
  have HK0 : 0≤ K i:=native_continuum_mixed_clock_nonneg (dim n) M.bf M.hf
    (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) as ho i
  have Hchi:=actual_general_continuum_chi_mem_unit_on_any_grid (n:=dim n) M.bf M.hf
    (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) as ho U (by omega) hU'
  have Hlp : |actualGeneralTargetRawLongitudinalPart (n:=dim n) M.bf M.hf as i U|≤
      2*CK*(1+Cmass)*Cl*M.data.d*profile:=by
    unfold actualGeneralTargetRawLongitudinalPart
    dsimp only
    rw [abs_mul,abs_of_nonneg (mul_nonneg Hchi.1 HK0)]
    have Hcoeff:=mul_le_mul Hchi.2 HK HK0 (by norm_num : (0:ℝ)≤ 1)
    simp only [one_mul] at Hcoeff
    have Hsum:=(abs_add_le _ _).trans (add_le_add (Hld (g.embed s)) (Hld g.mark))
    have HH:=mul_le_mul Hcoeff Hsum (abs_nonneg _) (by positivity : 0≤ CK*(1+Cmass)*M.data.d)
    convert HH using 1;ring
  have Hb' : |actualGeneralTargetRawFreshB0Part (n:=dim n) M.bf M.hf as i U| ≤
      Cb*M.data.d^2*di+Cb*M.data.d*density:=hjB i U hU hs hcut
  have Hj' : |actualGeneralTargetRawJointHighPart (n:=dim n) M.bf M.hf .lowTwoHigh as i U|≤ Cj*M.data.d*profile:=Hj
  have H4' : |actualGeneralTargetRawJointHighPart (n:=dim n) M.bf M.hf .fourGLow as i U|≤ C4*M.data.d*profile:=H4p
  change _ ≤ C*(M.data.d^2*di+M.data.d*density+M.data.d*profile)
  unfold actualGeneralTargetRawRestorationBudget
  have Hsum:=add_le_add (add_le_add (add_le_add (add_le_add Hb' Hj') Hq') Hlp) H4'
  apply Hsum.trans
  have Hmajor:=wall_raw_restoration_local_profile_algebra hCb.le hCj.le
    (mul_nonneg hCq.le hCB) (by positivity : 0 ≤ 2*CK*(1+Cmass)*Cl) hC4.le
    (mul_nonneg (sq_nonneg M.data.d) hdi) (mul_nonneg hdpos.le hdensity) (mul_nonneg hdpos.le hprofile)
  dsimp only [C]
  convert Hmajor using 1 <;> ring

end OAI.SKFluctuations.Cavity
