module

public import SKProof.Port.ComparisonActualOriginalQLowRestorationCompatibleSourceAlong
public import SKProof.Port.ComparisonActualOriginalQOriginalTargetB0
public import SKProof.Port.ComparisonActualOriginalQOriginalTaylorProfiles
public import SKProof.Port.ComparisonActualOriginalQSquareConsumerActualSharpFourTerminalAlong

@[expose] public section
open OAI.SKFluctuations.LaplaceWindowFormalization.ActualThetaZeroOverlapMinimum
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 18000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators

theorem eventually_actual_minimum_inherited_working_scale_joint_low_restoration_ledger_original_q
    (aDegree rBound : ℕ)
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0 ≤ Az) (hC0 : 0<C0) (hCt : 0 ≤ Ct) :
    ∃Cp : ℝ,0<Cp ∧ ∃Cq : ℝ,0<Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U ≤ as.length → T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs ≤ x → x ≤ W →
          partitionPoint 0 as U ≤ Ccut*W →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
        ∀a z : T.Slot,T.splitIndex a z<U →
          |nativeCenteredLowGammaLowRestoration n q U b h K S T
            (G.canonicalOriginalQSource M forms).restProduct a z| ≤
            4*(rBound:ℝ)*(rBound+1)*ClockTree.absJetVariation (rBound+2) 2*
              (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*
                sourceMonomialScale x W initial)*
              (actualLowErrorComparisonConstant Mclock Temp*
                (nativeOriginalCutLowErrorRadius n M.sweepBf M.sweepHf as (T.splitIndex a z)+1/(n+1:ℕ)))*
              (Cq*(1+Ccut)*W)^2 := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_inherited_canonical_continuum_even_all_degree_original_q
    (D:=D) aDegree 2 rBound (by norm_num) Bclock Temp Cf Cmass hTemp hCf hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cq,hCq,HQ⟩:=eventually_actual_minimum_inherited_continuum_low_profile_moment_original_q
    (D:=D) 4 (by norm_num) Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,hCp,Cq,hCq,?_⟩
  filter_upwards [HP,HQ] with n hnP hnQ
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hnP M hs0 hsxs hsource hxs L us hus hret hmesh,
    hnQ M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgrid hgridQ
  dsimp only at hgrid hgridQ ⊢
  intro U T hU hT G forms initial x W hxsx hxW hcut hmass a z haz
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let Mclock:=4*Cf+2*Temp
  let C:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*
    sourceMonomialScale x W initial
  let rho:=Cq*(1+Ccut)*W
  let d:=actualLowErrorComparisonConstant Mclock Temp*
    (nativeOriginalCutLowErrorRadius n M.sweepBf M.sweepHf as (T.splitIndex a z)+1/(n+1:ℕ))
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.sweepBf M.sweepHf
    M.sweep_bf_monotone M.sweep_hf_monotone (partitionPoint_mem as ho j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepBf u:ℝ) ≤ M.sweepBf v from M.sweep_bf_monotone hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepHf u:ℝ) ≤ M.sweepHf v from M.sweep_hf_monotone hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.sweepBf M.sweepHf M.sweep_bf_monotone M.sweep_hf_monotone) as ho
  have hK0 j : 0 ≤ K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HS j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HS i).1 (NNReal.coe_nonneg _))
  have HM : 0 ≤ Mclock:=by dsimp [Mclock];positivity
  have HC : 0 ≤ C:=by
    dsimp only [C]
    rw [←source_factor_scale_product]
    exact mul_nonneg (by positivity) (Finset.prod_nonneg fun i _=>
      (source_factor_scale_pos (M.hxs.trans_le hxsx) ((M.hxs.trans_le hxsx).trans_le hxW) initial i).le)
  have HW : 0<W:=(M.hxs.trans_le hxsx).trans_le hxW
  have Hrho : 0<rho:=by dsimp [rho];positivity
  have Hd : 0 ≤ d:=mul_nonneg (actualLowErrorComparisonConstant_nonneg Mclock hTemp)
    (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have Hclock j (_hj : j ≤ as.length) : |b j| ≤ Mclock∧|h j| ≤ Mclock∧|K j| ≤ Mclock := by
    have Hfield:=hsource _ (partitionPoint_mem as ho j)
    have Hh : h j ≤ 2*Cf := by
      have H:=mul_le_mul_of_nonneg_left
        (show M.xs+partitionPoint 0 as j ≤ 2 by linarith [(partitionPoint_mem as ho j).2]) hCf
      exact Hfield.2.trans (by linarith only [H])
    have HK : K j ≤ 2*Cf+Temp := by
      have H:=mul_le_mul_of_nonneg_left (HS j).2 (NNReal.coe_nonneg (M.sweepBf (partitionPoint 0 as j)))
      dsimp only [K]
      linarith [Hfield.1]
    rw [abs_of_nonneg (NNReal.coe_nonneg _),abs_of_nonneg (NNReal.coe_nonneg _),abs_of_nonneg (hK0 j)]
    dsimp only [Mclock]
    exact ⟨by linarith [Hfield.1],by linarith,by linarith⟩
  have HQmoment l (hl : l∈Icc (0:ℝ) 1) j (hj : j ≤ as.length) : (ClockTree.pairClock as j).disorderExpect
      (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l 1 b h K)
      (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U 1 b h K) j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^8) 0 ≤ rho^8 := by
    by_cases hju : j<U
    · have Hraw:=hgridQ U l 1 1 hl (by norm_num) (by norm_num) j hj
      apply Hraw.trans
      apply pow_le_pow_left₀ (mul_nonneg hCq.le (add_nonneg M.hxs.le (partitionPoint_mem as ho j).1))
      dsimp only [rho]
      have Hmass:=partitionPoint_mono as ho hju.le
      have Hscale : M.xs+partitionPoint 0 as j ≤ (1+Ccut)*W := by nlinarith only [hxsx,hxW,hcut,Hmass]
      exact (mul_le_mul_of_nonneg_left Hscale hCq.le).trans_eq (by ring)
    · have HE : (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U 1 b h K) j
          (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^8)=fun _=>0 := by
        funext σ
        simp only [ReplicaTree.coordinateProfile,cutLSlope,hju,ite_false,Pi.zero_apply,
          zero_mul,Finset.sum_const_zero,abs_zero,zero_pow (by norm_num : (8:ℕ)≠0)]
      rw [HE]
      simp only [ClockTree.disorderExpect,mul_zero,Finset.sum_const_zero]
      exact pow_nonneg Hrho.le _
  apply native_centered_low_gamma_low_restoration_wholeLaw_bound n U q b h S T ho hT
    (G.canonicalOriginalQSource M forms).restProduct a z hU haz HC Hrho HM Hd
    (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
    (fun i=>by cases i <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm
    _ Hclock _ HQmoment
  · intro l hl
    simpa only [ActualNaturalBoundaryShape.product_eq_restProduct] using
      hgrid U T l 1 hl (by norm_num) hT G forms initial x W hxsx hxW hmass
  · intro l hl
    have H:=actual_minimum_inherited_current_low_error_radius_le_original_original_q M Temp Cf hTemp hCf hsource hxs
      ho U hl (show (1:ℝ)∈Icc 0 1 by norm_num) _ (T.splitIndex_le_clockLength a z)
    dsimp only at H
    simpa only [haz,ite_true] using H

end OAI.SKFluctuations.Cavity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 18000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators

theorem eventually_actual_minimum_inherited_working_scale_canonical_joint_LOW_restoration_price_original_q
    (aDegree rBound : ℕ)
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0 ≤ Az) (hC0 : 0<C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U ≤ as.length → T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs ≤ x → x ≤ W →
          partitionPoint 0 as U ≤ Ccut*W →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
        ∀a z : T.Slot,T.splitIndex a z<U →
          |nativeCenteredLowGammaLowRestoration n q U b h K S T
            (G.canonicalOriginalQSource M forms).restProduct a z|  ≤
            C*sourceMonomialScale x W initial*
              (actualLowErrorComparisonConstant Mclock Temp*
                (nativeOriginalCutLowErrorRadius n M.sweepBf M.sweepHf as (T.splitIndex a z)+1/(n+1:ℕ)))*W^2 := by
  obtain ⟨Cp,hCp,Cq,hCq,H⟩:=eventually_actual_minimum_inherited_working_scale_joint_low_restoration_ledger_original_q
    (D:=D) aDegree rBound Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  let base:=4*(rBound:ℝ)*(rBound+1)*absJetVariation (rBound+2) 2*
    (Real.exp (wholeLawRowComparisonConstant rBound*(4*Cf+2*Temp))*Cp^aDegree)*(Cq*(1+Ccut))^2
  have hbase : 0 ≤ base:=by
    have HV:=absJetVariation_nonneg (rBound+2) 2
    dsimp only [base]
    positivity
  refine ⟨base+1,by positivity,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro U T hU hT G forms initial x W hxsx hxW hcut hmass a z haz
  have Hraw:=hj U T hU hT G forms initial x W hxsx hxW hcut hmass a z haz
  let Z:=sourceMonomialScale x W initial
  let d:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
    (nativeOriginalCutLowErrorRadius n M.sweepBf M.sweepHf (finiteCutMasses us jGrid) (T.splitIndex a z)+1/(n+1:ℕ))
  have hZ : 0 ≤ Z:=by
    dsimp only [Z]
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos (M.hxs.trans_le hxsx) ((M.hxs.trans_le hxsx).trans_le hxW) initial e).le
  have hd : 0 ≤ d:=by
    dsimp only [d,nativeOriginalCutLowErrorRadius]
    exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp) (by positivity)
  have Hmajor:=mul_le_mul_of_nonneg_right (show base ≤ base+1 by linarith)
    (show 0 ≤ Z*d*W^2 by positivity)
  apply Hraw.trans
  convert Hmajor using 1 <;> dsimp only [base,Z,d] <;> ring

end OAI.SKFluctuations.Cavity

noncomputable section
set_option autoImplicit false
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_minimum_inherited_working_scale_resource_joint_LOW_restoration_from_minimum_original_q
    (degree rBound : ℕ) (Bclock Temp Cf Cmass Ccut : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(i star U k : ℕ) (seed : List NativeResourceMark)
          (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U seed k T P → i ≤ star → star < U →
        U ≤ as.length → T.leaves ≤ rBound → seed.length+k ≤ degree →
        ∀x W : ℝ,M.xs ≤ x → x ≤ W → W ≤ 1 →
        partitionPoint 0 as i ≤ Cmass*x → partitionPoint 0 as star ≤ Cmass*W →
        partitionPoint 0 as U ≤ Ccut*W →
        ∀a z : T.Slot,T.splitIndex a z<U →
        let R:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
          (nativeOriginalCutLowErrorRadius n M.sweepBf M.sweepHf as (T.splitIndex a z)+1/(n+1:ℕ))
        |(W⁻¹)^k*nativeActualResourceJointLowRestoration_original_q M U P a z| ≤
          |P.coefficient| *nativeResourceScale x W 1 seed*(C*R*W^2) := by
  classical
  have HP (a : Fin (degree+1)):=eventually_actual_minimum_inherited_working_scale_canonical_joint_LOW_restoration_price_original_q
    (D:=D) a.val rBound Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  choose C hC HC using HP
  let Cmax:=1+∑a : Fin (degree+1),C a
  have hsum : 0 ≤ ∑a : Fin (degree+1),C a:=Finset.sum_nonneg (fun a _=>(hC a).le)
  have hCmax : 0 < Cmax:=by dsimp only [Cmax];linarith
  have hdom a : C a ≤ Cmax:=by
    have H:=Finset.single_le_sum (fun a _=>(hC a).le) (Finset.mem_univ a)
    dsimp only [Cmax]
    linarith
  obtain ⟨A,hA,HA⟩:=eventually_actual_minimum_inherited_raw_resource_pair_budget_original_q
    (D:=D) (degree+1) (by omega) Bclock Temp Cf Cmass hTemp hCf hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  have hA0 : 0 < A:=zero_lt_one.trans_le hA
  refine ⟨Cmax*A^degree,by positivity,?_⟩
  filter_upwards [Filter.eventually_all.mpr HC,HA] with n hn hnA
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  have Hgrids a:=hn a M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [Filter.eventually_all.mpr Hgrids,hnA M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hj hjA
  dsimp only at hj hjA ⊢
  intro i star U k seed T P hP hi hs hU hT hdepth x W hxsx hxW hW1 hmi hms hcut aSlot z haz
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let R:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
    (nativeOriginalCutLowErrorRadius n M.sweepBf M.sweepHf as (T.splitIndex aSlot z)+1/(n+1:ℕ))
  let G:=nativeActualResourceCanonicalShape P.live hi (hs.trans_le hU)
  let I:=nativeActualResourceInitialFactors P.live
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hR : 0 ≤ R:=mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp) (by
    dsimp only [nativeOriginalCutLowErrorRadius]
    positivity)
  have hprice : 0 ≤ Cmax*R*W^2:=by positivity
  have Hdegree : P.resources.length ≤ degree+1:=by rw [hP.total_factor_depth];omega
  have Hpair:=hjA U i star T P Hdegree (hi.trans (hs.le.trans hU)) (hs.le.trans hU)
    x W hxsx hxW hmi hms 1 1 (by norm_num) (by norm_num)
  have Hlive : P.live.factors.length ≤ degree:=by
    have Hlen:=hP.total_factor_depth
    simp only [NativeResourceTerm.resources,List.length_append,NativeResourceMonomial.tags,List.length_map] at Hlen
    omega
  let a : Fin (degree+1):=⟨P.live.factors.length,by omega⟩
  have HL:=hj a U T hU hT G (fun _=>.centered) I x W hxsx hxW hcut
    (native_actual_resource_canonical_source_mass P.live hi (hs.trans_le hU) Cmass x W hmi hms) aSlot z haz
  rw [native_actual_resource_live_scale_eq_annotations] at HL
  have Hcenter : nativePhysicalResourceCenter n M.sweepBf M.sweepHf as=
      (fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)):=by
    funext j
    exact (native_ordered_source_center_eq_completed n M.sweepBf M.sweepHf
      M.sweep_bf_monotone M.sweep_hf_monotone (partitionPoint_mem as ho j)).symm
  rw [←Hcenter] at HL
  have HL' : |nativeCenteredLowGammaLowRestoration n q U b h K (nativePhysicalResourceCenter n M.sweepBf M.sweepHf as) T
      (G.canonicalOriginalQSource M (fun _=>NativeSourceFactorForm.centered)).restProduct aSlot z| ≤
      nativeResourceScale x W 1 P.live.tags*(Cmax*R*W^2):=by
    apply HL.trans
    have Hdom:=mul_le_mul_of_nonneg_left (hdom a)
      (show 0 ≤ nativeResourceScale x W 1 P.live.tags*R*W^2 by
        exact mul_nonneg (mul_nonneg (actual_resource_raw_scale_pos _ (M.hxs.trans_le hxsx) ((M.hxs.trans_le hxsx).trans_le hxW)).le hR) (sq_nonneg W))
    convert Hdom using 1 <;> ring
  have H:=actual_resource_joint_LOW_normalized_price_le_original_q M hP hdepth ho hi (hs.trans_le hU) hU
    aSlot z hA hxsx hxW hprice Hpair HL'
  apply H.trans_eq
  ring

end OAI.SKFluctuations.Cavity

noncomputable section
set_option autoImplicit false
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 28000000

theorem eventually_actual_minimum_inherited_working_scale_centered_resource_joint_LOW_restoration_from_minimum_original_q
    (degree rBound : ℕ) (Bclock Temp Cf Cmass Ccut : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(i star U k : ℕ) (seed : List NativeResourceMark)
          (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U seed k T P → i ≤ star → star < U →
        U ≤ as.length → T.leaves ≤ rBound → seed.length+k ≤ degree →
        ∀x W : ℝ,M.xs ≤ x → x ≤ W → W ≤ 1 →
        partitionPoint 0 as i ≤ Cmass*x → partitionPoint 0 as star ≤ Cmass*W →
        partitionPoint 0 as U ≤ Ccut*W →
        ∀a z : T.Slot,T.splitIndex a z<U →
        let R:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
          (nativeOriginalCutLowErrorRadius n M.sweepBf M.sweepHf as (T.splitIndex a z)+1/(n+1:ℕ))
        |(W⁻¹)^k*nativeActualOriginalCenteredResourceJointLowRestoration_original_q M U P a z| ≤
          |P.coefficient| *nativeResourceScale x W 1 seed*(C*R*W^2) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_working_scale_resource_joint_LOW_restoration_from_minimum_original_q
    (D:=D) degree rBound Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro i star U k seed T P hP hi hs hU hT hdepth x W hxsx hxW hW1 hmi hms hcut a z haz
  have ho:=finiteCutMasses_ordered us hus jGrid
  rw [native_actual_original_centered_resource_joint_LOW_restoration_eq_two_resources_original_q M U P ho hU a z,mul_add]
  have HP:=hj i star U k seed T P hP hi hs hU hT hdepth x W hxsx hxW hW1 hmi hms hcut a z haz
  have HF:=hj i star U k seed T P.freeze hP.freeze hi hs hU hT hdepth x W hxsx hxW hW1 hmi hms hcut a z haz
  simp only [NativeResourceTerm.freeze,abs_neg] at HF
  apply ((abs_add_le _ _).trans (add_le_add HP HF)).trans_eq
  ring

end OAI.SKFluctuations.Cavity

noncomputable section
set_option autoImplicit false
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 22000000

theorem actual_inherited_working_scale_resource_fresh_joint_LOW_restoration_rate_along_original_q
    (degree rBound : ℕ) (Bclock Temp Cf Cmass Ccut : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 < Ccut)
    {m delta cl cu Az C0 Ct D Tstar Lwin Cwindow : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠ n : ℕ in atTop,ActualOriginalQSmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠ n : ℕ in atTop,IsActualSharpCalibratedSlowWindow_original_q (M n) (W n) Tstar Lwin Cwindow (w n)) :
    ∃err : ℕ→ℝ,Tendsto err atTop (𝓝 0) ∧ ∀ᶠ n : ℕ in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star ∈ us →
      ∀ᶠ jGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        ∀U : ℕ,star < U → U ≤ as.length → partitionPoint 0 as U ≤ min (Ccut*W n) 1 →
        ∀(i k : ℕ) (seed : List NativeResourceMark) (T : ClockTree (Spin (dim n)×Bool) as) (P : NativeResourceTerm i star T),
          NativeActualResourceGenerated i star U seed k T P → i ≤ star →
          T.leaves ≤ rBound → seed.length+k ≤ degree →
          ∀x : ℝ,(M n).xs ≤ x → x ≤ W n →
          partitionPoint 0 as i ≤ Cmass*x → partitionPoint 0 as star ≤ Cmass*W n →
          |((W n)⁻¹)^k*nativeActualOriginalFreshResourceJointLowRestoration_original_q (M n) U P| ≤
              |P.coefficient| *nativeResourceScale x (W n) 1 seed*err n*(W n*(M n).xs^2) := by
  obtain ⟨C,hC,HC⟩:=eventually_actual_minimum_inherited_working_scale_centered_resource_joint_LOW_restoration_from_minimum_original_q
    (D:=D) degree (rBound+1) Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut.le
    hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cerr:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp
  let eta:=actualMassSavingExponent m delta
  let err:=fun n=>C*((dim n+1:ℕ):ℝ)^(-eta/32)
  have HR:=eventually_actual_sharp_star_original_low_radius_saving_along_original_q hm hdelta hC0 Cerr
    (actualLowErrorComparisonConstant_nonneg _ hTemp) dim hdim M W hcanonical hWlim w hw
  have Hpow:=(tendsto_rpow_neg_atTop (show 0 < eta/32 from div_pos
    (actualMassSavingExponent_pos hm hdelta) (by norm_num))).comp
    (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
  have Herr : Tendsto err atTop (𝓝 0):=by
    simpa only [err,Function.comp_def,mul_zero,neg_div] using Hpow.const_mul C
  refine ⟨err,Herr,?_⟩
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hdim.eventually HC,HR,Hsource,HW1,Hcutoff] with n hnC hnR hsource hW1 hnCutoff
  have hxW : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hx1:=hxW.trans hW1
  intro L us hus hret hmesh hstar
  filter_upwards [hnC (M n) hnCutoff.1 hnCutoff.2 hsource hx1 L us hus hret hmesh,hnR us hus hstar] with jGrid hgridC hgridR
  dsimp only at hgridC hgridR ⊢
  intro U hs hU hcut i k seed T P hP hi hT hdepth x hxsx hxWscale hmi hms
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let g:=nativeFreshAtSlot T 0 P.live.test.target star
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hg : g.tree.leaves ≤ rBound+1:=by
    have H:=T.markedAttach_leaves 0 g (nativeFreshAtSlot_mem T 0 P.live.test.target star)
    omega
  have Hsplit : g.tree.splitIndex (g.embed P.live.test.target) g.mark=star:=by
    rw [g.tree.splitIndex_symm,nativeFreshAtSlot_split,T.splitIndex_self,
      min_eq_left (hs.le.trans hU)]
  have H:=hgridC i star U k seed g.tree (P.retarget 0) hP.retarget hi hs hU hg (by simpa using hdepth)
    x (W n) hxsx hxWscale hW1 hmi hms (hcut.trans (min_le_left _ _)) (g.embed P.live.test.target) g.mark
    (by rw [Hsplit];exact hs)
  rw [Hsplit] at H
  simp only [NativeResourceTerm.retarget] at H
  rw [native_actual_original_fresh_resource_joint_LOW_restoration_eq_centered_retarget_original_q (M n) U P ho]
  have HD:=mul_le_mul_of_nonneg_left hgridR
    (show 0 ≤ |P.coefficient| *nativeResourceScale x (W n) 1 seed*C*(W n)^2 by
      exact mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (actual_resource_raw_scale_pos _ ((M n).hxs.trans_le hxsx) (((M n).hxs.trans_le hxsx).trans_le hxWscale)).le) hC.le) (sq_nonneg _))
  have hW : W n≠0:=((M n).hxs.trans_le hxW).ne'
  apply H.trans
  convert HD using 1 <;> (try dsimp only [err,eta,Cerr,star,as]) <;> field_simp [hW]

end OAI.SKFluctuations.Cavity

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 22000000
set_option backward.isDefEq.respectTransparency false

theorem actual_inherited_initial_joint_LOW_restoration_forest_rate_along_original_q
    (depth : ℕ) (Bclock Temp Cf Cmass Ccut cK : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 < Ccut) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D Tstar Lwin Cwindow : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠn in atTop,ActualOriginalQSmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow_original_q (M n) (W n) Tstar Lwin Cwindow (w n)) :
    ∃err : ℕ→ℝ,(∀n,0 ≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧ ∀ᶠn in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        ∀(i U : ℕ) (hi : i ≤ star) (hs : star<U) (hU : U ≤ as.length),
        partitionPoint 0 as U ≤ min (Ccut*W n) 1 →
        partitionPoint 0 as star ≤ Cmass*W n →
        cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).sweepBf (M n).sweepHf as star →
        ∀x : ℝ,(M n).xs ≤ x → x ≤ W n → partitionPoint 0 as i ≤ Cmass*x → ∀seedMass : ℝ,
        let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) as i star seedMass (hi.trans (hs.le.trans hU))
        ((nativeActualMinimumFourCenteredForest_original_q (M n) hs hU (W n) depth [st]).map
          (fun Q=>|nativeActualOriginalFourJointLowRestorationError_original_q (M n) U (W n) Q|)).sum ≤
            err n*x*(M n).xs^2 := by
  let degree:=1+depth
  let rBound:=2+6*depth
  obtain ⟨eLow,heLow,HLow⟩:=actual_inherited_working_scale_resource_fresh_joint_LOW_restoration_rate_along_original_q
    degree (rBound+1) Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M W hcanonical hWlim Hsource Hcutoff w hw
  let Cd:=Real.exp (-4*(Temp+2*Cf))*cK
  let Cw:=(Temp+2*Cf)/Cd
  let Vv:=nativeActualWeightedFrontierCost nativeActualOriginalFourGCenteredBranches Cw 3 2 depth
  have hCd : 0 < Cd:=by dsimp only [Cd];positivity
  have hCw : 0 ≤ Cw:=by dsimp only [Cw];positivity
  have hVv : 0 ≤ Vv:=nativeActualWeightedFrontierCost_nonneg _ hCw _ _ _
  let err:=fun n=>(4*Vv/Cd)*|eLow n|
  have Herr : Tendsto err atTop (𝓝 0):=by
    simpa only [err,mul_zero,abs_zero] using heLow.abs.const_mul (4*Vv/Cd)
  refine ⟨err,fun n=>by dsimp only [err];positivity,Herr,?_⟩
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [HLow,Hsource,HW1] with n hnL hsource hW1
  have hxW : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hxs1:=hxW.trans hW1
  have hW : 0 < W n:=(M n).hxs.trans_le hxW
  intro L us hus hret hmesh hstar
  filter_upwards [hnL L us hus hret hmesh hstar] with jGrid hgridL
  dsimp only at hgridL ⊢
  intro i U hi hs hU hcut hmassstar hstarK x hxsx hxWscale hmi seedMass
  have hx : 0 < x:=(M n).hxs.trans_le hxsx
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let K:=nativeContinuumMixedClock (dim n) (M n).sweepBf (M n).sweepHf as
  let b:=fun j=>((M n).sweepBf (partitionPoint 0 as j):ℝ)
  let Γ:=nativeOriginalHighRowGamma (n:=dim n) (as:=as) U K
  let weight:=fun (Q : NativeActualResourceState (Spin (dim n)×Bool) as i star) tag=>
    nativeOriginalClockParentWeight (W n) U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag)
  let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) as i star seedMass (hi.trans (hs.le.trans hU))
  let rows:=nativeActualMinimumFourCenteredForest_original_q (M n) hs hU (W n) depth [st]
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have HW Q tag : |weight Q tag| ≤ Cw:=
    actual_continuum_four_G_weight_bound_of_small_source_clocks_original_q (M n) hCf hsource hxs1 hW hcK as ho hs hU hstarK Q tag
  have Hleaves Q (hQ : Q∈[st]) : Q.tree.leaves ≤ 2:=by
    have hQ' : Q=st:=by simpa using hQ
    subst Q
    exact nativeActualInitialState_leaves_le as i star seedMass (hi.trans (hs.le.trans hU))
  have Hseed Q (hQ : Q∈[st]) : NativeActualResourceGenerated i star U [.initial] Q.generation Q.tree Q.term:=by
    have hQ' : Q=st:=by simpa using hQ
    subst Q
    exact .physical (.seed as hU seedMass .initial (Or.inl rfl) (hi.trans (hs.le.trans hU)))
  have Hvalid Q (hQ : Q∈rows) := nativeActualFourCenteredForest_valid Γ hs (hs.le.trans hU) weight depth [st] Hseed Q hQ
  have Hgen Q (hQ : Q∈rows) := nativeActualFourCenteredForest_generation_bound Γ hs (hs.le.trans hU) weight depth [st]
    0 (by
      intro P hP
      have hP' : P=st:=by simpa using hP
      subst P
      rfl) Q hQ
  have Hleaf Q (hQ : Q∈rows) :=nativeActualFourCenteredForest_leaves_bound Γ hs (hs.le.trans hU) weight depth [st]
    2 Hleaves Q hQ
  have Hrow Q (hQ : Q∈rows) : |nativeActualOriginalFourJointLowRestorationError_original_q (M n) U (W n) Q| ≤
      |Q.term.coefficient| *(2/Cd)*(x*|eLow n| *(M n).xs^2):=by
    have HV:=Hvalid Q hQ
    have HG:=Hgen Q hQ
    have HT:=Hleaf Q hQ
    have HD : [NativeResourceMark.initial].length+Q.generation ≤ degree:=by dsimp only [degree,List.length];omega
    let g:=nativeFreshAtSlot Q.tree 0 Q.term.live.test.target star
    have hg : g.tree.leaves ≤ rBound+1:=by
      have HH:=Q.tree.markedAttach_leaves 0 g (nativeFreshAtSlot_mem Q.tree 0 Q.term.live.test.target star)
      dsimp only [rBound]
      omega
    have Hlow0:=hgridL U hs hU hcut i Q.generation [.initial] Q.tree Q.term HV hi
      (by dsimp only [rBound];omega) HD x hxsx hxWscale hmi hmassstar
    have Hlow1:=hgridL U hs hU hcut i Q.generation [.initial] g.tree (Q.term.retarget 0) HV.retarget hi
      hg HD x hxsx hxWscale hmi hmassstar
    simp only [nativeResourceScale,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
      NativeResourceMark.savedScale,mul_one,NativeResourceTerm.retarget] at Hlow0 Hlow1
    have Hlowmajor : |Q.term.coefficient| *x*eLow n*(W n*(M n).xs^2) ≤
        |Q.term.coefficient| *W n*(x*|eLow n| *(M n).xs^2):=by
      have H:=mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (le_abs_self (eLow n))
          (mul_nonneg (abs_nonneg Q.term.coefficient) hx.le))
        (show 0 ≤ W n*(M n).xs^2 by positivity)
      convert H using 1
      ring
    have Herror:=actual_minimum_four_joint_LOW_restoration_error_abs_le_original_q (M n) hCf hsource hxs1 Q ho hs hU hW hcK
      (show 0 ≤ x*|eLow n| *(M n).xs^2 by positivity) hstarK
      (Hlow0.trans Hlowmajor) (Hlow1.trans Hlowmajor)
    simpa only [Cd] using Herror
  have Hvariation:=nativeActualFourCenteredForest_coefficient_variation_le ho Γ
    (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one ho U K Q p) hs (hs.le.trans hU) weight
    hCw HW depth [st] 2 Hleaves
  have Htotal : (rows.map (fun Q=>|Q.term.coefficient|)).sum ≤ 2*Vv:=by
    change (rows.map (fun Q=>|Q.term.coefficient|)).sum ≤
      2*Vv*([st].map (fun Q=>|Q.term.coefficient|)).sum at Hvariation
    have hcoeff : st.term.coefficient=1:=rfl
    simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,hcoeff,
      abs_one,add_zero,mul_one] using Hvariation
  have Hsum:=List.sum_le_sum Hrow
  rw [List.sum_map_mul_right,List.sum_map_mul_right] at Hsum
  apply Hsum.trans
  have H:=mul_le_mul_of_nonneg_right Htotal
    (show 0 ≤ (2/Cd)*(x*|eLow n| *(M n).xs^2) by positivity)
  convert H using 1 <;> (try dsimp only [err]) <;> ring

end OAI.SKFluctuations.Cavity
