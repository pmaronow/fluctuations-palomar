module

public import ComparisonActualHighWallOriginalTargetThirdLowThermalBudget
public import ComparisonActualHighWallOriginalConstantTaylorProfile

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option autoImplicit false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000

theorem eventually_actual_high_wall_original_target_Taylor_remainder_thermal_profile
    (dOrder : ℕ) (hd : 0 < dOrder) (p : ℝ) (hp : 2 < p)
    (hOrder : p/(p-2) ≤ (dOrder:ℝ)) (Bclock Ccut : ℝ) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d → ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock n M.bf M.hf as
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀i U : ℕ,i < U → U ≤ as.length → Ccut*M.data.d ≤ 1 →
          partitionPoint 0 as U ≤ Ccut*M.data.d →
        let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i
        let R:=M.data.highErrorEnvelope M.alpha as U
        let Cerr:=actualLowErrorComparisonConstant (2*M.data.T) M.data.T
        let di:=nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ)
        |nativeActualTaylorRemainder n q U b h K g.tree (fun _=>1) (g.embed (singleSlot as)) g.mark| ≤
          C*(M.data.d*(g.tree.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+
            M.data.d*(g.tree.forkCost R+edgeBudget 0 as R))+
            M.data.d^2*Cerr*di+M.data.d*Cerr*
              (∫u in 0..Ccut*M.data.d,Real.sqrt (orderedPathB (n+1) M.bf M.hf u-
                (orderedPathS (n+1) M.bf M.hf u)^2))) := by
  obtain ⟨CH,hCH,HH⟩:=eventually_actual_high_wall_original_constant_HIGH_profile
    (D:=D) 2 dOrder hd p hp hOrder Bclock Ccut hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨CL,hCL,HL⟩:=eventually_actual_high_wall_original_target_third_LOW_thermal_integral_budget
    (D:=D) Bclock Ccut hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  let C:=2*CH+CL+1
  refine ⟨C,by dsimp only [C];positivity,?_⟩
  filter_upwards [HH,HL] with n hnH hnL
  intro M hwork L us hus hret hmesh
  filter_upwards [hnH M hwork L us hus hret hmesh,hnL M hwork L us hus hret hmesh] with jGrid hjH hjL
  dsimp only at hjH hjL ⊢
  intro i U hi hU hcut1 hcut
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i
  let R:=M.data.highErrorEnvelope M.alpha as U
  let profile:=g.tree.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+
    M.data.d*(g.tree.forkCost R+edgeBudget 0 as R)
  let Cerr:=actualLowErrorComparisonConstant (2*M.data.T) M.data.T
  let di:=nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ)
  let I:=∫u in 0..Ccut*M.data.d,Real.sqrt (orderedPathB (n+1) M.bf M.hf u-(orderedPathS (n+1) M.bf M.hf u)^2)
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hdpos:=M.data.hd
  have hCe : 0 ≤ Cerr:=actualLowErrorComparisonConstant_nonneg _ (M.data.hepsilon.1.le.trans M.data.hepsilon.2.le)
  have hdi : 0 ≤ di:=add_nonneg (Real.sqrt_nonneg _) (by positivity)
  have hI : 0 ≤ I:=intervalIntegral.integral_nonneg (mul_nonneg hCcut hdpos.le) (fun _ _=>Real.sqrt_nonneg _)
  have hg : g.tree.leaves ≤ 2:=by
    have H:=(single (S:=Spin n×Bool) as).markedAttach_leaves 0 g (nativeFreshAtSlot_mem _ _ _ _)
    simpa only [single_leaves_exact] using H
  have hR j : 0 ≤ R j:=M.data.highErrorEnvelope_nonneg M.alpha as U j
  have hprofile : 0 ≤ profile:=by
    exact add_nonneg (add_nonneg (g.tree.forkCost_nonneg (fun j=>Real.rpow_nonneg (hR j) _))
      (edgeBudget_nonneg ho (fun j=>Real.rpow_nonneg (hR j) _)))
      (mul_nonneg hdpos.le (add_nonneg (g.tree.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)))
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.bf u:ℝ) ≤ M.bf v from M.data.bf_monotone M.alpha hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.hf u:ℝ) ≤ M.hf v from M.data.hf_monotone M.alpha hu hv huv) as ho
  have H:=native_actual_taylor_remainder_abs_le_HIGH_LOW n q U b h K g.tree ho (fun _=>1)
    (g.embed (singleSlot as)) g.mark
    (fun j z=>by cases z <;> exact NNReal.coe_nonneg _)
    (fun z=>by cases z <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _)
    (native_continuum_mixed_clock_nonneg n M.bf M.hf (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) as ho)
    hbm hhm (native_continuum_mixed_clock_monotone n M.bf M.hf (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) as ho)
    (CH*M.data.d*profile) (CL*M.data.d^2*Cerr*di+CL*M.data.d*Cerr*I)
    (by positivity) (by positivity)
    (fun l t hl ht part=>hjH U g.tree hU hg hcut (g.embed (singleSlot as)) g.mark l t hl ht part)
    (fun l t hl ht=>hjL i U hi hU hcut1 hcut l t hl ht)
  apply H.trans
  have H0 : 0 ≤ M.data.d*profile:=mul_nonneg hdpos.le hprofile
  have H1 : 0 ≤ M.data.d^2*Cerr*di:=by positivity
  have H2 : 0 ≤ M.data.d*Cerr*I:=by positivity
  change 2*(CH*M.data.d*profile)+(CL*M.data.d^2*Cerr*di+CL*M.data.d*Cerr*I)/2 ≤
    C*(M.data.d*profile+M.data.d^2*Cerr*di+M.data.d*Cerr*I)
  dsimp only [C]
  nlinarith only [mul_nonneg hCL.le H0,mul_nonneg hCH.le H1,mul_nonneg hCH.le H2,
    mul_nonneg hCL.le H1,mul_nonneg hCL.le H2,H0,H1,H2]

end OAI.SKFluctuations.Cavity
