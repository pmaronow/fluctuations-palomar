module

public import ComparisonActualHighWallOriginalTaylorRemainderThermalProfile
public import ComparisonActualHighWallJointLowCubicPrice

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option autoImplicit false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000

theorem eventually_actual_high_wall_original_target_Taylor_remainder_uniform_thermal_profile_along
    (dOrder : ℕ) (hd : 0 < dOrder) (p : ℝ) (hp : 2 < p)
    (hOrder : p/(p-2) ≤ (dOrder:ℝ)) (Bclock Ccut : ℝ) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn in atTop,
      ∀M : ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d → ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock (dim n) M.bf M.hf as
        let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀i U : ℕ,i < U → U ≤ as.length → Ccut*M.data.d ≤ 1 →
          partitionPoint 0 as U ≤ Ccut*M.data.d →
        let g:=nativeFreshAtSlot (single (S:=Spin (dim n)×Bool) as) 0 (singleSlot as) i
        let R:=M.data.highErrorEnvelope M.alpha as U
        let di:=nativeOriginalCutLowErrorRadius (dim n) M.bf M.hf as i+1/(dim n+1:ℕ)
        |nativeActualTaylorRemainder (dim n) q U b h K g.tree (fun _=>1) (g.embed (singleSlot as)) g.mark| ≤
          C*(M.data.d*(g.tree.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+
            M.data.d*(g.tree.forkCost R+edgeBudget 0 as R))+
            M.data.d^2*di+M.data.d*
              (∫u in 0..Ccut*M.data.d,Real.sqrt (orderedPathB (dim n+1) M.bf M.hf u-
                (orderedPathS (dim n+1) M.bf M.hf u)^2))) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_high_wall_original_target_Taylor_remainder_thermal_profile
    (D:=D) dOrder hd p hp hOrder Bclock Ccut hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  let CB:=actualLowErrorComparisonConstant (2*max Bclock 0) (max Bclock 0)
  have hCB : 0 ≤ CB:=actualLowErrorComparisonConstant_nonneg _ (le_max_right _ _)
  let Cuniform:=C*(CB+1)
  refine ⟨Cuniform,by dsimp only [Cuniform];positivity,?_⟩
  filter_upwards [hdim.eventually H] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro i U hi hU hcut1 hcut
  have Hraw:=hj i U hi hU hcut1 hcut
  let as:=finiteCutMasses us jGrid
  let g:=nativeFreshAtSlot (single (S:=Spin (dim n)×Bool) as) 0 (singleSlot as) i
  let R:=M.data.highErrorEnvelope M.alpha as U
  let profile:=g.tree.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+
    M.data.d*(g.tree.forkCost R+edgeBudget 0 as R)
  let Cerr:=actualLowErrorComparisonConstant (2*M.data.T) M.data.T
  let di:=nativeOriginalCutLowErrorRadius (dim n) M.bf M.hf as i+1/(dim n+1:ℕ)
  let I:=∫u in 0..Ccut*M.data.d,Real.sqrt (orderedPathB (dim n+1) M.bf M.hf u-
    (orderedPathS (dim n+1) M.bf M.hf u)^2)
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hR j : 0 ≤ R j:=M.data.highErrorEnvelope_nonneg M.alpha as U j
  have hprofile : 0 ≤ profile:=by
    exact add_nonneg (add_nonneg (g.tree.forkCost_nonneg (fun j=>Real.rpow_nonneg (hR j) _))
      (edgeBudget_nonneg ho (fun j=>Real.rpow_nonneg (hR j) _)))
      (mul_nonneg M.data.hd.le (add_nonneg (g.tree.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)))
  have hDi : 0 ≤ di:=add_nonneg (Real.sqrt_nonneg _) (by positivity)
  have hI : 0 ≤ I:=intervalIntegral.integral_nonneg (mul_nonneg hCcut M.data.hd.le) (fun _ _=>Real.sqrt_nonneg _)
  have Hclock : Cerr ≤ CB:=actual_wall_low_error_comparison_constant_le
    (M.data.hepsilon.1.trans M.data.hepsilon.2).le (M.hT.trans (le_max_left _ _))
  have Hfactor : C*Cerr ≤ Cuniform:=by
    have HH:=mul_le_mul_of_nonneg_left Hclock hC.le
    dsimp only [Cuniform]
    nlinarith only [HH,hC]
  have HC : C ≤ Cuniform:=by dsimp only [Cuniform];nlinarith only [mul_nonneg hC.le hCB]
  have H0:=mul_le_mul_of_nonneg_right HC (mul_nonneg M.data.hd.le hprofile)
  have H1:=mul_le_mul_of_nonneg_right Hfactor (mul_nonneg (sq_nonneg M.data.d) hDi)
  have H2:=mul_le_mul_of_nonneg_right Hfactor (mul_nonneg M.data.hd.le hI)
  apply Hraw.trans
  change C*(M.data.d*profile+M.data.d^2*Cerr*di+M.data.d*Cerr*I) ≤
    Cuniform*(M.data.d*profile+M.data.d^2*di+M.data.d*I)
  convert add_le_add (add_le_add H0 H1) H2 using 1 <;> ring

end OAI.SKFluctuations.Cavity
