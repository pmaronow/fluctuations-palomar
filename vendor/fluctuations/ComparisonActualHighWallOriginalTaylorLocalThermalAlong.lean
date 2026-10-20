module

public import ComparisonActualHighWallOriginalTaylorRemainderUniformThermalAlong
public import ComparisonActualHighWallTargetRawRestorationLocalThermalAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option autoImplicit false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000

theorem eventually_actual_high_wall_original_target_Taylor_local_thermal_profile_along
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
        ∀i U : ℕ,i < U → U ≤ as.length → Ccut*M.data.d ≤ 1 →
          partitionPoint 0 as U ≤ Ccut*M.data.d →
        let g:=nativeFreshAtSlot (single (S:=Spin (dim n)×Bool) as) 0 (singleSlot as) i
        let R:=M.data.highErrorEnvelope M.alpha as U
        let di:=nativeOriginalCutLowErrorRadius (dim n) M.bf M.hf as i+1/(dim n+1:ℕ)
        |actualGeneralTargetOriginalTaylorPart (n:=dim n) M.bf M.hf as i U| ≤
          C*(M.data.d*(g.tree.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+
            M.data.d*(g.tree.forkCost R+edgeBudget 0 as R))+
            M.data.d^2*di+M.data.d*
              (∫u in 0..Ccut*M.data.d,Real.sqrt (orderedPathB (dim n+1) M.bf M.hf u-
                (orderedPathS (dim n+1) M.bf M.hf u)^2))) := by
  obtain ⟨CR,hCR,HR⟩:=eventually_actual_high_wall_original_target_Taylor_remainder_uniform_thermal_profile_along
    (D:=D) dOrder hd p hp hOrder Bclock Ccut hCcut hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim
  obtain ⟨CB,hCB,HB⟩:=eventually_actual_high_wall_original_target_raw_restoration_local_thermal_profile_along
    (D:=D) dOrder hd p hp hOrder Bclock Ccut Ccut hCcut hCcut hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim
  refine ⟨CR+CB,by positivity,?_⟩
  filter_upwards [HR,HB] with n hnR hnB
  intro M hwork L us hus hret hmesh
  filter_upwards [hnR M hwork L us hus hret hmesh,hnB M hwork L us hus hret hmesh] with jGrid hjR hjB
  dsimp only at hjR hjB ⊢
  intro i U hi hU hcut1 hcut
  let as:=finiteCutMasses us jGrid
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hmass : partitionPoint 0 as i ≤ Ccut*M.data.d:=(partitionPoint_mono as ho hi.le).trans hcut
  have Hb:=hjB i U hi hU hmass hcut
  rw [min_eq_left hcut1] at Hb
  have Hr : |actualGeneralTargetRawTaylorRemainder (n:=dim n) M.bf M.hf as i U| ≤ _:=hjR i U hi hU hcut1 hcut
  have H:=actual_general_target_original_Taylor_abs_le_raw_restoration_and_Taylor (n:=dim n) M.bf M.hf as ho hi hU
  exact H.trans ((add_le_add Hb Hr).trans_eq (by ring))

end OAI.SKFluctuations.Cavity
