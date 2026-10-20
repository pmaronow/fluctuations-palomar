module

public import ComparisonActualGeneralTargetRawB0Readout
public import ComparisonActualHighWallSecondLowSoleRootTargetUniformThermalAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_high_wall_original_target_raw_B0_uniform_local_thermal_budget_along
    (Bclock Ccut : ℝ) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        ∀(i U : ℕ),U≤as.length → i<U → partitionPoint 0 as U≤Ccut*M.data.d →
        let di:=nativeOriginalCutLowErrorRadius (dim n) M.bf M.hf as i+1/(dim n+1:ℕ)
        |actualGeneralTargetRawFreshB0Part (n:=dim n) M.bf M.hf as i U|≤
          C*M.data.d^2*di+C*M.data.d*
            (∫u in 0..min (Ccut*M.data.d) 1,Real.sqrt (orderedPathB (dim n+1) M.bf M.hf u-
              (orderedPathS (dim n+1) M.bf M.hf u)^2)) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_high_wall_second_low_sole_root_target_B0_uniform_local_thermal_budget_along
    (D:=D) Bclock Ccut hCcut hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro i U hU hi hcut
  rw [actual_general_target_raw_fresh_B0_eq_sole_root_joint_ledger]
  exact hk i U hU hi hcut

end OAI.SKFluctuations.Cavity
