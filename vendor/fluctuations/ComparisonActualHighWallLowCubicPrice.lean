module

public import ComparisonActualHighWallLowCostBudget
public import ComparisonActualHighWallCenteredResourceTransientLow

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_high_wall_centered_resource_transient_LOW_cubic_price
    (degree rBound : ℕ) (Bclock Cmass Ccut : ℝ) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(i star U k : ℕ) (seed : List NativeResourceMark)
          (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U seed k T P → i ≤ star → star < U →
        U ≤ as.length → T.leaves ≤ rBound → seed.length+k ≤ degree →
        partitionPoint 0 as i ≤ Cmass*M.data.d → partitionPoint 0 as star ≤ Cmass*M.data.d →
        partitionPoint 0 as U ≤ Ccut*M.data.d →
        ∀(a z : T.Slot) (part : NativeTransientLowErrorPart) (l t : ℝ),
        l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 →
        |(M.data.d⁻¹)^k*actualGeneralOriginalCenteredResourceTransientLowPart M.bf M.hf U P a z part l t| ≤
          |P.coefficient| *nativeResourceScale M.data.d M.data.d 1 seed*(C*M.data.d^3) := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_high_wall_centered_resource_transient_LOW_from_minimum
    (D:=D) degree rBound Bclock Cmass Ccut hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cr,hCr,HR⟩:=eventually_actual_high_wall_full_LOW_cost_bigO
    (D:=D) rBound Bclock Ccut hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp*Cr,mul_pos hCp hCr,?_⟩
  filter_upwards [HP,HR] with n hnP hnR
  intro M hwork L us hus hret hmesh
  filter_upwards [hnP M hwork M.data.hd1 L us hus hret hmesh,
    hnR M hwork L us hus hret hmesh] with jGrid hjP hjR
  dsimp only at hjP hjR ⊢
  intro i star U k seed T P hP hi hs hU hT hdepth hmi hms hcut a z part l t hl ht
  have HP:=hjP i star U k seed T P hP hi hs hU hT hdepth hmi hms hcut a z part l t hl ht
  have HR:=hjR U i star T part l t hU hT hcut hl ht
  have hscale : 0 ≤ |P.coefficient| *nativeResourceScale M.data.d M.data.d 1 seed :=
    mul_nonneg (abs_nonneg _) (actual_resource_raw_scale_pos seed M.data.hd M.data.hd).le
  apply HP.trans
  apply (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left HR (mul_nonneg hCp.le (sq_nonneg _))) hscale).trans_eq
  ring

end OAI.SKFluctuations.Cavity
