module

public import ComparisonActualHighWallResourceFourGLowRestorationFromMinimum
public import ComparisonActualHighWallResourceCTwoHighFromMinimum

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_high_wall_resource_joint_HIGH_restoration_from_minimum
    (kind : NativeJointHighRestorationKind) (degree dOrder rBound : ℕ) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Cmass Ccut : ℝ) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
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
        U ≤ as.length → T.leaves ≤ rBound →
        seed.length+k ≤ degree →
        partitionPoint 0 as i ≤ Cmass*M.data.d → partitionPoint 0 as star ≤ Cmass*M.data.d →
        partitionPoint 0 as U ≤ Ccut*M.data.d →
        ∀a z : T.Slot,T.splitIndex a z < U →
        let R:=M.data.highErrorEnvelope M.alpha as U
        |(M.data.d⁻¹)^k*actualGeneralResourceJointHighRestoration kind M.bf M.hf U P a z| ≤
          |P.coefficient| *nativeResourceScale M.data.d M.data.d 1 seed*
            (C*M.data.d*(T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+
              M.data.d*(T.forkCost R+edgeBudget 0 as R))) := by
  cases kind with
  | lowTwoHigh=>
    exact eventually_actual_high_wall_resource_C_two_high_from_minimum degree dOrder rBound hd p hp hOrder
      Bclock Cmass Ccut hCmass hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  | fourGLow=>
    obtain ⟨C,hC,H⟩:=eventually_actual_high_wall_resource_four_G_low_restoration_from_minimum
      (D:=D) degree dOrder rBound hd p hp hOrder Bclock Cmass Ccut hCmass hCcut hm hdelta hroom
      hcl hcu hAz hC0 hCt
    refine ⟨C,hC,?_⟩
    filter_upwards [H] with n hn
    intro M hwork L us hus hret hmesh
    filter_upwards [hn M hwork L us hus hret hmesh] with jGrid hj
    dsimp only at hj ⊢
    intro i star U k seed T P hP hi hs hU hT hdepth hmi hms hcut a z _haz
    exact hj i star U k seed T P hP hi hs hU hT hdepth hmi hms hcut a z

end OAI.SKFluctuations.Cavity
