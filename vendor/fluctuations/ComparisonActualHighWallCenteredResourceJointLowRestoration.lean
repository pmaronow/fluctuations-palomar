module

public import ComparisonActualHighWallResourceJointLowRestoration
public import ComparisonActualGeneralCenteredResourceJointLowRestorationReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 28000000

theorem eventually_actual_high_wall_centered_resource_joint_LOW_restoration_from_minimum
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
        ∀a z : T.Slot,T.splitIndex a z<U →
        let R:=actualLowErrorComparisonConstant (2*M.data.T) M.data.T*
          (nativeOriginalCutLowErrorRadius n M.bf M.hf as (T.splitIndex a z)+1/(n+1:ℕ))
        |(M.data.d⁻¹)^k*actualGeneralOriginalCenteredResourceJointLowRestoration M.bf M.hf U P a z| ≤
          |P.coefficient| *nativeResourceScale M.data.d M.data.d 1 seed*(C*R*M.data.d^2) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_high_wall_resource_joint_LOW_restoration_from_minimum
    (D:=D) degree rBound Bclock Cmass Ccut hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [H] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro i star U k seed T P hP hi hs hU hT hdepth hmi hms hcut a z haz
  have ho:=finiteCutMasses_ordered us hus jGrid
  rw [actual_general_original_centered_resource_joint_LOW_restoration_eq_two_resources M.bf M.hf
    (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) U P ho hU a z,mul_add]
  have HP:=hj i star U k seed T P hP hi hs hU hT hdepth hmi hms hcut a z haz
  have HF:=hj i star U k seed T P.freeze hP.freeze hi hs hU hT hdepth hmi hms hcut a z haz
  simp only [NativeResourceTerm.freeze,abs_neg] at HF
  apply ((abs_add_le _ _).trans (add_le_add HP HF)).trans_eq
  ring

end OAI.SKFluctuations.Cavity
