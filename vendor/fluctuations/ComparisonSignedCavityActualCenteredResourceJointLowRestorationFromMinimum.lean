module

public import ComparisonSignedCavityActualResourceJointLowRestorationFromMinimum
public import ComparisonSignedCavityActualCenteredResourceJointLowRestorationReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 28000000

theorem eventually_actual_minimum_inherited_centered_resource_joint_LOW_restoration_from_minimum
    (degree rBound : ℕ) (Bclock Temp Cf Cmass Ccut : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(i star U k : ℕ) (seed : List NativeResourceMark)
          (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U seed k T P → i ≤ star → star < U →
        U ≤ as.length → T.leaves ≤ rBound → seed.length+k ≤ degree →
        ∀W : ℝ,M.xs ≤ W → W ≤ 1 →
        partitionPoint 0 as i ≤ Cmass*M.xs → partitionPoint 0 as star ≤ Cmass*W →
        partitionPoint 0 as U ≤ Ccut*W →
        ∀a z : T.Slot,T.splitIndex a z<U →
        let R:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
          (nativeOriginalCutLowErrorRadius n M.bf M.hf as (T.splitIndex a z)+1/(n+1:ℕ))
        |(W⁻¹)^k*nativeActualOriginalCenteredResourceJointLowRestoration M U P a z| ≤
          |P.coefficient| *nativeResourceScale M.xs W 1 seed*(C*R*W^2) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_resource_joint_LOW_restoration_from_minimum
    (D:=D) degree rBound Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [H] with n hn
  intro M hsource hxs L us hus hret hmesh
  filter_upwards [hn M hsource hxs L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro i star U k seed T P hP hi hs hU hT hdepth W hxW hW1 hmi hms hcut a z haz
  have ho:=finiteCutMasses_ordered us hus jGrid
  rw [native_actual_original_centered_resource_joint_LOW_restoration_eq_two_resources M U P ho hU a z,mul_add]
  have HP:=hj i star U k seed T P hP hi hs hU hT hdepth W hxW hW1 hmi hms hcut a z haz
  have HF:=hj i star U k seed T P.freeze hP.freeze hi hs hU hT hdepth W hxW hW1 hmi hms hcut a z haz
  simp only [NativeResourceTerm.freeze,abs_neg] at HF
  apply ((abs_add_le _ _).trans (add_le_add HP HF)).trans_eq
  ring

end OAI.SKFluctuations.Cavity
