module

public import ComparisonActualHighWallResourceTransientLow
public import ComparisonActualGeneralCenteredResourceTransientLowReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 28000000

theorem eventually_actual_high_wall_centered_resource_transient_LOW_from_minimum
    (degree rBound : ℕ) (Bclock Cmass Ccut : ℝ) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d → M.data.d ≤ 1 →
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
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock n M.bf M.hf as
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let R:=nativeWholeLawErrorRadius n as (cutFullVariance n q U l t b h K)
          (nativeTransientLowErrorPartDirection n U i star b h K part)
        |(M.data.d⁻¹)^k*actualGeneralOriginalCenteredResourceTransientLowPart M.bf M.hf U P a z part l t| ≤
          |P.coefficient| *nativeResourceScale M.data.d M.data.d 1 seed*
            (C*M.data.d^2*(T.forkCost R+edgeBudget 0 as R)) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_high_wall_resource_transient_LOW_from_minimum
    (D:=D) degree rBound Bclock Cmass Ccut hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [H] with n hn
  intro M hwork hW1 L us hus hret hmesh
  filter_upwards [hn M hwork hW1 L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro i star U k seed T P hP hi hs hU hT hdepth hmi hms hcut a z part l t hl ht
  have ho:=finiteCutMasses_ordered us hus jGrid
  rw [actual_general_original_centered_resource_transient_LOW_eq_two_resources M.bf M.hf
    U P ho a z part l t,mul_add]
  have HP:=hj i star U k seed T P hP hi hs hU hT hdepth hmi hms hcut a z part l t hl ht
  have HF:=hj i star U k seed T P.freeze hP.freeze hi hs hU hT hdepth hmi hms hcut a z part l t hl ht
  simp only [NativeResourceTerm.freeze,abs_neg] at HF
  apply ((abs_add_le _ _).trans (add_le_add HP HF)).trans_eq
  ring

end OAI.SKFluctuations.Cavity
