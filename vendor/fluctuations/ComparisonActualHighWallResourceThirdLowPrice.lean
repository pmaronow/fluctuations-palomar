module

public import ComparisonActualHighWallLowCubicPrice
public import ComparisonActualGeneralResourceThirdLowReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_high_wall_centered_resource_third_LOW_cubic_price
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
        ∀(a z : T.Slot) (l t : ℝ),l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 →
        |(M.data.d⁻¹)^k*actualGeneralOriginalCenteredResourceThirdLowPart M.bf M.hf U P a z l t| ≤
          |P.coefficient| *nativeResourceScale M.data.d M.data.d 1 seed*(C*M.data.d^3) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_high_wall_centered_resource_transient_LOW_cubic_price
    (D:=D) degree rBound Bclock Cmass Ccut hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨3*C,by positivity,?_⟩
  filter_upwards [H] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro i star U k seed T P hP hi hs hU hT hdepth hmi hms hcut a z l t hl ht
  have HE part:=hj i star U k seed T P hP hi hs hU hT hdepth hmi hms hcut a z part l t hl ht
  rw [actual_general_original_centered_resource_third_LOW_eq_sum,mul_add,mul_add]
  apply ((abs_add_le _ _).trans (add_le_add
    ((abs_add_le _ _).trans (add_le_add (HE .initial) (HE .star))) (HE .moving))).trans_eq
  ring

theorem eventually_actual_high_wall_fresh_resource_third_LOW_cubic_price
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
        ∀l t : ℝ,l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 →
        |(M.data.d⁻¹)^k*actualGeneralOriginalFreshResourceThirdLowPart M.bf M.hf U P l t| ≤
          |P.coefficient| *nativeResourceScale M.data.d M.data.d 1 seed*(C*M.data.d^3) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_high_wall_centered_resource_third_LOW_cubic_price
    (D:=D) degree (rBound+1) Bclock Cmass Ccut hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro i star U k seed T P hP hi hs hU hT hdepth hmi hms hcut l t hl ht
  let g:=nativeFreshAtSlot T 0 P.live.test.target star
  have hg : g.tree.leaves ≤ rBound+1:=by
    have H:=T.markedAttach_leaves 0 g (nativeFreshAtSlot_mem T 0 P.live.test.target star)
    omega
  rw [actual_general_original_fresh_resource_third_LOW_eq_centered_retarget M.bf M.hf U P
    (finiteCutMasses_ordered us hus jGrid)]
  exact hj i star U k seed g.tree (P.retarget 0) hP.retarget hi hs hU hg hdepth hmi hms hcut
    (g.embed P.live.test.target) g.mark l t hl ht

end OAI.SKFluctuations.Cavity
