module

public import ComparisonActualHighWallResourceThirdLowOriginalProfile
public import ComparisonActualHighWallPersistentLowThermalCost
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

theorem eventually_actual_high_wall_centered_resource_third_LOW_local_thermal_profile
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
        Ccut*M.data.d ≤ 1 → partitionPoint 0 as U ≤ Ccut*M.data.d →
        ∀(a z : T.Slot) (l t : ℝ),l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 →
        let di:=nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ)
        let ds:=nativeOriginalCutLowErrorRadius n M.bf M.hf as star+1/(n+1:ℕ)
        let I:=∫u in 0..Ccut*M.data.d,Real.sqrt (orderedPathB (n+1) M.bf M.hf u-
          (orderedPathS (n+1) M.bf M.hf u)^2)
        |(M.data.d⁻¹)^k*actualGeneralOriginalCenteredResourceThirdLowPart M.bf M.hf U P a z l t| ≤
          |P.coefficient| *nativeResourceScale M.data.d M.data.d 1 seed*(C*M.data.d^2*(di+ds+I)) := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_high_wall_centered_resource_third_LOW_original_profile
    (D:=D) degree rBound Bclock Cmass Ccut hCmass hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  let CB:=actualLowErrorComparisonConstant (2*max Bclock 0) (max Bclock 0)
  have hCB : 0 ≤ CB:=actualLowErrorComparisonConstant_nonneg _ (le_max_right _ _)
  let C:=Cp*(CB+1)*((rBound:ℝ)+4)
  refine ⟨C,by dsimp only [C];positivity,?_⟩
  filter_upwards [HP] with n hnP
  intro M hwork L us hus hret hmesh
  filter_upwards [hnP M hwork L us hus hret hmesh,
    actual_high_wall_persistent_LOW_thermal_cost_on_final_nets M Ccut hCcut us hus] with jGrid hjP hjCost
  dsimp only at hjP hjCost ⊢
  intro i star U k seed T P hP hi hs hU hT hdepth hmi hms hcut1 hcut a z l t hl ht
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let R:=nativeWholeLawErrorRadius n as (cutFullVariance n q U l t b h K) (cutLowError n U b h K)
  let Cerr:=actualLowErrorComparisonConstant (2*M.data.T) M.data.T
  let di:=nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ)
  let ds:=nativeOriginalCutLowErrorRadius n M.bf M.hf as star+1/(n+1:ℕ)
  let I:=∫u in 0..Ccut*M.data.d,Real.sqrt (orderedPathB (n+1) M.bf M.hf u-
    (orderedPathS (n+1) M.bf M.hf u)^2)
  have hdi : 0 ≤ di:=add_nonneg (Real.sqrt_nonneg _) (by positivity)
  have hds : 0 ≤ ds:=add_nonneg (Real.sqrt_nonneg _) (by positivity)
  have hI : 0 ≤ I:=intervalIntegral.integral_nonneg (mul_nonneg hCcut M.data.hd.le) (fun _ _=>Real.sqrt_nonneg _)
  have hsite : (1/(n+1:ℕ):ℝ) ≤ di:=le_add_of_nonneg_left (Real.sqrt_nonneg _)
  have Hmaj : (rBound:ℝ)*(di+ds)+I+3/(n+1:ℕ) ≤ ((rBound:ℝ)+4)*(di+ds+I):=by
    have Hsite : (3/(n+1:ℕ):ℝ) ≤ 3*di:=by
      simpa only [mul_div,mul_one] using mul_le_mul_of_nonneg_left hsite (by norm_num : (0:ℝ) ≤ 3)
    nlinarith only [Hsite,hdi,hds,hI,mul_nonneg (Nat.cast_nonneg rBound) hI]
  have Hclock : Cerr ≤ CB+1:=by
    have H:=actual_wall_low_error_comparison_constant_le (M.data.hepsilon.1.trans M.data.hepsilon.2).le
      (M.hT.trans (le_max_left Bclock 0))
    exact H.trans (by linarith)
  have Hcost:=hjCost i star U rBound T (hP.persistentLowForks hi) hi hs hU hT hcut1 hcut l t hl ht
  have Hcost' : T.forkCost R+edgeBudget 0 as R ≤
      (CB+1)*((rBound:ℝ)+4)*(di+ds+I):=by
    apply Hcost.trans
    have HH:=mul_le_mul Hclock Hmaj (by positivity : 0 ≤ (rBound:ℝ)*(di+ds)+I+3/(n+1:ℕ)) (by positivity : 0 ≤ CB+1)
    convert HH using 1; ring
  have H:=hjP i star U k seed T P hP hi hs hU hT hdepth hmi hms hcut a z l t hl ht
  have hscale : 0 ≤ |P.coefficient| *nativeResourceScale M.data.d M.data.d 1 seed:=
    mul_nonneg (abs_nonneg _) (actual_resource_raw_scale_pos seed M.data.hd M.data.hd).le
  apply H.trans
  have HH:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left Hcost'
    (mul_nonneg hCp.le (sq_nonneg M.data.d))) hscale
  convert HH using 1; dsimp only [C]; ring

theorem eventually_actual_high_wall_fresh_resource_third_LOW_local_thermal_profile
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
        Ccut*M.data.d ≤ 1 → partitionPoint 0 as U ≤ Ccut*M.data.d →
        ∀l t : ℝ,l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 →
        let di:=nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ)
        let ds:=nativeOriginalCutLowErrorRadius n M.bf M.hf as star+1/(n+1:ℕ)
        let I:=∫u in 0..Ccut*M.data.d,Real.sqrt (orderedPathB (n+1) M.bf M.hf u-
          (orderedPathS (n+1) M.bf M.hf u)^2)
        |(M.data.d⁻¹)^k*actualGeneralOriginalFreshResourceThirdLowPart M.bf M.hf U P l t| ≤
          |P.coefficient| *nativeResourceScale M.data.d M.data.d 1 seed*(C*M.data.d^2*(di+ds+I)) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_high_wall_centered_resource_third_LOW_local_thermal_profile
    (D:=D) degree (rBound+1) Bclock Cmass Ccut hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro i star U k seed T P hP hi hs hU hT hdepth hmi hms hcut1 hcut l t hl ht
  let g:=nativeFreshAtSlot T 0 P.live.test.target star
  have hg : g.tree.leaves ≤ rBound+1:=by
    have H:=T.markedAttach_leaves 0 g (nativeFreshAtSlot_mem T 0 P.live.test.target star)
    omega
  rw [actual_general_original_fresh_resource_third_LOW_eq_centered_retarget M.bf M.hf U P
    (finiteCutMasses_ordered us hus jGrid)]
  exact hj i star U k seed g.tree (P.retarget 0) hP.retarget hi hs hU hg hdepth hmi hms hcut1 hcut
    (g.embed P.live.test.target) g.mark l t hl ht

end OAI.SKFluctuations.Cavity
