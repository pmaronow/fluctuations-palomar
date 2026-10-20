module

public import ComparisonActualHighWallContinuumGammaRadius

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 12000000

theorem eventually_actual_high_wall_continuum_clock_mass_upper
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃CK : ℝ,0 < CK ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      M.xs=M.data.d → ∀as : List PositiveMass,MassOrdered 0 as → ∀j : ℕ,
        nativeContinuumMixedClock n M.bf M.hf as j ≤ CK*(M.xs+partitionPoint 0 as j) := by
  obtain ⟨Cs,hCs,HS⟩:=eventually_actual_high_wall_mass_mean_upper
    (D:=D) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let B:=max Bclock 0
  let CK:=2+B*Cs
  have hB : 0 ≤ B:=le_max_right _ _
  refine ⟨CK,by dsimp only [CK];positivity,?_⟩
  filter_upwards [HS] with n hn
  intro M hwork as ho j
  let u:=partitionPoint 0 as j
  have hu:=partitionPoint_mem as ho j
  have Hmean : orderedPathS (n+1) M.bf M.hf u ≤ Cs*(M.xs+u):=by
    by_cases hz : u=0
    · simp only [hz,orderedPathS,orderedPathPair_zero,add_zero]
      exact mul_nonneg hCs.le M.hxs.le
    · exact hn M u ⟨lt_of_le_of_ne hu.1 (Ne.symm hz),hu.2⟩
  have Hsource:=M.data.small_source_clock_budget M.alpha hwork.ge hu
  have Hb : (M.bf u:ℝ) ≤ B:=Hsource.1.trans (M.hT.trans (le_max_left _ _))
  have Hprod:=mul_le_mul Hb Hmean (M.mass_mean_nonneg hu) hB
  have hnat : 0 ≤ M.xs+u:=add_nonneg M.hxs.le hu.1
  dsimp only [nativeContinuumMixedClock,CK,u] at *
  nlinarith only [Hsource.2,Hprod,hnat]

end OAI.SKFluctuations.Cavity
