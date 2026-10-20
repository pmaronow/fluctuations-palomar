module

public import ComparisonSignedCavityInheritedTargetScalarCutExchange
public import SKProof.Port.ComparisonActualOriginalQPullbackFourProducers
public import SKProof.Port.ComparisonActualOriginalQTargetGCutEnvelope
public import SKProof.Port.ComparisonActualOriginalQTargetGCutDensity
public import ComparisonSignedCavityTargetScalarCutExchange
public import ComparisonSignedCavityScalarInheritedContinuumRemainder
public import ComparisonNativeActualInheritedClocks

@[expose] public section

noncomputable section
set_option linter.unusedVariables false
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree Cavity
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 14000000

theorem eventually_actual_minimum_inherited_continuum_cut_clock_upper_original_q
    (Bclock Temp Cf A : ℝ) (hT : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hA : 0 ≤ A)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃R : ℝ,0 < R ∧∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs → ActualOriginalQSmallSourceClocks M Temp Cf →
      ∀as : List PositiveMass,MassOrdered 0 as →
      ∀W : ℝ,0 ≤ W → M.xs ≤ W →
      ∀V : ℕ,partitionPoint 0 as V ≤ A*W →
        nativeContinuumMixedClock n M.sweepBf M.sweepHf as (V-1) ≤ R*W := by
  obtain ⟨Cs,hCs,HS⟩:=ActualThetaZeroOverlapMinimum.eventually_actual_mass_mean_upper_original_q
    (D:=D) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let Ck:=Cf+Temp*Cs
  let R:=Ck*(1+A)+1
  have hCk : 0 ≤ Ck:=by dsimp only [Ck];positivity
  have hR : 0 < R:=by dsimp only [R];positivity
  refine ⟨R,hR,?_⟩
  filter_upwards [HS] with n hn
  intro M hs0 hsxs hsource as ho W hW hxW V hmass
  let u:=partitionPoint 0 as V
  have hu : u∈Icc (0:ℝ) 1:=partitionPoint_mem as ho V
  have HS' : orderedPathS (n+1) M.sweepBf M.sweepHf u ≤ Cs*(M.xs+u) := by
    by_cases hp : 0 < u
    · exact hn M hs0 hsxs u ⟨hp,hu.2⟩
    · have hz : u=0:=le_antisymm (le_of_not_gt hp) hu.1
      rw [hz,orderedPathS,orderedPathPair_zero]
      simpa only [add_zero] using mul_nonneg hCs.le M.hxs.le
  have Hsource:=hsource u hu
  have Hprod:=mul_le_mul Hsource.1 HS' (M.mass_mean_nonneg hu) hT
  have HK : nativeContinuumMixedClock n M.sweepBf M.sweepHf as V ≤ Ck*(M.xs+u) := by
    dsimp only [nativeContinuumMixedClock,Ck,u]
    dsimp only [u] at Hsource Hprod
    nlinarith only [Hsource.2,Hprod]
  have Hsize : M.xs+u ≤ (1+A)*W:=by
    change u ≤ A*W at hmass
    nlinarith only [hxW,hmass]
  have H : nativeContinuumMixedClock n M.sweepBf M.sweepHf as V ≤ Ck*(1+A)*W:=
    HK.trans (by convert mul_le_mul_of_nonneg_left Hsize hCk using 1;ring)
  have Hmon:=native_continuum_mixed_clock_monotone n M.sweepBf M.sweepHf
    M.inherited_bf_monotone M.inherited_hf_monotone as ho (show V-1 ≤ V from Nat.sub_le _ _)
  apply Hmon.trans (H.trans _)
  dsimp only [R]
  nlinarith only [hW]

end OAI.SKFluctuations.LaplaceWindowFormalization
