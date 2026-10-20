module

public import ComparisonSignedCavityTargetScalarCutExchange
public import ComparisonSignedCavityScalarInheritedContinuumRemainder
public import ComparisonNativeActualInheritedClocks

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree Cavity
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 14000000

theorem eventually_actual_minimum_inherited_continuum_cut_clock_upper
    (Bclock Temp Cf A : ℝ) (hT : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hA : 0 ≤ A)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃R : ℝ,0 < R ∧∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf →
      ∀as : List PositiveMass,MassOrdered 0 as →
      ∀W : ℝ,0 ≤ W → M.xs ≤ W →
      ∀V : ℕ,partitionPoint 0 as V ≤ A*W →
        nativeContinuumMixedClock n M.bf M.hf as (V-1) ≤ R*W := by
  obtain ⟨Cs,hCs,HS⟩:=eventually_actual_minimum_mass_mean_upper
    (D:=D) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let Ck:=Cf+Temp*Cs
  let R:=Ck*(1+A)+1
  have hCk : 0 ≤ Ck:=by dsimp only [Ck];positivity
  have hR : 0 < R:=by dsimp only [R];positivity
  refine ⟨R,hR,?_⟩
  filter_upwards [HS] with n hn
  intro M hsource as ho W hW hxW V hmass
  let u:=partitionPoint 0 as V
  have hu : u∈Icc (0:ℝ) 1:=partitionPoint_mem as ho V
  have HS' : orderedPathS (n+1) M.bf M.hf u ≤ Cs*(M.xs+u) := by
    by_cases hp : 0 < u
    · exact hn M u ⟨hp,hu.2⟩
    · have hz : u=0:=le_antisymm (le_of_not_gt hp) hu.1
      rw [hz,orderedPathS,orderedPathPair_zero]
      simpa only [add_zero] using mul_nonneg hCs.le M.hxs.le
  have Hsource:=hsource u hu
  have Hprod:=mul_le_mul Hsource.1 HS' (M.mass_mean_nonneg hu) hT
  have HK : nativeContinuumMixedClock n M.bf M.hf as V ≤ Ck*(M.xs+u) := by
    dsimp only [nativeContinuumMixedClock,Ck,u]
    dsimp only [u] at Hsource Hprod
    nlinarith only [Hsource.2,Hprod]
  have Hsize : M.xs+u ≤ (1+A)*W:=by
    change u ≤ A*W at hmass
    nlinarith only [hxW,hmass]
  have H : nativeContinuumMixedClock n M.bf M.hf as V ≤ Ck*(1+A)*W:=
    HK.trans (by convert mul_le_mul_of_nonneg_left Hsize hCk using 1;ring)
  have Hmon:=native_continuum_mixed_clock_monotone n M.bf M.hf
    M.inherited_bf_monotone M.inherited_hf_monotone as ho (show V-1 ≤ V from Nat.sub_le _ _)
  apply Hmon.trans (H.trans _)
  dsimp only [R]
  nlinarith only [hW]

theorem eventually_actual_minimum_inherited_scalar_connected_cut_exchange
    (Bclock Temp Cf A : ℝ) (hT : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hA : 0 ≤ A)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃R : ℝ,0 < R ∧∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf →
      ∀as : List PositiveMass,MassOrdered 0 as →
      ∀W : ℝ,0 ≤ W → M.xs ≤ W →
      ∀U V : ℕ,0 < U → U ≤ V → partitionPoint 0 as V ≤ A*W →
      ∀r : ℕ,∀T : ClockTree (Spin n×Bool) as,T.leaves ≤ r →∀a c e f : T.Slot,
        |fullScalarCutConnected4 T U (nativeContinuumMixedClock n M.bf M.hf as) a c e f-
          fullScalarCutConnected4 T V (nativeContinuumMixedClock n M.bf M.hf as) a c e f| ≤
          3*(ClockTree.errorJetVariation r 0 0*((r:ℝ)+1))*R*W := by
  obtain ⟨R,hR,HR⟩:=eventually_actual_minimum_inherited_continuum_cut_clock_upper
    (D:=D) Bclock Temp Cf A hT hCf hA hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨R,hR,?_⟩
  filter_upwards [HR] with n hn
  intro M hsource as ho W hW hxW U V hU hUV hmass r T hleaves a c e f
  have H:=native_full_scalar_connected_four_cut_difference T ho r hleaves U V hU hUV
    (nativeContinuumMixedClock n M.bf M.hf as)
    (native_continuum_mixed_clock_monotone n M.bf M.hf M.inherited_bf_monotone M.inherited_hf_monotone as ho)
    (native_continuum_mixed_clock_nonneg n M.bf M.hf M.inherited_bf_monotone M.inherited_hf_monotone as ho) a c e f
  have hconst : 0 ≤ 3*(ClockTree.errorJetVariation r 0 0*((r:ℝ)+1)):=by
    exact mul_nonneg (by norm_num) (mul_nonneg (ClockTree.errorJetVariation_nonneg r 0 0) (by positivity))
  have H':=mul_le_mul_of_nonneg_left (hn M hsource as ho W hW hxW V hmass) hconst
  exact H.trans (by convert H' using 1;ring)

end OAI.SKFluctuations.LaplaceWindowFormalization
