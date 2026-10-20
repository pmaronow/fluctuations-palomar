module

public import ComparisonSignedCavityInheritedContinuumScalarFourBound
public import ComparisonActualHighOnlyAnalyticBasics
public import ComparisonActualHighOnlyResourcePhysicalFactories
public import ComparisonActualHighOnlyPullbackFourInterfaces
public import ComparisonActualHighOnlySourceProjectionAlong
public import ComparisonActualHighOnlyGaCurrentPrerequisites

@[expose] public section

noncomputable section
set_option linter.unusedVariables false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
set_option maxHeartbeats 14000000
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy LaplaceWindowFormalization ActualHighOnlyOverlapMinimum
open scoped BigOperators Topology NNReal

theorem eventually_actual_minimum_inherited_continuum_scalar_four_deeper_bound_high_only
    (r : ℕ) (Bclock Temp Cf : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cg : ℝ,0 < Cg ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf →
      ∀(as : List PositiveMass),MassOrdered 0 as →
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        ∀(tree : ClockTree (Spin n×Bool) as) (U : ℕ),0 < U → tree.leaves ≤ r →
        ∀a c e f : tree.Slot,a≠c → U ≤ tree.splitIndex a c →
        tree.splitIndex a c < tree.splitIndex e f →
        let v:=M.R (partitionPoint 0 as (tree.splitIndex a c))
        M.xs ≤ v → M.z ≤ v →
        |fullScalarCutConnected4 tree U K a c e f| ≤ Cg*v := by
  obtain ⟨Cs,hCs,HS⟩:=eventually_actual_high_only_mass_mean_upper
    (D:=D) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let Ck:=Cf+Temp*Cs+1
  have hCk : 0 < Ck:=by dsimp only [Ck];positivity
  let Cr:=ClockTree.errorJetVariation r 0 0*((r:ℝ)+1)+1
  have hCr : 0 < Cr:=by
    have H:=ClockTree.errorJetVariation_nonneg r 0 0
    dsimp only [Cr]
    positivity
  refine ⟨Cr*(Ck*(1+cu)),by positivity,?_⟩
  filter_upwards [HS] with n hnS
  intro M hs0 hsxs hsource as ho
  dsimp only
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  have HSunit j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.bf M.hf
    (M.inherited_bf_monotone) (M.inherited_hf_monotone) (partitionPoint_mem as ho j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.bf u:ℝ) ≤ M.bf v from M.inherited_bf_monotone hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.hf u:ℝ) ≤ M.hf v from M.inherited_hf_monotone hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.bf M.hf (M.inherited_bf_monotone) (M.inherited_hf_monotone)) as ho
  have hK0 j : 0 ≤ K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HSunit j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HSunit i).1 (NNReal.coe_nonneg _))
  intro tree U hU hleaves a c e f hac hUtarget hdeep hxv hzv
  let j:=tree.splitIndex a c
  let v:=M.R (partitionPoint 0 as j)
  have hu:=partitionPoint_mem as ho j
  have hv:=M.R_bounds (partitionPoint 0 as j)
  have hmass : partitionPoint 0 as j ≤ cu*v:=by
    have Hreg:=(M.regular v ⟨hzv,hv.2⟩).2
    rw [M.R_spec_high hu (M.hxs.trans_le hxv)] at Hreg
    exact Hreg
  have HSu : S j ≤ Cs*(M.xs+partitionPoint 0 as j):=by
    by_cases hz : partitionPoint 0 as j=0
    · simp only [S,hz,orderedPathS,orderedPathPair_zero]
      have hxs:=M.hxs
      positivity
    · exact hnS M hs0 hsxs _ ⟨lt_of_le_of_ne hu.1 (Ne.symm hz),hu.2⟩
  have Hsource:=hsource _ hu
  have Hprod:=mul_le_mul Hsource.1 HSu (HSunit j).1 hTemp
  have Hraw : K j ≤ Ck*(M.xs+partitionPoint 0 as j):=by
    dsimp only [K,Ck] at *
    nlinarith only [Hsource.2,Hprod,M.hxs,hu.1]
  have Hsum : M.xs+partitionPoint 0 as j ≤ (1+cu)*v:=by linarith only [hxv,hmass]
  have Hbound : K j ≤ (Ck*(1+cu))*v:=
    Hraw.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left Hsum hCk.le)
  have HC:=native_full_scalar_four_deeper_split_abs_le_clock tree ho r hleaves U hU K hKm hK0
    a c e f hac hUtarget hdeep
  exact HC.trans (by
    change Cr*K j ≤ _
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left Hbound hCr.le)

end OAI.SKFluctuations.Cavity
