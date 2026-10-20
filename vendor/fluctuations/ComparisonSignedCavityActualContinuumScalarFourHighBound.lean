module

public import ComparisonSignedCavityScalarFourSplitLocality
public import ComparisonSignedCavityBareContinuumLowProfile

@[expose] public section

noncomputable section
set_option maxHeartbeats 14000000
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy LaplaceWindowFormalization
open scoped BigOperators Topology NNReal

theorem eventually_actual_minimum_bare_continuum_scalar_four_deeper_bound
    (r : ℕ) (Bclock Temp : ℝ) (hTemp : 0 ≤ Temp)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cg : ℝ,0 < Cg ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        (∀u,M.b u=Temp) → (∀u,M.h u=0) →
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
  obtain ⟨Cs,hCs,HS⟩:=eventually_actual_minimum_continuum_center_bound
    (D:=D) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cf:=NativeOverlapMinimum.bareSourceClockConstant cl Az D
  have hCf : 0 ≤ Cf:=NativeOverlapMinimum.bare_source_clock_constant_nonneg hcl hAz
  let Ck:=Cf+Temp*Cs+1
  have hCk : 0 < Ck:=by dsimp only [Ck];positivity
  let Cr:=ClockTree.errorJetVariation r 0 0*((r:ℝ)+1)+1
  have hCr : 0 < Cr:=by
    have H:=ClockTree.errorJetVariation_nonneg r 0 0
    dsimp only [Cr]
    positivity
  refine ⟨Cr*(Ck*(1+cu)),by positivity,?_⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually HS] with n hnS
  intro M hb hh as ho
  dsimp only
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  have had:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have HSunit j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.bf M.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) (partitionPoint_mem as ho j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.bf u:ℝ) ≤ M.bf v from toNNReal_monotoneOn had.1 hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.hf u:ℝ) ≤ M.hf v from toNNReal_monotoneOn had.2.1 hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.bf M.hf (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1)) as ho
  have hK0 j : 0 ≤ K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HSunit j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HSunit i).1 (NNReal.coe_nonneg _))
  intro tree U hU hleaves a c e f hac hUtarget hdeep hxv hzv
  let j:=tree.splitIndex a c
  let v:=M.R (partitionPoint 0 as j)
  have hu:=partitionPoint_mem as ho j
  have hv:=comparisonSweepQuantile_bounds M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha (partitionPoint 0 as j)
  have hmass : partitionPoint 0 as j ≤ cu*v:=by
    have Hreg:=(M.regular v ⟨hzv,hv.2⟩).2
    rw [comparisonSweepQuantile_spec M.context.hc M.context.hk M.context.hkc
      M.context.hm M.context.hM M.alpha hu] at Hreg
    exact Hreg
  have Hcenter:=native_ordered_source_center_eq_completed n M.bf M.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) hu
  have HSu : S j ≤ Cs*(M.xs+partitionPoint 0 as j):=by
    have HC:=continuum_center_bound_closed_interval (n+1) M.bf M.hf M.hxs.le hCs.le (hnS M) _ hu
    rw [←Hcenter] at HC
    exact (le_abs_self _).trans HC
  have Hsource:=M.bare_source_clock_bounds hcl hAz Temp hb hh hu
  have Hprod:=mul_le_mul Hsource.2.1 HSu (HSunit j).1 hTemp
  have Hraw : K j ≤ Ck*(M.xs+partitionPoint 0 as j):=by
    dsimp only [K,Ck,Cf] at *
    nlinarith only [Hsource.2.2.2,Hprod,M.hxs,hu.1]
  have Hsum : M.xs+partitionPoint 0 as j ≤ (1+cu)*v:=by linarith only [hxv,hmass]
  have Hbound : K j ≤ (Ck*(1+cu))*v:=
    Hraw.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left Hsum hCk.le)
  have HC:=native_full_scalar_four_deeper_split_abs_le_clock tree ho r hleaves U hU K hKm hK0
    a c e f hac hUtarget hdeep
  exact HC.trans (by
    change Cr*K j ≤ _
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left Hbound hCr.le)

end OAI.SKFluctuations.Cavity
