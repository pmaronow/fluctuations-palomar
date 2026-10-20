module

public import ComparisonSignedCavityActualContinuumScalarFourHighBound
public import ComparisonSignedCavityActualTerminalGAtom

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy LaplaceWindowFormalization
open scoped BigOperators Topology NNReal

theorem eventually_actual_minimum_bare_scalar_four_raw_scale_bound
    (r : ℕ) (Bclock Temp : ℝ) (hTemp : 0 ≤ Temp)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        (∀u,M.b u=Temp) → (∀u,M.h u=0) → M.xs ≤ 1 →
      ∀(as : List PositiveMass),MassOrdered 0 as →
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        ∀(tree : ClockTree (Spin n×Bool) as) (U : ℕ),0 < U → tree.leaves ≤ r →
        ∀a c e f : tree.Slot,a ≠ c → U ≤ tree.splitIndex a c →
        let v:=M.R (partitionPoint 0 as (tree.splitIndex a c))
        M.xs ≤ v → M.z ≤ v →
        |fullScalarCutConnected4 tree U K a c e f| *
          (M.xs+partitionPoint 0 as (tree.splitIndex e f)) ≤ C*v := by
  obtain ⟨Cg,hCg,HG⟩:=eventually_actual_minimum_bare_continuum_scalar_four_deeper_bound
    (D:=D) r Bclock Temp hTemp hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨2*(1+cu)+2*Cg,by positivity,?_⟩
  filter_upwards [HG] with n hn
  intro M hb hh hxs as ho
  dsimp only
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  intro tree U hU htree a c e f hac hUac hxv hzv
  let j:=tree.splitIndex a c
  let je:=tree.splitIndex e f
  let v:=M.R (partitionPoint 0 as j)
  have hv0:0 ≤ v:=M.hxs.le.trans hxv
  have he0:0 ≤ M.xs+partitionPoint 0 as je:=add_nonneg M.hxs.le (partitionPoint_mem as ho je).1
  by_cases hdeep:j < je
  · have Hκ:=hn M hb hh as ho tree U hU htree a c e f hac hUac hdeep hxv hzv
    have hraw:M.xs+partitionPoint 0 as je ≤ 2:=by linarith only [hxs,(partitionPoint_mem as ho je).2]
    have H:=mul_le_mul Hκ hraw he0 (mul_nonneg hCg.le hv0)
    apply H.trans
    change Cg*v*2 ≤ (2*(1+cu)+2*Cg)*v
    nlinarith only [mul_nonneg (by positivity : 0 ≤ 2*(1+cu)) hv0]
  · have hje:je ≤ j:=Nat.le_of_not_gt hdeep
    have hu:=partitionPoint_mem as ho j
    have hv:=comparisonSweepQuantile_bounds M.context.hc M.context.hk M.context.hkc
      M.context.hm M.context.hM M.alpha (partitionPoint 0 as j)
    have hmass:partitionPoint 0 as j ≤ cu*v:=by
      have Hreg:=(M.regular v ⟨hzv,hv.2⟩).2
      rw [comparisonSweepQuantile_spec M.context.hc M.context.hk M.context.hkc
        M.context.hm M.context.hM M.alpha hu] at Hreg
      exact Hreg
    have hraw:M.xs+partitionPoint 0 as je ≤ (1+cu)*v:=by
      have Hmono:=partitionPoint_mono as ho hje
      linarith only [hxv,hmass,Hmono]
    have Hκ:=native_full_scalar_connected_four_abs_le_two tree ho U K a c e f
    have H:=mul_le_mul Hκ hraw he0 (by norm_num : (0:ℝ) ≤ 2)
    apply H.trans
    change 2*((1+cu)*v) ≤ (2*(1+cu)+2*Cg)*v
    nlinarith only [mul_nonneg hCg.le hv0]

end OAI.SKFluctuations.Cavity
