module

public import ComparisonSignedCavityMinimumSourceClocks
public import ComparisonSignedCavityScalarMinimumBuffer

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity
set_option maxHeartbeats 4000000

theorem eventually_actual_minimum_bare_finite_mean_clock_bounds
    (Bclock Temp : ℝ) (hT : 0 ≤ Temp) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cs Ck : ℝ,0 < Cs ∧ 0 < Ck ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        (∀u,M.b u=Temp) → (∀u,M.h u=0) → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        ∀j ≤ as.length,
          finitePhysicalMean (n+1) as (retainedStarMatrix M.bf as) (retainedStarField M.hf as) j ≤
            Cs*(M.xs+partitionPoint 0 as j) ∧
          retainedStarMixedClock n M.bf M.hf as j ≤ Ck*(M.xs+partitionPoint 0 as j) := by
  let Cf:=NativeOverlapMinimum.bareSourceClockConstant cl Az D
  have hCf : 0 ≤ Cf := NativeOverlapMinimum.bare_source_clock_constant_nonneg hcl hAz
  obtain ⟨Cs,hCs,HS⟩:=eventually_actual_minimum_deleted_raw_on_retained_net
    (D:=D) 1 (by norm_num) Bclock (4*Cf+2*Temp) Temp hm hdelta hroom
    hcl hcu hAz hC0 hCt
  let Ck:=Cf+Temp*Cs+1
  have hCk : 0 < Ck := by dsimp [Ck];positivity
  refine ⟨Cs,Ck,hCs,hCk,?_⟩
  filter_upwards [HS] with n hn
  intro M hb hh hxs L us hus hret hmesh
  filter_upwards [hn M L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro j hj
  let as:=finiteCutMasses us k
  have ho : MassOrdered 0 as := finiteCutMasses_ordered us hus k
  have HC:=M.bare_sampled_full_square_clock_budget hcl hAz Temp hb hh hxs as ho
  have HB:=(M.bare_source_clock_bounds hcl hAz Temp hb hh (partitionPoint_mem as ho as.length)).2.1
  have HR:=hk j hj HC HB
  have hmass:=partitionPoint_mem as ho j
  have hnatural : 0 ≤ Cs*(M.xs+partitionPoint 0 as j) :=
    mul_nonneg hCs.le (add_nonneg M.hxs.le hmass.1)
  have Hmean:=finitePhysicalMean_le_of_deleted_raw n 1 (by norm_num) ho
    (retainedStarMatrix M.bf as) (retainedStarField M.hf as) j hj
    (fun l=>(M.bf (partitionPoint 0 as l)).coe_nonneg)
    (fun l=>(M.hf (partitionPoint 0 as l)).coe_nonneg) hnatural HR
  have Hclock:=M.bare_source_clock_bounds hcl hAz Temp hb hh hmass
  have Hprod:=mul_le_mul Hclock.2.1 Hmean
    (finitePhysicalMean_nonneg (n+1) as (retainedStarMatrix M.bf as) (retainedStarField M.hf as) j) hT
  refine ⟨Hmean,?_⟩
  change (M.hf (partitionPoint 0 as j):ℝ)+(M.bf (partitionPoint 0 as j):ℝ)*
    finitePhysicalMean (n+1) as (retainedStarMatrix M.bf as) (retainedStarField M.hf as) j ≤ _
  have Hfield:=Hclock.2.2.2
  dsimp only [Ck,Cf] at *
  nlinarith [hmass.1,M.hxs]

end OAI.SKFluctuations.LaplaceWindowFormalization
