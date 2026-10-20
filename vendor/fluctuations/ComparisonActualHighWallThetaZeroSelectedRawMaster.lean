module

public import ComparisonActualHighWallThetaZeroRetainedRaw
public import ComparisonActualHighWallThetaZeroRetainedRowsBasics
public import ComparisonActualHighWallSelectedMaster

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 18000000
attribute [local instance] Classical.propDecidable

namespace ActualThetaZeroOverlapMinimum
variable {n:ℕ} {m delta cl cu Az C0 Ct D Bclock:ℝ}

structure SelectedRawMaster
    (Q:ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (Dcuts:Finset ℝ) (ell:ℕ) (Craw:ℝ) where
  nodes:List PositiveMass
  bound:∀u∈nodes,u.val≤1
  retains:∀d∈Dcuts,∀hp:0<Q.alpha.val.val d,
    (⟨Q.alpha.val.val d,hp⟩:PositiveMass)∈nodes
  sampler:ℕ→ℕ
  strict:StrictMono sampler
  raw:∀j,physicalRawRatio (n+1) ell
    (sampleClockSteps Q.shiftedNativeModel.q 0 (finiteCutMasses nodes (sampler j)))
    0 Q.xs (Measure.pi fun k=>gaussianReal 0 (Q.shiftedNativeModel.q 0 k))
    id measurable_id≤Craw

end ActualThetaZeroOverlapMinimum

theorem eventually_exists_actual_theta_zero_selected_raw_master
    (ell:ℕ) (hell:2<ell) (Bclock:ℝ) {m delta cl cu Az C0 Ct D:ℝ}
    (hm:0 < m) (hdelta:0 < delta) (hroom:delta < 3*m)
    (hcl:0<cl) (hcu:0<cu) (hAz:0≤Az) (hC0:0<C0) (hCt:0≤Ct):
    ∃Craw:ℝ,1≤Craw ∧ ∀ᶠn:ℕ in atTop,
      ∀(Q:ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (Dcuts:Finset ℝ),
        Nonempty (ActualThetaZeroOverlapMinimum.SelectedRawMaster Q Dcuts ell Craw):=by
  have horder:ell-1+1=ell:=by omega
  obtain ⟨C0raw,hC0raw,Hraw⟩:=eventually_actual_theta_zero_original_boundary_raw
    (ell-1) Bclock (D:=D) hm hdelta hroom hcl hcu hAz hC0 hCt
  let Craw:=max 1 (Real.sqrt (2*C0raw))
  refine ⟨Craw,le_max_left _ _,?_⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually Hraw] with n hn
  intro Q Dcuts
  let extra:=finiteBoundaryMassNodes (Dcuts.image Q.alpha.val.val)
  have hextra:∀u∈extra,u.val≤1:=finiteBoundaryMassNodes_bound _ (fun d hd=>by
    obtain ⟨r,_,rfl⟩:=Finset.mem_image.mp hd
    exact (Q.alpha.val.property.1 r).2)
  obtain ⟨us,hus,_,hretains,hraw⟩:=hn Q (⟨1,by norm_num⟩:PositiveMass)
    le_rfl extra hextra
  have retain d (hd:d∈Dcuts) (hp:0<Q.alpha.val.val d):
      (⟨Q.alpha.val.val d,hp⟩:PositiveMass)∈us:=
    hretains _ (finiteBoundaryMassNodes_mem _
      (Finset.mem_image.mpr ⟨d,hd,rfl⟩) hp)
  have rawBound:∀ᶠj in atTop,physicalRawRatio (n+1) ell
      (sampleClockSteps Q.shiftedNativeModel.q 0 (finiteCutMasses us j)) 0 Q.xs
      (Measure.pi fun k=>gaussianReal 0 (Q.shiftedNativeModel.q 0 k))
      id measurable_id≤Craw:=by
    filter_upwards [hraw] with j hj
    dsimp only at hj
    rw [horder] at hj
    have HS:=Real.sq_sqrt (show 0≤2*C0raw by positivity)
    have Hsqrt:=Real.sqrt_nonneg (2*C0raw)
    apply le_trans _ (le_max_right 1 (Real.sqrt (2*C0raw)))
    nlinarith [hj.1]
  obtain ⟨J0,hJ0⟩:=eventually_atTop.mp rawBound
  exact ⟨{
    nodes:=us
    bound:=hus
    retains:=retain
    sampler:=fun j=>j+J0
    strict:=fun i j hij=>Nat.add_lt_add_right hij J0
    raw:=fun j=>hJ0 (j+J0) (by omega) }⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
