module

public import ComparisonNativeInheritedCompletedBufferClocks
public import ComparisonNativeStarAllOrder
public import ComparisonNativeStarMinimumProjection
public import ComparisonSignedCavityActualBoundarySchedule

@[expose] public section

noncomputable section
set_option maxHeartbeats 7000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations
open Hierarchy LaplaceWindowFormalization
namespace NativeStarBuffer

theorem actual_minimum_inherited_original_star_projection_geometry
    {n : ℕ} {m delta cl cu Az C0 Ct Ddepth Bclock : ℝ}
    (M : NativeOverlapMinimum n m delta cl cu Az C0 Ct Ddepth Bclock)
    (hcl : 0 < cl) (hcu : 0 ≤ cu)
    (hN : 1 ≤ (n:ℝ)) (hlog : 1 ≤ Real.log (n:ℝ)) (hnd : 1/(n:ℝ) ≤ M.context.d)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (hend : partitionEnd 0 as=1)
    {mesh W s v theta ce Rmacro F Cprof H H₀ Lcount a₀ : ℝ}
    (hmesh : 0 ≤ mesh) (hpart : PartitionMesh mesh 0 as)
    (hW : 0 < W) (hWs : W ≤ s) (hsmall : mesh/M.context.floor ≤ s/16)
    (hfour : 4*s ≤ 1) (hce : 0 < ce)
    (hstrength : ce*W^2 ≤ laplaceComparisonStrength M.context.d M.lam W)
    (hregular : M.z ≤ s/2) (hmacro : 0 < Rmacro)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F)
    (hxss : M.xs ≤ s) (hv : 0 < v) (hv1 : v ≤ 1) (htheta : 0 < theta)
    (hCprof : 0 ≤ Cprof) (hcaproom : Cprof*v ≤ 1)
    (hcap : 0 < M.context.M (Cprof*v))
    (hshortlater : laplaceComparisonStrength M.context.d M.lam v*theta*v/
      (3*M.context.M (Cprof*v)*Real.log (n:ℝ)) ≤ ce*W^3/(24*Real.log (n:ℝ)))
    (hHlater : F/((cl/8)^2*s) ≤ H)
    (hHfirst : (1+4*cu)*s ≤ H*a₀^2) (hHupper : H ≤ H₀/v)
    {J fork t : ℕ} (hJ : 1 ≤ J) (hJmacro : Rmacro ≤ (2:ℝ)^J*s)
    (hJone : (2:ℝ)^J*s ≤ 1) (hcount : ((J+4:ℕ):ℝ) ≤ Lcount*Real.log (n:ℝ))
    (hfork : fork ≤ t) (ht : t ≤ as.length)
    (htradius : M.R (partitionPoint 0 as t) ≤ s/2)
    (htradiusv : M.R (partitionPoint 0 as t) ≤ v)
    (ha₀ : 0 < a₀) (hanchor : a₀ ≤ partitionPoint 0 as fork)
    (htcap : partitionPoint 0 as t ≤ Cprof*v)
    (hgap : theta*v ≤ partitionPoint 0 as t-partitionPoint 0 as fork) :
    Nonempty (OriginalStarProjectionGeometry
      (sampleClockSteps (completedPathClock n M.bf M.hf) 0 as) fork t
      M.xs H v theta M.context.d M.lam M.context.E delta Cprof Lcount H₀ Bclock) := by
  classical
  let R := M.R
  let rg : Fin (as.length+2) → ℝ := fun i=>R (partitionPoint 0 as i.val)
  let high := radiusGridCut rg (4*s)
  let steps := sampleClockSteps (completedPathClock n M.bf M.hf) 0 as
  let field : GaussianStep (FeatureIndex n) → ℝ≥0 := fun st=>st.2 (Sum.inl ⟨0,M.context.hn⟩)
  let D₀ := laplaceComparisonStrength M.context.d M.lam v*theta*v/
    (3*M.context.M (Cprof*v)*Real.log (n:ℝ))
  have hs : 0 < s := hW.trans_le hWs
  have hlogpos : 0 < Real.log (n:ℝ) := zero_lt_one.trans_le hlog
  have hreg (r : ℝ) (hr : r∈Icc (s/2) 1) :
      cl*r ≤ M.alpha.val.val r  ∧  M.alpha.val.val r ≤ cu*r :=
    M.regular r ⟨hregular.trans hr.1,hr.2⟩
  have hmono : Monotone rg := fun i j hij=>
    comparisonSweepQuantile_monotone M.context.hc M.context.hk M.context.hkc
      M.context.hm M.context.hM M.alpha (partitionPoint_mono as ho hij)
  have hz : rg 0=0 := by
    simpa [rg,R,partitionPoint,partitionValues] using
      comparisonSweepQuantile_zero M.context.hc M.context.hk M.context.hkc
        M.context.hm M.context.hM M.alpha
  have hlast : rg (Fin.last (as.length+1))=1 := by
    change M.R (partitionPoint 0 as (as.length+1))=1
    rw [Cavity.partitionPoint_after_final 0 as _ (by omega),hend]
    exact comparisonSweepQuantile_one M.context.hc M.context.hk M.context.hkc
      M.context.hm M.context.hM M.alpha
  have hsteps : ∀j : Fin (as.length+1),rg j.succ-rg j.castSucc ≤ mesh/M.context.floor :=
    fun j=>Cavity.actual_comparison_partition_radius_step_le M.context.hc M.context.hk
      M.context.hkc M.context.hm M.context.hM M.alpha as ho hmesh hpart j.val
  have hhighbound := radiusGridPoint_bounds rg hmono
    (show rg 0 < 4*s by rw [hz]; positivity)
    (show 4*s ≤ rg (Fin.last (as.length+1)) by rw [hlast]; exact hfour) hsteps
  change 4*s-mesh/M.context.floor ≤ M.R (partitionPoint 0 as high)  ∧
    M.R (partitionPoint 0 as high) < 4*s at hhighbound
  have hhigh : high ≤ as.length := radiusGridCut_le rg (4*s)
  have hhighradius : 2*s ≤ M.R (partitionPoint 0 as high) := by linarith [hhighbound.1]
  have hhf : MonotoneOn M.hf (Icc (0:ℝ) 1) := by
    exact toNNReal_monotoneOn (comparisonVariableEndpoint_clocks_admissible M.context.hc
      M.context.hk M.context.hkc M.context.hm M.context.hM M.b M.h M.context.hd.ne'
      M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha).2.1
  have hbf : MonotoneOn M.bf (Icc (0:ℝ) 1) := by
    exact toNNReal_monotoneOn (comparisonVariableEndpoint_clocks_admissible M.context.hc
      M.context.hk M.context.hkc M.context.hm M.context.hM M.b M.h M.context.hd.ne'
      M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha).1
  have hB : physicalFieldDuration field steps ≤ Bclock := by
    rw [sampledFieldDuration_total n M.context.hn M.bf M.hf hbf hhf as ho hend]
    exact M.clockBudget
  obtain ⟨cs,u,a,D,hlen,htu,huhigh,hub,hlastcs,hends,hclocks,hscales,_,_⟩ :=
    Cavity.exists_actual_comparison_boundary_projection_schedule n M.context.hn
      M.context.hc M.context.hk M.context.hkc M.context.hm M.context.hM M.alpha M.b M.h
      M.hb M.hlb M.hh M.hh0 hN hlog M.context.hd hnd M.hlam M.hld
      as ho hend hmesh hpart hs hsmall hW hWs hce hstrength hcl hcu hmacro
      hFmass hFradius M.hxs.le hxss hreg hJ hJmacro hJone hhigh htradius hhighradius M.clockBudget
  have hcapactual : M.context.M (partitionPoint 0 as t) ≤ M.context.M (Cprof*v) :=
    M.context.hm (partitionPoint_mem as ho t) ⟨mul_nonneg hCprof hv.le,hcaproom⟩ htcap
  have hstrengtht : laplaceComparisonStrength M.context.d M.lam v ≤
      laplaceComparisonStrength M.context.d M.lam (M.R (partitionPoint 0 as t)) :=
    (laplaceComparisonStrength_monotonicities M.context.hd.ne' M.hlam (r₀:=0) le_rfl).1
      (comparisonSweepQuantile_bounds M.context.hc M.context.hk M.context.hkc
        M.context.hm M.context.hM M.alpha _) ⟨hv.le,hv1⟩ htradiusv
  have hshort := comparison_inherited_completed_mass_innovation_clock M.context.hc M.context.hk
    M.context.hkc M.context.hm M.context.hM M.alpha n M.context.hn M.b M.hb M.hlb M.h M.hh M.hh0
    hN hlog M.context.hd hnd M.hlam M.hld (mul_nonneg htheta.le hv.le) hcap
    (laplaceComparisonStrength_pos M.context.d M.hlam v).le as ho
    (show fork ≤ fork from le_rfl) hfork htu ht (by simpa only [sampleClockSteps_length] using hub) ha₀.le hanchor hcapactual hgap hstrengtht
  dsimp only at hshort
  have hfirst : M.xs+physicalCutMass 0 steps u ≤ H*a₀^2 := by
    have humass : physicalCutMass 0 steps u=partitionPoint 0 as u :=
      physicalCutMass_sampleClockSteps _ _ _ u (huhigh.trans hhigh)
    rw [humass]
    have hhreg := hreg (M.R (partitionPoint 0 as high))
      ⟨by linarith, (comparisonSweepQuantile_bounds M.context.hc M.context.hk
        M.context.hkc M.context.hm M.context.hM M.alpha _).2⟩
    rw [comparisonSweepQuantile_spec M.context.hc M.context.hk M.context.hkc
      M.context.hm M.context.hM M.alpha (partitionPoint_mem as ho high)] at hhreg
    have hmasshi : partitionPoint 0 as high ≤ cu*(4*s) :=
      hhreg.2.trans (mul_le_mul_of_nonneg_left hhighbound.2.le hcu)
    have hmassu := partitionPoint_mono as ho huhigh
    nlinarith
  have hg : 0 < laplaceComparisonStrength M.context.d M.lam v :=
    laplaceComparisonStrength_pos M.context.d M.hlam v
  refine ⟨{
    D₀ := D₀
    duration_floor := le_rfl
    duration_pos := by dsimp [D₀]; positivity
    u := u
    cs := cs
    a := a
    D := D
    a₀ := a₀
    Dshort := physicalFieldDuration field (cutSlice steps fork t)
    central_le := htu
    terminal_bound := hub
    last_cut := hlastcs
    short_amplitude := ha₀
    short_floor := by simpa only [D₀,steps,field,mul_assoc] using hshort.1
    short_upper := (physicalFieldDuration_slice_le field steps fork t).trans hB
    short_clock := hshort.2
    first_anchor := hfirst
    layer_cuts := hends
    layer_clocks := ?_
    anchors := ?_
    count := ?_
    anchor_upper := hHupper }⟩
  · intro j
    exact ⟨(hclocks j).1,hshortlater.trans (hclocks j).2.1,(hclocks j).2.2.1,
      ((hclocks j).2.2.2).earlier_fork hfork⟩
  · intro i j hij
    exact (hscales i j hij).trans (mul_le_mul_of_nonneg_right hHlater (sq_nonneg (a j)))
  · simpa only [hlen,Nat.add_assoc] using hcount

end NativeStarBuffer
end OAI.SKFluctuations
