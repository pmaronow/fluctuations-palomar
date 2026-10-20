module

public import ComparisonActualHighWallShortProjection
public import ComparisonActualHighWallBoundarySchedule
public import ComparisonNativeStarAllOrder

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 15000000
set_option backward.isDefEq.respectTransparency false
namespace NativeStarBuffer
theorem actual_high_wall_original_star_projection_geometry
    {n : ℕ} {m delta cl cu Az C0 Ct Ddepth Bclock : ℝ}
    (M : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct Ddepth Bclock)
    (hcl : 0 < cl) (hcu : 0 ≤ cu)
    (hN : 1 ≤ (n:ℝ)) (hlog : 1 ≤ Real.log (n:ℝ)) (hnd : 1/(n:ℝ) ≤ M.data.d)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (hend : partitionEnd 0 as=1)
    {mesh W s v theta ce Rmacro F Cprof H H₀ Lcount a₀ : ℝ}
    (hmesh : 0 ≤ mesh) (hpart : PartitionMesh mesh 0 as)
    (hW : 0 < W) (hWs : W ≤ s) (hwall : M.data.rmin ≤ s/2) (hsmall : mesh/(M.data.k 1) ≤ s/16)
    (hfour : 4*s ≤ 1) (hce : 0 < ce)
    (hstrength : ce*W^2 ≤ M.data.g W)
    (hregular : M.z ≤ s/2) (hmacro : 0 < Rmacro)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F)
    (hxss : M.xs ≤ s) (hv : 0 < v) (hv1 : v ≤ 1) (htheta : 0 < theta)
    (hCprof : 0 ≤ Cprof) (hcaproom : Cprof*v ≤ 1)
    (hcap : 0 < M.data.M (Cprof*v))
    (hshortlater : M.data.g v*theta*v/
      (3*M.data.M (Cprof*v)*Real.log (n:ℝ)) ≤ ce*W^3/(24*Real.log (n:ℝ)))
    (hHlater : F/((cl/8)^2*s) ≤ H)
    (hHfirst : (1+4*cu)*s ≤ H*a₀^2) (hHupper : H ≤ H₀/v)
    {J fork t : ℕ} (hJ : 1 ≤ J) (hJmacro : Rmacro ≤ (2:ℝ)^J*s)
    (hJone : (2:ℝ)^J*s ≤ 1) (hcount : ((J+4:ℕ):ℝ) ≤ Lcount*Real.log (n:ℝ))
    (hfork : fork ≤ t) (ht : t ≤ as.length)
    (htradius : (M.data.wallRadius M.alpha) (partitionPoint 0 as t) ≤ s/2)
    (htradiusv : (M.data.wallRadius M.alpha) (partitionPoint 0 as t) ≤ v)
    (ha₀ : 0 < a₀) (hanchorHigh : M.data.s ≤ a₀) (hanchor : a₀ ≤ partitionPoint 0 as fork)
    (htcap : partitionPoint 0 as t ≤ Cprof*v)
    (hgap : theta*v ≤ partitionPoint 0 as t-partitionPoint 0 as fork) :
    Nonempty (OriginalStarProjectionGeometry
      (sampleClockSteps (completedPathClock n M.bf M.hf) 0 as) fork t
      M.xs H v theta M.data.d (M.data.d^2) M.data.E delta Cprof Lcount H₀ Bclock) := by
  classical
  let R := (M.data.wallRadius M.alpha)
  let rg : Fin (as.length+2) → ℝ := fun i=>R (partitionPoint 0 as i.val)
  let high := radiusGridCut rg (4*s)
  let steps := sampleClockSteps (completedPathClock n M.bf M.hf) 0 as
  let field : GaussianStep (FeatureIndex n) → ℝ≥0 := fun st=>st.2 (Sum.inl ⟨0,M.data.hn⟩)
  let D₀ := M.data.g v*theta*v/
    (3*M.data.M (Cprof*v)*Real.log (n:ℝ))
  have hs : 0 < s := hW.trans_le hWs
  have hlogpos : 0 < Real.log (n:ℝ) := zero_lt_one.trans_le hlog
  have hreg (r : ℝ) (hr : r∈Icc (s/2) 1) :
      cl*r ≤ M.alpha.val.val r  ∧  M.alpha.val.val r ≤ cu*r :=
    M.regular r ⟨hregular.trans hr.1,hr.2⟩
  have hmono : Monotone rg := fun i j hij=>
    M.data.wallRadius_monotone M.alpha (partitionPoint_mono as ho hij)
  have hz : rg 0=M.data.rmin := by
    simpa [rg,R,partitionPoint] using M.data.wallRadius_before M.alpha (u:=0) M.data.hs.1.le
  have hlast : rg (Fin.last (as.length+1))=1 := by
    change (M.data.wallRadius M.alpha) (partitionPoint 0 as (as.length+1))=1
    rw [Cavity.partitionPoint_after_final 0 as _ (by omega),hend]
    exact M.data.wallRadius_one M.alpha
  have hsteps : ∀j : Fin (as.length+1),rg j.succ-rg j.castSucc ≤ mesh/(M.data.k 1) :=
    fun j=>M.data.sampled_radius_step_le M.alpha as ho hmesh hpart j.val
  have hhighbound := radiusGridPoint_bounds rg hmono
    (show rg 0 < 4*s by rw [hz];linarith [hwall])
    (show 4*s ≤ rg (Fin.last (as.length+1)) by rw [hlast]; exact hfour) hsteps
  change 4*s-mesh/(M.data.k 1) ≤ (M.data.wallRadius M.alpha) (partitionPoint 0 as high)  ∧
    (M.data.wallRadius M.alpha) (partitionPoint 0 as high) < 4*s at hhighbound
  have hhigh : high ≤ as.length := radiusGridCut_le rg (4*s)
  have hhighradius : 2*s ≤ (M.data.wallRadius M.alpha) (partitionPoint 0 as high) := by linarith [hhighbound.1]
  have hhf : MonotoneOn M.hf (Icc (0:ℝ) 1) := M.data.hf_monotone M.alpha
  have hbf : MonotoneOn M.bf (Icc (0:ℝ) 1) := M.data.bf_monotone M.alpha
  have hB : physicalFieldDuration field steps ≤ Bclock := by
    rw [sampledFieldDuration_total n M.data.hn M.bf M.hf hbf hhf as ho hend]
    exact (M.data.field_clock_budget M.alpha).trans M.hT
  obtain ⟨cs,u,a,D,hlen,htu,huhigh,hub,hlastcs,hends,hclocks,hscales,_hcount,_hDpos⟩ :=
    Cavity.exists_actual_high_wall_boundary_projection_schedule M.data M.alpha hN hlog hnd
      as ho hend hmesh hpart hs hwall hsmall hW hWs hce hstrength hcl hcu hmacro
      hFmass hFradius M.hxs.le hxss hreg hJ hJmacro hJone hhigh htradius hhighradius
  have hcapactual : M.data.M (partitionPoint 0 as t) ≤ M.data.M (Cprof*v) :=
    M.data.hm (partitionPoint_mem as ho t) ⟨mul_nonneg hCprof hv.le,hcaproom⟩ htcap
  have hstrengtht : M.data.g v ≤ M.data.g (M.data.wallRadius M.alpha (partitionPoint 0 as t)) :=
    (laplaceComparisonStrength_monotonicities M.data.hd.ne' (sq_pos_of_pos M.data.hd)
      M.data.hrbounds.1.le).1
      ⟨(M.data.wallRadius_bounds M.alpha _).1,
        (M.data.wallRadius_bounds M.alpha _).2⟩
      ⟨(M.data.wallRadius_bounds M.alpha _).1.trans htradiusv,hv1⟩ htradiusv
  have hshort := M.data.completed_mass_innovation_clock M.alpha hN hlog hnd as ho
    (show fork ≤ fork from le_rfl) hfork htu ht
    (by simpa only [sampleClockSteps_length] using hub) ha₀.le hanchor
    (hanchorHigh.trans hanchor) (mul_nonneg htheta.le hv.le) hcap
    (laplaceComparisonStrength_pos M.data.d (sq_pos_of_pos M.data.hd) v).le
    hcapactual hgap hstrengtht
  dsimp only at hshort
  have hfirst : M.xs+physicalCutMass 0 steps u ≤ H*a₀^2 := by
    have humass : physicalCutMass 0 steps u=partitionPoint 0 as u :=
      physicalCutMass_sampleClockSteps _ _ _ u (huhigh.trans hhigh)
    rw [humass]
    have hhreg := hreg (M.data.wallRadius M.alpha (partitionPoint 0 as high))
      ⟨by linarith,(M.data.wallRadius_bounds M.alpha _).2⟩
    have hmasshigh : M.data.s ≤ partitionPoint 0 as high :=
      (M.data.wallRadius_high_mass M.alpha
        (by linarith [hhighradius,hwall])).le
    rw [M.data.wallRadius_spec M.alpha
      ⟨hmasshigh,(partitionPoint_mem as ho high).2⟩] at hhreg
    have hmasshi : partitionPoint 0 as high ≤ cu*(4*s) :=
      hhreg.2.trans (mul_le_mul_of_nonneg_left hhighbound.2.le hcu)
    have hmassu := partitionPoint_mono as ho huhigh
    nlinarith
  have hg : 0 < M.data.g v :=
    laplaceComparisonStrength_pos M.data.d (sq_pos_of_pos M.data.hd) v
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
    exact ⟨(hclocks j).1,hshortlater.trans (hclocks j).2.1,(hclocks j).2.2.1.trans M.hT,
      ((hclocks j).2.2.2).earlier_fork hfork⟩
  · intro i j hij
    exact (hscales i j hij).trans (mul_le_mul_of_nonneg_right hHlater (sq_nonneg (a j)))
  · simpa only [hlen,Nat.add_assoc] using hcount

end NativeStarBuffer
end OAI.SKFluctuations
