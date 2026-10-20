module

public import ComparisonSignedCavityRestBoundarySchedule
public import ComparisonActualHighOnlyInnovation
public import ComparisonActualHighOnlyClocks

@[expose] public section
noncomputable section
set_option maxHeartbeats 18000000
set_option linter.unusedVariables false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity
namespace ActualHighOnlyOverlapMinimum
variable {size : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable (a : LaplaceWindowFormalization.ActualHighOnlyOverlapMinimum (size+1) m delta cl cu Az C0 Ct D Bclock)
theorem R_monotone : Monotone a.R :=
  omittedSweepQuantile_monotone zero_le_one ⟨a.data.hs.1,a.data.hs1⟩ a.data.hc a.data.hk a.data.hkc a.data.hm a.data.hM a.alpha
theorem R_bounds (u : ℝ) : a.R u∈Icc (0:ℝ) 1 :=
  omittedSweepQuantile_bounds zero_le_one ⟨a.data.hs.1,a.data.hs1⟩ a.data.hc a.data.hk a.data.hkc a.data.hm a.data.hM a.alpha u
theorem R_one : a.R 1=1 := by
  exact omittedSweepQuantile_one zero_le_one ⟨a.data.hs.1,a.data.hs1⟩ a.data.hc a.data.hk a.data.hkc a.data.hm a.data.hM a.alpha
theorem R_spec_high {u : ℝ} (hu : u∈Icc (0:ℝ) 1) (hR : 0 < a.R u) : a.alpha.val.val (a.R u)=u := by
  exact omittedSweepQuantile_spec zero_le_one ⟨a.data.hs.1,a.data.hs1⟩ a.data.hc a.data.hk a.data.hkc a.data.hm a.data.hM a.alpha ⟨(a.radius_high_mass hR).le,hu.2⟩
theorem original_hf_radius_coe {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    (a.hf u:ℝ)=a.h u+laplaceComparisonStrength a.data.d a.lam (a.R u)*a.R u := by
  by_cases hs : a.data.s ≤ u
  · exact (a.high_clock_coe ⟨hs,hu.2⟩).2
  · have hR : a.R u=0 := by
      have H:=a.R_monotone (le_of_not_ge hs)
      have HL:=omittedSweepQuantile_left zero_le_one ⟨a.data.hs.1,a.data.hs1⟩ a.data.hc a.data.hk a.data.hkc a.data.hm a.data.hM a.alpha
      change a.R a.data.s=0 at HL
      linarith [(a.R_bounds u).1]
    rw [(a.inherited_clock_coe hu).2,hR]
    simp

theorem sampled_grid_field_growth (n : ℕ) (hn : 0 < n)
    (hN : 1 ≤ a.data.N) (hlog : 1 ≤ Real.log a.data.N) (hnd : 1/a.data.N ≤ a.data.d)
    {mesh s t : ℝ} (as : List PositiveMass) (ho : MassOrdered 0 as)
    (hmesh : 0 ≤ mesh) (hpart : PartitionMesh mesh 0 as)
    (hs : 0 < s) (hst : s ≤ t) (ht : t ≤ 1) :
    let rg : Fin (as.length+2)→ℝ:=fun i=>a.R (partitionPoint 0 as i.val)
    let τ:=radiusGridCut rg
    let steps:=sampleClockSteps (completedPathClock n a.bf a.hf) 0 as
    t ≤ rg (Fin.last (as.length+1)) →
      ((1/3)/Real.log a.data.N)*laplaceComparisonStrength a.data.d a.lam t*(t-s-mesh/a.data.floor) ≤
        physicalFieldDuration (fun st=>st.2 (Sum.inl ⟨0,hn⟩)) (steps.take (τ t))-
        physicalFieldDuration (fun st=>st.2 (Sum.inl ⟨0,hn⟩)) (steps.take (τ s)) := by
  let rg : Fin (as.length+2)→ℝ:=fun i=>a.R (partitionPoint 0 as i.val)
  let τ:=radiusGridCut rg
  let steps:=sampleClockSteps (completedPathClock n a.bf a.hf) 0 as
  dsimp only
  intro hlast
  have hmono : Monotone rg:=fun i j hij=>a.R_monotone (partitionPoint_mono as ho hij)
  have hz : rg 0=0:=by simpa [rg,partitionPoint,partitionValues] using a.R_zero
  have hsteps : ∀j : Fin (as.length+1),rg j.succ-rg j.castSucc ≤ mesh/a.data.floor:=
    fun j=>a.sampled_radius_step_le as ho hmesh hpart j.val
  have hsamp:=radiusGridPoint_bounds rg hmono (by rw [hz];exact hs) (hst.trans hlast) hsteps
  have htamp:=radiusGridPoint_bounds rg hmono (by rw [hz];exact hs.trans_le hst) hlast hsteps
  have hsrad:=a.R_bounds (partitionPoint 0 as (τ s))
  have htrad:=a.R_bounds (partitionPoint 0 as (τ t))
  have hidx : τ s ≤ τ t:=radiusGridCut_monotone rg hst
  have hdist : t-s-mesh/a.data.floor ≤ a.R (partitionPoint 0 as (τ t))-a.R (partitionPoint 0 as (τ s)):=by
    change t-mesh/a.data.floor ≤ a.R (partitionPoint 0 as (τ t)) ∧ a.R (partitionPoint 0 as (τ t))<t at htamp
    change s-mesh/a.data.floor ≤ a.R (partitionPoint 0 as (τ s)) ∧ a.R (partitionPoint 0 as (τ s))<s at hsamp
    linarith [hsamp.2]
  have hrad:=a.R_monotone (partitionPoint_mono as ho hidx)
  have hg:=actual_comparison_radius_field_increment_lower hN hlog a.data.hd hnd a.hlam a.hld hsrad.1 htrad.2 hrad
  have hanti:=(laplaceComparisonStrength_monotonicities a.data.hd.ne' a.hlam (r₀:=0) le_rfl).1
    htrad ⟨hs.le.trans hst,ht⟩ htamp.2.le
  have hcoef : 0 ≤ ((1:ℝ)/3)/Real.log a.data.N:=by positivity
  have hsave:=mul_le_mul_of_nonneg_left hdist (mul_nonneg hcoef (laplaceComparisonStrength_pos a.data.d a.hlam t).le)
  have hg':=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hanti hcoef) (sub_nonneg.mpr hrad)
  rw [sampledFieldDuration_index n hn a.bf a.hf a.bf_monotone a.hf_monotone as ho (τ t) (radiusGridCut_le rg t),
    sampledFieldDuration_index n hn a.bf a.hf a.bf_monotone a.hf_monotone as ho (τ s) (radiusGridCut_le rg s),
    physicalCutMass_sampleClockSteps _ _ _ _ (radiusGridCut_le rg t),physicalCutMass_sampleClockSteps _ _ _ _ (radiusGridCut_le rg s)]
  rw [a.original_hf_radius_coe (partitionPoint_mem as ho (τ t)),a.original_hf_radius_coe (partitionPoint_mem as ho (τ s))]
  have hbare:=a.hh (partitionPoint_mem as ho (τ s)) (partitionPoint_mem as ho (τ t)) (partitionPoint_mono as ho hidx)
  have H:=hsave.trans (hg'.trans hg)
  linarith

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem exists_actual_high_only_rest_boundary_projection_schedule
    (n : ℕ) (hn : 0 < n) {size : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (a : LaplaceWindowFormalization.ActualHighOnlyOverlapMinimum (size+1) m delta cl cu Az C0 Ct D Bclock)
    {mesh s W ce cReg Rmacro F xs B : ℝ}
    (hN : 1 ≤ a.data.N) (hlog : 1 ≤ Real.log a.data.N) (hnd : 1/a.data.N ≤ a.data.d)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    (hend : partitionEnd 0 as=1) (hmesh : 0 ≤ mesh) (hpart : PartitionMesh mesh 0 as)
    (hs : 0 < s) (hsmall : mesh/a.data.floor ≤ s/16) (hW : 0 < W) (hWs : W ≤ s)
    (hce : 0 < ce) (hstrength : ce*W^2 ≤ laplaceComparisonStrength a.data.d a.lam W)
    (hcReg : 0 < cReg) (hcu : 0 ≤ cu) (hmacro : 0 < Rmacro)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F)
    (hxs : 0 ≤ xs) (hxss : xs ≤ s)
    (hregular : ∀r∈Icc (s/2) 1,cReg*r ≤ a.alpha.val.val r ∧ a.alpha.val.val r ≤ cu*r)
    {J low high : ℕ} (hJ : 1 ≤ J) (hJmacro : Rmacro ≤ (2:ℝ)^J*s)
    (hJone : (2:ℝ)^J*s ≤ 1) (hhigh : high ≤ as.length)
    (hlow : a.R (partitionPoint 0 as low) ≤ s/2)
    (hhighradius : 2*s ≤ a.R (partitionPoint 0 as high)) :
    let steps:=nativeSampledPhysicalSteps n a.bf a.hf as
    (a.hf 1:ℝ)-(a.hf 0:ℝ) ≤ B →
    ∃(cs : List (ℝ×ℕ)) (t : ℕ) (anchor duration : Fin cs.length→ℝ),
      cs.length=J+2 ∧ low ≤ t ∧ t ≤ high ∧ t ≤ steps.length+1 ∧
      lastLayerCut cs t=steps.length+1 ∧
      (∀j,cutPredecessor cs t j ≤ (cs.get j).2 ∧ (cs.get j).2 ≤ steps.length+1) ∧
      (∀j,0 < anchor j ∧ ce*W^3/(24*Real.log a.data.N) ≤ duration j ∧ duration j ≤ B ∧
        PhysicalProjectionClock n steps low (cutPredecessor cs t j) (cs.get j).2 (anchor j) (duration j)) ∧
      (∀i j,i ≤ j.succ → xs+physicalCutMass 0 steps (overlapComponentEnd cs t i) ≤
        (F/((cReg/8)^2*s))*(anchor j)^2) ∧
      ((physicalOverlapResidualPairs cs).card:ℝ)^2 ≤ ((J+3:ℕ):ℝ)^4 ∧
      0 < ce*W^3/(24*Real.log a.data.N) := by
  let c:=a.data.floor
  let N:=a.data.N
  let d:=a.data.d
  let lam:=a.lam
  have hd:=a.data.hd
  have hlam:=a.hlam
  classical
  let Q := a.R
  let rg : Fin (as.length+2)→ℝ := fun i=>Q (partitionPoint 0 as i.val)
  let τ := radiusGridCut rg
  let bf := fun u=>a.bf u
  let hf := fun u=>a.hf u
  let steps := nativeSampledPhysicalSteps n bf hf as
  let D₀ := ce*W^3/(24*Real.log N)
  dsimp only
  intro hBclock
  have hlogpos : 0<Real.log N := zero_lt_one.trans_le hlog
  have hmono : Monotone rg := fun i j hij=>
    a.R_monotone (partitionPoint_mono as ho hij)
  have hτ : Monotone τ := radiusGridCut_monotone rg
  have hL (r : ℝ) : τ r ≤ steps.length := by
    simpa only [steps,nativeSampledPhysicalSteps,sampleClockSteps_length] using radiusGridCut_le rg r
  have hz : rg 0=0 := by
    simpa [rg,Q,partitionPoint,partitionValues] using a.R_zero
  have hlast : rg (Fin.last (as.length+1))=1 := by
    change Q (partitionPoint 0 as (as.length+1))=1
    rw [partitionPoint_after_final 0 as _ (by omega),hend]
    exact a.R_one
  have hsteps : ∀ j : Fin (as.length+1),rg j.succ-rg j.castSucc ≤ mesh/c :=
    fun j=>a.sampled_radius_step_le as ho hmesh hpart j.val
  have htwo : 2*s ≤ (2:ℝ)^J*s := by
    have H := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hJ
    simpa only [pow_one] using mul_le_mul_of_nonneg_right H hs.le
  have hsone : s ≤ 1 := by linarith
  have hbf : MonotoneOn bf (Icc (0:ℝ) 1) := a.bf_monotone
  have hhf : MonotoneOn hf (Icc (0:ℝ) 1) := a.hf_monotone
  let fd := fun st : GaussianStep (FeatureIndex n)=>st.2 (Sum.inl ⟨0,hn⟩)
  have hB : physicalFieldDuration fd steps ≤ B := by
    have H := native_sampled_field_duration_index n bf hf hbf hhf as ho ⟨0,hn⟩ as.length le_rfl
    have he : steps.take as.length=steps := by
      have : steps.length=as.length := sampleClockSteps_length _ _ _
      rw [←this,List.take_length]
    change physicalFieldDuration fd (steps.take as.length)=_ at H
    rw [he,partitionPoint_after_final 0 as _ le_rfl,hend] at H
    rw [H]
    exact hBclock
  have hmasses (r : ℝ) (hr : r∈Icc s ((2:ℝ)^J*s)) :
      (cReg/2)*r ≤ physicalCutMass 0 steps (τ r) ∧
        physicalCutMass 0 steps (τ r) ≤ cu*r := by
    have hbnd := radiusGridPoint_bounds rg hmono (by rw [hz]; exact hs.trans_le hr.1)
      (by rw [hlast]; exact hr.2.trans hJone) hsteps
    change r-mesh/c ≤ Q (partitionPoint 0 as (τ r)) ∧
      Q (partitionPoint 0 as (τ r))<r at hbnd
    have hreg : Q (partitionPoint 0 as (τ r))∈Icc (s/2) 1 := by
      constructor
      · linarith [hbnd.1,hr.1]
      · exact (a.R_bounds _).2
    have H := hregular _ hreg
    rw [a.R_spec_high (partitionPoint_mem as ho (τ r)) (by linarith [hreg.1])] at H
    rw [show physicalCutMass 0 steps (τ r)=partitionPoint 0 as (τ r) from
      physicalCutMass_sampleClockSteps _ _ _ _ (radiusGridCut_le rg r)]
    constructor
    · have hhalf : r/2 ≤ Q (partitionPoint 0 as (τ r)) := by linarith [hbnd.1,hr.1]
      have H' := (mul_le_mul_of_nonneg_left hhalf hcReg.le).trans H.1
      nlinarith
    · exact H.2.trans (mul_le_mul_of_nonneg_left hbnd.2.le hcu)
  have hfork : low ≤ τ s := by
    have hbnd := radiusGridPoint_bounds rg hmono (by rw [hz]; exact hs)
      (by rw [hlast]; exact hsone) hsteps
    change s-mesh/c ≤ Q (partitionPoint 0 as (τ s)) ∧ _ at hbnd
    by_contra hnot
    have H' := a.R_monotone
      (partitionPoint_mono as ho (show τ s ≤ low by omega))
    change Q (partitionPoint 0 as low) ≤ s/2 at hlow
    linarith [hbnd.1]
  have hgr (r : ℝ) (hr : r∈Icc s ((2:ℝ)^J*s)) :
      ce*W^3 ≤ laplaceComparisonStrength d lam r*r := by
    have hmgr := (laplaceComparisonStrength_monotonicities hd.ne' hlam (r₀:=0) le_rfl).2
      ⟨hW.le,hWs.trans hsone⟩ ⟨hs.le.trans hr.1,hr.2.trans hJone⟩ (hWs.trans hr.1)
    have H := mul_le_mul_of_nonneg_right hstrength hW.le
    have H' : ce*W^3 ≤ laplaceComparisonStrength d lam W*W := by nlinarith [H]
    exact H'.trans hmgr
  have hfirst : D₀ ≤ physicalFieldDuration fd (steps.take (τ (2*s)))-
      physicalFieldDuration fd (steps.take (τ s)) := by
    have H := a.sampled_grid_field_growth n hn hN hlog hnd as ho hmesh hpart hs
      (by linarith : s ≤ 2*s) (htwo.trans hJone)
      (by change 2*s ≤ rg (Fin.last (as.length+1)); rw [hlast]; exact htwo.trans hJone)
    have hg := hgr (2*s) ⟨by linarith,htwo⟩
    have hwidth : (2*s)/8 ≤ 2*s-s-mesh/c := by linarith
    have hgpos := laplaceComparisonStrength_pos d hlam (2*s)
    have hwid := mul_le_mul_of_nonneg_left hwidth
      (show 0 ≤ ((1:ℝ)/3)/Real.log N*laplaceComparisonStrength d lam (2*s) by positivity)
    have hsc := mul_le_mul_of_nonneg_left hg (show 0 ≤ 1/(24*Real.log N) by positivity)
    rw [←native_sampled_field_duration_take_eq_completed n bf hf as ⟨0,hn⟩,
      ←native_sampled_field_duration_take_eq_completed n bf hf as ⟨0,hn⟩] at H
    apply le_trans _ (hwid.trans H)
    dsimp only [D₀]
    convert hsc using 1 <;> ring
  have hdyad (r : ℝ) (hr : r∈Icc (2*s) ((2:ℝ)^J*s)) :
      D₀ ≤ physicalFieldDuration fd (steps.take (τ r))-
        physicalFieldDuration fd (steps.take (τ (3*r/4))) := by
    have hrpos : 0<r := by linarith [hr.1]
    have H := a.sampled_grid_field_growth n hn hN hlog hnd as ho hmesh hpart (by positivity : 0<3*r/4)
      (by linarith : 3*r/4 ≤ r) (hr.2.trans hJone)
      (by change r ≤ rg (Fin.last (as.length+1)); rw [hlast]; exact hr.2.trans hJone)
    have hg := hgr r ⟨by linarith [hr.1],hr.2⟩
    have hwidth : r/8 ≤ r-3*r/4-mesh/c := by linarith [hr.1]
    have hgpos := laplaceComparisonStrength_pos d hlam r
    have hwid := mul_le_mul_of_nonneg_left hwidth
      (show 0 ≤ ((1:ℝ)/3)/Real.log N*laplaceComparisonStrength d lam r by positivity)
    have hsc := mul_le_mul_of_nonneg_left hg (show 0 ≤ 1/(24*Real.log N) by positivity)
    rw [←native_sampled_field_duration_take_eq_completed n bf hf as ⟨0,hn⟩,
      ←native_sampled_field_duration_take_eq_completed n bf hf as ⟨0,hn⟩] at H
    apply le_trans _ (hwid.trans H)
    dsimp only [D₀]
    convert hsc using 1 <;> ring
  obtain ⟨cs,t,anchor,duration,hlen,ht,_htlen,hlastcs,_,hends,hclock,hscale⟩ :=
    physicalOverlapDyadicCertificates n steps (sampleClockSteps_ordered _ _ ho)
      (show 0<cReg/2 by positivity) hxs hxss hs hcu hmacro hFmass hFradius hJ
      τ hτ hL hJmacro hfork fd
      (native_sampled_field_homogeneous n bf hf as ⟨0,hn⟩) hB
      (fun r hr=>(hmasses r hr).1) (fun r hr=>(hmasses r hr).2) hfirst hdyad
  have htbefore : t ≤ high := by
    rw [ht]
    have H := radiusGridPoint_bounds rg hmono (by rw [hz]; positivity : rg 0<2*s)
      (by rw [hlast]; exact htwo.trans hJone) hsteps
    change _ ∧ Q (partitionPoint 0 as (τ (2*s)))<2*s at H
    by_contra hnot
    have H' := a.R_monotone
      (partitionPoint_mono as ho (show high ≤ τ (2*s) by omega))
    change 2*s ≤ Q (partitionPoint 0 as high) at hhighradius
    linarith [H.2]
  have htlen : t ≤ steps.length+1 := by
    have H := htbefore.trans hhigh
    simpa only [steps,nativeSampledPhysicalSteps,sampleClockSteps_length] using H.trans (Nat.le_succ as.length)
  have htlow : low ≤ t := by
    rw [ht]
    exact hfork.trans (hτ (by linarith))
  refine ⟨cs,t,anchor,duration,hlen,htlow,htbefore,htlen,hlastcs,hends,hclock,?_,?_,?_⟩
  · simpa only [show (cReg/2)/4=cReg/8 by ring] using hscale
  · have H : ((physicalOverlapResidualPairs cs).card:ℝ) ≤ ((cs.length+1:ℕ):ℝ)^2 := by
      exact_mod_cast physicalOverlapResidualPairs_card_le cs
    have H' := pow_le_pow_left₀ (Nat.cast_nonneg (physicalOverlapResidualPairs cs).card) H 2
    simpa only [hlen,Nat.add_assoc,←pow_mul] using H'
  · positivity

end OAI.SKFluctuations.Cavity
