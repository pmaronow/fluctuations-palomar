module

public import ComparisonSignedCavityGroupedContinuation
public import ConstrainedForwardGeometry
public import PhysicalComparisonRadiusSampling
public import ComparisonSignedCavityMassInnovation
public import UpperWallIteration

@[expose] public section

noncomputable section
set_option maxHeartbeats 4500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem partitionPoint_step_le_mesh {a mesh : ℝ} (as : List PositiveMass)
    (hm : PartitionMesh mesh a as) (hmesh : 0 ≤ mesh) (j : ℕ) :
    partitionPoint a as (j+1)-partitionPoint a as j ≤ mesh := by
  induction as generalizing a j with
  | nil => simpa [partitionPoint,partitionValues] using hmesh
  | cons m as ih =>
    cases j with
    | zero => simpa [partitionPoint,partitionValues] using hm.1
    | succ j => simpa [partitionPoint,partitionValues] using ih hm.2 j

section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
  (hkc : ∀ r∈Icc (0:ℝ) 1,c ≤ k r)
  (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

theorem actual_comparison_partition_radius_step_le
    (α : inverseIntegralConstraints 0 0 k M) (as : List PositiveMass)
    (ho : MassOrdered 0 as) {mesh : ℝ} (hmesh : 0 ≤ mesh)
    (hpart : PartitionMesh mesh 0 as) (j : ℕ) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    R (partitionPoint 0 as (j+1))-R (partitionPoint 0 as j) ≤ mesh/c := by
  dsimp only
  have H := (comparisonSweepQuantile_lipschitzOn hc hk hkc hm hM α).dist_le_mul
    _ (partitionPoint_mem as ho (j+1)) _ (partitionPoint_mem as ho j)
  have hp := partitionPoint_mono as ho (Nat.le_succ j)
  have hR := comparisonSweepQuantile_monotone hc hk hkc hm hM α hp
  change abs (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as (j+1))-
    comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as j)) ≤
    c⁻¹*abs (partitionPoint 0 as (j+1)-partitionPoint 0 as j) at H
  rw [abs_of_nonneg (sub_nonneg.mpr hR),abs_of_nonneg (sub_nonneg.mpr hp)] at H
  apply H.trans
  have hg := partitionPoint_step_le_mesh as hpart hmesh j
  simpa only [div_eq_mul_inv,mul_comm] using
    mul_le_mul_of_nonneg_left hg (inv_nonneg.mpr hc.le)

theorem exists_actual_comparison_pre_high_cut
    (α : inverseIntegralConstraints 0 0 k M) (as : List PositiveMass)
    (ho : MassOrdered 0 as) {mesh v cReg : ℝ}
    (hmesh : 0 ≤ mesh) (hpart : PartitionMesh mesh 0 as)
    (hv : 0<v) (hsmall : mesh/c ≤ v/16) (hcReg : 0 ≤ cReg)
    {low high : ℕ} (hhigh : high ≤ as.length)
    (hvr : comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as high)=v)
    (hlow : comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as low) ≤ v/2)
    (hregular : ∀ r∈Icc (v/2) v,cReg*r ≤ α.val.val r) :
    ∃ pre : ℕ, low ≤ pre ∧ pre ≤ high ∧
      11*v/16 ≤ comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as pre) ∧
      comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as pre)<3*v/4 ∧
      cReg*v/2 ≤ partitionPoint 0 as pre ∧
      v/4 ≤ comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as high)-
        comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as pre) := by
  classical
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let rg : Fin (as.length+2)→ℝ := fun i=>R (partitionPoint 0 as i.val)
  have hmono : Monotone rg := fun i j hij=>
    comparisonSweepQuantile_monotone hc hk hkc hm hM α (partitionPoint_mono as ho hij)
  have hz : rg 0=0 := by
    change R (partitionPoint 0 as 0)=0
    simpa [R,partitionPoint,partitionValues] using
      comparisonSweepQuantile_zero hc hk hkc hm hM α
  have hlast : 3*v/4 ≤ rg (Fin.last (as.length+1)) := by
    have H := hmono (show (⟨high,by omega⟩ : Fin (as.length+2)) ≤ Fin.last (as.length+1)
      from Fin.le_last _)
    have : rg ⟨high,by omega⟩=v := hvr
    rw [this] at H
    linarith
  have hsteps : ∀ j : Fin (as.length+1),rg j.succ-rg j.castSucc ≤ mesh/c := by
    intro j
    exact actual_comparison_partition_radius_step_le hc hk hkc hm hM α as ho hmesh hpart j.val
  let pre := radiusGridCut rg (3*v/4)
  have hb := radiusGridPoint_bounds rg hmono
    (by rw [hz]; positivity : rg 0<3*v/4) hlast hsteps
  have hb' : 3*v/4-mesh/c ≤ R (partitionPoint 0 as pre) ∧
      R (partitionPoint 0 as pre)<3*v/4 := hb
  have hpre : 11*v/16 ≤ R (partitionPoint 0 as pre) := by linarith [hb'.1]
  have hbefore : pre ≤ high := by
    by_contra hn
    have H := comparisonSweepQuantile_monotone hc hk hkc hm hM α
      (partitionPoint_mono as ho (show high ≤ pre by omega))
    rw [hvr] at H
    linarith [hb'.2]
  have hafter : low ≤ pre := by
    by_contra hn
    have H := comparisonSweepQuantile_monotone hc hk hkc hm hM α
      (partitionPoint_mono as ho (show pre ≤ low by omega))
    change R (partitionPoint 0 as low) ≤ v/2 at hlow
    linarith
  have hrange : R (partitionPoint 0 as pre)∈Icc (v/2) v := by
    constructor <;> linarith [hb'.2]
  have ha := hregular _ hrange
  rw [comparisonSweepQuantile_spec hc hk hkc hm hM α (partitionPoint_mem as ho pre)] at ha
  have hmass : cReg*v/2 ≤ partitionPoint 0 as pre := by
    simpa only [mul_div_assoc] using (mul_le_mul_of_nonneg_left hrange.1 hcReg).trans ha
  refine ⟨pre,hafter,hbefore,hpre,hb'.2,hmass,?_⟩
  rw [hvr]
  linarith [hb'.2]

end

theorem actual_completed_sample_field_homogeneous (n : ℕ) (b h : ℝ→ℝ≥0)
    (as : List PositiveMass) (i₀ : Fin n) :
    ∀ st∈sampleClockSteps (completedPathClock n b h) 0 as,
      ∀ i : Fin n,st.2 (Sum.inl i)=st.2 (Sum.inl i₀) := by
  have hg (xs : List PositiveMass) (a : ℝ) :
      ∀ st∈sampleClockSteps (completedPathClock n b h) a xs,
        ∀ i : Fin n,st.2 (Sum.inl i)=st.2 (Sum.inl i₀) := by
    induction xs generalizing a with
    | nil => simp [sampleClockSteps]
    | cons m xs ih =>
      intro st hst i
      rcases List.mem_cons.mp hst with rfl|hst
      · rfl
      · exact ih m.val _ hst i
  exact hg as 0

theorem actual_completed_sample_field_duration_slice (n : ℕ) (hn : 0<n)
    (b h : ℝ→ℝ≥0) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (as : List PositiveMass)
    (ho : MassOrdered 0 as) {pre high : ℕ} (hp : pre ≤ high) (hhb : high ≤ as.length) :
    physicalFieldDuration (fun st=>st.2 (Sum.inl ⟨0,hn⟩))
      (cutSlice (sampleClockSteps (completedPathClock n b h) 0 as) pre high)=
      (h (partitionPoint 0 as high):ℝ)-(h (partitionPoint 0 as pre):ℝ) := by
  rw [physicalFieldDuration_slice_eq _ _ hp,
    sampledFieldDuration_index n hn b h hb hh as ho high hhb,
    sampledFieldDuration_index n hn b h hb hh as ho pre (hp.trans hhb),
    physicalCutMass_sampleClockSteps _ _ _ high hhb,
    physicalCutMass_sampleClockSteps _ _ _ pre (hp.trans hhb)]
  ring

theorem exists_actual_comparison_pre_high_innovation
    (n : ℕ) (hn : 0<n) {c N d lam mesh v cReg : ℝ} {k M : ℝ→ℝ}
    (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
    (hkc : ∀ r∈Icc (0:ℝ) 1,c ≤ k r)
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)
    (α : inverseIntegralConstraints 0 0 k M) (b h : ℝ→ℝ)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hlb : lam ≤ b 0)
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0)
    (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N) (hd : 0<d) (hnd : 1/N ≤ d)
    (hlam : 0<lam) (hld : lam ≤ d^2)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    (hmesh : 0 ≤ mesh) (hpart : PartitionMesh mesh 0 as)
    (hv : 0<v) (hsmall : mesh/c ≤ v/16) (hcReg : 0<cReg)
    {low high w : ℕ} (hhigh : high ≤ as.length) (hhw : high ≤ w) (hw : w ≤ as.length+1)
    (hvr : comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as high)=v)
    (hlow : comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as low) ≤ v/2)
    (hregular : ∀ r∈Icc (v/2) v,cReg*r ≤ α.val.val r) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
    let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
    let steps := sampleClockSteps (completedPathClock n bf hf) 0 as
    ∃ pre : ℕ,low ≤ pre ∧ pre ≤ high ∧
      cReg*v/2 ≤ partitionPoint 0 as pre ∧
      let D := physicalFieldDuration (fun st=>st.2 (Sum.inl ⟨0,hn⟩)) (cutSlice steps pre high)
      0<D ∧ laplaceComparisonStrength d lam v*v/(12*Real.log N) ≤ D ∧
        PhysicalProjectionClock n steps low high w (cReg*v/2) D := by
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
  let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
  let steps := sampleClockSteps (completedPathClock n bf hf) 0 as
  dsimp only
  obtain ⟨pre,hafter,hbefore,_,_,hmass,hwidth⟩ := exists_actual_comparison_pre_high_cut
    hc hk hkc hm hM α as ho hmesh hpart hv hsmall hcReg.le hhigh hvr hlow hregular
  have had := strengthSweep_clocks_admissible b R hd.ne' hlam.le hlb hb
    ((comparisonSweepQuantile_monotone hc hk hkc hm hM α).monotoneOn _)
    (fun u _=>comparisonSweepQuantile_bounds hc hk hkc hm hM α u)
  have hbf : MonotoneOn bf (Icc (0:ℝ) 1) := toNNReal_monotoneOn had.1
  have hhf : MonotoneOn hf (Icc (0:ℝ) 1) := toNNReal_monotoneOn (hh.add had.2.1)
  have H := comparisonVariableEndpointField_radius_gap hc hk hkc hm hM
    hN hlog hd hnd hlam hld h hh hh0 α
    (partitionPoint_mem as ho pre) (partitionPoint_mem as ho high)
    (partitionPoint_mono as ho hbefore)
    (by rw [←hvr]; exact (comparisonSweepQuantile_bounds hc hk hkc hm hM α _).2)
    hvr.le
  dsimp only at H
  have hlogpos : 0<Real.log N := zero_lt_one.trans_le hlog
  have hspos : 0<laplaceComparisonStrength d lam v := laplaceComparisonStrength_pos d hlam v
  have Hwidth := mul_le_mul_of_nonneg_left hwidth
    (show 0 ≤ ((1:ℝ)/3)/Real.log N*laplaceComparisonStrength d lam v by positivity)
  have hduration : laplaceComparisonStrength d lam v*v/(12*Real.log N) ≤
      physicalFieldDuration (fun st=>st.2 (Sum.inl ⟨0,hn⟩)) (cutSlice steps pre high) := by
    rw [actual_completed_sample_field_duration_slice n hn bf hf hbf hhf as ho hbefore hhigh]
    have hcoef := (Hwidth.trans H)
    change _ ≤ ((hf (partitionPoint 0 as high)-hf (partitionPoint 0 as pre):ℝ≥0):ℝ) at hcoef
    rw [NNReal.coe_sub (hhf (partitionPoint_mem as ho pre) (partitionPoint_mem as ho high)
      (partitionPoint_mono as ho hbefore))] at hcoef
    convert hcoef using 1
    ring
  have hs : OrderedSteps 0 steps := sampleClockSteps_ordered _ _ ho
  have hclock := physicalProjectionClock_of_full_field_layer n steps hs
    (show 0 ≤ cReg*v/2 by positivity) (fun st=>st.2 (Sum.inl ⟨0,hn⟩))
    (actual_completed_sample_field_homogeneous n bf hf as ⟨0,hn⟩)
    hafter hbefore hhw
    (by simpa only [steps,sampleClockSteps_length] using hhigh)
    (by simpa only [steps,sampleClockSteps_length] using hw)
    (by simpa only [steps,physicalCutMass_sampleClockSteps _ _ _ pre (hbefore.trans hhigh)] using hmass)
  refine ⟨pre,hafter,hbefore,hmass,?_,hduration,hclock⟩
  exact lt_of_lt_of_le (by positivity : 0<laplaceComparisonStrength d lam v*v/(12*Real.log N)) hduration

theorem actual_comparison_grid_field_growth
    (n : ℕ) (hn : 0<n) {c N d lam mesh s t : ℝ} {k M : ℝ→ℝ}
    (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
    (hkc : ∀ r∈Icc (0:ℝ) 1,c ≤ k r)
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)
    (α : inverseIntegralConstraints 0 0 k M) (b h : ℝ→ℝ)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hlb : lam ≤ b 0)
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0)
    (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N) (hd : 0<d) (hnd : 1/N ≤ d)
    (hlam : 0<lam) (hld : lam ≤ d^2)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    (hmesh : 0 ≤ mesh) (hpart : PartitionMesh mesh 0 as)
    (hs : 0<s) (hst : s ≤ t) (ht : t ≤ 1) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    let rg : Fin (as.length+2)→ℝ := fun i=>R (partitionPoint 0 as i.val)
    let τ := radiusGridCut rg
    let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
    let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
    let steps := sampleClockSteps (completedPathClock n bf hf) 0 as
    t ≤ rg (Fin.last (as.length+1)) →
      ((1/3)/Real.log N)*laplaceComparisonStrength d lam t*(t-s-mesh/c) ≤
        physicalFieldDuration (fun st=>st.2 (Sum.inl ⟨0,hn⟩)) (steps.take (τ t))-
        physicalFieldDuration (fun st=>st.2 (Sum.inl ⟨0,hn⟩)) (steps.take (τ s)) := by
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let rg : Fin (as.length+2)→ℝ := fun i=>R (partitionPoint 0 as i.val)
  let τ := radiusGridCut rg
  let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
  let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
  let steps := sampleClockSteps (completedPathClock n bf hf) 0 as
  dsimp only
  intro hlast
  have hmono : Monotone rg := fun i j hij=>
    comparisonSweepQuantile_monotone hc hk hkc hm hM α (partitionPoint_mono as ho hij)
  have hz : rg 0=0 := by
    simpa [rg,R,partitionPoint,partitionValues] using comparisonSweepQuantile_zero hc hk hkc hm hM α
  have hsteps : ∀ j : Fin (as.length+1),rg j.succ-rg j.castSucc ≤ mesh/c :=
    fun j=>actual_comparison_partition_radius_step_le hc hk hkc hm hM α as ho hmesh hpart j.val
  have hsamp := radiusGridPoint_bounds rg hmono (by rw [hz]; exact hs) (hst.trans hlast) hsteps
  have htamp := radiusGridPoint_bounds rg hmono (by rw [hz]; exact hs.trans_le hst) hlast hsteps
  have hsrad : R (partitionPoint 0 as (τ s))∈Icc (0:ℝ) 1 :=
    comparisonSweepQuantile_bounds hc hk hkc hm hM α _
  have htrad : R (partitionPoint 0 as (τ t))∈Icc (0:ℝ) 1 :=
    comparisonSweepQuantile_bounds hc hk hkc hm hM α _
  have hidx : τ s ≤ τ t := radiusGridCut_monotone rg hst
  have hdist : t-s-mesh/c ≤ R (partitionPoint 0 as (τ t))-R (partitionPoint 0 as (τ s)) := by
    change t-mesh/c ≤ R (partitionPoint 0 as (τ t)) ∧
      R (partitionPoint 0 as (τ t))<t at htamp
    change s-mesh/c ≤ R (partitionPoint 0 as (τ s)) ∧
      R (partitionPoint 0 as (τ s))<s at hsamp
    linarith [hsamp.2]
  have hrad := comparisonSweepQuantile_monotone hc hk hkc hm hM α (partitionPoint_mono as ho hidx)
  have hg := actual_comparison_radius_field_increment_lower hN hlog hd hnd hlam hld
    hsrad.1 htrad.2 hrad
  have hanti := (laplaceComparisonStrength_monotonicities hd.ne' hlam (r₀:=0) le_rfl).1
    htrad ⟨hs.le.trans hst,ht⟩ htamp.2.le
  have hcoef : 0 ≤ ((1:ℝ)/3)/Real.log N := by positivity
  have hsave := mul_le_mul_of_nonneg_left hdist
    (mul_nonneg hcoef (laplaceComparisonStrength_pos d hlam t).le)
  have hg' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hanti hcoef)
    (sub_nonneg.mpr hrad)
  have had := strengthSweep_clocks_admissible b R hd.ne' hlam.le hlb hb
    ((comparisonSweepQuantile_monotone hc hk hkc hm hM α).monotoneOn _)
    (fun u _=>comparisonSweepQuantile_bounds hc hk hkc hm hM α u)
  have hbf : MonotoneOn bf (Icc (0:ℝ) 1) := toNNReal_monotoneOn had.1
  have hhf : MonotoneOn hf (Icc (0:ℝ) 1) := toNNReal_monotoneOn (hh.add had.2.1)
  rw [sampledFieldDuration_index n hn bf hf hbf hhf as ho (τ t) (radiusGridCut_le rg t),
    sampledFieldDuration_index n hn bf hf hbf hhf as ho (τ s) (radiusGridCut_le rg s),
    physicalCutMass_sampleClockSteps _ _ _ _ (radiusGridCut_le rg t),
    physicalCutMass_sampleClockSteps _ _ _ _ (radiusGridCut_le rg s)]
  have hnon (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
      0 ≤ h u+laplaceComparisonStrength d lam (R u)*R u :=
    add_nonneg (hh0.trans (hh (by norm_num) hu hu.1))
      (mul_nonneg (laplaceComparisonStrength_pos d hlam _).le
        (comparisonSweepQuantile_bounds hc hk hkc hm hM α u).1)
  dsimp only [hf]
  rw [Real.coe_toNNReal _ (hnon _ (partitionPoint_mem as ho (τ t))),
    Real.coe_toNNReal _ (hnon _ (partitionPoint_mem as ho (τ s)))]
  have hbare := hh (partitionPoint_mem as ho (τ s)) (partitionPoint_mem as ho (τ t))
    (partitionPoint_mono as ho hidx)
  have H := hsave.trans (hg'.trans hg)
  dsimp only [R] at H
  linarith

theorem partitionPoint_after_final (a : ℝ) (as : List PositiveMass) (j : ℕ)
    (hj : as.length ≤ j) : partitionPoint a as j=partitionEnd a as := by
  induction as generalizing a j with
  | nil => rfl
  | cons m as ih =>
    cases j with
    | zero => simp at hj
    | succ j => exact ih m.val j (by simpa using hj)

theorem exists_actual_comparison_boundary_projection_schedule
    (n : ℕ) (hn : 0<n) {c N d lam mesh s W ce cReg cu Rmacro F xs B : ℝ}
    {k M : ℝ→ℝ}
    (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
    (hkc : ∀ r∈Icc (0:ℝ) 1,c ≤ k r)
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)
    (α : inverseIntegralConstraints 0 0 k M) (b h : ℝ→ℝ)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hlb : lam ≤ b 0)
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0)
    (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N) (hd : 0<d) (hnd : 1/N ≤ d)
    (hlam : 0<lam) (hld : lam ≤ d^2)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    (hend : partitionEnd 0 as=1) (hmesh : 0 ≤ mesh) (hpart : PartitionMesh mesh 0 as)
    (hs : 0<s) (hsmall : mesh/c ≤ s/16) (hW : 0<W) (hWs : W ≤ s)
    (hce : 0<ce) (hstrength : ce*W^2 ≤ laplaceComparisonStrength d lam W)
    (hcReg : 0<cReg) (hcu : 0 ≤ cu) (hmacro : 0<Rmacro)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F)
    (hxs : 0 ≤ xs) (hxss : xs ≤ s)
    (hregular : ∀ r∈Icc (s/2) 1,cReg*r ≤ α.val.val r ∧ α.val.val r ≤ cu*r)
    {J low high : ℕ} (hJ : 1 ≤ J) (hJmacro : Rmacro ≤ (2:ℝ)^J*s)
    (hJone : (2:ℝ)^J*s ≤ 1) (hhigh : high ≤ as.length)
    (hlow : comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as low) ≤ s/2)
    (hhighradius : 2*s ≤ comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as high)) :
    let Q := comparisonSweepQuantile hc hk hkc hm hM α
    let bf := fun u=>(b u-laplaceComparisonStrength d lam (Q u)).toNNReal
    let hf := fun u=>(h u+laplaceComparisonStrength d lam (Q u)*Q u).toNNReal
    let steps := sampleClockSteps (completedPathClock n bf hf) 0 as
    (hf 1:ℝ)-(hf 0:ℝ) ≤ B →
    ∃ (cs : List (ℝ×ℕ)) (t : ℕ) (a D : Fin cs.length→ℝ),
      cs.length=J+2 ∧ low ≤ t ∧ t ≤ high ∧ t ≤ steps.length+1 ∧
      lastLayerCut cs t=steps.length+1 ∧
      (∀ j,cutPredecessor cs t j ≤ (cs.get j).2 ∧ (cs.get j).2 ≤ steps.length+1) ∧
      (∀ j,0<a j ∧ ce*W^3/(24*Real.log N) ≤ D j ∧ D j ≤ B ∧
        PhysicalProjectionClock n steps low (cutPredecessor cs t j) (cs.get j).2 (a j) (D j)) ∧
      (∀ i j,i ≤ j.succ → xs+physicalCutMass 0 steps (overlapComponentEnd cs t i) ≤
        (F/((cReg/8)^2*s))*(a j)^2) ∧
      ((physicalOverlapResidualPairs cs).card:ℝ)^2 ≤ ((J+3:ℕ):ℝ)^4 ∧
      0<ce*W^3/(24*Real.log N) := by
  classical
  let Q := comparisonSweepQuantile hc hk hkc hm hM α
  let rg : Fin (as.length+2)→ℝ := fun i=>Q (partitionPoint 0 as i.val)
  let τ := radiusGridCut rg
  let bf := fun u=>(b u-laplaceComparisonStrength d lam (Q u)).toNNReal
  let hf := fun u=>(h u+laplaceComparisonStrength d lam (Q u)*Q u).toNNReal
  let steps := sampleClockSteps (completedPathClock n bf hf) 0 as
  let D₀ := ce*W^3/(24*Real.log N)
  dsimp only
  intro hBclock
  have hlogpos : 0<Real.log N := zero_lt_one.trans_le hlog
  have hmono : Monotone rg := fun i j hij=>
    comparisonSweepQuantile_monotone hc hk hkc hm hM α (partitionPoint_mono as ho hij)
  have hτ : Monotone τ := radiusGridCut_monotone rg
  have hL (r : ℝ) : τ r ≤ steps.length := by
    simpa only [steps,sampleClockSteps_length] using radiusGridCut_le rg r
  have hz : rg 0=0 := by
    simpa [rg,Q,partitionPoint,partitionValues] using comparisonSweepQuantile_zero hc hk hkc hm hM α
  have hlast : rg (Fin.last (as.length+1))=1 := by
    change Q (partitionPoint 0 as (as.length+1))=1
    rw [partitionPoint_after_final 0 as _ (by omega),hend]
    exact comparisonSweepQuantile_one hc hk hkc hm hM α
  have hsteps : ∀ j : Fin (as.length+1),rg j.succ-rg j.castSucc ≤ mesh/c :=
    fun j=>actual_comparison_partition_radius_step_le hc hk hkc hm hM α as ho hmesh hpart j.val
  have htwo : 2*s ≤ (2:ℝ)^J*s := by
    have H := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hJ
    simpa only [pow_one] using mul_le_mul_of_nonneg_right H hs.le
  have hsone : s ≤ 1 := by linarith
  have had := strengthSweep_clocks_admissible b Q hd.ne' hlam.le hlb hb
    ((comparisonSweepQuantile_monotone hc hk hkc hm hM α).monotoneOn _)
    (fun u _=>comparisonSweepQuantile_bounds hc hk hkc hm hM α u)
  have hbf : MonotoneOn bf (Icc (0:ℝ) 1) := toNNReal_monotoneOn had.1
  have hhf : MonotoneOn hf (Icc (0:ℝ) 1) := toNNReal_monotoneOn (hh.add had.2.1)
  let fd := fun st : GaussianStep (FeatureIndex n)=>st.2 (Sum.inl ⟨0,hn⟩)
  have hB : physicalFieldDuration fd steps ≤ B := by
    have H := sampledFieldDuration_index n hn bf hf hbf hhf as ho as.length le_rfl
    have he : steps.take as.length=steps := by
      have : steps.length=as.length := sampleClockSteps_length _ _ _
      rw [←this,List.take_length]
    change physicalFieldDuration fd (steps.take as.length)=_ at H
    rw [he,physicalCutMass_sampleClockSteps _ _ _ _ le_rfl,
      partitionPoint_after_final 0 as _ le_rfl,hend] at H
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
      · exact (comparisonSweepQuantile_bounds hc hk hkc hm hM α _).2
    have H := hregular _ hreg
    rw [comparisonSweepQuantile_spec hc hk hkc hm hM α (partitionPoint_mem as ho (τ r))] at H
    rw [physicalCutMass_sampleClockSteps _ _ _ _ (radiusGridCut_le rg r)]
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
    have H' := comparisonSweepQuantile_monotone hc hk hkc hm hM α
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
    have H := actual_comparison_grid_field_growth n hn hc hk hkc hm hM α b h hb hlb hh hh0
      hN hlog hd hnd hlam hld as ho hmesh hpart hs
      (by linarith : s ≤ 2*s) (htwo.trans hJone)
      (by change 2*s ≤ rg (Fin.last (as.length+1)); rw [hlast]; exact htwo.trans hJone)
    have hg := hgr (2*s) ⟨by linarith,htwo⟩
    have hwidth : (2*s)/8 ≤ 2*s-s-mesh/c := by linarith
    have hgpos := laplaceComparisonStrength_pos d hlam (2*s)
    have hwid := mul_le_mul_of_nonneg_left hwidth
      (show 0 ≤ ((1:ℝ)/3)/Real.log N*laplaceComparisonStrength d lam (2*s) by positivity)
    have hsc := mul_le_mul_of_nonneg_left hg (show 0 ≤ 1/(24*Real.log N) by positivity)
    apply le_trans _ (hwid.trans H)
    dsimp only [D₀]
    convert hsc using 1 <;> ring
  have hdyad (r : ℝ) (hr : r∈Icc (2*s) ((2:ℝ)^J*s)) :
      D₀ ≤ physicalFieldDuration fd (steps.take (τ r))-
        physicalFieldDuration fd (steps.take (τ (3*r/4))) := by
    have hrpos : 0<r := by linarith [hr.1]
    have H := actual_comparison_grid_field_growth n hn hc hk hkc hm hM α b h hb hlb hh hh0
      hN hlog hd hnd hlam hld as ho hmesh hpart (by positivity : 0<3*r/4)
      (by linarith : 3*r/4 ≤ r) (hr.2.trans hJone)
      (by change r ≤ rg (Fin.last (as.length+1)); rw [hlast]; exact hr.2.trans hJone)
    have hg := hgr r ⟨by linarith [hr.1],hr.2⟩
    have hwidth : r/8 ≤ r-3*r/4-mesh/c := by linarith [hr.1]
    have hgpos := laplaceComparisonStrength_pos d hlam r
    have hwid := mul_le_mul_of_nonneg_left hwidth
      (show 0 ≤ ((1:ℝ)/3)/Real.log N*laplaceComparisonStrength d lam r by positivity)
    have hsc := mul_le_mul_of_nonneg_left hg (show 0 ≤ 1/(24*Real.log N) by positivity)
    apply le_trans _ (hwid.trans H)
    dsimp only [D₀]
    convert hsc using 1 <;> ring
  obtain ⟨cs,t,a,D,hlen,ht,_htlen,hlastcs,_,hends,hclock,hscale⟩ :=
    physicalOverlapDyadicCertificates n steps (sampleClockSteps_ordered _ _ ho)
      (show 0<cReg/2 by positivity) hxs hxss hs hcu hmacro hFmass hFradius hJ
      τ hτ hL hJmacro hfork fd
      (actual_completed_sample_field_homogeneous n bf hf as ⟨0,hn⟩) hB
      (fun r hr=>(hmasses r hr).1) (fun r hr=>(hmasses r hr).2) hfirst hdyad
  have htbefore : t ≤ high := by
    rw [ht]
    have H := radiusGridPoint_bounds rg hmono (by rw [hz]; positivity : rg 0<2*s)
      (by rw [hlast]; exact htwo.trans hJone) hsteps
    change _ ∧ Q (partitionPoint 0 as (τ (2*s)))<2*s at H
    by_contra hnot
    have H' := comparisonSweepQuantile_monotone hc hk hkc hm hM α
      (partitionPoint_mono as ho (show high ≤ τ (2*s) by omega))
    change 2*s ≤ Q (partitionPoint 0 as high) at hhighradius
    linarith [H.2]
  have htlen : t ≤ steps.length+1 := by
    have H := htbefore.trans hhigh
    simpa only [steps,sampleClockSteps_length] using H.trans (Nat.le_succ as.length)
  have htlow : low ≤ t := by
    rw [ht]
    exact hfork.trans (hτ (by linarith))
  refine ⟨cs,t,a,D,hlen,htlow,htbefore,htlen,hlastcs,hends,hclock,?_,?_,?_⟩
  · simpa only [show (cReg/2)/4=cReg/8 by ring] using hscale
  · have H : ((physicalOverlapResidualPairs cs).card:ℝ) ≤ ((cs.length+1:ℕ):ℝ)^2 := by
      exact_mod_cast physicalOverlapResidualPairs_card_le cs
    have H' := pow_le_pow_left₀ (Nat.cast_nonneg (physicalOverlapResidualPairs cs).card) H 2
    simpa only [hlen,Nat.add_assoc,←pow_mul] using H'
  · positivity

theorem exists_actual_boundary_dyadic_count {N exponent s Rmacro : ℝ}
    (hN : 1<N) (hlog : 1 ≤ Real.log N) (hs : 0<s) (hmacro : 0<Rmacro)
    (hsR : 2*s ≤ Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hlower : N^(-exponent) ≤ s) :
    ∃ J : ℕ,1 ≤ J ∧ Rmacro ≤ (2:ℝ)^J*s ∧ (2:ℝ)^J*s ≤ 1 ∧
      ((J+3:ℕ):ℝ) ≤ (exponent/Real.log 2+4)*Real.log N := by
  let X := Rmacro/s
  let J := PositiveLaplaceAssembly.logarithmicCount 2 X
  have hN0 : 0<N := zero_lt_one.trans hN
  have hX : 0<X := div_pos hmacro hs
  have hX2 : 2 ≤ X := (le_div_iff₀ hs).mpr hsR
  have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hlogX : 0<Real.log X := Real.log_pos (lt_of_lt_of_le (by norm_num : (1:ℝ)<2) hX2)
  have hceil := Nat.le_ceil (Real.log X/Real.log 2)
  have hJ : 1 ≤ J := by
    by_contra hnot
    have hJ0 : J=0 := by omega
    change Real.log X/Real.log 2 ≤ (J:ℝ) at hceil
    rw [hJ0] at hceil
    simp only [Nat.cast_zero] at hceil
    have : 0<Real.log X/Real.log 2 := div_pos hlogX hlog2
    exact not_le_of_gt this hceil
  have hreach := PositiveLaplaceAssembly.pow_logarithmicCount_ge (by norm_num : (1:ℝ)<2) hX
  have hreach' : Rmacro ≤ (2:ℝ)^J*s := (div_le_iff₀ hs).mp hreach
  have hclt := Nat.ceil_lt_add_one (div_nonneg hlogX.le hlog2.le)
  change (J:ℝ)<Real.log X/Real.log 2+1 at hclt
  have hupper : (2:ℝ)^J<2*X := by
    apply (Real.log_lt_log_iff (by positivity : 0<(2:ℝ)^J) (by positivity : 0<2*X)).mp
    rw [Real.log_pow,Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hX.ne']
    have H := (mul_lt_mul_of_pos_right hclt hlog2)
    have he : (Real.log X/Real.log 2+1)*Real.log 2=Real.log X+Real.log 2 := by
      field_simp
    rw [he] at H
    linarith
  have hupper' : (2:ℝ)^J*s ≤ 1 := by
    have H := mul_lt_mul_of_pos_right hupper hs
    have he : (2*X)*s=2*Rmacro := by dsimp only [X]; field_simp
    rw [he] at H
    linarith
  have hXpower : X ≤ N^exponent := by
    apply (div_le_iff₀ hs).mpr
    have H := mul_le_mul_of_nonneg_left hlower (Real.rpow_nonneg hN0.le exponent)
    rw [←Real.rpow_add hN0,add_neg_cancel,Real.rpow_zero] at H
    exact (hRhalf.trans (by norm_num : (1:ℝ)/2 ≤ 1)).trans H
  have hlogbound := Real.log_le_log hX hXpower
  rw [Real.log_rpow hN0] at hlogbound
  have hcount : (J:ℝ) ≤ exponent/Real.log 2*Real.log N+1 := by
    have H := div_le_div_of_nonneg_right hlogbound hlog2.le
    have he : (exponent*Real.log N)/Real.log 2=exponent/Real.log 2*Real.log N := by ring
    rw [he] at H
    linarith
  refine ⟨J,hJ,hreach',hupper',?_⟩
  simp only [Nat.cast_add,Nat.cast_ofNat]
  nlinarith

theorem actual_physical_projection_clock_suffix {n : ℕ}
    {steps : List (GaussianStep (FeatureIndex n))} {fork v w : ℕ} {a D : ℝ}
    (h : PhysicalProjectionClock n steps fork v w a D) :
    PhysicalProjectionClock n (steps.drop fork) 0 (v-fork) (w-fork) a D := by
  cases h with
  | gaussian common tail mid pre skip a D ho hc =>
    have H := PhysicalProjectionClock.gaussian [] tail mid pre skip a D ho hc
    simpa only [List.nil_append,List.length_nil,zero_add,List.drop_left,
      Nat.add_sub_cancel_left] using H
  | terminal common tail pre skip a D ho hc =>
    have H := PhysicalProjectionClock.terminal [] tail pre skip a D ho hc
    simpa only [List.nil_append,List.length_nil,zero_add,List.drop_left,
      List.length_append,Nat.add_sub_cancel_left,Nat.add_assoc] using H

theorem actual_direct_test_calibration_strength {d lam x C : ℝ}
    (hd : 0<d) (hlam : 0<lam) (hld : lam ≤ d^2) (hx : 0<x)
    (hC : 1 ≤ C) (hcompare : x^2 ≤ C^2*laplaceComparisonStrength d lam x) :
    let W := max x (Real.sqrt (laplaceComparisonStrength d lam x))
    0<W ∧ W ≤ C*d ∧ (1/C^3)*W^2 ≤ laplaceComparisonStrength d lam W := by
  let g := laplaceComparisonStrength d lam
  let W := max x (Real.sqrt (g x))
  have hgpos : 0<g x := laplaceComparisonStrength_pos d hlam x
  have hgle : g x ≤ lam := laplaceComparisonStrength_le d hlam.le x
  have hCpos : 0<C := zero_lt_one.trans_le hC
  have hC2 : 1 ≤ C^2 := by nlinarith
  have hW : 0<W := hx.trans_le (le_max_left _ _)
  have hWsq : W^2 ≤ C^2*g x := by
    by_cases h : Real.sqrt (g x) ≤ x
    · simpa only [W,max_eq_left h] using hcompare
    · rw [show W=Real.sqrt (g x) from max_eq_right (le_of_not_ge h),Real.sq_sqrt hgpos.le]
      nlinarith
  have hWsqlam : W^2 ≤ C^2*lam := hWsq.trans (mul_le_mul_of_nonneg_left hgle (sq_nonneg C))
  have hWd : W ≤ C*d := by
    have H := hWsqlam.trans (mul_le_mul_of_nonneg_left hld (sq_nonneg C))
    have hCd : 0<C*d := mul_pos hCpos hd
    nlinarith
  have hC23 : C^2 ≤ C^3 := by
    have H := mul_le_mul_of_nonneg_left hC (sq_nonneg C)
    simpa only [mul_one,pow_succ] using H
  have hfirst : W^2/C^3 ≤ lam := by
    apply (div_le_iff₀ (by positivity : 0<C^3)).mpr
    have H := hWsqlam.trans (mul_le_mul_of_nonneg_right hC23 hlam.le)
    simpa only [mul_comm] using H
  have hsecond : W^2/C^3 ≤ d^3/W := by
    apply (le_div_iff₀ hW).mpr
    have he : W^2/C^3*W=W^3/C^3 := by ring
    rw [he]
    apply (div_le_iff₀ (by positivity : 0<C^3)).mpr
    have H := pow_le_pow_left₀ hW.le hWd 3
    simpa only [mul_pow,mul_comm] using H
  have H := (le_min hfirst hsecond).trans (laplaceComparisonStrength_lower hd hlam hW)
  exact ⟨hW,hWd,by simpa only [one_div,mul_comm,div_eq_mul_inv,mul_one] using H⟩

theorem actual_comparison_boundary_schedule_high_anchor
    {c s cReg cu F : ℝ} {k M : ℝ→ℝ}
    (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
    (hkc : ∀ r∈Icc (0:ℝ) 1,c ≤ k r)
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)
    (α : inverseIntegralConstraints 0 0 k M) (as : List PositiveMass)
    (ho : MassOrdered 0 as) (hs : 0<s) (hcReg : 0<cReg) (hF : 0 ≤ F)
    {high : ℕ}
    (hhighradius : comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as high)=4*s)
    (hregular : ∀ r∈Icc (s/2) 1,cReg*r ≤ α.val.val r ∧ α.val.val r ≤ cu*r) :
    0<partitionPoint 0 as high ∧
      F/((cReg/8)^2*s) ≤ (4*cu*F/(cReg/8)^2)/(partitionPoint 0 as high) := by
  have hr : comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as high)∈Icc (s/2) 1 := by
    constructor
    · rw [hhighradius]; linarith
    · exact (comparisonSweepQuantile_bounds hc hk hkc hm hM α _).2
  have H := hregular _ hr
  rw [comparisonSweepQuantile_spec hc hk hkc hm hM α (partitionPoint_mem as ho high)] at H
  rw [hhighradius] at H
  have hmass : 0<partitionPoint 0 as high :=
    lt_of_lt_of_le (by positivity : 0<cReg*(4*s)) H.1
  refine ⟨hmass,?_⟩
  apply (div_le_div_iff₀ (by positivity : 0<(cReg/8)^2*s) hmass).mpr
  have he : (4*cu*F/(cReg/8)^2)*((cReg/8)^2*s)=F*(cu*(4*s)) := by
    field_simp
  rw [he]
  exact mul_le_mul_of_nonneg_left H.2 hF

end OAI.SKFluctuations.Cavity
