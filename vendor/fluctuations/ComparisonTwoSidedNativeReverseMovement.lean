module

public import PhysicalComparisonSampledCell
public import VariableEndpointComparisonCaps
public import ComparisonReverseMovementScale

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 1000000

theorem physicalSampledNodeSecondMoment_increment_le (n : ℕ) (b h : ℝ→ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh : ℝ} (hm : PartitionMesh mesh 0 as) {i j : ℕ}
    (hi : i≤as.length) (hj : j≤as.length)
    (hui : 0<partitionPoint 0 as i) (huj : 0<partitionPoint 0 as j) :
    let q := completedPathClock (n+1) b h
    let steps := sampleClockSteps q 0 as
    physicalPathSecondMoment (n+1) steps (q 0) j-
      physicalPathSecondMoment (n+1) steps (q 0) i ≤
      orderedPathS (n+1) b h (partitionPoint 0 as j)-
        orderedPathS (n+1) b h (partitionPoint 0 as i)+
      2*(mesh*(2*ClockTree.errorJetVariation 2 0 0*
        clockVariationBound (physicalFeatureCoordinateBound n) q)) := by
  dsimp only
  have hierror := abs_le.mp (physicalSampledNodeSecondMoment_error n b h hb hh as ho he hm i hi hui)
  have hjerror := abs_le.mp (physicalSampledNodeSecondMoment_error n b h hb hh as ho he hm j hj huj)
  linarith

theorem physicalSampledNodeSecondMoment_abs_le (n : ℕ) (b h : ℝ→ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh : ℝ} (hm : PartitionMesh mesh 0 as) {i j : ℕ}
    (hi : i≤as.length) (hj : j≤as.length)
    (hui : 0<partitionPoint 0 as i) (huj : 0<partitionPoint 0 as j) :
    let q := completedPathClock (n+1) b h
    let steps := sampleClockSteps q 0 as
    |physicalPathSecondMoment (n+1) steps (q 0) j-
      physicalPathSecondMoment (n+1) steps (q 0) i| ≤
      |orderedPathS (n+1) b h (partitionPoint 0 as j)-
        orderedPathS (n+1) b h (partitionPoint 0 as i)|+
      2*(mesh*(2*ClockTree.errorJetVariation 2 0 0*
        clockVariationBound (physicalFeatureCoordinateBound n) q)) := by
  dsimp only
  have hierror := abs_le.mp (physicalSampledNodeSecondMoment_error n b h hb hh as ho he hm i hi hui)
  have hjerror := abs_le.mp (physicalSampledNodeSecondMoment_error n b h hb hh as ho he hm j hj huj)
  have hlo := neg_abs_le (orderedPathS (n+1) b h (partitionPoint 0 as j)-
    orderedPathS (n+1) b h (partitionPoint 0 as i))
  have hup := le_abs_self (orderedPathS (n+1) b h (partitionPoint 0 as j)-
    orderedPathS (n+1) b h (partitionPoint 0 as i))
  apply abs_le.mpr
  constructor <;> linarith

theorem physicalSideMovementMoment_comm (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (q0 : FeatureIndex n→ℝ≥0)
    (i j : ℕ) :
    physicalSideMovementMoment n steps q0 i j=physicalSideMovementMoment n steps q0 j i := by
  unfold physicalSideMovementMoment
  simp only [norm_sub_rev]

theorem sampleClockSteps_congr_on_mass_interval {ι : Type*}
    (q q' : ℝ→ι→ℝ≥0) (heq : ∀u∈Icc (0:ℝ) 1,q u=q' u)
    {u : ℝ} (as : List PositiveMass) (ho : MassOrdered u as) :
    sampleClockSteps q u as=sampleClockSteps q' u as := by
  induction as generalizing u with
  | nil=>rfl
  | cons v as ih=>
    have hu : u∈Icc (0:ℝ) 1 := massOrdered_bounds ho
    have hv : v.val∈Icc (0:ℝ) 1 := massOrdered_bounds ho.2.2
    simp only [sampleClockSteps,heq u hu,heq v.val hv,ih ho.2.2]

section
variable {c : ℝ} {k M : ℝ → ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c≤k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)

theorem comparisonVariableEndpoint_sampled_clocks_eq
    (n : ℕ) (b h g : ℝ→ℝ) (hg : Continuous g)
    (α : inverseIntegralConstraints 0 0 k M)
    (as : List PositiveMass) (ho : MassOrdered 0 as) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    let ei := omittedExtension zero_le_one
      (constrainedCoefficient zero_le_one hc hk hkc hm hM g hg α)
    let qi := omittedExtension zero_le_one
      (constrainedCoefficient zero_le_one hc hk hkc hm hM (fun r=>g r*r)
        (hg.mul continuous_id) α)
    let inv := completedPathClock n (fun u=>(b u-ei u).toNNReal) (fun u=>(h u+qi u).toNNReal)
    let sweep := completedPathClock n (fun u=>(b u-g (R u)).toNNReal)
      (fun u=>(h u+g (R u)*R u).toNNReal)
    inv 0=sweep 0 ∧ sampleClockSteps inv 0 as=sampleClockSteps sweep 0 as := by
  dsimp only
  have heq (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
      completedPathClock n
        (fun v=>(b v-omittedExtension zero_le_one
          (constrainedCoefficient zero_le_one hc hk hkc hm hM g hg α) v).toNNReal)
        (fun v=>(h v+omittedExtension zero_le_one
          (constrainedCoefficient zero_le_one hc hk hkc hm hM (fun r=>g r*r)
            (hg.mul continuous_id) α) v).toNNReal) u=
      completedPathClock n (fun v=>(b v-g (comparisonSweepQuantile hc hk hkc hm hM α v)).toNNReal)
        (fun v=>(h v+g (comparisonSweepQuantile hc hk hkc hm hM α v)*
          comparisonSweepQuantile hc hk hkc hm hM α v).toNNReal) u := by
    dsimp only [completedPathClock]
    rw [fullMassCoefficient_eq_sweepQuantile hc hk hkc hm hM g hg α hu,
      fullMassCoefficient_eq_sweepQuantile hc hk hkc hm hM (fun r=>g r*r)
        (hg.mul continuous_id) α hu]
  exact ⟨heq 0 (by norm_num),sampleClockSteps_congr_on_mass_interval _ _ heq as ho⟩

theorem actual_variableEndpoint_sampled_cap_increment
    {N d lam : ℝ} (hN : 1≤N) (hlog : 1≤Real.log N) (hd : 0<d)
    (hnd : 1/N≤d) (hlam : 0<lam) (hld : lam≤d^2)
    (n : ℕ) (b h : ℝ → ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hlb : lam≤b 0) (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0≤h 0) (α : inverseIntegralConstraints 0 0 k M)
    (H J : ℝ → ℝ) (hH : AbsolutelyContinuousOnInterval H 0 1)
    (hJ : ∀r∈Icc (0:ℝ) 1,0<J r)
    (hD : ∀ᵐ r,r∈Icc (0:ℝ) 1→HasDerivAt H
      (J r*radiusComparisonGradient (laplaceComparisonStrength d lam) α.val.val
        (orderedPathS (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal))
        (orderedPathB (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal)) r) r)
    {a z : ℝ} (ha : 0≤a) (hz : z≤1)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh : ℝ} (hmesh : PartitionMesh mesh 0 as) {i j : ℕ}
    (hij : i≤j) (hj : j≤as.length) (hui : 0<partitionPoint 0 as i)
    (hs : comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as i)∈Ioo a z)
    (ht : comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as j)∈Ioo a z)
    (haH : H a=0) (hzH : H z=0)
    (hsH : H (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as i))<0)
    (htH : H (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as j))<0) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
    let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
    let q := completedPathClock (n+1) bf hf
    let steps := sampleClockSteps q 0 as
    physicalPathSecondMoment (n+1) steps (q 0) j-
      physicalPathSecondMoment (n+1) steps (q 0) i ≤
      9*Real.log N*(z-a)+2*(mesh*(2*ClockTree.errorJetVariation 2 0 0*
        clockVariationBound (physicalFeatureCoordinateBound n) q)) := by
  dsimp only
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
  let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
  let q := completedPathClock (n+1) bf hf
  let steps := sampleClockSteps q 0 as
  have hi : i≤as.length := hij.trans hj
  have hmass : partitionPoint 0 as i≤partitionPoint 0 as j := partitionPoint_mono as ho hij
  have huj : 0<partitionPoint 0 as j := hui.trans_le hmass
  have hrad := comparisonSweepQuantile_monotone hc hk hkc hm hM α hmass
  have had := comparisonVariableEndpoint_clocks_admissible hc hk hkc hm hM b h
    hd.ne' hlam.le hlb hb hh hh0 α
  have hinc := (actual_variableEndpoint_comparison_cap_interior_geometry hc hk hkc hm hM
    hN hlog hd hnd hlam hld (n+1) (by omega) b h hb hlb hh hh0 α H J hH hJ hD
    ha hz hs ht hrad haH hzH hsH htH).1
  have hsi := abs_le.mp (physicalComparisonSampledNode_radius_error hc hk hkc hm hM
    n bf hf (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1)
    α as ho he hmesh i hi hui)
  have hsj := abs_le.mp (physicalComparisonSampledNode_radius_error hc hk hkc hm hM
    n bf hf (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1)
    α as ho he hmesh j hj huj)
  dsimp only [R,bf,hf,q,steps] at hsi hsj ⊢
  linarith

theorem actual_variableEndpoint_sampled_cap_reverse_fourth
    {N d lam : ℝ} (hN : 1≤N) (hlog : 1≤Real.log N) (hd : 0<d)
    (hnd : 1/N≤d) (hlam : 0<lam) (hld : lam≤d^2)
    (n l : ℕ) (hl : 2<l) (b h : ℝ → ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hlb : lam≤b 0) (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0≤h 0) (α : inverseIntegralConstraints 0 0 k M)
    (H J : ℝ → ℝ) (hH : AbsolutelyContinuousOnInterval H 0 1)
    (hJ : ∀r∈Icc (0:ℝ) 1,0<J r)
    (hD : ∀ᵐ r,r∈Icc (0:ℝ) 1→HasDerivAt H
      (J r*radiusComparisonGradient (laplaceComparisonStrength d lam) α.val.val
        (orderedPathS (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal))
        (orderedPathB (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal)) r) r)
    {a z : ℝ} (ha : 0≤a) (hz : z≤1)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh : ℝ} (hmesh : PartitionMesh mesh 0 as) {i j : ℕ}
    (hij : i≤j) (hj : j≤as.length) (hui : 0<partitionPoint 0 as i)
    (hs : comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as i)∈Ioo a z)
    (ht : comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as j)∈Ioo a z)
    (haH : H a=0) (hzH : H z=0)
    (hsH : H (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as i))<0)
    (htH : H (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as j))<0)
    {xs : ℝ} (hxs : 0<xs) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
    let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
    let q := completedPathClock (n+1) bf hf
    let steps := sampleClockSteps q 0 as
    physicalSideMovementMoment (n+1) steps (q 0) i j ≤
      (9*Real.log N*(z-a)+2*(mesh*(2*ClockTree.errorJetVariation 2 0 0*
        clockVariationBound (physicalFeatureCoordinateBound n) q)))^
        (((l:ℝ)-2)/((l:ℝ)-1))*
      ((2*physicalRawRatio (n+1) l steps 0 xs
        (Measure.pi fun v=>gaussianReal 0 (q 0 v)) id measurable_id)^(2*l)*
        (xs+physicalCutMass 0 steps j)^l)^(1/((l:ℝ)-1)) := by
  dsimp only
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
  let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
  let q := completedPathClock (n+1) bf hf
  let steps := sampleClockSteps q 0 as
  have hsteps : OrderedSteps 0 steps := sampleClockSteps_ordered q as ho
  have hjsteps : j ≤ steps.length+1 := by simp only [steps,sampleClockSteps_length];omega
  have hinc := actual_variableEndpoint_sampled_cap_increment hc hk hkc hm hM
    hN hlog hd hnd hlam hld n b h hb hlb hh hh0 α H J hH hJ hD
    ha hz as ho he hmesh hij hj hui hs ht haH hzH hsH htH
  have hbase : 0≤physicalPathSecondMoment (n+1) steps (q 0) j-
      physicalPathSecondMoment (n+1) steps (q 0) i := by
    rw [←physical_movement_second_eq_profile_increment (n+1) steps hsteps (q 0) hij]
    exact integral_nonneg (fun _=>sq_nonneg _)
  have hlR : (2:ℝ)<l := by exact_mod_cast hl
  have hp : 0≤((l:ℝ)-2)/((l:ℝ)-1) := div_nonneg (by linarith) (by linarith)
  have hpow := Real.rpow_le_rpow hbase hinc hp
  have hraw := physical_movement_fourth_le_raw_interpolation (n+1) l hl steps hsteps (q 0)
    hxs hij hjsteps
  have hQ0 : 0≤physicalRawRatio (n+1) l steps 0 xs
      (Measure.pi fun v=>gaussianReal 0 (q 0 v)) id measurable_id :=
    zero_le_one.trans (physicalRawRatio_one_le (n+1) l steps 0 xs _ id measurable_id)
  have hmass0 : 0≤xs+physicalCutMass 0 steps j :=
    add_nonneg hxs.le (physicalCutMass_mem steps hsteps j).1
  exact hraw.trans (mul_le_mul_of_nonneg_right hpow (by positivity))

end

end OAI.SKFluctuations.LaplaceWindowFormalization
