module

public import ComparisonActualHighWallOverlapAmplitude
public import ComparisonCalibrationFloorMass
public import ComparisonSignedCavityActualBoundarySchedule

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization.ActualHighWallData
open Set MeasureTheory ProbabilityTheory Filter Hierarchy Cavity
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 10000000
variable {n : ℕ} {delta : ℝ} (a : ActualHighWallData n delta)

def wallRadius (alpha : a.Profile) : ℝ→ℝ :=
  comparisonCalibrationConstrainedRadius a.hr a.hc a.hk a.hkc a.hm a.hM alpha

theorem wallRadius_bounds (alpha : a.Profile) (u : ℝ) : a.wallRadius alpha u∈Icc a.rmin 1 := by
  exact (constrainedQuantile a.hr a.hc a.hk a.hkc a.hm a.hM alpha
    (projIcc a.s 1 (comparison_calibration_mass_origin_le_one alpha) u)).property

theorem wallRadius_monotone (alpha : a.Profile) : Monotone (a.wallRadius alpha) := by
  apply Monotone.IccExtend (comparison_calibration_mass_origin_le_one alpha)
  intro u v huv
  exact (inverseConstraintOrderIso a.hr a.hc a.hk a.hkc a.hm a.hM alpha).symm.monotone huv

theorem wallRadius_spec (alpha : a.Profile) {u : ℝ} (hu : u∈Icc a.s 1) :
    alpha.val.val (a.wallRadius alpha u)=u := by
  unfold wallRadius comparisonCalibrationConstrainedRadius
  rw [IccExtend_of_mem _ _ hu]
  exact constrainedQuantile_spec a.hr a.hc a.hk a.hkc a.hm a.hM alpha ⟨u,hu⟩

theorem wallRadius_inverse (alpha : a.Profile) {r : ℝ} (hr : r∈Icc a.rmin 1) :
    a.wallRadius alpha (alpha.val.val r)=r :=
  comparison_calibration_constrained_radius_inverse a.hr a.hc a.hk a.hkc a.hm a.hM alpha hr

theorem wallRadius_left (alpha : a.Profile) : a.wallRadius alpha a.s=a.rmin := by
  simpa only [alpha.property.1] using a.wallRadius_inverse alpha ⟨le_rfl,a.hr⟩

theorem wallRadius_one (alpha : a.Profile) : a.wallRadius alpha 1=1 := by
  simpa only [alpha.property.2.1] using a.wallRadius_inverse alpha ⟨a.hr,le_rfl⟩

theorem wallRadius_before (alpha : a.Profile) {u : ℝ} (hu : u ≤ a.s) :
    a.wallRadius alpha u=a.rmin := by
  apply le_antisymm
  · have h:=a.wallRadius_monotone alpha hu
    simpa only [a.wallRadius_left alpha] using h
  · exact (a.wallRadius_bounds alpha u).1

theorem wallRadius_high_mass (alpha : a.Profile) {u : ℝ}
    (hu : a.rmin < a.wallRadius alpha u) : a.s < u := by
  by_contra hn
  rw [a.wallRadius_before alpha (le_of_not_gt hn)] at hu
  exact lt_irrefl _ hu

theorem wallRadius_lipschitz (alpha : a.Profile) :
    LipschitzWith ⟨1/(a.k 1),div_nonneg zero_le_one a.hc.le⟩ (a.wallRadius alpha) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h:=(constrainedQuantile_lipschitz a.hr a.hc a.hk a.hkc a.hm a.hM alpha).dist_le_mul
    (projIcc a.s 1 (comparison_calibration_mass_origin_le_one alpha) x)
    (projIcc a.s 1 (comparison_calibration_mass_origin_le_one alpha) y)
  change dist (a.wallRadius alpha x) (a.wallRadius alpha y) ≤ 
    (1/(a.k 1))*dist (projIcc a.s 1 (comparison_calibration_mass_origin_le_one alpha) x)
      (projIcc a.s 1 (comparison_calibration_mass_origin_le_one alpha) y) at h
  apply h.trans
  have hp:=(LipschitzWith.projIcc (comparison_calibration_mass_origin_le_one alpha)).dist_le_mul x y
  change dist _ _ ≤ (1:ℝ)*dist x y at hp
  change (1/(a.k 1))*dist _ _ ≤ (1/(a.k 1))*dist x y
  simpa only [one_mul] using mul_le_mul_of_nonneg_left hp (div_nonneg zero_le_one a.hc.le)

theorem high_field_clock (alpha : a.Profile) {u : ℝ} (hu : u∈Icc a.s 1) :
    (a.hf alpha u:ℝ)=a.g (a.wallRadius alpha u)*a.wallRadius alpha u := by
  rw [(a.clock_coe alpha ⟨a.hs.1.le.trans hu.1,hu.2⟩).2]
  dsimp only [h]
  rw [wallChangedField_on a.hr a.hs1 a.hc a.hk a.hkc a.hm a.hM a.g a.hg.continuous
    a.T a.epsilon a.theta a.tau a.d alpha hu]
  have he:a.wallRadius alpha u=(constrainedQuantile a.hr a.hc a.hk a.hkc a.hm a.hM alpha ⟨u,hu⟩:ℝ) := by
    unfold wallRadius comparisonCalibrationConstrainedRadius
    rw [IccExtend_of_mem _ _ hu]
    rfl
  rw [he]

theorem high_field_radius_gap (alpha : a.Profile)
    (hN : 1 ≤ a.N) (hlog : 1 ≤ Real.log a.N) (hnd : 1/a.N ≤ a.d)
    {u v : ℝ} (hu : u∈Icc a.s 1) (hv : v∈Icc a.s 1) (huv : u ≤ v) :
    ((1/3)/Real.log a.N)*a.g (a.wallRadius alpha v)*
      (a.wallRadius alpha v-a.wallRadius alpha u) ≤ 
        (a.hf alpha v:ℝ)-(a.hf alpha u:ℝ) := by
  rw [a.high_field_clock alpha hv,a.high_field_clock alpha hu]
  exact actual_comparison_radius_field_increment_lower hN hlog a.hd hnd
    (sq_pos_of_pos a.hd) le_rfl
    (a.hrbounds.1.le.trans (a.wallRadius_bounds alpha u).1)
    (a.wallRadius_bounds alpha v).2 (a.wallRadius_monotone alpha huv)

theorem sampled_radius_step_le (alpha : a.Profile) (as : List PositiveMass)
    (ho : MassOrdered 0 as) {mesh : ℝ} (hmesh : 0 ≤ mesh)
    (hpart : PartitionMesh mesh 0 as) (j : ℕ) :
    a.wallRadius alpha (partitionPoint 0 as (j+1))-
      a.wallRadius alpha (partitionPoint 0 as j) ≤ mesh/(a.k 1) := by
  have h:=(a.wallRadius_lipschitz alpha).dist_le_mul
    (partitionPoint 0 as (j+1)) (partitionPoint 0 as j)
  have hp:=partitionPoint_mono as ho (Nat.le_succ j)
  have hR:=a.wallRadius_monotone alpha hp
  change abs (a.wallRadius alpha (partitionPoint 0 as (j+1))-
    a.wallRadius alpha (partitionPoint 0 as j)) ≤ (1/(a.k 1))*
      abs (partitionPoint 0 as (j+1)-partitionPoint 0 as j) at h
  rw [abs_of_nonneg (sub_nonneg.mpr hR),abs_of_nonneg (sub_nonneg.mpr hp)] at h
  apply h.trans
  have hm:=partitionPoint_step_le_mesh as hpart hmesh j
  simpa only [div_eq_mul_inv,mul_comm,one_mul] using
    mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr a.hc.le)

theorem sampled_grid_field_growth (alpha : a.Profile)
    (hN : 1 ≤ a.N) (hlog : 1 ≤ Real.log a.N) (hnd : 1/a.N ≤ a.d)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    {mesh s t : ℝ} (hmesh : 0 ≤ mesh) (hpart : PartitionMesh mesh 0 as)
    (hstart : a.rmin < s-mesh/(a.k 1)) (hst : s ≤ t) (ht : t ≤ 1) :
    let R:=a.wallRadius alpha
    let rg : Fin (as.length+2)→ℝ:=fun i=>R (partitionPoint 0 as i.val)
    let cut:=radiusGridCut rg
    let steps:=sampleClockSteps (completedPathClock n (a.bf alpha) (a.hf alpha)) 0 as
    t ≤ rg (Fin.last (as.length+1)) →
      ((1/3)/Real.log a.N)*a.g t*(t-s-mesh/(a.k 1)) ≤ 
        physicalFieldDuration (fun st=>st.2 (Sum.inl ⟨0,a.hn⟩)) (steps.take (cut t))-
        physicalFieldDuration (fun st=>st.2 (Sum.inl ⟨0,a.hn⟩)) (steps.take (cut s)) := by
  dsimp only
  let R:=a.wallRadius alpha
  let rg : Fin (as.length+2)→ℝ:=fun i=>R (partitionPoint 0 as i.val)
  let cut:=radiusGridCut rg
  let steps:=sampleClockSteps (completedPathClock n (a.bf alpha) (a.hf alpha)) 0 as
  intro hlast
  have hmono : Monotone rg:=fun i j hij=>
    a.wallRadius_monotone alpha (partitionPoint_mono as ho hij)
  have hz : rg 0=a.rmin := by
    change a.wallRadius alpha (partitionPoint 0 as 0)=a.rmin
    rw [show partitionPoint 0 as 0=0 from by simp [partitionPoint,partitionValues]]
    exact a.wallRadius_before alpha a.hs.1.le
  have hmeshdiv : 0 ≤ mesh/(a.k 1):=div_nonneg hmesh a.hc.le
  have hsroot : rg 0 < s:=by rw [hz];linarith
  have hsteps : ∀j : Fin (as.length+1),rg j.succ-rg j.castSucc ≤ mesh/(a.k 1) :=
    fun j=>a.sampled_radius_step_le alpha as ho hmesh hpart j.val
  have hsamp:=radiusGridPoint_bounds rg hmono hsroot (hst.trans hlast) hsteps
  have htamp:=radiusGridPoint_bounds rg hmono (hsroot.trans_le hst) hlast hsteps
  change s-mesh/(a.k 1) ≤ R (partitionPoint 0 as (cut s)) ∧ R (partitionPoint 0 as (cut s)) < s at hsamp
  change t-mesh/(a.k 1) ≤ R (partitionPoint 0 as (cut t)) ∧ R (partitionPoint 0 as (cut t)) < t at htamp
  have hidx : cut s ≤ cut t:=radiusGridCut_monotone rg hst
  have hrad : R (partitionPoint 0 as (cut s)) ≤ R (partitionPoint 0 as (cut t)) :=
    a.wallRadius_monotone alpha (partitionPoint_mono as ho hidx)
  have hslow : a.rmin < R (partitionPoint 0 as (cut s)) := by
    exact hstart.trans_le hsamp.1
  have hsMass : partitionPoint 0 as (cut s)∈Icc a.s 1 :=
    ⟨(a.wallRadius_high_mass alpha hslow).le,(partitionPoint_mem as ho (cut s)).2⟩
  have htMass : partitionPoint 0 as (cut t)∈Icc a.s 1 :=
    ⟨hsMass.1.trans (partitionPoint_mono as ho hidx),(partitionPoint_mem as ho (cut t)).2⟩
  have hdist : t-s-mesh/(a.k 1) ≤ 
      R (partitionPoint 0 as (cut t))-R (partitionPoint 0 as (cut s)) := by
    linarith [hsamp.2,htamp.1]
  have hcoef : 0 ≤ ((1:ℝ)/3)/Real.log a.N := by positivity
  have hanti := (laplaceComparisonStrength_monotonicities a.hd.ne' (sq_pos_of_pos a.hd)
    a.hrbounds.1.le).1 (a.wallRadius_bounds alpha _) ⟨by linarith,ht⟩
    htamp.2.le
  have hsave:=mul_le_mul_of_nonneg_left hdist
    (mul_nonneg hcoef (laplaceComparisonStrength_pos a.d (sq_pos_of_pos a.hd) t).le)
  have hg:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hanti hcoef)
    (sub_nonneg.mpr hrad)
  have hfield:=a.high_field_radius_gap alpha hN hlog hnd hsMass htMass
    (partitionPoint_mono as ho hidx)
  have hfinal:=hsave.trans (hg.trans hfield)
  rw [sampledFieldDuration_index n a.hn (a.bf alpha) (a.hf alpha)
      (a.bf_monotone alpha) (a.hf_monotone alpha) as ho (cut t) (radiusGridCut_le rg t),
    sampledFieldDuration_index n a.hn (a.bf alpha) (a.hf alpha)
      (a.bf_monotone alpha) (a.hf_monotone alpha) as ho (cut s) (radiusGridCut_le rg s),
    physicalCutMass_sampleClockSteps _ _ _ _ (radiusGridCut_le rg t),
    physicalCutMass_sampleClockSteps _ _ _ _ (radiusGridCut_le rg s)]
  exact hfinal.trans_eq (by ring)

end OAI.SKFluctuations.LaplaceWindowFormalization.ActualHighWallData
