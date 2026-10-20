module

public import PhysicalComparisonSampledCell
public import FiniteRadiusCellIntervals
public import VariableEndpointComparisonPotential

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 1000000

theorem physicalSampledSecondMoment_clipped_monotone (n : ℕ)
    (b h : ℝ→ℝ≥0) (as : List PositiveMass) (ho : MassOrdered 0 as) :
    Monotone (fun j=>physicalPathSecondMoment n
      (sampleClockSteps (completedPathClock n b h) 0 as) (completedPathClock n b h 0)
        (min j as.length)) := by
  intro i j hij
  exact physicalPathSecondMoment_mono n _ (sampleClockSteps_ordered _ _ ho) _
    (min_le_min_right _ hij) (by simpa only [sampleClockSteps_length] using min_le_right j as.length)

section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0 < c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

def comparisonPhysicalRadiusDensity (n dphys : ℕ)
    (e : Fin (dphys+1) ≃ FeatureIndex (n+1)) (d lam : ℝ) (b h : ℝ→ℝ)
    (α : inverseIntegralConstraints 0 0 k M) (as : List PositiveMass)
    (ho : MassOrdered 0 as) : ℝ→ℝ :=
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
  let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
  let q := completedPathClock (n+1) bf hf
  let steps := sampleClockSteps q 0 as
  let ha : OrderedSteps 0 (steps++[]) := by
    simpa only [List.append_nil] using sampleClockSteps_ordered q _ ho
  physicalRadiusCellEnergyDensity n dphys e (q 0) steps [] ha 0 R 0 as

def comparisonPhysicalRadiusMeasure (n dphys : ℕ)
    (e : Fin (dphys+1) ≃ FeatureIndex (n+1)) (d lam : ℝ) (b h : ℝ→ℝ)
    (α : inverseIntegralConstraints 0 0 k M) (as : List PositiveMass)
    (ho : MassOrdered 0 as) : Measure ℝ :=
  volume.withDensity (fun r=>ENNReal.ofReal
    (comparisonPhysicalRadiusDensity hc hk hkc hm hM n dphys e d lam b h α as ho r))

theorem comparisonPhysicalRadiusDensity_mem_Icc (n dphys : ℕ)
    (e : Fin (dphys+1) ≃ FeatureIndex (n+1)) (d lam : ℝ) (b h : ℝ→ℝ)
    (α : inverseIntegralConstraints 0 0 k M) (as : List PositiveMass)
    (ho : MassOrdered 0 as) (r : ℝ) :
    comparisonPhysicalRadiusDensity hc hk hkc hm hM n dphys e d lam b h α as ho r∈Icc (0:ℝ) 1 := by
  exact physicalRadiusCellEnergyDensity_mem_Icc n dphys e _ _ _ _ 0 _
    (comparisonSweepQuantile_monotone hc hk hkc hm hM α) as ho r

theorem comparisonPhysicalRadiusMeasure_interval_le
    {N d lam p z mesh : ℝ} (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N)
    (hd : 0 < d) (hnd : 1/N ≤ d) (hlam : 0 < lam) (hld : lam ≤ d^2)
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (b h : ℝ→ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0) (hlb : lam ≤ b 0)
    (α : inverseIntegralConstraints 0 0 k M) (as : List PositiveMass)
    (ho : MassOrdered 0 as) (hend : partitionEnd 0 as=1)
    (hmesh : PartitionMesh mesh 0 as) (hmesh0 : 0 ≤ mesh)
    (hp : 0 < p) (hpz : p ≤ z) (hz : z ≤ 1) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
    let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
    let q := completedPathClock (n+1) bf hf
    let S := fun r=>orderedPathS (n+1) bf hf (α.val.val r)
    let F := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam z)
    let Cnode := 2*ClockTree.errorJetVariation 2 0 0*
      clockVariationBound (physicalFeatureCoordinateBound n) q
    comparisonPhysicalRadiusMeasure hc hk hkc hm hM n dphys e d lam b h α as ho (Ioo p z) ≤
      ENNReal.ofReal ((S z-S p)/F)+ENNReal.ofReal (2*(mesh*Cnode)/F+2*(mesh/c)) := by
  dsimp only
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
  let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
  let q := completedPathClock (n+1) bf hf
  let steps := sampleClockSteps q 0 as
  let ha : OrderedSteps 0 (steps++[]) := by
    simpa only [List.append_nil] using sampleClockSteps_ordered q _ ho
  let C := fun j=>physicalRootedCapCellTrace n dphys e (q 0) steps [] ha j
  let x := fun j=>R (partitionPoint 0 as j)
  let y := fun j=>physicalPathSecondMoment (n+1) steps (q 0) (min j as.length)
  let S := fun r=>orderedPathS (n+1) bf hf (α.val.val r)
  let Sext := fun r : ℝ=>S (projIcc (0:ℝ) 1 zero_le_one r)
  let F := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam z)
  let Cnode := 2*ClockTree.errorJetVariation 2 0 0*
    clockVariationBound (physicalFeatureCoordinateBound n) q
  have had := comparisonVariableEndpoint_clocks_admissible hc hk hkc hm hM b h
    hd.ne' hlam.le hlb hb hh hh0 α
  have hbf : MonotoneOn bf (Icc (0:ℝ) 1) := toNNReal_monotoneOn had.1
  have hhf : MonotoneOn hf (Icc (0:ℝ) 1) := toNNReal_monotoneOn had.2.1
  have hSm : MonotoneOn S (Icc (0:ℝ) 1) :=
    (comparisonVariableEndpoint_radius_moments hc hk hkc hm hM (n+1) (by omega)
      b h hd.ne' hlam.le hlb hb hh hh0 α).1
  have hSext : Monotone Sext := by
    intro u v huv
    exact hSm (projIcc 0 1 zero_le_one u).property (projIcc 0 1 zero_le_one v).property
      (monotone_projIcc zero_le_one huv)
  have hSextEq r (hr : r∈Icc (0:ℝ) 1) : Sext r=S r := by
    simp only [Sext,projIcc_of_mem zero_le_one hr]
  have hx : Monotone x := (comparisonSweepQuantile_monotone hc hk hkc hm hM α).comp
    (partitionPoint_mono as ho)
  have hy : Monotone y := physicalSampledSecondMoment_clipped_monotone (n+1) bf hf as ho
  have hC (j : ℕ) : C j∈Icc (0:ℝ) 1 := physicalRootedCapCellTrace_mem_Icc n dphys e _ _ _ _ j
  have hF : 0 < F := mul_pos (by positivity) (mul_pos
    (div_pos (by norm_num) (by linarith)) (laplaceComparisonStrength_pos d hlam z))
  have hCn : 0 ≤ Cnode := by
    dsimp only [Cnode]
    exact mul_nonneg (mul_nonneg (by norm_num) (ClockTree.errorJetVariation_nonneg _ _ _))
      (clockVariationBound_nonneg (physicalFeatureCoordinateBound n) q
        (completedPathClock_monotone (n+1) hbf hhf))
  have hnode (j : ℕ) (hj : j ≤ as.length) (hxi : x j∈Icc p z) :
      |y j-Sext (x j)| ≤ mesh*Cnode := by
    have hx01 : x j∈Icc (0:ℝ) 1 := comparisonSweepQuantile_bounds hc hk hkc hm hM α _
    have hj0 : 0 < j := by
      by_contra hnj
      have hjz : j=0 := by omega
      subst j
      have hr0 : R (partitionPoint 0 as 0)=0 := by
        simpa only [α.property.1,partitionPoint,partitionValues_zero,id_eq,R] using
          comparisonSweepQuantile_inverse hc hk hkc hm hM α (by norm_num : (0:ℝ)∈Icc 0 1)
      have hpx : p ≤ R (partitionPoint 0 as 0) := hxi.1
      rw [hr0] at hpx
      linarith
    rw [hSextEq _ hx01]
    have ht := physicalComparisonSampledNode_radius_error hc hk hkc hm hM n bf hf hbf hhf α
      as ho hend hmesh j hj (massPartition_point_pos 0 as hj0 hj)
    simpa only [y,min_eq_left hj,Cnode,x,S,R,q,steps] using ht
  have hinc (j : ℕ) (hj : j < as.length) (_ : p ≤ x j) (hjz : x (j+1) ≤ z) :
      (x (j+1)-x j)*C j ≤ (y (j+1)-y j)/F := by
    have ht := physicalComparisonSampledCell_increment_at_index hc hk hkc hm hM
      hN hlog hd hnd hlam hld n dphys e b h hh hh0 α as ho j hj hz hjz
    dsimp only at ht
    change ((x (j+1)-x j).toNNReal:ℝ)*C j ≤ _ at ht
    rw [Real.coe_toNNReal _ (sub_nonneg.mpr (hx (Nat.le_succ j)))] at ht
    simpa only [y,min_eq_left hj.le,min_eq_left (by omega : j+1 ≤ as.length),
      C,x,R,bf,hf,q,steps,ha,F] using ht
  have hbound r : finiteRadiusCellDensity as.length x C r ≤ 1 := by
    rw [←radiusCellEnergyDensity_eq_finite_sum R 0 as C r]
    exact (radiusCellEnergyDensity_mem_Icc R
      (comparisonSweepQuantile_monotone hc hk hkc hm hM α) as ho C hC r).2
  have ht := finite_radius_cell_measure_interval_le hx hy hSext hpz (mul_nonneg hmesh0 hCn) hF
    (div_nonneg hmesh0 hc.le) (fun j _=>(hC j).1)
    (fun j hj=>comparisonSampledRadius_point_mesh hc hk hkc hm hM α as ho hmesh j hj)
    hbound hnode hinc
  rw [hSextEq p ⟨hp.le,hpz.trans hz⟩,hSextEq z ⟨hp.le.trans hpz,hz⟩] at ht
  simpa only [comparisonPhysicalRadiusMeasure,comparisonPhysicalRadiusDensity,
    physicalRadiusCellEnergyDensity,Nat.zero_add,radiusCellEnergyDensity_eq_finite_sum,
    R,bf,hf,q,steps,ha,C,x,S,F,Cnode] using ht
end
end OAI.SKFluctuations.LaplaceWindowFormalization
