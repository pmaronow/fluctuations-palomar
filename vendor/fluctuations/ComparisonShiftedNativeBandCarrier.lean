module

public import ComparisonActualHighWallPotential
public import ComparisonCalibrationFloorMass
public import ComparisonNativeConstructedRows
public import ComparisonNativeRadiusCellLengths

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 8000000
attribute [local instance] Classical.propDecidable

structure ShiftedNativeBandModel where
  rmin : ℝ
  u0 : ℝ
  c : ℝ
  k : ℝ → ℝ
  M : ℝ → ℝ
  hr : rmin ≤ 1
  hu : u0 ∈ Icc (0:ℝ) 1
  hc : 0 < c
  hk : ContinuousOn k (Icc rmin 1)
  hkc : ∀r∈Icc rmin 1,c ≤ k r
  hm : MonotoneOn M (Icc (0:ℝ) 1)
  hM : 0 ≤ M 1
  alpha : inverseIntegralConstraints rmin u0 k M
  n : ℕ
  bf : ℝ → ℝ≥0
  hf : ℝ → ℝ≥0
  hbf : MonotoneOn bf (Icc (0:ℝ) 1)
  hhf : MonotoneOn hf (Icc (0:ℝ) 1)

namespace ShiftedNativeBandModel
variable (m : ShiftedNativeBandModel)

abbrev R := comparisonCalibrationConstrainedRadius m.hr m.hc m.hk m.hkc m.hm m.hM m.alpha
abbrev q := completedPathClock (m.n+1) m.bf m.hf
abbrev thermal := fun u=>orderedPathB (m.n+1) m.bf m.hf u-
  (orderedPathS (m.n+1) m.bf m.hf u)^2

theorem R_eq {u : ℝ} (hu : u∈Icc m.u0 1) :
    m.R u=constrainedQuantile m.hr m.hc m.hk m.hkc m.hm m.hM m.alpha ⟨u,hu⟩ := by
  exact IccExtend_of_mem _ _ hu

theorem R_continuous : Continuous m.R :=
  comparison_calibration_constrained_radius_continuous m.hr m.hc m.hk m.hkc m.hm m.hM m.alpha

theorem R_monotone : Monotone m.R := by
  apply Monotone.IccExtend
  intro u v huv
  exact (inverseConstraintOrderIso m.hr m.hc m.hk m.hkc m.hm m.hM m.alpha).symm.monotone huv

theorem R_bounds (u : ℝ) : m.R u∈Icc m.rmin 1 :=
  (constrainedQuantile m.hr m.hc m.hk m.hkc m.hm m.hM m.alpha
    (projIcc m.u0 1 (comparison_calibration_mass_origin_le_one m.alpha) u)).property

theorem R_spec {u : ℝ} (hu : u∈Icc m.u0 1) : m.alpha.val.val (m.R u)=u := by
  rw [m.R_eq hu]
  exact constrainedQuantile_spec m.hr m.hc m.hk m.hkc m.hm m.hM m.alpha ⟨u,hu⟩

theorem R_inverse {r : ℝ} (hr : r∈Icc m.rmin 1) : m.R (m.alpha.val.val r)=r :=
  comparison_calibration_constrained_radius_inverse m.hr m.hc m.hk m.hkc m.hm m.hM m.alpha hr

theorem R_left : m.R m.u0=m.rmin := by
  simpa only [m.alpha.property.1] using m.R_inverse (r:=m.rmin) ⟨le_rfl,m.hr⟩

theorem R_one : m.R 1=1 := by
  simpa only [m.alpha.property.2.1] using m.R_inverse (r:=1) ⟨m.hr,le_rfl⟩

theorem R_lipschitz : LipschitzWith ⟨1/m.c,div_nonneg zero_le_one m.hc.le⟩ m.R := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hh := (constrainedQuantile_lipschitz m.hr m.hc m.hk m.hkc m.hm m.hM m.alpha).dist_le_mul
    (projIcc m.u0 1 (comparison_calibration_mass_origin_le_one m.alpha) x)
    (projIcc m.u0 1 (comparison_calibration_mass_origin_le_one m.alpha) y)
  change dist (m.R x) (m.R y) ≤ (1/m.c)*dist
    (projIcc m.u0 1 (comparison_calibration_mass_origin_le_one m.alpha) x)
    (projIcc m.u0 1 (comparison_calibration_mass_origin_le_one m.alpha) y) at hh
  apply hh.trans
  have hp := (LipschitzWith.projIcc (comparison_calibration_mass_origin_le_one m.alpha)).dist_le_mul x y
  change dist _ _ ≤ (1:ℝ)*dist x y at hp
  exact mul_le_mul_of_nonneg_left (by simpa only [one_mul] using hp)
    (div_nonneg zero_le_one m.hc.le)

theorem density_floor_ae : ∀ᵐ r,r∈Icc m.rmin 1 → m.k r ≤ deriv m.alpha.val.val r :=
  (lipschitz_ae_deriv_lower_iff m.hr
    (inverseIntegralConstraints_lipschitz m.hm m.hM m.alpha.property) m.hk).mpr
      (fun r hr s hs hrs=>(m.alpha.property.2.2 r hr s hs hrs).1)

theorem mass_radius_cell_substitution (f : ℝ→ℝ)
    {u v : ℝ} (hu : u∈Icc m.u0 1) (hv : v∈Icc m.u0 1) (huv : u≤v) :
    (∫s in u..v,f s)=∫r in Icc (m.R u) (m.R v),deriv m.alpha.val.val r*f (m.alpha.val.val r) := by
  have hRu := m.R_bounds u
  have hRv := m.R_bounds v
  have hrad := m.R_monotone huv
  have hsub : Icc (m.R u) (m.R v)⊆Icc m.rmin 1 := Icc_subset_Icc hRu.1 hRv.2
  have hLip := (inverseIntegralConstraints_lipschitz m.hm m.hM m.alpha.property).mono hsub
  have himage : m.alpha.val.val '' Icc (m.R u) (m.R v)=Icc u v := by
    have ht := hLip.continuousOn.image_Icc_of_monotoneOn hrad (m.alpha.val.property.2.monotoneOn _)
    simpa only [m.R_spec hu,m.R_spec hv] using ht
  have hinj := (inverseConstraint_strictMonoOn m.hc m.hk m.hkc m.alpha.property).mono hsub
  rw [intervalIntegral.integral_of_le huv,←integral_Icc_eq_integral_Ioc,
    ←himage,lipschitz_interval_integral_image hrad hLip hinj.injOn]
  apply setIntegral_congr_fun measurableSet_Icc
  intro r _
  dsimp only
  rw [abs_of_nonneg m.alpha.val.property.2.deriv_nonneg]

def rows (as : List PositiveMass) (ag zg : ℝ) :
    Finset (Fin ((sampleClockSteps m.q 0 as).length+1)) :=
  Finset.univ.filter (fun i=>
    0<pathMassDifferences (sampleClockSteps m.q 0 as) 0 i ∧
    m.u0≤partitionPoint 0 as i.val ∧
    ag ≤ m.R (partitionPoint 0 as i.val) ∧ m.R (partitionPoint 0 as (i.val+1)) ≤ zg)

def rowRadius (as : List PositiveMass)
    (i : Fin ((sampleClockSteps m.q 0 as).length+1)) : ℝ :=
  m.R (physicalCutMass 0 (sampleClockSteps m.q 0 as) i.val)

theorem rowRadius_monotone (as : List PositiveMass) (ho : MassOrdered 0 as) :
    Monotone (m.rowRadius as) := by
  intro i j hij
  exact m.R_monotone (physicalCutMass_monotone _ (sampleClockSteps_ordered _ _ ho) hij)

def bin (as : List PositiveMass) (ag zg : ℝ) (U : Set ℝ)
    (bins : ℕ) (w : ℝ) (bb : Fin bins) :
    Finset (Fin ((sampleClockSteps m.q 0 as).length+1)) :=
  NativeUnitHeight.bin
    (fun i=>physicalPathSecondMoment (m.n+1) (sampleClockSteps m.q 0 as) (m.q 0) i.val)
    (m.rows as ag zg) (firstWholeUnitCell U (m.rowRadius as)) bins w bb

theorem bin_exists_coordinates (as : List PositiveMass) (ho : MassOrdered 0 as)
    (ag zg : ℝ) (U : Set ℝ) (bins : ℕ) (w : ℝ) (bb : Fin bins) :
    Nonempty (NativeConstructedCoordinates (sampleClockSteps m.q 0 as)
      (m.bin as ag zg U bins w bb) (m.rowRadius as) U) := by
  apply exists_nativeConstructedCoordinates _ (sampleClockSteps_ordered _ _ ho) _ _ _
    (m.rowRadius_monotone as ho) U
  intro i hi
  have hrow := (Finset.mem_filter.mp hi).1
  change i∈Finset.univ.filter _ at hrow
  exact (Finset.mem_filter.mp hrow).2.1

def unitColumn (as : List PositiveMass) {K : ℕ}
    (J : Finset (Fin ((sampleClockSteps m.q 0 as).length+1)))
    (unit : Fin ((sampleClockSteps m.q 0 as).length+1)→Fin K) (col : Fin K→ℝ) : ℝ→ℝ :=
  radiusCellEnergyDensity m.R 0 as (nativeSelectedColumn J unit col)

theorem unitColumn_measurable (as : List PositiveMass) {K : ℕ}
    (J : Finset (Fin ((sampleClockSteps m.q 0 as).length+1)))
    (unit : Fin ((sampleClockSteps m.q 0 as).length+1)→Fin K) (col : Fin K→ℝ) :
    Measurable (m.unitColumn as J unit col) := radiusCellEnergyDensity_measurable _ _ _ _

def radiusDensity (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (m.n+1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) : ℝ→ℝ :=
  physicalRadiusCellEnergyDensity (a := 0) m.n dphys e (m.q 0)
    (sampleClockSteps m.q 0 as) [] (by simpa using sampleClockSteps_ordered m.q _ ho)
    0 m.R 0 as

def radiusMeasure (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (m.n+1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) : Measure ℝ :=
  volume.withDensity (fun r=>ENNReal.ofReal (m.radiusDensity dphys e as ho r))

theorem radiusDensity_bounds (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (m.n+1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) (r : ℝ) :
    m.radiusDensity dphys e as ho r∈Icc (0:ℝ) 1 :=
  physicalRadiusCellEnergyDensity_mem_Icc _ _ _ _ _ _ _ _ _ m.R_monotone _ ho r

theorem radiusMeasure_le_volume (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (m.n+1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) : m.radiusMeasure dphys e as ho≤volume := by
  exact radiusCellEnergyMeasure_le_volume _ m.R_monotone as ho _
    (fun j=>physicalRootedCapCellTrace_mem_Icc _ _ _ _ _ _ _ (0+j))

end ShiftedNativeBandModel

namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}

abbrev shiftedNativeModel
    (a : ActualHighWallOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock) :
    ShiftedNativeBandModel where
  rmin := a.data.rmin
  u0 := a.data.s
  c := a.data.k 1
  k := a.data.k
  M := a.data.M
  hr := a.data.hr
  hu := ⟨a.data.hs.1.le,a.data.hs1⟩
  hc := a.data.hc
  hk := a.data.hk
  hkc := a.data.hkc
  hm := a.data.hm
  hM := a.data.hM
  alpha := a.alpha
  n := n
  bf := a.bf
  hf := a.hf
  hbf := a.data.bf_monotone a.alpha
  hhf := a.data.hf_monotone a.alpha

theorem shiftedNativeModel_physical_law
    (a : ActualHighWallOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) :
    rootedHierarchyPathLaw (uniformWeight (n+1)) (finiteFeature (n+1))
      (a.shiftedNativeModel.q 0) (sampleClockSteps a.shiftedNativeModel.q 0 as)=
    rootedHierarchyPathLaw (uniformWeight (n+1)) (finiteFeature (n+1))
      (completedPathClock (n+1) a.bf a.hf 0)
      (sampleClockSteps (completedPathClock (n+1) a.bf a.hf) 0 as) := rfl

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
