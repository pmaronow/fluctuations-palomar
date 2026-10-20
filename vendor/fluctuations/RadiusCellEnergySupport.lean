module

public import PhysicalComparisonTraceMeasure

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy
open scoped Topology NNReal BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

theorem radiusCellEnergyDensity_eq_zero_outside (R : ℝ→ℝ)
    (hR : ∀u,R u∈Icc (0:ℝ) 1) (u : ℝ) (as : List PositiveMass)
    (C : ℕ→ℝ) {r : ℝ} (hr : r∉Icc (0:ℝ) 1) :
    radiusCellEnergyDensity R u as C r=0 := by
  induction as generalizing u C with
  | nil=>rfl
  | cons a as ih=>
    have hnot : r∉Ioc (R u) (R a.val) := by
      intro hh
      exact hr ⟨(hR u).1.trans hh.1.le,hh.2.trans (hR a.val).2⟩
    simp only [radiusCellEnergyDensity,indicator_of_notMem hnot,ih a.val _,zero_add]

theorem radiusCellEnergyMeasure_le_compact_volume (R : ℝ→ℝ) (hR : Monotone R)
    (hRb : ∀u,R u∈Icc (0:ℝ) 1) {u : ℝ} (as : List PositiveMass)
    (ho : MassOrdered u as) (C : ℕ→ℝ) (hC : ∀j,C j∈Icc (0:ℝ) 1) :
    radiusCellEnergyMeasure R u as C ≤ volume.restrict (Icc (0:ℝ) 1) := by
  rw [←withDensity_indicator_one measurableSet_Icc]
  unfold radiusCellEnergyMeasure
  apply withDensity_mono
  apply ae_of_all
  intro r
  by_cases hr : r∈Icc (0:ℝ) 1
  · rw [indicator_of_mem hr]
    change ENNReal.ofReal (radiusCellEnergyDensity R u as C r) ≤ 1
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal
      (radiusCellEnergyDensity_mem_Icc R hR as ho C hC r).2
  · rw [indicator_of_notMem hr]
    change ENNReal.ofReal (radiusCellEnergyDensity R u as C r) ≤ 0
    rw [radiusCellEnergyDensity_eq_zero_outside R hRb u as C hr,
      ENNReal.ofReal_zero]

section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0 < c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

theorem comparisonPhysicalRadiusDensity_eq_zero_outside (n dphys : ℕ)
    (e : Fin (dphys+1) ≃ FeatureIndex (n+1)) (d lam : ℝ) (b h : ℝ→ℝ)
    (α : inverseIntegralConstraints 0 0 k M) (as : List PositiveMass)
    (ho : MassOrdered 0 as) {r : ℝ} (hr : r∉Icc (0:ℝ) 1) :
    comparisonPhysicalRadiusDensity hc hk hkc hm hM n dphys e d lam b h α as ho r=0 :=
  radiusCellEnergyDensity_eq_zero_outside _
    (comparisonSweepQuantile_bounds hc hk hkc hm hM α) _ _ _ hr

theorem comparisonPhysicalRadiusMeasure_le_compact_volume (n dphys : ℕ)
    (e : Fin (dphys+1) ≃ FeatureIndex (n+1)) (d lam : ℝ) (b h : ℝ→ℝ)
    (α : inverseIntegralConstraints 0 0 k M) (as : List PositiveMass)
    (ho : MassOrdered 0 as) :
    comparisonPhysicalRadiusMeasure hc hk hkc hm hM n dphys e d lam b h α as ho ≤
      volume.restrict (Icc (0:ℝ) 1) := by
  apply radiusCellEnergyMeasure_le_compact_volume _
    (comparisonSweepQuantile_monotone hc hk hkc hm hM α)
    (comparisonSweepQuantile_bounds hc hk hkc hm hM α) as ho
  intro j
  exact physicalRootedCapCellTrace_mem_Icc _ _ _ _ _ _ _ _

instance comparisonPhysicalRadiusMeasure_isFinite (n dphys : ℕ)
    (e : Fin (dphys+1) ≃ FeatureIndex (n+1)) (d lam : ℝ) (b h : ℝ→ℝ)
    (α : inverseIntegralConstraints 0 0 k M) (as : List PositiveMass)
    (ho : MassOrdered 0 as) :
    IsFiniteMeasure (comparisonPhysicalRadiusMeasure hc hk hkc hm hM n dphys e d lam b h α as ho) :=
  isFiniteMeasure_of_le (volume.restrict (Icc (0:ℝ) 1))
    (comparisonPhysicalRadiusMeasure_le_compact_volume hc hk hkc hm hM n dphys e d lam b h α as ho)

end
end OAI.SKFluctuations.LaplaceWindowFormalization
