module

public import ComparisonNativeActualOriginalMassMismatch
public import ComparisonNormalizedClockCoupling

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 6000000
attribute [local instance] Measure.Subtype.measureSpace

namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable {M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}

def Potential.originalOrderFloor (p : M.Potential) : Set ParisiFinite.OrderPoint :=
  {w | 0 < p.H (M.R w)}

theorem Potential.originalOrderFloor_eq_preimage (p : M.Potential) :
    p.originalOrderFloor=(fun w : ParisiFinite.OrderPoint=>M.R w) ⁻¹' p.positiveRadiusSet := by
  ext w
  have hr:=comparisonSweepQuantile_bounds M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha (w:ℝ)
  exact ⟨fun hw=>⟨hr,hw⟩,fun hw=>hw.2⟩

theorem Potential.originalOrderFloor_measurable (p : M.Potential) :
    MeasurableSet p.originalOrderFloor := by
  rw [p.originalOrderFloor_eq_preimage]
  exact p.positiveRadiusSet_measurable.preimage
    ((comparisonSweepQuantile_continuous M.context.hc M.context.hk M.context.hkc
      M.context.hm M.context.hM M.alpha).measurable.comp measurable_subtype_coe)

theorem Potential.originalOrderFloor_indicator (p : M.Potential) (w : ParisiFinite.OrderPoint) :
    p.originalOrderFloor.indicator (fun _=>(1:ℝ)) w=p.positiveMassMask w := by
  rw [p.originalOrderFloor_eq_preimage]
  rfl

theorem Potential.originalOrderFloor_mass_le (p : M.Potential) (v : ℝ) :
    ((uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict {w | (w:ℝ) ≤ v}).real
      p.originalOrderFloor ≤ M.context.N^(-delta)*M.context.U := by
  have hglobal : (uniformOrderMass : Measure ParisiFinite.OrderPoint).real
      p.originalOrderFloor ≤ M.context.N^(-delta)*M.context.U := by
    rw [←integral_indicator_one p.originalOrderFloor_measurable]
    simp_rw [show (1 : ParisiFinite.OrderPoint→ℝ)=(fun _=>(1:ℝ)) from rfl,
      p.originalOrderFloor_indicator]
    change (∫w : unitInterval,p.positiveMassMask (w:ℝ)∂volume) ≤ _
    rw [unitInterval.measurePreserving_coe.integral_comp unitInterval.measurableEmbedding_coe]
    exact p.positiveMassMask_mass_le
  rw [measureReal_restrict_apply' (measurableSet_le measurable_subtype_coe measurable_const)]
  exact (measureReal_mono inter_subset_left).trans hglobal

theorem Potential.originalOrderFloor_normalized_mass_le
    (p : M.Potential) (v : ℝ) {x : ℝ} (hx : 0 < x) :
    (comparisonNormalizedClockMass x v).real p.originalOrderFloor ≤
      (M.context.N^(-delta)*M.context.U)/x := by
  unfold comparisonNormalizedClockMass
  rw [measureReal_ennreal_smul_apply,ENNReal.toReal_ofReal (one_div_nonneg.mpr hx.le)]
  have H:=div_le_div_of_nonneg_right (p.originalOrderFloor_mass_le v) hx.le
  convert H using 1; ring

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
