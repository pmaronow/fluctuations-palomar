module

public import OAI.Probability.SKBarriers.Parisi.CDFMinimizer
public import Paper.ParisiSolution
public import FRSB.CDFMeasureExt

@[expose] public section

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open OAI.SK.Analytic

namespace SKBarriers2.Bridge

def realMeasure (μ : Paper.ParisiMeasure) : ProbabilityMeasure ℝ :=
  μ.map Subtype.val

@[simp] theorem coe_realMeasure (μ : Paper.ParisiMeasure) :
    (realMeasure μ : Measure ℝ) = (μ : Measure Paper.Overlap).map Subtype.val := rfl

theorem realMeasure_mass_one (μ : Paper.ParisiMeasure) :
    (realMeasure μ : Measure ℝ) (Icc 0 1) = 1 := by
  rw [coe_realMeasure, Measure.map_apply measurable_subtype_coe measurableSet_Icc]
  have hpre : Subtype.val ⁻¹' Icc (0 : ℝ) 1 = (univ : Set Paper.Overlap) := by
    ext q
    exact iff_of_true q.property (mem_univ q)
  rw [hpre, measure_univ]

theorem cdf_realMeasure (μ : Paper.ParisiMeasure) (t : ℝ) :
    cdf (realMeasure μ : Measure ℝ) t = Paper.parisiCDF μ t :=
  (FRSB.parisiCDF_eq_realCDF μ t).symm

theorem cdf_realMeasure_eq (μ : Paper.ParisiMeasure) :
    (cdf (realMeasure μ : Measure ℝ) : ℝ → ℝ) = Paper.parisiCDF μ :=
  funext (cdf_realMeasure μ)

theorem realMeasure_injective : Function.Injective realMeasure := by
  intro μ ν h
  apply ProbabilityMeasure.toMeasure_injective
  apply (MeasurableEmbedding.subtype_coe measurableSet_Icc).map_injective
  exact congrArg (fun ρ : ProbabilityMeasure ℝ => (ρ : Measure ℝ)) h

def overlapMeasure (μ : ProbabilityMeasure ℝ)
    (hμ : (μ : Measure ℝ) (Icc 0 1) = 1) : Paper.ParisiMeasure :=
  ⟨(μ : Measure ℝ).comap Subtype.val, ⟨by
    rw [comap_subtype_coe_apply measurableSet_Icc, Subtype.coe_image_univ]
    exact hμ⟩⟩

theorem realMeasure_overlapMeasure (μ : ProbabilityMeasure ℝ)
    (hμ : (μ : Measure ℝ) (Icc 0 1) = 1) :
    realMeasure (overlapMeasure μ hμ) = μ := by
  apply ProbabilityMeasure.toMeasure_injective
  change ((μ : Measure ℝ).comap Subtype.val).map Subtype.val = (μ : Measure ℝ)
  rw [map_comap_subtype_coe measurableSet_Icc]
  apply Measure.restrict_eq_self_of_ae_mem
  exact (mem_ae_iff_prob_eq_one measurableSet_Icc).mpr hμ

theorem overlapMeasure_realMeasure (μ : Paper.ParisiMeasure) :
    overlapMeasure (realMeasure μ) (realMeasure_mass_one μ) = μ := by
  apply realMeasure_injective
  exact realMeasure_overlapMeasure (realMeasure μ) (realMeasure_mass_one μ)

theorem cdf_overlapMeasure (μ : ProbabilityMeasure ℝ)
    (hμ : (μ : Measure ℝ) (Icc 0 1) = 1) (t : ℝ) :
    Paper.parisiCDF (overlapMeasure μ hμ) t = cdf (μ : Measure ℝ) t := by
  rw [← cdf_realMeasure, realMeasure_overlapMeasure]

def measureEquiv : Paper.ParisiMeasure ≃
    {μ : ProbabilityMeasure ℝ // (μ : Measure ℝ) (Icc 0 1) = 1} where
  toFun μ := ⟨realMeasure μ, realMeasure_mass_one μ⟩
  invFun μ := overlapMeasure μ.val μ.property
  left_inv := overlapMeasure_realMeasure
  right_inv μ := Subtype.ext (realMeasure_overlapMeasure μ.val μ.property)

theorem scalarSpinTerminal_eq_log_cosh_add (x : ℝ) :
    scalarSpinTerminal x = Real.log (Real.cosh x) + Real.log 2 := by
  rw [scalarSpinTerminal, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
    (Real.cosh_pos x).ne']
  exact add_comm _ _

theorem correction_integral_eq (μ : Paper.ParisiMeasure) :
    (∫ t in Icc (0 : ℝ) 1, t * cdf (realMeasure μ : Measure ℝ) t) =
      ∫ t in (0 : ℝ)..1, t * Paper.parisiCDF μ t := by
  simp_rw [cdf_realMeasure]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Icc_eq_integral_Ioc]

theorem scalarCDFParisi_eq_of_value (β : ℝ) (μ : Paper.ParisiMeasure)
    (hvalue : scalarCDFValue β (cdf (realMeasure μ : Measure ℝ)) 0 1 0 =
      Paper.parisiPotential β μ (0, 0) + Real.log 2) :
    scalarCDFParisi β (cdf (realMeasure μ : Measure ℝ)) =
      Paper.parisiPDEFunctional β 0 μ := by
  rw [scalarCDFParisi, hvalue, correction_integral_eq]
  unfold Paper.parisiPDEFunctional Paper.parisiFunctional
  dsimp only
  rw [add_comm (Paper.parisiPotential β μ (0, 0))]

end SKBarriers2.Bridge
