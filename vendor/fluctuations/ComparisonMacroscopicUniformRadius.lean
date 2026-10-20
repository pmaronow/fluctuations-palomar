module

public import ComparisonMacroscopicUniformDensity
public import ActualMixedClockCDF
public import JointScalarNearMinimum

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy Function
open scoped Topology NNReal

theorem scalar_reference_quantiles_uniform_global_band
    {β : ℝ≥0} (hβ : 0 < β) (hT : 1 < (β:ℝ)^2) :
    ∃c C : ℝ,0 < c ∧ 0 < C ∧ ∀r : ℝ→ℝ,
      MonotoneOn r (Icc (0:ℝ) 1) →
      ∀hrb : ∀u∈Icc (0:ℝ) 1,r u∈Icc (0:ℝ) 1,
      quantileMassProfile r hrb ∈ scalarReferenceMinimizers β hβ →
      ∀u∈Ioo (0:ℝ) 1,c*u ≤ r u ∧ r u ≤ C*u := by
  obtain ⟨c,C,hc,hC,hband⟩ := macro_scalar_minimizers_uniform_quantile hβ hT
  refine ⟨c,C,hc,hC,?_⟩
  intro r hr hrb hmin u hu
  let alpha := quantileMassProfile r hrb
  have hprofile : alpha∈scalarProfiles := hmin.1
  have hrc : ∀x,ContinuousWithinAt alpha.val (Ici x) x := quantileMassProfile_right_continuous r hrb
  have hb := hband alpha hprofile (scalarReferenceMinimizers_isMinimizer hmin) hrc
  have hule : scalarQuantile alpha u ≤ r u := by
    apply (scalarQuantile_le_iff hprofile ⟨hu.1,hu.2.le⟩).mpr
    rw [profileStieltjes_eq_of_rightContinuous alpha hrc]
    exact quantile_cdf_lower_of_value_le r hr hrb ⟨hu.1.le,hu.2.le⟩ le_rfl
  have huupper {v : ℝ} (hv : v∈Ioo (0:ℝ) 1) (huv : u < v) :
      r u ≤ scalarQuantile alpha v := by
    by_contra h
    have hcdf := quantileMassProfile_le_of_larger_clock r hr hrb
      ⟨hu.1.le,hu.2.le⟩ (lt_of_not_ge h)
    have hge := scalarQuantile_cdf_ge hprofile ⟨hv.1,hv.2.le⟩
    rw [profileStieltjes_eq_of_rightContinuous alpha hrc] at hge
    exact (not_le_of_gt huv) (hge.trans hcdf)
  refine ⟨(hb u hu).1.trans hule,?_⟩
  apply le_of_forall_pos_le_add
  intro epsilon hepsilon
  let t := min (epsilon/C) ((1-u)/2)
  have ht : 0 < t := lt_min (div_pos hepsilon hC) (by linarith [hu.2])
  have htu : u+t < 1 := by
    have h := min_le_right (epsilon/C) ((1-u)/2)
    dsimp only [t] at *
    linarith [hu.2]
  have htC : C*t ≤ epsilon := by
    have h := (le_div_iff₀ hC).mp (min_le_left (epsilon/C) ((1-u)/2))
    simpa only [mul_comm,t] using h
  have hv : u+t∈Ioo (0:ℝ) 1 := ⟨by linarith [hu.1],htu⟩
  have hru := huupper hv (by linarith : u < u+t)
  have hq := (hb (u+t) hv).2
  nlinarith

end OAI.SKFluctuations.LaplaceWindowFormalization
