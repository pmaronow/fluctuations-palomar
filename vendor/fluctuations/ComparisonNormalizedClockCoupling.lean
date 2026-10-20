module

public import ComparisonLocalClockCDF
public import ActualMixedClockCDF

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy ProbabilityTheory
open scoped Topology ENNReal
set_option maxHeartbeats 2200000

def comparisonNormalizedClockMass (x v : ℝ) : Measure ParisiFinite.OrderPoint :=
  ENNReal.ofReal (1/x) • (uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict
    {w | (w:ℝ)≤v}

instance comparisonNormalizedClockMass_finite (x v : ℝ) :
    IsFiniteMeasure (comparisonNormalizedClockMass x v) := by
  constructor
  simp only [comparisonNormalizedClockMass,Measure.smul_apply,smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

theorem comparison_normalized_clock_cdf_exact (q : ℝ→ℝ)
    (hq : MonotoneOn q (Icc (0:ℝ) 1))
    (hqb : ∀u∈Icc (0:ℝ) 1,q u∈Icc (0:ℝ) 1)
    {x v R t : ℝ} (hx : 0<x) (hv : v∈Icc (0:ℝ) 1)
    (ht : t≤R) (hcut : x*R<q v) :
    comparisonClockCDF (comparisonNormalizedClockMass x v) (fun w=>q (w:ℝ)/x) t=
      (quantileMassProfile q hqb).val (x*t)/x := by
  have hset : {w : ParisiFinite.OrderPoint | q (w:ℝ)/x≤t}∩{w : ParisiFinite.OrderPoint | (w:ℝ)≤v}=
      {w : ParisiFinite.OrderPoint | q (w:ℝ)≤x*t} := by
    ext w
    constructor
    · intro hw
      change q (w:ℝ)≤x*t
      have hh := (div_le_iff₀ hx).mp hw.1
      simpa only [mul_comm] using hh
    · intro hw
      have hvw : (w:ℝ)≤v := by
        by_contra hh
        have hm := hq hv w.property (le_of_not_ge hh)
        have htr := mul_le_mul_of_nonneg_left ht hx.le
        change q (w:ℝ)≤x*t at hw
        linarith
      change q (w:ℝ)≤x*t at hw
      exact ⟨(div_le_iff₀ hx).mpr (by simpa only [mul_comm] using hw),hvw⟩
  unfold comparisonClockCDF comparisonNormalizedClockMass
  rw [measureReal_ennreal_smul_apply,ENNReal.toReal_ofReal (one_div_nonneg.mpr hx.le),
    measureReal_restrict_apply' (measurableSet_le measurable_subtype_coe measurable_const),hset,
    quantileMassProfile_cdf q hq hqb]
  ring

theorem comparison_normalized_clock_error_exact (q r : ℝ→ℝ)
    {x v : ℝ} (hx : 0<x) :
    (∫w : ParisiFinite.OrderPoint,|q (w:ℝ)/x-r (w:ℝ)/x|∂comparisonNormalizedClockMass x v)=
      (∫w : ParisiFinite.OrderPoint in {w | (w:ℝ)≤v},|q (w:ℝ)-r (w:ℝ)|
        ∂(uniformOrderMass : Measure ParisiFinite.OrderPoint))/x^2 := by
  unfold comparisonNormalizedClockMass
  rw [integral_smul_measure,ENNReal.toReal_ofReal (one_div_nonneg.mpr hx.le)]
  simp_rw [←sub_div,abs_div,abs_of_pos hx]
  rw [integral_div]
  simp only [smul_eq_mul]
  ring

theorem comparison_normalized_clock_pair_cdf_exact (q r : ℝ→ℝ)
    (hq : MonotoneOn q (Icc (0:ℝ) 1)) (hr : MonotoneOn r (Icc (0:ℝ) 1))
    (hqb : ∀u∈Icc (0:ℝ) 1,q u∈Icc (0:ℝ) 1)
    (hrb : ∀u∈Icc (0:ℝ) 1,r u∈Icc (0:ℝ) 1)
    {x v R : ℝ} (hx : 0<x) (hv : v∈Icc (0:ℝ) 1)
    (hqcut : x*R<q v) (hrcut : x*R<r v) :
    ∀t≤R,
      comparisonClockCDF (comparisonNormalizedClockMass x v) (fun w=>q (w:ℝ)/x) t=
        (quantileMassProfile q hqb).val (x*t)/x ∧
      comparisonClockCDF (comparisonNormalizedClockMass x v) (fun w=>r (w:ℝ)/x) t=
        (quantileMassProfile r hrb).val (x*t)/x := by
  intro t ht
  exact ⟨comparison_normalized_clock_cdf_exact q hq hqb hx hv ht hqcut,
    comparison_normalized_clock_cdf_exact r hr hrb hx hv ht hrcut⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
