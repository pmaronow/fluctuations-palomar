module

public import ComparisonNormalizedClockCoupling

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy ProbabilityTheory
open scoped Topology ENNReal
set_option maxHeartbeats 2600000

theorem comparison_normalized_local_temperature_clock_cdf_exact (q : ℝ→ℝ)
    (hq : MonotoneOn q (Icc (0:ℝ) 1))
    (hqb : ∀u∈Icc (0:ℝ) 1,q u∈Icc (0:ℝ) 1)
    {gamma x v R t : ℝ} (hgamma : 0<gamma) (hx : 0<x)
    (hv : v∈Icc (0:ℝ) 1) (ht : t≤R) (hcut : gamma*(x*R)<q v) :
    comparisonClockCDF (comparisonNormalizedClockMass x v)
      (fun w=>q (w:ℝ)/(gamma*x)) t=
        (quantileMassProfile q hqb).val (gamma*(x*t))/x := by
  have hden : 0<gamma*x := mul_pos hgamma hx
  have hset : {w : ParisiFinite.OrderPoint | q (w:ℝ)/(gamma*x)≤t}∩
      {w : ParisiFinite.OrderPoint | (w:ℝ)≤v}=
        {w : ParisiFinite.OrderPoint | q (w:ℝ)≤gamma*(x*t)} := by
    ext w
    constructor
    · intro hw
      change q (w:ℝ)≤gamma*(x*t)
      have hh := (div_le_iff₀ hden).mp hw.1
      nlinarith only [hh]
    · intro hw
      have hvw : (w:ℝ)≤v := by
        by_contra hh
        have hm := hq hv w.property (le_of_not_ge hh)
        have htr := mul_le_mul_of_nonneg_left ht hden.le
        change q (w:ℝ)≤gamma*(x*t) at hw
        nlinarith only [hm,htr,hw,hcut]
      change q (w:ℝ)≤gamma*(x*t) at hw
      exact ⟨(div_le_iff₀ hden).mpr (by nlinarith only [hw]),hvw⟩
  unfold comparisonClockCDF comparisonNormalizedClockMass
  rw [measureReal_ennreal_smul_apply,ENNReal.toReal_ofReal (one_div_nonneg.mpr hx.le),
    measureReal_restrict_apply' (measurableSet_le measurable_subtype_coe measurable_const),hset,
    quantileMassProfile_cdf q hq hqb]
  ring

theorem comparison_normalized_local_temperature_clock_error_integrable (q r : ℝ→ℝ)
    (hq : MonotoneOn q (Icc (0:ℝ) 1)) (hr : MonotoneOn r (Icc (0:ℝ) 1))
    (hqb : ∀u∈Icc (0:ℝ) 1,q u∈Icc (0:ℝ) 1)
    (hrb : ∀u∈Icc (0:ℝ) 1,r u∈Icc (0:ℝ) 1)
    {gamma x v : ℝ} (hgamma : 0<gamma) (hx : 0<x) :
    Integrable (fun w : ParisiFinite.OrderPoint=>|q (w:ℝ)/(gamma*x)-r (w:ℝ)/x|)
      (comparisonNormalizedClockMass x v) := by
  have hqm : Monotone (fun w : ParisiFinite.OrderPoint=>q (w:ℝ)) :=
    fun a b hab=>hq a.property b.property hab
  have hrm : Monotone (fun w : ParisiFinite.OrderPoint=>r (w:ℝ)) :=
    fun a b hab=>hr a.property b.property hab
  have hm : AEStronglyMeasurable
      (fun w : ParisiFinite.OrderPoint=>|q (w:ℝ)/(gamma*x)-r (w:ℝ)/x|)
      (comparisonNormalizedClockMass x v) :=
    ((hqm.measurable.div_const (gamma*x)).sub (hrm.measurable.div_const x)).abs.aestronglyMeasurable
  apply (integrable_const ((1/gamma+1)/x)).mono' hm
  apply Eventually.of_forall
  intro w
  rw [Real.norm_eq_abs,abs_abs]
  calc
    |q (w:ℝ)/(gamma*x)-r (w:ℝ)/x| ≤
        |q (w:ℝ)/(gamma*x)|+|r (w:ℝ)/x| := abs_sub _ _
    _ ≤ 1/(gamma*x)+1/x := by
      apply add_le_add
      · rw [abs_div,abs_of_nonneg (hqb w w.property).1,abs_of_pos (mul_pos hgamma hx)]
        exact div_le_div_of_nonneg_right (hqb w w.property).2 (mul_pos hgamma hx).le
      · rw [abs_div,abs_of_nonneg (hrb w w.property).1,abs_of_pos hx]
        exact div_le_div_of_nonneg_right (hrb w w.property).2 hx.le
    _ = (1/gamma+1)/x := by ring

end OAI.SKFluctuations.LaplaceWindowFormalization
