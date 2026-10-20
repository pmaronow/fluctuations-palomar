module

public import SKConstants.ScalarForwardPicardPaths
public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants
set_option backward.isDefEq.respectTransparency false

theorem scalarStieltjes_noAtoms (f : StieltjesFunction ℝ) (hf : Continuous f) :
    NullSingletonClass f.measure := by
  constructor
  intro x
  rw [f.measure_singleton, hf.continuousAt.continuousWithinAt.leftLim_eq]
  simp

def scalarStieltjesWeightedPath (f : StieltjesFunction ℝ) (hf : Continuous f)
    (T : ℝ≥0) (B : ScalarContinuousPath T) : ScalarContinuousPath T where
  toFun t := f t * B t -
    ∫ s in (0 : ℝ)..(t : ℝ), IccExtend T.coe_nonneg B s ∂f.measure
  continuous_toFun := by
    let : NullSingletonClass f.measure := scalarStieltjes_noAtoms f hf
    have hB : Continuous (IccExtend T.coe_nonneg B) := B.continuous.Icc_extend'
    have hInt : ∀ a b : ℝ, IntervalIntegrable (IccExtend T.coe_nonneg B) f.measure a b :=
      fun a b => (hB.continuousOn.integrableOn_compact isCompact_uIcc).intervalIntegrable
    exact ((hf.comp continuous_subtype_val).mul B.continuous).sub
      ((intervalIntegral.continuous_primitive hInt 0).comp continuous_subtype_val)

theorem measurable_scalarStieltjesWeightedPath (f : StieltjesFunction ℝ)
    (hf : Continuous f) (T : ℝ≥0) : Measurable (scalarStieltjesWeightedPath f hf T) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  have hc : Continuous (fun p : ScalarContinuousPath T × ℝ =>
      IccExtend T.coe_nonneg p.1 p.2) :=
    continuous_eval.comp (continuous_fst.prodMk
      ((continuous_projIcc (h := T.coe_nonneg)).comp continuous_snd))
  have hi := hc.measurable.stronglyMeasurable.integral_prod_right'
    (ν := f.measure.restrict (Ioc (0 : ℝ) (t : ℝ)))
  have he : (fun B : ScalarContinuousPath T => scalarStieltjesWeightedPath f hf T B t) =
      fun B : ScalarContinuousPath T => f t * B t - ∫ s in Ioc (0 : ℝ) (t : ℝ),
        IccExtend T.coe_nonneg B s ∂f.measure := by
    funext B
    exact congrArg (fun q => f t * B t - q)
      (intervalIntegral.integral_of_le t.property.1)
  rw [he]
  exact ((ContinuousMap.measurable_eval t).const_mul _).sub hi.measurable

theorem scalarStieltjesWeightedPath_congr_prefix (f : StieltjesFunction ℝ)
    (hf : Continuous f) (T : ℝ≥0) (B C : ScalarContinuousPath T) (a : ℝ≥0)
    (hBC : ∀ t : Icc (0 : ℝ) (T : ℝ), (t : ℝ) ≤ a → B t = C t)
    (t : Icc (0 : ℝ) (T : ℝ)) (ht : (t : ℝ) ≤ a) :
    scalarStieltjesWeightedPath f hf T B t = scalarStieltjesWeightedPath f hf T C t := by
  change f t * B t - _ = f t * C t - _
  rw [hBC t ht]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  have hs0 : 0 ≤ s := by simpa only [min_eq_left t.property.1] using hs.1
  have hst : s ≤ t := by simpa only [max_eq_right t.property.1] using hs.2
  change B (projIcc 0 (T : ℝ) T.coe_nonneg s) = C (projIcc 0 (T : ℝ) T.coe_nonneg s)
  rw [projIcc_of_mem _ ⟨hs0,hst.trans t.property.2⟩]
  exact hBC ⟨s,hs0,hst.trans t.property.2⟩ (hst.trans ht)

def scalarTwoDriverWeightedPath (f g : StieltjesFunction ℝ)
    (hf : Continuous f) (hg : Continuous g) (T : ℝ≥0)
    (p : ScalarContinuousPath T × ScalarContinuousPath T) : ScalarContinuousPath T :=
  -scalarStieltjesWeightedPath f hf T p.1 + scalarStieltjesWeightedPath g hg T p.2

theorem measurable_scalarTwoDriverWeightedPath (f g : StieltjesFunction ℝ)
    (hf : Continuous f) (hg : Continuous g) (T : ℝ≥0) :
    Measurable (scalarTwoDriverWeightedPath f g hf hg T) :=
  ((measurable_scalarStieltjesWeightedPath f hf T).comp measurable_fst).neg.add
    ((measurable_scalarStieltjesWeightedPath g hg T).comp measurable_snd)

theorem scalarTwoDriverWeightedPath_congr_prefix (f g : StieltjesFunction ℝ)
    (hf : Continuous f) (hg : Continuous g) (T : ℝ≥0)
    (B C D E : ScalarContinuousPath T) (a : ℝ≥0)
    (hBC : ∀ t : Icc (0 : ℝ) (T : ℝ), (t : ℝ) ≤ a → B t = C t)
    (hDE : ∀ t : Icc (0 : ℝ) (T : ℝ), (t : ℝ) ≤ a → D t = E t)
    (t : Icc (0 : ℝ) (T : ℝ)) (ht : (t : ℝ) ≤ a) :
    scalarTwoDriverWeightedPath f g hf hg T (B,D) t =
      scalarTwoDriverWeightedPath f g hf hg T (C,E) t := by
  change -scalarStieltjesWeightedPath f hf T B t +
    scalarStieltjesWeightedPath g hg T D t =
    -scalarStieltjesWeightedPath f hf T C t + scalarStieltjesWeightedPath g hg T E t
  rw [scalarStieltjesWeightedPath_congr_prefix f hf T B C a hBC t ht,
    scalarStieltjesWeightedPath_congr_prefix g hg T D E a hDE t ht]

def scalarTwoDriverPicardPath (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g) (T : ℝ≥0)
    (p : ℝ × (ScalarContinuousPath T × ScalarContinuousPath T)) : ScalarContinuousPath T :=
  scalarForwardPicardPath b T (p.1,scalarTwoDriverWeightedPath f g hf hg T p.2)

theorem measurable_scalarTwoDriverPicardPath (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g) (T : ℝ≥0) :
    Measurable (scalarTwoDriverPicardPath b f g hf hg T) :=
  (measurable_scalarForwardPicardPath b T).comp
    (measurable_fst.prodMk ((measurable_scalarTwoDriverWeightedPath f g hf hg T).comp measurable_snd))

theorem scalarTwoDriverPicardPath_congr_prefix (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g) (T : ℝ≥0)
    (z : ℝ) (B C D E : ScalarContinuousPath T) (a : ℝ≥0) (ha : a ≤ T)
    (hBC : ∀ t : Icc (0 : ℝ) (T : ℝ), (t : ℝ) ≤ a → B t = C t)
    (hDE : ∀ t : Icc (0 : ℝ) (T : ℝ), (t : ℝ) ≤ a → D t = E t)
    (t : Icc (0 : ℝ) (T : ℝ)) (ht : (t : ℝ) ≤ a) :
    scalarTwoDriverPicardPath b f g hf hg T (z,(B,D)) t =
      scalarTwoDriverPicardPath b f g hf hg T (z,(C,E)) t := by
  apply scalarForwardPicardPath_congr_prefix b T z _ _ a ha _ t ht
  intro s hs
  exact scalarTwoDriverWeightedPath_congr_prefix f g hf hg T B C D E a hBC hDE s hs

end SKConstants
