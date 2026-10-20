module

public import SKConstants.ParisiCDFCoordinateExpectation
public import SKConstants.ParisiCDFRestartMGF
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology ContDiff
namespace SKConstants.ParisiFullSupport
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.ZeroTemperatureSK.WeakIto SKConstantsOAI.SK.Analytic
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type*} [MeasurableSpace Ω]
variable (W : BrownianSystem Ω) (β : ℝ) (α : StieltjesFunction ℝ)
  (ha : ∀ z, α z∈Icc (0:ℝ) 1) (h1 : α 1=1) (hβ : β≠0)
  {T : ℝ} (hT0 : 0≤T) (hT1 : T<1)

def physicalCDFRestartCoordinateCutoffField (a x0 : ℝ) (ha0 : 0 ≤ a) (n : ℕ) :=
  translatedTimeField (physicalCDFCoordinateCutoffField β α ha h1 hβ hT0 hT1 n) a x0 ha0

lemma physicalCDFRestartCoordinateCutoffField_f (a x0 : ℝ) (ha0 : 0 ≤ a) (n : ℕ) (v x : ℝ) :
    (physicalCDFRestartCoordinateCutoffField β α ha h1 hβ hT0 hT1 a x0 ha0 n).f v x =
    scalarSmoothCutoff n (x0+x)*compactCDFJet β α T 0 ((a+v)/β^2) (x0+x) := by
  unfold physicalCDFRestartCoordinateCutoffField translatedTimeField
  exact physicalCDFCoordinateCutoffField_f β α ha h1 hβ hT0 hT1 n (a+v) (x0+x)

lemma physicalCDFRestartCoordinateCutoff_expected_right_derivative
    (a x0 : ℝ) (ha0 : 0 ≤ a) (n : ℕ) (v : ℝ≥0) (hv : (a+(v:ℝ))/β^2<T) :
    HasDerivWithinAt
      ((physicalCDFRestartCoordinateCutoffField β α ha h1 hβ hT0 hT1 a x0 ha0 n).expected
        (SKConstants.BoundedLipschitzDrift.translated (finiteTemperatureCDFDrift β α ha h1) a x0) W)
      (∫ w, physicalCDFCoordinateCutoffRate β α T n (a+v)
        (x0+(SKConstants.BoundedLipschitzDrift.translated
          (finiteTemperatureCDFDrift β α ha h1) a x0).solution W.driver v w) ∂W.law) (Ioi (v:ℝ)) v := by
  have hvT : (v:ℝ)<T/(1/β^2)-a := by
    rw [div_div_eq_mul_div,div_one]
    have H := (div_lt_iff₀ (sq_pos_of_ne_zero hβ)).mp hv
    linarith
  have H := (physicalCDFRestartCoordinateCutoffField β α ha h1 hβ hT0 hT1 a x0 ha0 n).expected_hasDerivWithinAt_right
    (SKConstants.BoundedLipschitzDrift.translated (finiteTemperatureCDFDrift β α ha h1) a x0) W v hvT
    ((translatedCDFDrift_path_right_continuous W β α ha h1 a x0).mono (fun w hw => hw v))
  convert H using 1
  apply integral_congr_ae
  apply ae_of_all
  intro w
  change physicalCDFCoordinateCutoffRate β α T n (a+v) _ =
    (translatedTimeField (physicalCDFCoordinateCutoffField β α ha h1 hβ hT0 hT1 n) a x0 ha0).generator
      (fun r y => (finiteTemperatureCDFDrift β α ha h1).f (a+r) (x0+y)) v _
  rw [translatedTimeField_generator]
  unfold TimeField.generator
  rw [finiteTemperatureCDFDrift_eq_compact β α ha h1 hβ hT1.le
    ⟨div_nonneg (add_nonneg ha0 v.coe_nonneg) (sq_nonneg β),hv.le⟩]
  exact (physicalCDFCoordinateCutoff_generator β α ha h1 hβ hT0 hT1 n (a+v) _).symm

lemma physicalCDFRestartCoordinateCutoff_expected_zero
    (a x0 : ℝ) (ha0 : 0 ≤ a) (n : ℕ) :
    (physicalCDFRestartCoordinateCutoffField β α ha h1 hβ hT0 hT1 a x0 ha0 n).expected
      (SKConstants.BoundedLipschitzDrift.translated (finiteTemperatureCDFDrift β α ha h1) a x0) W 0 =
    scalarSmoothCutoff n x0*compactCDFJet β α T 0 (a/β^2) x0 := by
  let := W.isProbability
  unfold TimeField.expected
  simp only [Real.toNNReal_zero,BoundedLipschitzDrift.solution_zero,
    physicalCDFRestartCoordinateCutoffField_f,add_zero,integral_const,probReal_univ,one_smul]

lemma physicalCDFRestartCoordinateCutoff_expectation_integral
    (a x0 : ℝ) (ha0 : 0 ≤ a) (n : ℕ) (V : ℝ) (hV0 : 0 ≤ V) (hVT : (a+V)/β^2<T) :
    (physicalCDFRestartCoordinateCutoffField β α ha h1 hβ hT0 hT1 a x0 ha0 n).expected
      (SKConstants.BoundedLipschitzDrift.translated (finiteTemperatureCDFDrift β α ha h1) a x0) W V -
      scalarSmoothCutoff n x0*compactCDFJet β α T 0 (a/β^2) x0 =
    ∫ v in 0..V, ∫ w, physicalCDFCoordinateCutoffRate β α T n (a+v)
      (x0+(SKConstants.BoundedLipschitzDrift.translated
        (finiteTemperatureCDFDrift β α ha h1) a x0).solution W.driver (Real.toNNReal v) w) ∂W.law := by
  have hFam := boundedSmoothFamily_translate
    (physicalCDFCoordinateCutoffRate_family β α ha h1 hβ hT0 hT1 n) a x0
  have H := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hV0
    ((physicalCDFRestartCoordinateCutoffField β α ha h1 hβ hT0 hT1 a x0 ha0 n).expected_continuous
      (SKConstants.BoundedLipschitzDrift.translated (finiteTemperatureCDFDrift β α ha h1) a x0) W).continuousOn
    (fun v hv => ?_)
    (bounded_family_expected_intervalIntegrable W
      (SKConstants.BoundedLipschitzDrift.translated (finiteTemperatureCDFDrift β α ha h1) a x0) hFam 0 V)
  · simpa only [physicalCDFRestartCoordinateCutoff_expected_zero W β α ha h1 hβ hT0 hT1 a x0 ha0 n] using H.symm
  · have hv0 : 0 ≤ v := hv.1.le
    have hvT : (a+v)/β^2<T := (div_le_div_of_nonneg_right
      (add_le_add_right hv.2.le a) (sq_nonneg β)).trans_lt hVT
    have HD := physicalCDFRestartCoordinateCutoff_expected_right_derivative W β α ha h1 hβ hT0 hT1
      a x0 ha0 n (Real.toNNReal v) (by simpa only [Real.coe_toNNReal v hv0] using hvT)
    simpa only [Real.coe_toNNReal v hv0] using HD

def physicalCDFRestartCoordinateExpected (a x0 V : ℝ) : ℝ :=
  ∫ w, (x0+(SKConstants.BoundedLipschitzDrift.translated
    (finiteTemperatureCDFDrift β α ha h1) a x0).solution W.driver (Real.toNNReal V) w)*
      compactCDFJet β α T 0 ((a+V)/β^2)
        (x0+(SKConstants.BoundedLipschitzDrift.translated
          (finiteTemperatureCDFDrift β α ha h1) a x0).solution W.driver (Real.toNNReal V) w) ∂W.law

lemma physicalCDFRestartCoordinateCutoff_expected_tendsto
    (a x0 : ℝ) (ha0 : 0 ≤ a) (V : ℝ) :
    Tendsto (fun n => (physicalCDFRestartCoordinateCutoffField β α ha h1 hβ hT0 hT1 a x0 ha0 n).expected
      (SKConstants.BoundedLipschitzDrift.translated (finiteTemperatureCDFDrift β α ha h1) a x0) W V) atTop
      (𝓝 (physicalCDFRestartCoordinateExpected W β α ha h1 (T:=T) a x0 V)) := by
  let := W.isProbability
  let b := SKConstants.BoundedLipschitzDrift.translated (finiteTemperatureCDFDrift β α ha h1) a x0
  obtain ⟨C,hC⟩ := (compactCDFGradient_family β α ha h1 hβ hT0 hT1).bound
  have hm (n : ℕ) := (integrable_family_comp (P:=W.law)
    (physicalCDFRestartCoordinateCutoffField β α ha h1 hβ hT0 hT1 a x0 ha0 n).smooth V
    (b.solution_measurable W (Real.toNNReal V))).aestronglyMeasurable
  unfold TimeField.expected physicalCDFRestartCoordinateExpected
  apply tendsto_integral_of_dominated_convergence
    (fun w => |x0+b.solution W.driver (Real.toNNReal V) w| * (C:ℝ)) hm
    (((integrable_const x0).add (b.solution_integrable W (Real.toNNReal V))).abs.mul_const _) _ _
  · intro n
    exact Eventually.of_forall (fun w => by
      rw [physicalCDFRestartCoordinateCutoffField_f]
      simp only [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul (scalarSmoothCutoff_abs_le n _)
        (by simpa only [compactCDFJet,iteratedDeriv_zero] using hC ((a+V)/β^2) _)
        (abs_nonneg _) (abs_nonneg _))
  · exact Eventually.of_forall (fun w =>
      (by simpa only [physicalCDFRestartCoordinateCutoffField_f] using
        (scalarSmoothCutoff_tendsto (x0+b.solution W.driver (Real.toNNReal V) w)).mul_const (compactCDFJet β α T 0 ((a+V)/β^2) (x0+b.solution W.driver (Real.toNNReal V) w))))

include hβ hT0 hT1 in
lemma physicalCDFRestartCoordinateCutoffRate_expected_tendsto
    (a x0 v : ℝ) :
    Tendsto (fun n => ∫ w, physicalCDFCoordinateCutoffRate β α T n (a+v)
      (x0+(SKConstants.BoundedLipschitzDrift.translated
        (finiteTemperatureCDFDrift β α ha h1) a x0).solution W.driver (Real.toNNReal v) w) ∂W.law) atTop
      (𝓝 (∫ w, physicalCDFCoordinateRate β α T (a+v)
        (x0+(SKConstants.BoundedLipschitzDrift.translated
          (finiteTemperatureCDFDrift β α ha h1) a x0).solution W.driver (Real.toNNReal v) w) ∂W.law)) := by
  let := W.isProbability
  obtain ⟨C,hC⟩ := physicalCDFCoordinateCutoffRate_uniform_bound β α ha h1 hβ hT0 hT1
  apply tendsto_integral_of_dominated_convergence (fun _ : Ω => (C:ℝ))
    (fun n => (integrable_family_comp (P:=W.law)
      (boundedSmoothFamily_translate (physicalCDFCoordinateCutoffRate_family β α ha h1 hβ hT0 hT1 n) a x0) v
      ((SKConstants.BoundedLipschitzDrift.translated
        (finiteTemperatureCDFDrift β α ha h1) a x0).solution_measurable W (Real.toNNReal v))).aestronglyMeasurable)
    (integrable_const _) _ _
  · intro n
    exact Eventually.of_forall (fun w => by simpa only [Real.norm_eq_abs] using hC n (a+v) _)
  · exact Eventually.of_forall (fun w => physicalCDFCoordinateCutoffRate_tendsto β α (a+v) _)

include hβ hT0 hT1 in
lemma physicalCDFRestartCoordinateCutoff_integral_tendsto
    (a x0 V : ℝ) (hV0 : 0 ≤ V) :
    Tendsto (fun n => ∫ v in 0..V, ∫ w, physicalCDFCoordinateCutoffRate β α T n (a+v)
      (x0+(SKConstants.BoundedLipschitzDrift.translated
        (finiteTemperatureCDFDrift β α ha h1) a x0).solution W.driver (Real.toNNReal v) w) ∂W.law) atTop
      (𝓝 (∫ v in 0..V, ∫ w, physicalCDFCoordinateRate β α T (a+v)
        (x0+(SKConstants.BoundedLipschitzDrift.translated
          (finiteTemperatureCDFDrift β α ha h1) a x0).solution W.driver (Real.toNNReal v) w) ∂W.law)) := by
  let := W.isProbability
  obtain ⟨C,hC⟩ := physicalCDFCoordinateCutoffRate_uniform_bound β α ha h1 hβ hT0 hT1
  simp only [intervalIntegral.integral_of_le hV0]
  apply tendsto_integral_of_dominated_convergence (fun _ : ℝ => (C:ℝ))
    (fun n => (bounded_family_expected_stronglyMeasurable W
      (SKConstants.BoundedLipschitzDrift.translated (finiteTemperatureCDFDrift β α ha h1) a x0)
      (boundedSmoothFamily_translate (physicalCDFCoordinateCutoffRate_family β α ha h1 hβ hT0 hT1 n) a x0)).aestronglyMeasurable.mono_measure
        Measure.restrict_le_self) (integrable_const _) _ _
  · intro n
    exact Eventually.of_forall (fun v => by
      have H := norm_integral_le_of_norm_le_const (μ:=W.law) (C:=(C:ℝ))
        (f:=fun w => physicalCDFCoordinateCutoffRate β α T n (a+v)
          (x0+(SKConstants.BoundedLipschitzDrift.translated
            (finiteTemperatureCDFDrift β α ha h1) a x0).solution W.driver (Real.toNNReal v) w))
        (Eventually.of_forall (fun w => by simpa only [Real.norm_eq_abs] using hC n (a+v) _))
      simpa only [probReal_univ,mul_one] using H)
  · exact Eventually.of_forall (fun v => physicalCDFRestartCoordinateCutoffRate_expected_tendsto
      W β α ha h1 hβ hT0 hT1 a x0 v)

include hβ hT0 hT1 in
theorem physicalCDFRestartCoordinateExpected_integral
    (a x0 : ℝ) (ha0 : 0 ≤ a) (V : ℝ) (hV0 : 0 ≤ V) (hVT : (a+V)/β^2<T) :
    physicalCDFRestartCoordinateExpected W β α ha h1 (T:=T) a x0 V -
      x0*compactCDFJet β α T 0 (a/β^2) x0 =
    ∫ v in 0..V, ∫ w, physicalCDFCoordinateRate β α T (a+v)
      (x0+(SKConstants.BoundedLipschitzDrift.translated
        (finiteTemperatureCDFDrift β α ha h1) a x0).solution W.driver (Real.toNNReal v) w) ∂W.law := by
  have H := (physicalCDFRestartCoordinateCutoff_expected_tendsto W β α ha h1 hβ hT0 hT1 a x0 ha0 V).sub
    ((scalarSmoothCutoff_tendsto x0).mul_const (compactCDFJet β α T 0 (a/β^2) x0))
  simp only [physicalCDFRestartCoordinateCutoff_expectation_integral W β α ha h1 hβ hT0 hT1 a x0 ha0 _ V hV0 hVT] at H
  exact tendsto_nhds_unique H (physicalCDFRestartCoordinateCutoff_integral_tendsto
    W β α ha h1 hβ hT0 hT1 a x0 V hV0)

end SKConstants.ParisiFullSupport
