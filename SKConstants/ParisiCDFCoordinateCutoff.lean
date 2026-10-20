module

public import SKConstants.ParisiBoundedExpectation

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace SKConstants.ParisiFullSupport
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.SK.Analytic
variable {Ω : Type*} [MeasurableSpace Ω]
variable (W : BrownianSystem Ω) (β : ℝ) (α : StieltjesFunction ℝ)
  (ha : ∀ z, α z∈Icc (0:ℝ) 1) (h1 : α 1=1) (hβ : β≠0)
  {T : ℝ} (hT0 : 0≤T) (hT1 : T<1)

def physicalCDFCoordinateCutoffField (n : ℕ) : TimeField (T/(1/β^2)) :=
  (staticTimeField _ (scalarSmoothCutoff n) (scalarSmoothCutoff_boundedSmooth n)).mul
    (physicalCDFJetField β α ha h1 hβ hT0 hT1 0)

def physicalCDFCoordinateRate (β : ℝ) (α : ℝ → ℝ) (T v x : ℝ) : ℝ :=
  compactCDFJet β α T 1 (v/β^2) x+
    compactCDFCoefficient α T (v/β^2)*
      (compactCDFJet β α T 0 (v/β^2) x*compactCDFJet β α T 0 (v/β^2) x)

def physicalCDFCoordinateCutoffRate (β : ℝ) (α : ℝ → ℝ) (T : ℝ) (n : ℕ) (v x : ℝ) : ℝ :=
  deriv (scalarSmoothCutoff n) x*physicalCDFCoordinateRate β α T v x+
    (1/2:ℝ)*(deriv (deriv (scalarSmoothCutoff n)) x*compactCDFJet β α T 0 (v/β^2) x)

include ha h1 hβ hT0 hT1 in
lemma physicalCDFCoordinateRate_family : BoundedSmoothFamily (physicalCDFCoordinateRate β α T) := by
  have hM := boundedSmoothFamily_time_comp
    (compactCDFGradient_family β α ha h1 hβ hT0 hT1) (measurable_id.div_const (β^2))
  have hH := boundedSmoothFamily_time_comp
    ((compactCDFGradient_family β α ha h1 hβ hT0 hT1).iteratedDeriv 1)
    (measurable_id.div_const (β^2))
  have hA := boundedSmoothFamily_time_comp (compactCDFCoefficient_family α ha T)
    (measurable_id.div_const (β^2))
  exact hH.add (hA.mul (hM.mul hM))

include ha h1 hβ hT0 hT1 in
lemma physicalCDFCoordinateCutoffRate_family (n : ℕ) :
    BoundedSmoothFamily (physicalCDFCoordinateCutoffRate β α T n) := by
  exact ((BoundedSmoothFamily.static (scalarSmoothCutoff_boundedSmooth n).deriv).mul
    (physicalCDFCoordinateRate_family β α ha h1 hβ hT0 hT1)).add
    (((BoundedSmoothFamily.static (scalarSmoothCutoff_boundedSmooth n).deriv.deriv).mul
      (boundedSmoothFamily_time_comp (compactCDFGradient_family β α ha h1 hβ hT0 hT1)
        (measurable_id.div_const (β^2)))).const_mul (1/2:ℝ))

lemma physicalCDFCoordinateCutoff_generator (n : ℕ) (v x : ℝ) :
    (physicalCDFCoordinateCutoffField β α ha h1 hβ hT0 hT1 n).generator
      (physicalCDFCompactDrift β α T) v x=physicalCDFCoordinateCutoffRate β α T n v x := by
  unfold physicalCDFCoordinateCutoffField
  rw [TimeField.generator_mul,physicalCDFGradient_generator_zero β α ha h1 hβ hT0 hT1]
  simp only [mul_zero,zero_add]
  change compactCDFJet β α T 0 ((1/β^2)*v) x*
    (deriv (scalarSmoothCutoff n) x*physicalCDFCompactDrift β α T v x+
      (1/2:ℝ)*deriv (deriv (scalarSmoothCutoff n)) x+0)+
    deriv (scalarSmoothCutoff n) x*deriv (compactCDFJet β α T 0 ((1/β^2)*v)) x=_
  rw [deriv_compactCDFJet β α ha h1 hβ hT0 hT1,
    show (1/β^2)*v=v/β^2 by ring]
  unfold physicalCDFCoordinateCutoffRate physicalCDFCoordinateRate physicalCDFCompactDrift
  ring

lemma physicalCDFCoordinateCutoff_expected_right_derivative (n : ℕ) (v : ℝ≥0)
    (hv : (v:ℝ)/β^2<T) :
    HasDerivWithinAt
      ((physicalCDFCoordinateCutoffField β α ha h1 hβ hT0 hT1 n).expected
        (finiteTemperatureCDFDrift β α ha h1) W)
      (∫ w, physicalCDFCoordinateCutoffRate β α T n v
        (finiteTemperatureCDFProcess W β α ha h1 v w) ∂W.law) (Ioi (v:ℝ)) v := by
  have hvT : (v:ℝ)<T/(1/β^2) := by
    rw [div_div_eq_mul_div,div_one]
    simpa only [mul_comm] using (div_lt_iff₀ (sq_pos_of_ne_zero hβ)).mp hv
  have H := (physicalCDFCoordinateCutoffField β α ha h1 hβ hT0 hT1 n).expected_hasDerivWithinAt_right
    (finiteTemperatureCDFDrift β α ha h1) W v hvT
    ((finiteTemperatureCDFDrift_path_right_continuous W β α ha h1).mono (fun w hw => hw v))
  convert H using 1
  apply integral_congr_ae
  filter_upwards [] with w
  unfold TimeField.generator
  rw [finiteTemperatureCDFDrift_eq_compact β α ha h1 hβ hT1.le
    ⟨div_nonneg v.coe_nonneg (sq_nonneg β),hv.le⟩]
  exact (physicalCDFCoordinateCutoff_generator β α ha h1 hβ hT0 hT1 n v _).symm

lemma physicalCDFCoordinateCutoff_expected_zero (n : ℕ) :
    (physicalCDFCoordinateCutoffField β α ha h1 hβ hT0 hT1 n).expected
      (finiteTemperatureCDFDrift β α ha h1) W 0=0 := by
  unfold TimeField.expected physicalCDFCoordinateCutoffField TimeField.mul staticTimeField
  simp only [Real.toNNReal_zero,BoundedLipschitzDrift.solution_zero,scalarSmoothCutoff,
    mul_zero,Real.tanh_zero,zero_mul,integral_zero]

lemma physicalCDFCoordinateCutoff_expectation_integral (n : ℕ) (V : ℝ)
    (hV0 : 0≤V) (hVT : V/β^2<T) :
    (physicalCDFCoordinateCutoffField β α ha h1 hβ hT0 hT1 n).expected
      (finiteTemperatureCDFDrift β α ha h1) W V=
      ∫ v in 0..V, ∫ w, physicalCDFCoordinateCutoffRate β α T n v
        (finiteTemperatureCDFProcess W β α ha h1 (Real.toNNReal v) w) ∂W.law := by
  have H := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hV0
    ((physicalCDFCoordinateCutoffField β α ha h1 hβ hT0 hT1 n).expected_continuous
      (finiteTemperatureCDFDrift β α ha h1) W).continuousOn
    (fun v hv => ?_)
    (bounded_family_expected_intervalIntegrable W (finiteTemperatureCDFDrift β α ha h1)
      (physicalCDFCoordinateCutoffRate_family β α ha h1 hβ hT0 hT1 n) 0 V)
  · simpa only [physicalCDFCoordinateCutoff_expected_zero W β α ha h1 hβ hT0 hT1 n,sub_zero,
      finiteTemperatureCDFProcess] using H.symm
  · have hv0 : 0≤v := hv.1.le
    have hvT : v/β^2<T := (div_le_div_of_nonneg_right hv.2.le (sq_nonneg β)).trans_lt hVT
    have HD := physicalCDFCoordinateCutoff_expected_right_derivative W β α ha h1 hβ hT0 hT1 n
      (Real.toNNReal v) (by simpa only [Real.coe_toNNReal v hv0] using hvT)
    simpa only [Real.coe_toNNReal v hv0,finiteTemperatureCDFProcess] using HD

end SKConstants.ParisiFullSupport
