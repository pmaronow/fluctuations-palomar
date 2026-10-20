module

public import SKConstants.ParisiCDFCoordinateExpectation
public import SKConstants.ParisiEquilibriumPotentialExpectation

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.WeakIto SKConstantsOAI.SK.Analytic ParisiFullSupport
variable {Ω : Type*} [MeasurableSpace Ω]

def parisiPreSusceptibilityExpected (W : BrownianSystem Ω) (β : ℝ)
    (ha : ∀ z, cdf (parisiEquilibriumMeasure β:Measure ℝ) z∈Icc (0:ℝ) 1)
    (h1 : cdf (parisiEquilibriumMeasure β:Measure ℝ) 1=1) (v : ℝ) : ℝ :=
  ∫ w, scalarCDFHessian β (cdf (parisiEquilibriumMeasure β:Measure ℝ)) (v/β^2)
    (Real.toNNReal (1-v/β^2))
    (finiteTemperatureCDFProcess W β (cdf (parisiEquilibriumMeasure β:Measure ℝ)) ha h1
      (Real.toNNReal v) w) ∂W.law

theorem parisiEquilibrium_coordinate_expectation (W : BrownianSystem Ω) (β : ℝ) (hβ : 1<β)
    (ha : ∀ z, cdf (parisiEquilibriumMeasure β:Measure ℝ) z∈Icc (0:ℝ) 1)
    (h1 : cdf (parisiEquilibriumMeasure β:Measure ℝ) 1=1)
    {V : ℝ} (hV : V∈Icc 0 (β^2*parisiEquilibriumSupportEndpoint β)) :
    (∫ w, finiteTemperatureCDFProcess W β (cdf (parisiEquilibriumMeasure β:Measure ℝ)) ha h1
      (Real.toNNReal V) w*
      scalarCDFGradient β (cdf (parisiEquilibriumMeasure β:Measure ℝ)) (V/β^2)
        (Real.toNNReal (1-V/β^2))
        (finiteTemperatureCDFProcess W β (cdf (parisiEquilibriumMeasure β:Measure ℝ)) ha h1
          (Real.toNNReal V) w) ∂W.law)=
      ∫ v in 0..V, parisiPreSusceptibilityExpected W β ha h1 v+
        cdf (parisiEquilibriumMeasure β:Measure ℝ) (v/β^2)*(v/β^2) := by
  let := W.isProbability
  let α := cdf (parisiEquilibriumMeasure β:Measure ℝ)
  let Q := parisiEquilibriumSupportEndpoint β
  let T := (Q+1)/2
  have hp : 0<β := zero_lt_one.trans hβ
  have hQ := (parisiEquilibriumSupportEndpoint_spec β hβ).1
  have hQT : Q<T := by dsimp [T]; linarith [hQ.2]
  have hT0 : 0≤T := by dsimp [T]; linarith [hQ.1]
  have hT1 : T<1 := by dsimp [T]; linarith [hQ.2]
  have hq {v : ℝ} (hv : v∈Icc 0 (β^2*Q)) : v/β^2∈Icc (0:ℝ) T :=
    ⟨div_nonneg hv.1 (sq_nonneg β), ((div_le_iff₀ (sq_pos_of_ne_zero hp.ne')).mpr
      (by simpa only [mul_comm] using hv.2)).trans hQT.le⟩
  have hVQ : V/β^2≤Q := (div_le_iff₀ (sq_pos_of_ne_zero hp.ne')).mpr
    (by simpa only [mul_comm] using hV.2)
  have HE : (∫ w, finiteTemperatureCDFProcess W β α ha h1 (Real.toNNReal V) w*
      scalarCDFGradient β α (V/β^2) (Real.toNNReal (1-V/β^2))
        (finiteTemperatureCDFProcess W β α ha h1 (Real.toNNReal V) w) ∂W.law)=
      physicalCDFCoordinateExpected W β α ha h1 T V := by
    unfold physicalCDFCoordinateExpected compactCDFJet compactCDFGradient
    simp only [iteratedDeriv_zero,cdfStripTime_eq (hq hV)]
  rw [HE,physicalCDFCoordinateExpected_integral W β α ha h1 hp.ne' hT0 hT1 V hV.1
    (hVQ.trans_lt hQT)]
  apply intervalIntegral.integral_congr
  intro v hv
  rw [uIcc_of_le hV.1] at hv
  have hvQ : v∈Icc 0 (β^2*Q) := ⟨hv.1,hv.2.trans hV.2⟩
  have hv1 : Real.toNNReal (1-v/β^2)≤1 := by
    rw [Real.toNNReal_le_iff_le_coe,NNReal.coe_one]
    linarith [(hq hvQ).1]
  have hx := (finiteTemperatureCDFDrift β α ha h1).solution_measurable W (Real.toNNReal v)
  have hM := compactCDFGradient_family β α ha h1 hp.ne' hT0 hT1
  have hiH := integrable_family_comp (P:=W.law) hM.deriv (v/β^2) hx
  have hiHj : Integrable (fun w => compactCDFJet β α T 1 (v/β^2)
      ((finiteTemperatureCDFDrift β α ha h1).solution W.driver (Real.toNNReal v) w)) W.law := by
    apply hiH.congr
    filter_upwards [] with w
    simp only [compactCDFJet,iteratedDeriv_one]
  have hiM := integrable_family_comp (P:=W.law) (hM.mul hM) (v/β^2) hx
  have hH : compactCDFJet β α T 1 (v/β^2)=
      scalarCDFHessian β α (v/β^2) (Real.toNNReal (1-v/β^2)) := by
    unfold compactCDFJet compactCDFGradient
    rw [iteratedDeriv_one,cdfStripTime_eq (hq hvQ)]
    exact funext (fun x => (scalarCDFGradient_hasDerivAt β ha α.mono _ _ hv1 x).deriv)
  have HM := (parisiEquilibrium_physicalBrownian_moments W β hβ ha h1 hvQ).1
  unfold physicalCDFCoordinateRate
  change (∫ w, compactCDFJet β α T 1 (v/β^2)
      ((finiteTemperatureCDFDrift β α ha h1).solution W.driver (Real.toNNReal v) w)+
      compactCDFCoefficient α T (v/β^2)*
        (compactCDFGradient β α T (v/β^2)
          ((finiteTemperatureCDFDrift β α ha h1).solution W.driver (Real.toNNReal v) w)*
         compactCDFGradient β α T (v/β^2)
          ((finiteTemperatureCDFDrift β α ha h1).solution W.driver (Real.toNNReal v) w)) ∂W.law)=_
  rw [integral_add hiHj (hiM.const_mul _),integral_const_mul]
  rw [hH,compactCDFCoefficient,cdfStripTime_eq (hq hvQ)]
  have HMs : (∫ w, compactCDFGradient β α T (v/β^2)
      ((finiteTemperatureCDFDrift β α ha h1).solution W.driver (Real.toNNReal v) w)*
      compactCDFGradient β α T (v/β^2)
      ((finiteTemperatureCDFDrift β α ha h1).solution W.driver (Real.toNNReal v) w) ∂W.law)=v/β^2 := by
    unfold compactCDFGradient
    rw [cdfStripTime_eq (hq hvQ)]
    simpa only [finiteTemperatureCDFProcess,pow_two] using HM
  rw [HMs]
  rfl

end SKConstants
