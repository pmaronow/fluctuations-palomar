module

public import SKConstants.ParisiEntropyDissipation
public import SKConstants.ParisiFullScalarProcess

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.SK.Analytic ParisiFullSupport
variable {Ω : Type*} [MeasurableSpace Ω]

lemma compactCDFGradient_eq_actualFull (β : ℝ) (hβ : β≠0) {T : ℝ}
    (hT0 : 0≤T) (hT1 : T≤1) (v x : ℝ) :
    compactCDFGradient β (cdf (parisiEquilibriumMeasure β:Measure ℝ)) T (v/β^2) x=
      actualParisiFullMagnetization β (β^2*cdfStripTime T (v/β^2)) x := by
  unfold compactCDFGradient actualParisiFullMagnetization
  rw [mul_div_cancel_left₀ _ (pow_ne_zero 2 hβ)]
  rw [cdfTimeClamp_eq ⟨(cdfStripTime_mem hT0 _).1,(cdfStripTime_mem hT0 _).2.trans hT1⟩]

lemma physicalCDFCanonicalField_bounds (β : ℝ) (hβ : β≠0)
    (ha : ∀ z, cdf (parisiEquilibriumMeasure β:Measure ℝ) z∈Icc (0:ℝ) 1)
    (h1 : cdf (parisiEquilibriumMeasure β:Measure ℝ) 1=1)
    {T : ℝ} (hT0 : 0≤T) (hT1 : T<1) :
    let F := physicalCDFJetField β (cdf (parisiEquilibriumMeasure β:Measure ℝ)) ha h1 hβ hT0 hT1 0
    (∀ v x, |F.f v x|<1) ∧
      (∀ v x, |deriv (F.f v) x|≤1-(F.f v x)^2) ∧ F.f 0 0=0 := by
  dsimp only
  have HE (v x : ℝ) :
      (physicalCDFJetField β (cdf (parisiEquilibriumMeasure β:Measure ℝ)) ha h1 hβ hT0 hT1 0).f v x=
        actualParisiFullMagnetization β (β^2*cdfStripTime T (v/β^2)) x := by
    change compactCDFGradient β (cdf (parisiEquilibriumMeasure β:Measure ℝ)) T ((1/β^2)*v) x=_
    rw [show (1/β^2)*v=v/β^2 by ring]
    exact compactCDFGradient_eq_actualFull β hβ hT0 hT1.le v x
  refine ⟨fun v x => by rw [HE];exact abs_lt.mpr (actualParisiFullMagnetization_strict_bounds _ _ _),?_,?_⟩
  · intro v x
    have HF : (physicalCDFJetField β (cdf (parisiEquilibriumMeasure β:Measure ℝ)) ha h1 hβ hT0 hT1 0).f v=
        actualParisiFullMagnetization β (β^2*cdfStripTime T (v/β^2)) := funext (HE v)
    rw [HF,(actualParisiFullMagnetization_hasDerivAt _ _ _).deriv]
    have HB := actualParisiFullMagnetization_curvature_bounds β (β^2*cdfStripTime T (v/β^2)) x
    simpa only [abs_of_nonneg HB.2.1] using HB.2.2
  · rw [HE]
    have hr := cdfTimeClamp_mem ((β^2*cdfStripTime T (0/β^2))/β^2)
    have ht : Real.toNNReal (1-cdfTimeClamp ((β^2*cdfStripTime T (0/β^2))/β^2))≤1 := by
      rw [Real.toNNReal_le_iff_le_coe,NNReal.coe_one]
      linarith [hr.1]
    have HO := parisiCDFGradient_odd β ha (cdf (parisiEquilibriumMeasure β:Measure ℝ)).mono
      (cdfTimeClamp ((β^2*cdfStripTime T (0/β^2))/β^2)) _ ht 0
    simp only [neg_zero] at HO
    unfold actualParisiFullMagnetization
    linarith

theorem parisiEquilibrium_entropy_dissipation (W : BrownianSystem Ω) (β : ℝ) (hβ : 1<β)
    (ha : ∀ z, cdf (parisiEquilibriumMeasure β:Measure ℝ) z∈Icc (0:ℝ) 1)
    (h1 : cdf (parisiEquilibriumMeasure β:Measure ℝ) 1=1)
    {V : ℝ} (hV : V∈Icc 0 (β^2*parisiEquilibriumSupportEndpoint β)) :
    (∫ w, binarySpinEntropy
      (scalarCDFGradient β (cdf (parisiEquilibriumMeasure β:Measure ℝ)) (V/β^2)
        (Real.toNNReal (1-V/β^2))
        (finiteTemperatureCDFProcess W β (cdf (parisiEquilibriumMeasure β:Measure ℝ)) ha h1
          (Real.toNNReal V) w)) ∂W.law)=Real.log 2-
      (1/2:ℝ)*(∫ v in 0..V, ∫ w,
        (scalarCDFHessian β (cdf (parisiEquilibriumMeasure β:Measure ℝ)) (v/β^2)
          (Real.toNNReal (1-v/β^2))
          (finiteTemperatureCDFProcess W β (cdf (parisiEquilibriumMeasure β:Measure ℝ)) ha h1
            (Real.toNNReal v) w))^2/
        (1-(scalarCDFGradient β (cdf (parisiEquilibriumMeasure β:Measure ℝ)) (v/β^2)
          (Real.toNNReal (1-v/β^2))
          (finiteTemperatureCDFProcess W β (cdf (parisiEquilibriumMeasure β:Measure ℝ)) ha h1
            (Real.toNNReal v) w))^2) ∂W.law) := by
  let α := cdf (parisiEquilibriumMeasure β:Measure ℝ)
  let Q := parisiEquilibriumSupportEndpoint β
  let T := (Q+1)/2
  have hp : 0<β := zero_lt_one.trans hβ
  have hQ := (parisiEquilibriumSupportEndpoint_spec β hβ).1
  have hQT : Q<T := by dsimp [T];linarith [hQ.2]
  have hT0 : 0≤T := by dsimp [T];linarith [hQ.1]
  have hT1 : T<1 := by dsimp [T];linarith [hQ.2]
  have hq {v : ℝ} (hv : v∈Icc 0 (β^2*Q)) : v/β^2∈Icc (0:ℝ) T :=
    ⟨div_nonneg hv.1 (sq_nonneg β), ((div_le_iff₀ (sq_pos_of_ne_zero hp.ne')).mpr
      (by simpa only [mul_comm] using hv.2)).trans hQT.le⟩
  let F := physicalCDFJetField β α ha h1 hp.ne' hT0 hT1 0
  have hBounds := physicalCDFCanonicalField_bounds β hp.ne' ha h1 hT0 hT1
  have hVT : V<T/(1/β^2) := by
    rw [div_div_eq_mul_div,div_one]
    have HH : V/β^2≤Q := (div_le_iff₀ (sq_pos_of_ne_zero hp.ne')).mpr
      (by simpa only [mul_comm] using hV.2)
    simpa only [mul_comm] using (div_lt_iff₀ (sq_pos_of_ne_zero hp.ne')).mp (HH.trans_lt hQT)
  have H := actualBrownian_entropy_dissipation F (finiteTemperatureCDFDrift β α ha h1) W
    hBounds.1 hBounds.2.1 V hV.1 hVT hBounds.2.2 (fun v hv x => ?_)
    (fun v => (finiteTemperatureCDFDrift_path_right_continuous W β α ha h1).mono (fun w hw => hw v))
  · have HF (v x : ℝ) : F.f v x=compactCDFGradient β α T (v/β^2) x := by
      change compactCDFGradient β α T ((1/β^2)*v) x=_
      rw [show (1/β^2)*v=v/β^2 by ring]
    have HFM (v : ℝ) : F.f v=compactCDFGradient β α T (v/β^2) := funext (HF v)
    have HLeft : (∫ w, binarySpinEntropy
        (scalarCDFGradient β α (V/β^2) (Real.toNNReal (1-V/β^2))
          (finiteTemperatureCDFProcess W β α ha h1 (Real.toNNReal V) w)) ∂W.law)=
        ∫ w, binarySpinEntropy (F.f V ((finiteTemperatureCDFDrift β α ha h1).solution W.driver (Real.toNNReal V) w)) ∂W.law := by
      simp only [HF,compactCDFGradient,cdfStripTime_eq (hq hV),finiteTemperatureCDFProcess]
    rw [HLeft,H]
    congr 2
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hV.1] at hv
    have hvQ : v∈Icc 0 (β^2*Q) := ⟨hv.1,hv.2.trans hV.2⟩
    have hv1 : Real.toNNReal (1-v/β^2)≤1 := by
      rw [Real.toNNReal_le_iff_le_coe,NNReal.coe_one]
      linarith [(hq hvQ).1]
    dsimp only
    apply integral_congr_ae
    filter_upwards [] with w
    unfold entropyDissipationRate
    rw [HFM]
    unfold compactCDFGradient
    rw [cdfStripTime_eq (hq hvQ)]
    have HD : deriv (scalarCDFGradient β α (v/β^2) (Real.toNNReal (1-v/β^2)))=
        scalarCDFHessian β α (v/β^2) (Real.toNNReal (1-v/β^2)) :=
      funext (fun x => (scalarCDFGradient_hasDerivAt β ha α.mono _ _ hv1 x).deriv)
    rw [HD]
    rfl
  · unfold TimeField.generator
    rw [finiteTemperatureCDFDrift_eq_compact β α ha h1 hp.ne' hT1.le (hq ⟨hv.1,hv.2.trans hV.2⟩)]
    exact physicalCDFGradient_generator_zero β α ha h1 hp.ne' hT0 hT1 v x

end SKConstants
