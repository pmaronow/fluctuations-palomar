module

public import SKConstants.ParisiEquilibriumCoordinateExpectation
public import SKConstants.ParisiBinaryEntropyTerminal
public import SKConstants.ParisiFullScalarProcess

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.ZeroTemperatureSK.WeakIto SKConstantsOAI.SK.Analytic ParisiFullSupport
variable {Ω : Type*} [MeasurableSpace Ω]

lemma parisiPreSusceptibilityExpected_intervalIntegrable (W : BrownianSystem Ω) (β : ℝ) (hβ : 1<β)
    (ha : ∀ z, cdf (parisiEquilibriumMeasure β:Measure ℝ) z∈Icc (0:ℝ) 1)
    (h1 : cdf (parisiEquilibriumMeasure β:Measure ℝ) 1=1)
    {V : ℝ} (hV : V∈Icc 0 (β^2*parisiEquilibriumSupportEndpoint β)) :
    IntervalIntegrable (parisiPreSusceptibilityExpected W β ha h1) volume 0 V := by
  let α := cdf (parisiEquilibriumMeasure β:Measure ℝ)
  let Q := parisiEquilibriumSupportEndpoint β
  let T := (Q+1)/2
  have hp : 0<β := zero_lt_one.trans hβ
  have hQ := (parisiEquilibriumSupportEndpoint_spec β hβ).1
  have hQT : Q<T := by dsimp [T];linarith [hQ.2]
  have hT0 : 0≤T := by dsimp [T];linarith [hQ.1]
  have hT1 : T<1 := by dsimp [T];linarith [hQ.2]
  have HG := boundedSmoothFamily_time_comp
    ((compactCDFGradient_family β α ha h1 hp.ne' hT0 hT1).iteratedDeriv 1)
    (measurable_id.div_const (β^2))
  have HI := bounded_family_expected_intervalIntegrable W (finiteTemperatureCDFDrift β α ha h1) HG 0 V
  apply HI.congr_uIoo
  intro v hv
  rw [uIoo_of_le hV.1] at hv
  have hvq : v/β^2∈Icc (0:ℝ) T :=
    ⟨div_nonneg hv.1.le (sq_nonneg β), ((div_le_iff₀ (sq_pos_of_ne_zero hp.ne')).mpr
      (by simpa only [mul_comm] using hv.2.le.trans hV.2)).trans hQT.le⟩
  have hv1 : Real.toNNReal (1-v/β^2)≤1 := by
    rw [Real.toNNReal_le_iff_le_coe,NNReal.coe_one];linarith [hvq.1]
  dsimp only
  unfold parisiPreSusceptibilityExpected
  apply integral_congr_ae
  filter_upwards [] with w
  change compactCDFJet β α T 1 (v/β^2) _=_
  unfold compactCDFJet compactCDFGradient
  rw [iteratedDeriv_one,cdfStripTime_eq hvq]
  rw [(scalarCDFGradient_hasDerivAt β ha α.mono _ _ hv1 _).deriv]
  rfl

lemma parisiPhysicalOverlapPenalty_intervalIntegrable (β : ℝ)
    (μ : ProbabilityMeasure ℝ) (A V : ℝ) :
    IntervalIntegrable (fun v => cdf (μ:Measure ℝ) (v/β^2)*(v/β^2)) volume A V := by
  have hmono : Monotone (fun v : ℝ => cdf (μ:Measure ℝ) (v/β^2)) :=
    (cdf (μ:Measure ℝ)).mono.comp (fun _ _ h => div_le_div_of_nonneg_right h (sq_nonneg β))
  exact (hmono.intervalIntegrable (μ:=volume)).mul_continuousOn (continuous_id.div_const _).continuousOn

theorem parisiEquilibrium_terminal_entropy_balance (W : BrownianSystem Ω) (β : ℝ) (hβ : 1<β)
    (ha : ∀ z, cdf (parisiEquilibriumMeasure β:Measure ℝ) z∈Icc (0:ℝ) 1)
    (h1 : cdf (parisiEquilibriumMeasure β:Measure ℝ) 1=1) :
    (∫ v in 0..(β^2*parisiEquilibriumSupportEndpoint β), parisiPreSusceptibilityExpected W β ha h1 v)+
      (∫ w, binarySpinEntropy (Real.tanh
        (finiteTemperatureCDFProcess W β (cdf (parisiEquilibriumMeasure β:Measure ℝ)) ha h1
          (Real.toNNReal (β^2*parisiEquilibriumSupportEndpoint β)) w)) ∂W.law)=
      parisiPhysicalValue β (parisiEquilibriumMeasure β) 0 0-
        (1/2:ℝ)*(∫ v in 0..(β^2*parisiEquilibriumSupportEndpoint β),
          cdf (parisiEquilibriumMeasure β:Measure ℝ) (v/β^2)*(v/β^2))-
        (β^2-β^2*parisiEquilibriumSupportEndpoint β)/2 := by
  let := W.isProbability
  let μ := parisiEquilibriumMeasure β
  let α := cdf (μ:Measure ℝ)
  let Q := parisiEquilibriumSupportEndpoint β
  let V := β^2*Q
  let b := finiteTemperatureCDFDrift β α ha h1
  let X := b.solution W.driver (Real.toNNReal V)
  have hp : 0<β := zero_lt_one.trans hβ
  have hQ := (parisiEquilibriumSupportEndpoint_spec β hβ).1
  have hV : V∈Icc 0 (β^2*Q) := ⟨mul_nonneg (sq_nonneg β) hQ.1.le,le_rfl⟩
  have hVb : V∈Icc 0 (β^2) := ⟨hV.1,mul_le_of_le_one_right (sq_nonneg β) hQ.2.le⟩
  have hcut : α (V/β^2)=1 := by
    apply actualParisiEquilibrium_cdf_one_after_support β hβ
    dsimp [V]
    rw [mul_div_cancel_left₀ _ (pow_ne_zero 2 hp.ne')]
  have hM : scalarCDFGradient β α (V/β^2) (Real.toNNReal (1-V/β^2))=Real.tanh := by
    have H := parisiPhysicalGradient_at_cdf_one β hp.ne' μ V hVb hcut
    rw [H]
    exact funext Real.tanh_eq_sinh_div_cosh |>.symm
  have hPhi : parisiPhysicalValue β μ V=fun y => Real.log (2*Real.cosh y)+(β^2-V)/2 :=
    parisiPhysicalValue_at_cdf_one β hp.ne' μ V hVb hcut
  have hXm := b.solution_measurable W (Real.toNNReal V)
  have hiYm : Integrable (fun w => X w*Real.tanh (X w)) W.law := by
    apply (b.solution_integrable W (Real.toNNReal V)).mul_bdd
      ((contDiff_tanh.continuous.measurable.comp hXm).aestronglyMeasurable)
    exact Eventually.of_forall (fun w => (Real.abs_tanh_lt_one (X w)).le)
  have hiH : Integrable (fun w => binarySpinEntropy (Real.tanh (X w))) W.law := by
    have hmeas : Measurable (fun w => binarySpinEntropy (Real.tanh (X w))) := by
      unfold binarySpinEntropy
      exact Real.binEntropy_continuous.measurable.comp
        ((measurable_const.add (contDiff_tanh.continuous.measurable.comp hXm)).div_const 2)
    apply Integrable.of_bound hmeas.aestronglyMeasurable (Real.log 2)
    filter_upwards [] with w
    have HB := binarySpinEntropy_bounds (Real.abs_tanh_lt_one (X w)).le
    simpa only [Real.norm_eq_abs,abs_of_nonneg HB.1] using HB.2
  have HE : (∫ w, parisiPhysicalValue β μ V (X w) ∂W.law)=
      (∫ w, binarySpinEntropy (Real.tanh (X w)) ∂W.law)+
      (∫ w, X w*Real.tanh (X w) ∂W.law)+(β^2-V)/2 := by
    have HH : (fun w => parisiPhysicalValue β μ V (X w))=fun w =>
        binarySpinEntropy (Real.tanh (X w))+X w*Real.tanh (X w)+(β^2-V)/2 := by
      funext w
      rw [hPhi,binarySpinEntropy_tanh]
      ring
    have hi12 := hiH.add hiYm
    change Integrable (fun w => binarySpinEntropy (Real.tanh (X w))+X w*Real.tanh (X w)) W.law at hi12
    rw [HH,integral_add hi12 (integrable_const _),integral_add hiH hiYm]
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
  have HPhi := parisiEquilibrium_potential_expectation W β hβ ha h1 hV
  have HYm := parisiEquilibrium_coordinate_expectation W β hβ ha h1 hV
  rw [hM] at HYm
  rw [intervalIntegral.integral_add (parisiPreSusceptibilityExpected_intervalIntegrable W β hβ ha h1 hV)
    (parisiPhysicalOverlapPenalty_intervalIntegrable β μ 0 V)] at HYm
  change (∫ w, parisiPhysicalValue β μ V (X w) ∂W.law)=_ at HPhi
  rw [HE] at HPhi
  change (∫ w, X w*Real.tanh (X w) ∂W.law)=_ at HYm
  change (∫ v in 0..V, parisiPreSusceptibilityExpected W β ha h1 v)+
    (∫ w, binarySpinEntropy (Real.tanh (X w)) ∂W.law)=_
  linarith

end SKConstants
