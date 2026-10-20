module

public import SKConstants.ParisiCDFGapCurvature
public import SKConstants.ParisiSupportInterval
public import SKConstants.ParisiEquilibriumAT

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.SK.Analytic ParisiFullSupport

variable {Ω : Type*} [MeasurableSpace Ω]

theorem parisiEquilibrium_full_support (W : BrownianSystem Ω) (β : ℝ) (hβ : 1<β) :
    (parisiEquilibriumMeasure β:Measure ℝ).support = Icc 0 (parisiEquilibriumSupportEndpoint β) ∧
    ∀ q∈Icc 0 (parisiEquilibriumSupportEndpoint β),
      scalarCDFOverlap β (cdf (parisiEquilibriumMeasure β:Measure ℝ)) q=q := by
  let μ := parisiEquilibriumMeasure β
  let α := cdf (μ:Measure ℝ)
  let Q := parisiEquilibriumSupportEndpoint β
  let T := (Q+1)/2
  have hp : 0<β := zero_lt_one.trans hβ
  have hβ0 := hp.ne'
  have hs := parisiEquilibriumSupportEndpoint_spec β hβ
  have hQ0 : 0<Q := hs.1.1
  have hQ1 : Q<1 := hs.1.2
  have hQT : Q<T := by dsimp [T]; linarith
  have hT0 : 0≤T := by dsimp [T]; linarith
  have hT1 : T<1 := by dsimp [T]; linarith
  have ha : ∀ z, α z∈Icc (0:ℝ) 1 := fun z => ⟨cdf_nonneg _ z,cdf_le_one _ z⟩
  have h1 : α 1=1 := supported_probability_cdf_one μ (parisiEquilibriumMeasure_upstream_spec β).1
  let G := fun q => physicalCDFJetSquareMoment W β α ha h1 T 0 (β^2*q)
  let R := standardCDFCurvatureMoment W β α ha h1 (T:=T)
  have hG : Continuous G :=
    (physicalCDFJetSquareMoment_continuous W β α ha h1 hβ0 hT0 hT1 0).comp
      (continuous_const.mul continuous_id)
  have hR : Continuous R := standardCDFCurvatureMoment_continuous W β α ha h1 hβ0 hT0 hT1
  have hGeq (q : ℝ) (hq : q∈Icc 0 Q) : G q=scalarCDFOverlap β α q := by
    exact (scalarCDFOverlap_eq_actualBrownian W β hp α ha h1 ⟨hq.1,hq.2.trans_lt hQ1⟩).trans
      (brownianCDFOverlap_eq_compact W β α ha h1 hβ0 ⟨hq.1,hq.2.trans hQT.le⟩) |>.symm
  have hReq (q : ℝ) (hq : q∈Icc 0 Q) : R q=β^2*scalarCDFSusceptibilitySquareAverage β α q := by
    unfold R standardCDFCurvatureMoment
    rw [←brownianCDFSusceptibilitySquare_eq_compact W β α ha h1 hβ0 hT1.le ⟨hq.1,hq.2.trans hQT.le⟩,
      ←scalarCDFSusceptibilitySquareAverage_eq_actualBrownian W β hp α ha h1 ⟨hq.1,hq.2.trans_lt hQ1⟩]
  have hD (q : ℝ) (hq : q∈Ioo 0 Q) : HasDerivAt G (R q) q := by
    have HD := physicalCDFJetSquareMoment_gradient_derivative W β α ha h1 hβ0 hT0 hT1
      (mul_pos (sq_pos_of_ne_zero hβ0) hq.1)
      (show (β^2*q)/β^2<T by rw [mul_div_cancel_left₀ _ (pow_ne_zero 2 hβ0)]; exact hq.2.trans hQT)
    convert HD.comp q ((hasDerivAt_id q).const_mul (β^2)) using 1 <;> first | rfl | dsimp [R,standardCDFCurvatureMoment]; ring
  have H := support_interval_of_gap_curvature μ Q G R hs.2.2.1
    (parisiEquilibrium_zero_mem_support β hβ0) hs.2.1.1 hG.continuousOn hR.continuousOn hD ?_ ?_ ?_
  · refine ⟨H.1,?_⟩
    intro q hq
    rw [←hGeq q hq]
    exact H.2 q hq
  · intro q hqs
    have hq := hs.2.2.1 hqs
    rw [hGeq q hq,hReq q hq]
    exact ⟨parisiEquilibrium_overlap_on_support β hβ0 q hqs,
      parisiEquilibrium_AT_on_support W β hp hqs⟩
  · intro a b c ha0 hab hb hc hconstant q hq
    exact standardCDFCurvatureMoment_second_deriv_pos W β α ha h1 hβ0 hT0 hT1 ha0
      (hb.trans hQT.le) hq hc hconstant
  · intro a b ha0 hab hb hconstant q hq
    exact standardCDFCurvatureMoment_deriv_pos_zero W β α ha h1 hβ0 hT0 hT1 ha0
      (hb.trans hQT.le) hq hconstant

theorem parisiEquilibrium_overlap_every_time (W : BrownianSystem Ω) (β : ℝ) (hβ : 1<β)
    {q : ℝ} (hq : q∈Icc 0 (parisiEquilibriumSupportEndpoint β)) :
    scalarCDFOverlap β (cdf (parisiEquilibriumMeasure β:Measure ℝ)) q=q :=
  (parisiEquilibrium_full_support W β hβ).2 q hq

end SKConstants
