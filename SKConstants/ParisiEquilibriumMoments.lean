module

public import SKConstants.ParisiEquilibriumFullSupport

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.SK.Analytic ParisiFullSupport
variable {Ω : Type*} [MeasurableSpace Ω]

lemma parisiEquilibrium_susceptibility_interior (W : BrownianSystem Ω) (β : ℝ) (hβ : 1<β)
    {q : ℝ} (hq : q∈Ioo 0 (parisiEquilibriumSupportEndpoint β)) :
    β^2*scalarCDFSusceptibilitySquareAverage β (cdf (parisiEquilibriumMeasure β:Measure ℝ)) q=1 := by
  have hp : 0<β := zero_lt_one.trans hβ
  have ha : ∀ z, cdf (parisiEquilibriumMeasure β:Measure ℝ) z∈Icc (0:ℝ) 1 :=
    fun z => ⟨cdf_nonneg _ z,cdf_le_one _ z⟩
  have h1 := supported_probability_cdf_one (parisiEquilibriumMeasure β)
    (parisiEquilibriumMeasure_upstream_spec β).1
  have HD := scalarCDFOverlap_hasDerivAt_actual W β hp _ ha h1
    ⟨hq.1,hq.2.trans (parisiEquilibriumSupportEndpoint_spec β hβ).1.2⟩
  have HI : HasDerivAt (scalarCDFOverlap β (cdf (parisiEquilibriumMeasure β:Measure ℝ))) 1 q :=
    (hasDerivAt_id q).congr_of_eventuallyEq (by
      filter_upwards [Ioo_mem_nhds hq.1 hq.2] with r hr
      exact parisiEquilibrium_overlap_every_time W β hβ ⟨hr.1.le,hr.2.le⟩)
  exact HD.unique HI

theorem parisiEquilibrium_susceptibility_every_time (W : BrownianSystem Ω) (β : ℝ) (hβ : 1<β)
    {q : ℝ} (hq : q∈Icc 0 (parisiEquilibriumSupportEndpoint β)) :
    β^2*scalarCDFSusceptibilitySquareAverage β (cdf (parisiEquilibriumMeasure β:Measure ℝ)) q=1 := by
  let α := cdf (parisiEquilibriumMeasure β:Measure ℝ)
  let Q := parisiEquilibriumSupportEndpoint β
  let T := (Q+1)/2
  have hp : 0<β := zero_lt_one.trans hβ
  have hQ := (parisiEquilibriumSupportEndpoint_spec β hβ).1
  have hQT : Q<T := by dsimp [T]; linarith [hQ.2]
  have hT0 : 0≤T := by dsimp [T]; linarith [hQ.1]
  have hT1 : T<1 := by dsimp [T]; linarith [hQ.2]
  have ha : ∀ z, α z∈Icc (0:ℝ) 1 := fun z => ⟨cdf_nonneg _ z,cdf_le_one _ z⟩
  have h1 : α 1=1 := supported_probability_cdf_one (parisiEquilibriumMeasure β)
    (parisiEquilibriumMeasure_upstream_spec β).1
  let R := standardCDFCurvatureMoment W β α ha h1 (T:=T)
  have hR : Continuous R := standardCDFCurvatureMoment_continuous W β α ha h1 hp.ne' hT0 hT1
  have heq (r : ℝ) (hr : r∈Icc 0 Q) : R r=β^2*scalarCDFSusceptibilitySquareAverage β α r := by
    unfold R standardCDFCurvatureMoment
    rw [←brownianCDFSusceptibilitySquare_eq_compact W β α ha h1 hp.ne' hT1.le ⟨hr.1,hr.2.trans hQT.le⟩,
      ←scalarCDFSusceptibilitySquareAverage_eq_actualBrownian W β hp α ha h1 ⟨hr.1,hr.2.trans_lt hQ.2⟩]
  have hi : Ioo 0 Q ⊆ {r | R r=1} := by
    intro r hr
    change R r=1
    rw [heq r ⟨hr.1.le,hr.2.le⟩]
    exact parisiEquilibrium_susceptibility_interior W β hβ hr
  have hclosed : IsClosed {r | R r=1} := isClosed_eq hR continuous_const
  have hfull := closure_minimal hi hclosed
  rw [closure_Ioo hQ.1.ne] at hfull
  rw [←heq q hq]
  exact hfull hq

theorem parisiEquilibrium_actualBrownian_moments (W : BrownianSystem Ω) (β : ℝ) (hβ : 1<β)
    (ha : ∀ z, cdf (parisiEquilibriumMeasure β:Measure ℝ) z∈Icc (0:ℝ) 1)
    (h1 : cdf (parisiEquilibriumMeasure β:Measure ℝ) 1=1)
    {q : ℝ} (hq : q∈Icc 0 (parisiEquilibriumSupportEndpoint β)) :
    brownianCDFOverlap W β (cdf (parisiEquilibriumMeasure β:Measure ℝ)) ha h1 q=q ∧
    brownianCDFSusceptibilitySquare W β (cdf (parisiEquilibriumMeasure β:Measure ℝ)) ha h1 q=1/β^2 := by
  have hp : 0<β := zero_lt_one.trans hβ
  have hq1 : q<1 := hq.2.trans_lt (parisiEquilibriumSupportEndpoint_spec β hβ).1.2
  constructor
  · rw [←scalarCDFOverlap_eq_actualBrownian W β hp _ ha h1 ⟨hq.1,hq1⟩]
    exact parisiEquilibrium_overlap_every_time W β hβ hq
  · rw [←scalarCDFSusceptibilitySquareAverage_eq_actualBrownian W β hp _ ha h1 ⟨hq.1,hq1⟩]
    apply (eq_div_iff (pow_ne_zero 2 hp.ne')).mpr
    simpa only [mul_comm] using parisiEquilibrium_susceptibility_every_time W β hβ hq

theorem parisiEquilibrium_physicalBrownian_moments (W : BrownianSystem Ω) (β : ℝ) (hβ : 1<β)
    (ha : ∀ z, cdf (parisiEquilibriumMeasure β:Measure ℝ) z∈Icc (0:ℝ) 1)
    (h1 : cdf (parisiEquilibriumMeasure β:Measure ℝ) 1=1)
    {v : ℝ} (hv : v∈Icc 0 (β^2*parisiEquilibriumSupportEndpoint β)) :
    (∫ w, (scalarCDFGradient β (cdf (parisiEquilibriumMeasure β:Measure ℝ))
      (v/β^2) (Real.toNNReal (1-v/β^2))
      (finiteTemperatureCDFProcess W β (cdf (parisiEquilibriumMeasure β:Measure ℝ)) ha h1
        (Real.toNNReal v) w))^2 ∂W.law)=v/β^2 ∧
    (∫ w, (scalarCDFHessian β (cdf (parisiEquilibriumMeasure β:Measure ℝ))
      (v/β^2) (Real.toNNReal (1-v/β^2))
      (finiteTemperatureCDFProcess W β (cdf (parisiEquilibriumMeasure β:Measure ℝ)) ha h1
        (Real.toNNReal v) w))^2 ∂W.law)=1/β^2 := by
  have hp : 0<β := zero_lt_one.trans hβ
  have hq : v/β^2∈Icc 0 (parisiEquilibriumSupportEndpoint β) :=
    ⟨div_nonneg hv.1 (sq_nonneg β), (div_le_iff₀ (sq_pos_of_ne_zero hp.ne')).mpr (by simpa only [mul_comm] using hv.2)⟩
  have H := parisiEquilibrium_actualBrownian_moments W β hβ ha h1 hq
  unfold brownianCDFOverlap brownianCDFSusceptibilitySquare at H
  rwa [mul_div_cancel₀ v (pow_ne_zero 2 hp.ne')] at H

end SKConstants
