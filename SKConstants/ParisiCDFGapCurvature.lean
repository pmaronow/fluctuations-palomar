module

public import SKConstants.ParisiCDFCoercivity
public import SKConstants.ParisiCDFStrictMoments
public import SKConstants.ParisiCDFCurvatureMoments

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace SKConstants.ParisiFullSupport

open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.SK.Analytic

variable {Ω : Type*} [MeasurableSpace Ω]
variable (W : BrownianSystem Ω) (β : ℝ) (α : StieltjesFunction ℝ)
  (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (h1 : α 1=1) (hβ : β≠0)
  {T : ℝ} (hT0 : 0≤T) (hT1 : T<1)

include hT1 in
lemma actualCDFSampleJet_eq_compact {q : ℝ} (hq : q ∈ Icc (0:ℝ) T) (n : ℕ) (w : Ω) :
    actualCDFSampleJet W β α ha h1 q (n+1) w = compactCDFJet β α T n q
      (finiteTemperatureCDFProcess W β α ha h1 (Real.toNNReal (β^2*q)) w) :=
  (compactCDFJet_eq_valueJet β α ha hT1.le hq n _).symm

lemma physicalCDFThirdMoment_eq_integral (c q : ℝ) :
    physicalCDFThirdMoment β α ha h1 hβ hT0 hT1 W c (β^2*q) =
      ∫ w, (compactCDFJet β α T 3 q
          (finiteTemperatureCDFProcess W β α ha h1 (Real.toNNReal (β^2*q)) w))^2-
        12*c*compactCDFJet β α T 1 q
          (finiteTemperatureCDFProcess W β α ha h1 (Real.toNNReal (β^2*q)) w)*
          (compactCDFJet β α T 2 q
          (finiteTemperatureCDFProcess W β α ha h1 (Real.toNNReal (β^2*q)) w))^2+
        6*c^2*(compactCDFJet β α T 1 q
          (finiteTemperatureCDFProcess W β α ha h1 (Real.toNNReal (β^2*q)) w))^4 ∂W.law := by
  unfold physicalCDFThirdMoment TimeField.expected
  simp_rw [physicalCDFThirdCurvatureField_eq]
  rw [mul_div_cancel_left₀ q (pow_ne_zero 2 hβ)]
  rfl

lemma physicalCDFSecondMoment_zero_eq_integral (q : ℝ) :
    physicalCDFSecondMoment β α ha h1 hβ hT0 hT1 W 0 (β^2*q) =
      ∫ w, (compactCDFJet β α T 2 q
        (finiteTemperatureCDFProcess W β α ha h1 (Real.toNNReal (β^2*q)) w))^2 ∂W.law := by
  unfold physicalCDFSecondMoment TimeField.expected physicalCDFSecondCurvatureField
    TimeField.add TimeField.mul TimeField.const_mul physicalCDFJetField rescaleTimeField
    compactCDFJetField physicalCDFCurvatureField
  simp only [mul_zero,zero_mul,add_zero]
  rw [show (1/β^2)*(β^2*q)=q by field_simp]
  simp only [←sq]
  rfl

lemma physicalCDFThirdMoment_pos {q c : ℝ} (hq : q ∈ Icc (0:ℝ) T)
    (hq0 : 0<q) (hc : 0<c) (hα : α q=c) (hcont : ContinuousAt α q) :
    0 < physicalCDFThirdMoment β α ha h1 hβ hT0 hT1 W c (β^2*q) := by
  have H := actualCDF_coercivity W β hβ α ha h1 ⟨hq0,hq.2.trans_lt hT1⟩ hcont
  rw [hα] at H
  simp_rw [actualCDFSampleJet_eq_compact W β α ha h1 hT1 hq 1,
    actualCDFSampleJet_eq_compact W β α ha h1 hT1 hq 2,
    actualCDFSampleJet_eq_compact W β α ha h1 hT1 hq 3] at H
  have he : (∫ w, coerciveJetPolynomial c
      (compactCDFJet β α T 1 q (finiteTemperatureCDFProcess W β α ha h1 (Real.toNNReal (β^2*q)) w))
      (compactCDFJet β α T 2 q (finiteTemperatureCDFProcess W β α ha h1 (Real.toNNReal (β^2*q)) w))
      (compactCDFJet β α T 3 q (finiteTemperatureCDFProcess W β α ha h1 (Real.toNNReal (β^2*q)) w)) ∂W.law) =
      c^2*physicalCDFThirdMoment β α ha h1 hβ hT0 hT1 W c (β^2*q) := by
    rw [physicalCDFThirdMoment_eq_integral,←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with w
    unfold coerciveJetPolynomial
    ring
  rw [he] at H
  unfold quarticJetPolynomial at H
  rw [integral_const_mul] at H
  have HP := actualCDF_curvature_quartic_pos W β α ha h1 hβ hT0 hT1 hq hq0
  have Hpos : 0 < (1/1000:ℝ)*(c^4*(∫ w,
      (compactCDFJet β α T 1 q (finiteTemperatureCDFProcess W β α ha h1
        (Real.toNNReal (β^2*q)) w))^4 ∂W.law)) := by positivity
  exact pos_of_mul_pos_right (Hpos.trans_le H) (sq_nonneg c)

lemma physicalCDFSecondMoment_zero_pos {q : ℝ} (hq : q ∈ Icc (0:ℝ) T) (hq0 : 0<q) :
    0 < physicalCDFSecondMoment β α ha h1 hβ hT0 hT1 W 0 (β^2*q) := by
  rw [physicalCDFSecondMoment_zero_eq_integral]
  exact actualCDF_third_square_pos W β α ha h1 hβ hT0 hT1 hq hq0

def standardCDFCurvatureMoment (q : ℝ) : ℝ :=
  β^2*physicalCDFJetSquareMoment W β α ha h1 T 1 (β^2*q)

def standardCDFSecondMoment (c q : ℝ) : ℝ :=
  β^4*physicalCDFSecondMoment β α ha h1 hβ hT0 hT1 W c (β^2*q)

include hβ hT0 hT1 in
lemma standardCDFCurvatureMoment_continuous :
    Continuous (standardCDFCurvatureMoment W β α ha h1 (T:=T)) :=
  continuous_const.mul ((physicalCDFJetSquareMoment_continuous W β α ha h1 hβ hT0 hT1 1).comp
    (continuous_const.mul continuous_id))

lemma standardCDFCurvatureMoment_derivative_on_constant {a b c q : ℝ}
    (ha0 : 0≤a) (hbT : b≤T) (hq : q∈Ioo a b)
    (hc : ∀ r∈Ioo a b, α r=c) :
    HasDerivAt (standardCDFCurvatureMoment W β α ha h1 (T:=T))
      (standardCDFSecondMoment W β α ha h1 hβ hT0 hT1 c q) q := by
  have H := physicalCDFCurvatureMoment_derivative_on_constant β α ha h1 hβ hT0 hT1 W
    (mul_nonneg (sq_nonneg β) ha0) (mul_le_mul_of_nonneg_left hbT (sq_nonneg β))
    (show β^2*q∈Ioo (β^2*a) (β^2*b) by
      exact ⟨mul_lt_mul_of_pos_left hq.1 (sq_pos_of_ne_zero hβ),
        mul_lt_mul_of_pos_left hq.2 (sq_pos_of_ne_zero hβ)⟩) (c:=c) ?_
  · change HasDerivAt (fun r => β^2*physicalCDFJetSquareMoment W β α ha h1 T 1 (β^2*r))
      (β^4*physicalCDFSecondMoment β α ha h1 hβ hT0 hT1 W c (β^2*q)) q
    convert ((H.comp q ((hasDerivAt_id q).const_mul (β^2))).const_mul (β^2)) using 1 <;> first | rfl | ring
  · intro r hr
    have hh : r/β^2∈Ioo a b := by
      constructor
      · apply (lt_div_iff₀ (sq_pos_of_ne_zero hβ)).mpr
        simpa only [mul_comm] using hr.1
      · apply (div_lt_iff₀ (sq_pos_of_ne_zero hβ)).mpr
        simpa only [mul_comm] using hr.2
    rw [compactCDFCoefficient,cdfStripTime_eq ⟨ha0.trans hh.1.le,hh.2.le.trans hbT⟩]
    exact hc _ hh

lemma standardCDFSecondMoment_derivative_on_constant {a b c q : ℝ}
    (ha0 : 0≤a) (hbT : b≤T) (hq : q∈Ioo a b)
    (hc : ∀ r∈Ioo a b, α r=c) :
    HasDerivAt (standardCDFSecondMoment W β α ha h1 hβ hT0 hT1 c)
      (β^6*physicalCDFThirdMoment β α ha h1 hβ hT0 hT1 W c (β^2*q)) q := by
  have H := physicalCDFSecondMoment_derivative_on_constant β α ha h1 hβ hT0 hT1 W
    (mul_nonneg (sq_nonneg β) ha0) (mul_le_mul_of_nonneg_left hbT (sq_nonneg β))
    (show β^2*q∈Ioo (β^2*a) (β^2*b) by
      exact ⟨mul_lt_mul_of_pos_left hq.1 (sq_pos_of_ne_zero hβ),
        mul_lt_mul_of_pos_left hq.2 (sq_pos_of_ne_zero hβ)⟩) (c:=c) ?_
  · change HasDerivAt (fun r => β^4*physicalCDFSecondMoment β α ha h1 hβ hT0 hT1 W c (β^2*r))
      (β^6*physicalCDFThirdMoment β α ha h1 hβ hT0 hT1 W c (β^2*q)) q
    convert ((H.comp q ((hasDerivAt_id q).const_mul (β^2))).const_mul (β^4)) using 1 <;> first | rfl | ring
  · intro r hr
    have hh : r/β^2∈Ioo a b := by
      constructor
      · apply (lt_div_iff₀ (sq_pos_of_ne_zero hβ)).mpr
        simpa only [mul_comm] using hr.1
      · apply (div_lt_iff₀ (sq_pos_of_ne_zero hβ)).mpr
        simpa only [mul_comm] using hr.2
    rw [compactCDFCoefficient,cdfStripTime_eq ⟨ha0.trans hh.1.le,hh.2.le.trans hbT⟩]
    exact hc _ hh

include hβ hT0 hT1 in
lemma standardCDFCurvatureMoment_second_deriv_pos {a b c q : ℝ}
    (ha0 : 0≤a) (hbT : b≤T) (hq : q∈Ioo a b) (hc0 : 0<c)
    (hc : ∀ r∈Ioo a b, α r=c) :
    0 < (deriv^[2] (standardCDFCurvatureMoment W β α ha h1 (T:=T))) q := by
  have hcont : ContinuousAt α q := continuousAt_const.congr_of_eventuallyEq (by
    filter_upwards [Ioo_mem_nhds hq.1 hq.2] with r hr
    exact hc r hr)
  have HP := physicalCDFThirdMoment_pos W β α ha h1 hβ hT0 hT1
    ⟨ha0.trans hq.1.le,hq.2.le.trans hbT⟩ (ha0.trans_lt hq.1) hc0 (hc q hq) hcont
  have HD := standardCDFSecondMoment_derivative_on_constant W β α ha h1 hβ hT0 hT1 ha0 hbT hq hc
  have HE : deriv (standardCDFCurvatureMoment W β α ha h1 (T:=T)) =ᶠ[𝓝 q]
      standardCDFSecondMoment W β α ha h1 hβ hT0 hT1 c := by
    filter_upwards [Ioo_mem_nhds hq.1 hq.2] with r hr
    exact (standardCDFCurvatureMoment_derivative_on_constant W β α ha h1 hβ hT0 hT1 ha0 hbT hr hc).deriv
  have HH := HD.congr_of_eventuallyEq HE
  change 0 < deriv (deriv (standardCDFCurvatureMoment W β α ha h1 (T:=T))) q
  rw [HH.deriv]
  exact mul_pos (by simpa only [←pow_mul] using pow_pos (sq_pos_of_ne_zero hβ) 3) HP

include hβ hT0 hT1 in
lemma standardCDFCurvatureMoment_deriv_pos_zero {a b q : ℝ}
    (ha0 : 0≤a) (hbT : b≤T) (hq : q∈Ioo a b)
    (hc : ∀ r∈Ioo a b, α r=0) :
    0 < deriv (standardCDFCurvatureMoment W β α ha h1 (T:=T)) q := by
  rw [(standardCDFCurvatureMoment_derivative_on_constant W β α ha h1 hβ hT0 hT1 ha0 hbT hq hc).deriv]
  unfold standardCDFSecondMoment
  exact mul_pos (by simpa only [←pow_mul] using pow_pos (sq_pos_of_ne_zero hβ) 2)
    (physicalCDFSecondMoment_zero_pos W β α ha h1 hβ hT0 hT1
      ⟨ha0.trans hq.1.le,hq.2.le.trans hbT⟩ (ha0.trans_lt hq.1))

end SKConstants.ParisiFullSupport
