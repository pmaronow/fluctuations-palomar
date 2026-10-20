module

public import SKConstants.ParisiCDFCurvatureFields

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
noncomputable section

namespace SKConstants.ParisiFullSupport

open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.SK.Analytic

variable {Ω : Type*} [MeasurableSpace Ω]
variable (β : ℝ) (α : StieltjesFunction ℝ)
  (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (h1 : α 1 = 1) (hβ : β ≠ 0)
  {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1)

def physicalCDFThirdCurvatureField (c : ℝ) : TimeField (T/(1/β^2)) :=
  (((physicalCDFJetField β α ha h1 hβ hT0 hT1 3).mul
    (physicalCDFJetField β α ha h1 hβ hT0 hT1 3)).add
    (((physicalCDFJetField β α ha h1 hβ hT0 hT1 1).mul
      ((physicalCDFJetField β α ha h1 hβ hT0 hT1 2).mul
        (physicalCDFJetField β α ha h1 hβ hT0 hT1 2))).const_mul (-12*c))).add
    (((physicalCDFCurvatureField β α ha h1 hβ hT0 hT1).mul
      (physicalCDFCurvatureField β α ha h1 hβ hT0 hT1)).const_mul (6*c^2))

lemma physicalCDFThirdCurvatureField_eq (c t x : ℝ) :
    (physicalCDFThirdCurvatureField β α ha h1 hβ hT0 hT1 c).f t x =
      (compactCDFJet β α T 3 (t/β^2) x)^2-
        12*c*compactCDFJet β α T 1 (t/β^2) x*(compactCDFJet β α T 2 (t/β^2) x)^2+
        6*c^2*(compactCDFJet β α T 1 (t/β^2) x)^4 := by
  dsimp only [physicalCDFThirdCurvatureField, physicalCDFCurvatureField,
    TimeField.add, TimeField.mul, TimeField.const_mul, physicalCDFJetField,
    rescaleTimeField, compactCDFJetField]
  rw [show (1/β^2)*t=t/β^2 by ring]
  ring

lemma physicalCDFSecondCurvatureField_generator_eq (c t x : ℝ)
    (hc : compactCDFCoefficient α T (t/β^2)=c) :
    (physicalCDFSecondCurvatureField β α ha h1 hβ hT0 hT1 c).generator
      (physicalCDFCompactDrift β α T) t x =
        (physicalCDFThirdCurvatureField β α ha h1 hβ hT0 hT1 c).f t x := by
  rw [physicalCDFThirdCurvatureField_eq]
  exact physicalCDFSecondCurvatureField_generator β α ha h1 hβ hT0 hT1 c t x hc

include hβ hT1 in
lemma physicalCDFField_expected_right_derivative (W : BrownianSystem Ω)
    (F G : TimeField (T/(1/β^2))) (v : ℝ≥0) (hv : (v:ℝ)/β^2 < T)
    (hg : ∀ x, F.generator (physicalCDFCompactDrift β α T) v x=G.f v x) :
    HasDerivWithinAt (F.expected (finiteTemperatureCDFDrift β α ha h1) W)
      (G.expected (finiteTemperatureCDFDrift β α ha h1) W v) (Ioi (v:ℝ)) v := by
  have hvH : (v:ℝ) < T/(1/β^2) := by
    simp only [one_div, div_inv_eq_mul]
    exact (div_lt_iff₀ (sq_pos_of_ne_zero hβ)).mp hv
  have hbr := (finiteTemperatureCDFDrift_path_right_continuous W β α ha h1).mono
    (fun w hw => hw v)
  have H := F.expected_hasDerivWithinAt_right (finiteTemperatureCDFDrift β α ha h1)
    W v hvH hbr
  convert H using 1
  unfold TimeField.expected
  apply integral_congr_ae
  filter_upwards [] with w
  simp only [Real.toNNReal_coe]
  have ht : (v:ℝ)/β^2 ∈ Icc (0:ℝ) T :=
    ⟨div_nonneg v.coe_nonneg (sq_nonneg β),hv.le⟩
  have hb : (finiteTemperatureCDFDrift β α ha h1).f v = physicalCDFCompactDrift β α T v := by
    funext x
    exact finiteTemperatureCDFDrift_eq_compact β α ha h1 hβ hT1.le ht x
  unfold TimeField.generator
  rw [hb]
  exact (hg _).symm

def physicalCDFSecondMoment (W : BrownianSystem Ω) (c : ℝ) : ℝ → ℝ :=
  (physicalCDFSecondCurvatureField β α ha h1 hβ hT0 hT1 c).expected
    (finiteTemperatureCDFDrift β α ha h1) W

def physicalCDFThirdMoment (W : BrownianSystem Ω) (c : ℝ) : ℝ → ℝ :=
  (physicalCDFThirdCurvatureField β α ha h1 hβ hT0 hT1 c).expected
    (finiteTemperatureCDFDrift β α ha h1) W

lemma physicalCDFCurvatureMoment_right_derivative (W : BrownianSystem Ω)
    (v : ℝ≥0) (hv : (v:ℝ)/β^2 < T) :
    HasDerivWithinAt (physicalCDFJetSquareMoment W β α ha h1 T 1)
      (physicalCDFSecondMoment β α ha h1 hβ hT0 hT1 W
        (compactCDFCoefficient α T ((v:ℝ)/β^2)) v) (Ioi (v:ℝ)) v := by
  have H := physicalCDFField_expected_right_derivative β α ha h1 hβ hT1 W
    (physicalCDFCurvatureField β α ha h1 hβ hT0 hT1)
    (physicalCDFSecondCurvatureField β α ha h1 hβ hT0 hT1
      (compactCDFCoefficient α T ((v:ℝ)/β^2))) v hv
    (physicalCDFCurvatureField_generator β α ha h1 hβ hT0 hT1 v)
  rw [physicalCDFJetSquareMoment_eq_expected W β α ha h1 hβ hT0 hT1 1]
  exact H

lemma physicalCDFSecondMoment_right_derivative (W : BrownianSystem Ω)
    (c : ℝ) (v : ℝ≥0) (hv : (v:ℝ)/β^2 < T)
    (hc : compactCDFCoefficient α T ((v:ℝ)/β^2)=c) :
    HasDerivWithinAt (physicalCDFSecondMoment β α ha h1 hβ hT0 hT1 W c)
      (physicalCDFThirdMoment β α ha h1 hβ hT0 hT1 W c v) (Ioi (v:ℝ)) v := by
  exact physicalCDFField_expected_right_derivative β α ha h1 hβ hT1 W
    (physicalCDFSecondCurvatureField β α ha h1 hβ hT0 hT1 c)
    (physicalCDFThirdCurvatureField β α ha h1 hβ hT0 hT1 c) v hv
    (fun x => physicalCDFSecondCurvatureField_generator_eq β α ha h1 hβ hT0 hT1 c v x hc)

lemma hasDerivAt_of_right_on_interval {f d : ℝ → ℝ} {a b q : ℝ}
    (hf : Continuous f) (hd : Continuous d) (hq : q ∈ Ioo a b)
    (hderiv : ∀ r ∈ Ioo a b, HasDerivWithinAt f (d r) (Ioi r) r) :
    HasDerivAt f (d q) q := by
  have hD : HasDerivAt (fun r => f a + ∫ t in a..r, d t) (d q) q :=
    (intervalIntegral.integral_hasDerivAt_right (hd.intervalIntegrable _ _)
      hd.stronglyMeasurable.stronglyMeasurableAtFilter hd.continuousAt).const_add (f a)
  apply hD.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hq.1 hq.2] with r hr
  have hi := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hr.1.le
    hf.continuousOn (fun t ht => hderiv t ⟨ht.1,ht.2.trans hr.2⟩)
    (hd.intervalIntegrable _ _)
  linarith

lemma physicalCDFCurvatureMoment_derivative_on_constant (W : BrownianSystem Ω)
    {a b c v : ℝ} (ha0 : 0 ≤ a) (hbT : b ≤ β^2*T) (hv : v ∈ Ioo a b)
    (hc : ∀ r ∈ Ioo a b, compactCDFCoefficient α T (r/β^2)=c) :
    HasDerivAt (physicalCDFJetSquareMoment W β α ha h1 T 1)
      (physicalCDFSecondMoment β α ha h1 hβ hT0 hT1 W c v) v := by
  apply hasDerivAt_of_right_on_interval
    (physicalCDFJetSquareMoment_continuous W β α ha h1 hβ hT0 hT1 1)
    (TimeField.expected_continuous _ _ _) hv
  intro r hr
  have hr0 := ha0.trans hr.1.le
  have hrT : r/β^2 < T := (div_lt_iff₀ (sq_pos_of_ne_zero hβ)).mpr
    (by simpa only [mul_comm] using hr.2.trans_le hbT)
  simpa only [Real.coe_toNNReal r hr0,hc r hr,physicalCDFSecondMoment] using
    physicalCDFCurvatureMoment_right_derivative β α ha h1 hβ hT0 hT1 W
      (Real.toNNReal r) (by simpa only [Real.coe_toNNReal r hr0] using hrT)

lemma physicalCDFSecondMoment_derivative_on_constant (W : BrownianSystem Ω)
    {a b c v : ℝ} (ha0 : 0 ≤ a) (hbT : b ≤ β^2*T) (hv : v ∈ Ioo a b)
    (hc : ∀ r ∈ Ioo a b, compactCDFCoefficient α T (r/β^2)=c) :
    HasDerivAt (physicalCDFSecondMoment β α ha h1 hβ hT0 hT1 W c)
      (physicalCDFThirdMoment β α ha h1 hβ hT0 hT1 W c v) v := by
  apply hasDerivAt_of_right_on_interval
    (TimeField.expected_continuous _ _ _) (TimeField.expected_continuous _ _ _) hv
  intro r hr
  have hr0 := ha0.trans hr.1.le
  have hrT : r/β^2 < T := (div_lt_iff₀ (sq_pos_of_ne_zero hβ)).mpr
    (by simpa only [mul_comm] using hr.2.trans_le hbT)
  simpa only [Real.coe_toNNReal r hr0,physicalCDFSecondMoment,physicalCDFThirdMoment] using
    physicalCDFSecondMoment_right_derivative β α ha h1 hβ hT0 hT1 W c
      (Real.toNNReal r) (by simpa only [Real.coe_toNNReal r hr0] using hrT)
      (by simpa only [Real.coe_toNNReal r hr0] using hc r hr)

end SKConstants.ParisiFullSupport
