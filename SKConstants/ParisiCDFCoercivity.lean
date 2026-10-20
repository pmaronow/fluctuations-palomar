module

public import SKConstants.ParisiCDFSampleCoercivity

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology ContDiff
noncomputable section

namespace SKConstants.ParisiFullSupport

open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.SK.Analytic

variable {Ω : Type*} [MeasurableSpace Ω]

lemma positiveGridQuartic_integral_tendsto (W : BrownianSystem Ω) (β : ℝ) (hβ : β ≠ 0)
    (α : StieltjesFunction ℝ) (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (h1 : α 1=1)
    {q : ℝ} (hq : q ∈ Ico (0:ℝ) 1) (hcont : ContinuousAt α q) :
    Tendsto (fun n => ∫ w, quarticJetPolynomial (positiveGridSampleCoefficient α q n)
      (positiveGridSampleJet W β α q n 2 w) ∂W.law) atTop
      (𝓝 (∫ w, quarticJetPolynomial (α q) (actualCDFSampleJet W β α ha h1 q 2 w) ∂W.law)) := by
  let := W.isProbability
  obtain ⟨C,hC,hB⟩ := positiveGridSampleJet_bound W β hβ α ha hq 0
  have hm (n : ℕ) : AEStronglyMeasurable (fun w => quarticJetPolynomial
      (positiveGridSampleCoefficient α q n) (positiveGridSampleJet W β α q n 2 w)) W.law := by
    exact (measurable_const.mul ((positiveGridSampleJet_measurable W β hβ α ha hq n 2).pow_const 4)).aestronglyMeasurable
  apply tendsto_integral_of_dominated_convergence (fun _ : Ω => C^4) hm (integrable_const _) _ _
  · intro n
    exact Eventually.of_forall (fun w => by
      simpa only [Real.norm_eq_abs,one_pow,one_mul,Nat.reduceAdd] using quarticJetPolynomial_bound
        (positiveGridSampleCoefficient_abs_le_one α ha q n) (hB n w))
  · filter_upwards [positiveGridSampleJet_tendsto W β hβ α ha h1 hq 2] with w hw
    exact ((positiveGridCoefficient_tendsto α ha hq.1 hcont).pow 4).mul (hw.pow 4)

lemma positiveGridCoercive_integral_tendsto (W : BrownianSystem Ω) (β : ℝ) (hβ : β ≠ 0)
    (α : StieltjesFunction ℝ) (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (h1 : α 1=1)
    {q : ℝ} (hq : q ∈ Ico (0:ℝ) 1) (hcont : ContinuousAt α q) :
    Tendsto (fun n => ∫ w, coerciveJetPolynomial (positiveGridSampleCoefficient α q n)
      (positiveGridSampleJet W β α q n 2 w) (positiveGridSampleJet W β α q n 3 w)
      (positiveGridSampleJet W β α q n 4 w) ∂W.law) atTop
      (𝓝 (∫ w, coerciveJetPolynomial (α q) (actualCDFSampleJet W β α ha h1 q 2 w)
        (actualCDFSampleJet W β α ha h1 q 3 w) (actualCDFSampleJet W β α ha h1 q 4 w) ∂W.law)) := by
  let := W.isProbability
  obtain ⟨A,hA,hBA⟩ := positiveGridSampleJet_bound W β hβ α ha hq 0
  obtain ⟨B,hB,hBB⟩ := positiveGridSampleJet_bound W β hβ α ha hq 1
  obtain ⟨C,hC,hBC⟩ := positiveGridSampleJet_bound W β hβ α ha hq 2
  have hm (n : ℕ) : AEStronglyMeasurable (fun w => coerciveJetPolynomial
      (positiveGridSampleCoefficient α q n) (positiveGridSampleJet W β α q n 2 w)
      (positiveGridSampleJet W β α q n 3 w) (positiveGridSampleJet W β α q n 4 w)) W.law := by
    have h2 := positiveGridSampleJet_measurable W β hβ α ha hq n 2
    have h3 := positiveGridSampleJet_measurable W β hβ α ha hq n 3
    have h4 := positiveGridSampleJet_measurable W β hβ α ha hq n 4
    exact (((measurable_const.mul (h4.pow_const 2)).sub
      ((measurable_const.mul h2).mul (h3.pow_const 2))).add
      (measurable_const.mul (h2.pow_const 4))).aestronglyMeasurable
  apply tendsto_integral_of_dominated_convergence
    (fun _ : Ω => C^2+12*A*B^2+6*A^4) hm (integrable_const _) _ _
  · intro n
    exact Eventually.of_forall (fun w => by
      simpa only [Real.norm_eq_abs,one_pow,mul_one,one_mul,Nat.reduceAdd] using coerciveJetPolynomial_bound
        (positiveGridSampleCoefficient_abs_le_one α ha q n) (hBA n w) (hBB n w) (hBC n w))
  · filter_upwards [positiveGridSampleJet_tendsto W β hβ α ha h1 hq 2,
      positiveGridSampleJet_tendsto W β hβ α ha h1 hq 3,
      positiveGridSampleJet_tendsto W β hβ α ha h1 hq 4] with w h2 h3 h4
    have hc := positiveGridCoefficient_tendsto α ha hq.1 hcont
    exact (((hc.pow 2).mul (h4.pow 2)).sub
      ((((hc.pow 3).const_mul 12).mul h2).mul (h3.pow 2))).add
      (((hc.pow 4).const_mul 6).mul (h2.pow 4))

theorem actualCDF_coercivity (W : BrownianSystem Ω) (β : ℝ) (hβ : β ≠ 0)
    (α : StieltjesFunction ℝ) (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (h1 : α 1=1)
    {q : ℝ} (hq : q ∈ Ioo (0:ℝ) 1) (hcont : ContinuousAt α q) :
    (1/1000:ℝ)*(∫ w, quarticJetPolynomial (α q)
      (actualCDFSampleJet W β α ha h1 q 2 w) ∂W.law) ≤
      ∫ w, coerciveJetPolynomial (α q) (actualCDFSampleJet W β α ha h1 q 2 w)
        (actualCDFSampleJet W β α ha h1 q 3 w) (actualCDFSampleJet W β α ha h1 q 4 w) ∂W.law := by
  apply le_of_tendsto_of_tendsto
    ((positiveGridQuartic_integral_tendsto W β hβ α ha h1 ⟨hq.1.le,hq.2⟩ hcont).const_mul (1/1000:ℝ))
    (positiveGridCoercive_integral_tendsto W β hβ α ha h1 ⟨hq.1.le,hq.2⟩ hcont)
  filter_upwards [positiveGridIndex_pos_eventually hq.1] with n hn
  exact positiveGridSample_coercivity W β hβ α ha ⟨hq.1.le,hq.2⟩ n hn

end SKConstants.ParisiFullSupport
