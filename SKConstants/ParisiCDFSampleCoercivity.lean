module

public import SKConstants.ParisiCDFPositiveGridPath
public import SKConstants.ParisiCDFCoercivePolynomials

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace SKConstants.ParisiFullSupport

open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.SK.Analytic

variable {Ω : Type*} [MeasurableSpace Ω]

def positiveGridValue (β : ℝ) (α : StieltjesFunction ℝ) (q : ℝ) (n : ℕ) : ℝ → ℝ :=
  scalarCDFValue β (positiveGridFunction α n) (positiveGridTime q n)
    (Real.toNNReal (1-(positiveGridTime q n:ℝ)))

lemma positiveGridValue_eq_boundary (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) {q : ℝ} (hq : q ∈ Ico (0:ℝ) 1) (n : ℕ) :
    positiveGridValue β α q n =
      backwardBoundary (gridCDFCoefficient (positiveGridCDF α n) (parisiGridMesh n))
        (Real.toNNReal (β^2)*parisiGridMesh n) (softAbs 1) (n+1) (positiveGridIndex q n) := by
  let γ := positiveGridCDF α n
  let c := gridCDFCoefficient γ (parisiGridMesh n)
  let H := Real.toNNReal (β^2)*parisiGridMesh n
  have hf := regularDatum_softAbs (by norm_num : (1:ℝ)≠0)
  have hLip := softAbs_lipschitz (by norm_num : (1:ℝ)≠0)
  have Hgrid := finiteValue_grid_eq_scalarCDFValue γ γ.mono (positiveGridCDF_bounds α ha n)
    β (parisiGridMesh n) (parisiGridMesh_pos n) (n+1) (parisiGridMesh_horizon n)
    ⟨(positiveGridTime q n).coe_nonneg,(positiveGridTime_le hq.1 n).trans_lt hq.2⟩
  have he : β^2*(positiveGridTime q n:ℝ)=(positiveGridIndex q n:ℝ)*(H:ℝ) := by
    simp only [H,positiveGridTime,NNReal.coe_mul,NNReal.coe_natCast,
      Real.coe_toNNReal _ (sq_nonneg β)]
    ring
  have HS := finiteValue_shift hf hLip c H (positiveGridIndex_lt hq n).le 0
    (t := 0) le_rfl
  simp only [add_zero,Nat.zero_add,finiteValue_zero hf hLip] at HS
  change finiteValue c H (softAbs 1) (n+1) 0
    ((positiveGridIndex q n:ℝ)*H)=backwardBoundary c H (softAbs 1) (n+1) (positiveGridIndex q n) at HS
  rw [he] at Hgrid
  exact Hgrid.symm.trans HS

lemma positiveGridValue_smooth (β : ℝ) (hβ : β ≠ 0) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) {q : ℝ} (hq : q ∈ Ico (0:ℝ) 1) (n : ℕ) :
    ContDiff ℝ ∞ (positiveGridValue β α q n) := by
  rw [positiveGridValue_eq_boundary β α ha hq]
  exact (cascade_regular (regularDatum_softAbs (by norm_num : (1:ℝ)≠0))
    (softAbs_lipschitz (by norm_num : (1:ℝ)≠0)) _ _ _ _).smooth

def positiveGridSampleJet (W : BrownianSystem Ω) (β : ℝ) (α : StieltjesFunction ℝ)
    (q : ℝ) (n m : ℕ) (w : Ω) : ℝ :=
  iteratedDeriv m (positiveGridValue β α q n)
    ((positiveGridFeedback β α n).solution W.driver (positiveGridPhysicalTime β q n) w)

def actualCDFSampleJet (W : BrownianSystem Ω) (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (h1 : α 1=1) (q : ℝ) (m : ℕ) (w : Ω) : ℝ :=
  iteratedDeriv m (scalarCDFValue β α q (Real.toNNReal (1-q)))
    (finiteTemperatureCDFProcess W β α ha h1 (Real.toNNReal (β^2*q)) w)

lemma positiveGridSampleJet_measurable (W : BrownianSystem Ω) (β : ℝ) (hβ : β ≠ 0)
    (α : StieltjesFunction ℝ) (ha : ∀ z, α z ∈ Icc (0:ℝ) 1)
    {q : ℝ} (hq : q ∈ Ico (0:ℝ) 1) (n m : ℕ) :
    Measurable (positiveGridSampleJet W β α q n m) :=
  (contDiff_iteratedDeriv_infty (positiveGridValue_smooth β hβ α ha hq n) m).continuous.measurable.comp
    ((positiveGridFeedback β α n).solution_measurable W (positiveGridPhysicalTime β q n))

lemma positiveGridSampleJet_bound (W : BrownianSystem Ω) (β : ℝ) (hβ : β ≠ 0)
    (α : StieltjesFunction ℝ) (ha : ∀ z, α z ∈ Icc (0:ℝ) 1)
    {q : ℝ} (hq : q ∈ Ico (0:ℝ) 1) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n w, |positiveGridSampleJet W β α q n (m+2) w| ≤ C := by
  obtain ⟨C,hC,hB⟩ := scalarCDFValue_uniform_coefficient_time_derivative_bounds hβ
    (show 0<1-q by linarith [hq.2]) m
  refine ⟨C,hC,fun n w => ?_⟩
  apply hB (positiveGridFunction α n) (positiveGridFunction_bounds α ha n)
    (positiveGridFunction_mono α n) (positiveGridTime q n)
    (Real.toNNReal (1-(positiveGridTime q n:ℝ)))
  · rw [Real.coe_toNNReal _ (by linarith [positiveGridTime_le hq.1 n,hq.2])]
    linarith [positiveGridTime_le hq.1 n]
  · rw [Real.toNNReal_le_iff_le_coe,NNReal.coe_one]
    linarith [(positiveGridTime q n).coe_nonneg]

lemma positiveGridSampleJet_tendsto (W : BrownianSystem Ω) (β : ℝ) (hβ : β ≠ 0)
    (α : StieltjesFunction ℝ) (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (h1 : α 1=1)
    {q : ℝ} (hq : q ∈ Ico (0:ℝ) 1) (m : ℕ) :
    ∀ᵐ w ∂W.law, Tendsto (fun n => positiveGridSampleJet W β α q n m w) atTop
      (𝓝 (actualCDFSampleJet W β α ha h1 q m w)) := by
  have ht : 0 < (Real.toNNReal (1-q):ℝ) := by
    rw [Real.coe_toNNReal _ (by linarith [hq.2])]
    linarith [hq.2]
  have ht1 : Real.toNNReal (1-q) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe,NNReal.coe_one]
    linarith [hq.1]
  have hF := (scalarCDFValue_contDiff_and_higher_derivative_limit ha α.mono hβ q _ ht ht1).1
  filter_upwards [positiveGridFeedback_sample_tendsto W β hβ α ha h1 hq] with w hw
  exact (positiveGridValue_jets_tendsto β hβ α ha h1 hq m).tendsto_comp
    (contDiff_iteratedDeriv_infty hF m).continuous.continuousAt hw

def positiveGridSampleCoefficient (α : StieltjesFunction ℝ) (q : ℝ) (n : ℕ) : ℝ :=
  gridCDFCoefficient (positiveGridCDF α n) (parisiGridMesh n) (positiveGridIndex q n)

lemma positiveGridSampleCoefficient_abs_le_one (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (q : ℝ) (n : ℕ) :
    |positiveGridSampleCoefficient α q n| ≤ 1 := by
  unfold positiveGridSampleCoefficient gridCDFCoefficient
  rw [Real.coe_toNNReal _ (positiveGridCDF_bounds α ha n _).1,
    abs_of_nonneg (positiveGridCDF_bounds α ha n _).1]
  exact (positiveGridCDF_bounds α ha n _).2

theorem positiveGridSample_coercivity (W : BrownianSystem Ω) (β : ℝ) (hβ : β ≠ 0)
    (α : StieltjesFunction ℝ) (ha : ∀ z, α z ∈ Icc (0:ℝ) 1)
    {q : ℝ} (hq : q ∈ Ico (0:ℝ) 1) (n : ℕ) (hi : 0 < positiveGridIndex q n) :
    (1/1000:ℝ)*(∫ w, quarticJetPolynomial (positiveGridSampleCoefficient α q n)
      (positiveGridSampleJet W β α q n 2 w) ∂W.law) ≤
      ∫ w, coerciveJetPolynomial (positiveGridSampleCoefficient α q n)
        (positiveGridSampleJet W β α q n 2 w) (positiveGridSampleJet W β α q n 3 w)
        (positiveGridSampleJet W β α q n 4 w) ∂W.law := by
  let c := gridCDFCoefficient (positiveGridCDF α n) (parisiGridMesh n)
  let H := Real.toNNReal (β^2)*parisiGridMesh n
  have hc (i : ℕ) : 0 < (c i:ℝ) := by
    dsimp only [c,gridCDFCoefficient]
    rw [Real.coe_toNNReal _ (positiveGridCDF_bounds α ha n _).1]
    exact positiveGridCDF_pos α ha n _
  have hm : Monotone c := by
    intro i j hij
    apply Real.toNNReal_mono
    apply (positiveGridCDF α n).mono
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) (parisiGridMesh n).coe_nonneg
  have hM (i : ℕ) : (c i:ℝ) ≤ 1 := by
    dsimp only [c,gridCDFCoefficient]
    rw [Real.coe_toNNReal _ (positiveGridCDF_bounds α ha n _).1]
    exact (positiveGridCDF_bounds α ha n _).2
  have HH := finite_feedback_coercivity W c hc hm hM
    (show 0<(H:ℝ) by dsimp [H]; positivity [sq_pos_of_ne_zero hβ,parisiGridMesh_pos n])
    hi (positiveGridIndex_lt hq n).le
  dsimp only at HH
  have hF := positiveGridValue_smooth β hβ α ha hq n
  rw [positiveGridValue_eq_boundary β α ha hq n] at hF
  change ContDiff ℝ ∞ (backwardBoundary c H (softAbs 1) (n+1) (positiveGridIndex q n)) at hF
  have hVal : positiveGridValue β α q n =
    backwardBoundary c H (softAbs 1) (n+1) (positiveGridIndex q n) :=
      positiveGridValue_eq_boundary β α ha hq n
  simp_rw [quarticMoment_scaled hF,coercivePolynomial_scaled hF,←hVal] at HH
  have ht : (positiveGridIndex q n:ℝ≥0)*H=positiveGridPhysicalTime β q n := by
    dsimp [H,positiveGridPhysicalTime,positiveGridTime]
    ring
  rw [ht] at HH
  exact HH

end SKConstants.ParisiFullSupport
