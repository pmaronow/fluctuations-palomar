module
public import SKConstants.ParisiTanhDensityContinuation
public import SKConstants.ParisiFullScalarProcess
public import SKConstants.ParisiCDFPositiveGridPath

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.SK.Analytic ParisiFullSupport
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type*} [MeasurableSpace Ω]
local instance ParisiPostMomentRatio_localInstance1 (W : BrownianSystem Ω) : IsProbabilityMeasure W.law := W.isProbability

lemma positiveGridFeedback_integral_boundedSmooth_tendsto
    (W : BrownianSystem Ω) (β : ℝ) (hβ : β ≠ 0) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (h1 : α 1=1)
    {q : ℝ} (hq : q ∈ Ico (0:ℝ) 1) {g : ℝ → ℝ} (hg : BoundedSmooth g) :
    Tendsto (fun n => ∫ w,g ((positiveGridFeedback β α n).solution W.driver
      (positiveGridPhysicalTime β q n) w) ∂W.law) atTop
      (𝓝 (∫ w,g (finiteTemperatureCDFProcess W β α ha h1 (Real.toNNReal (β^2*q)) w) ∂W.law)) := by
  obtain ⟨C,hC⟩ := hg.bound
  apply tendsto_integral_of_dominated_convergence (fun _ : Ω => (C:ℝ))
    (fun n => (hg.smooth.continuous.measurable.comp
      ((positiveGridFeedback β α n).solution_measurable W _)).aestronglyMeasurable)
    (integrable_const _) _ _
  · intro n
    exact ae_of_all _ (fun w => by simpa only [Real.norm_eq_abs,Function.comp_def] using hC _)
  · filter_upwards [positiveGridFeedback_sample_tendsto W β hβ α ha h1 hq] with w hw
    exact hg.smooth.continuous.continuousAt.tendsto.comp hw

lemma actualParisiPositiveGrid_tail_one (β : ℝ) (hβ : 1 < β)
    {q : ℝ} (hq : parisiEquilibriumSupportEndpoint β < q) (hq0 : 0 ≤ q) :
    ∀ᶠ n in atTop, ∀ j, positiveGridIndex q n ≤ j →
      gridCDFCoefficient (positiveGridCDF (cdf (parisiEquilibriumMeasure β:Measure ℝ)) n)
        (parisiGridMesh n) j = 1 := by
  filter_upwards [(positiveGridTime_tendsto hq0).eventually (lt_mem_nhds hq)] with n hn
  intro j hj
  have hx : parisiEquilibriumSupportEndpoint β ≤ (j:ℝ)*(parisiGridMesh n:ℝ) := by
    apply hn.le.trans
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hj) (parisiGridMesh n).coe_nonneg
  have H := actualParisiEquilibrium_cdf_one_after_support β hβ _ hx
  change Real.toNNReal (((parisiGridMesh n:ℝ)+
    cdf (parisiEquilibriumMeasure β:Measure ℝ) ((j:ℝ)*(parisiGridMesh n:ℝ)))/(1+(parisiGridMesh n:ℝ)))=1
  rw [H]
  have E : ((parisiGridMesh n:ℝ)+1)/(1+(parisiGridMesh n:ℝ))=1 := by
    rw [add_comm]
    exact div_self (by positivity)
  rw [E,Real.toNNReal_one]

lemma actualParisiFullProcess_postKernel_moment_ge
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) {q t : ℝ}
    (hq : q ∈ Ioo (parisiEquilibriumSupportEndpoint β) 1) (ht : 0 < t) :
    (3/4:ℝ)*(∫ w,varianceTilted 1 t (softAbs 1) (fun y => (scalarDefect y)^2)
      (actualParisiFullScalarProcess W β (Real.toNNReal (β^2*q)) w) ∂W.law) ≤
      ∫ w,varianceTilted 1 t (softAbs 1) (fun y => (scalarDefect y)^3)
        (actualParisiFullScalarProcess W β (Real.toNNReal (β^2*q)) w) ∂W.law := by
  let α := cdf (parisiEquilibriumMeasure β:Measure ℝ)
  have hb : β ≠ 0 := (zero_lt_one.trans hβ).ne'
  have ha : ∀ z, α z ∈ Icc (0:ℝ) 1 := fun z => ⟨cdf_nonneg _ z,cdf_le_one _ z⟩
  have h1 : α 1=1 := supported_probability_cdf_one (parisiEquilibriumMeasure β)
    (parisiEquilibriumMeasure_upstream_spec β).1
  have hq0 : 0 < q := (parisiEquilibriumSupportEndpoint_spec β hβ).1.1.trans hq.1
  have hq01 : q ∈ Ico (0:ℝ) 1 := ⟨hq0.le,hq.2⟩
  have hf := regularDatum_softAbs (by norm_num : (1:ℝ)≠0)
  have hLip := softAbs_lipschitz (by norm_num : (1:ℝ)≠0)
  have hg2 := (varianceTilted_family hf hLip (scalarDefect_boundedSmooth.pow 2)
    (by norm_num : (0:ℝ)≤1)).regular t
  have hg3 := (varianceTilted_family hf hLip (scalarDefect_boundedSmooth.pow 3)
    (by norm_num : (0:ℝ)≤1)).regular t
  apply le_of_tendsto_of_tendsto
    ((positiveGridFeedback_integral_boundedSmooth_tendsto W β hb α ha h1 hq01 hg2).const_mul (3/4:ℝ))
    (positiveGridFeedback_integral_boundedSmooth_tendsto W β hb α ha h1 hq01 hg3)
  filter_upwards [positiveGridIndex_pos_eventually hq0,
    actualParisiPositiveGrid_tail_one β hβ hq.1 hq0.le] with n hi hn
  let c := gridCDFCoefficient (positiveGridCDF α n) (parisiGridMesh n)
  let H := Real.toNNReal (β^2)*parisiGridMesh n
  have hc (j : ℕ) : 0 < (c j:ℝ) := by
    dsimp only [c,gridCDFCoefficient]
    rw [Real.coe_toNNReal _ (positiveGridCDF_bounds α ha n _).1]
    exact positiveGridCDF_pos α ha n _
  have hm : Monotone c := by
    intro i j hij
    apply Real.toNNReal_mono
    apply (positiveGridCDF α n).mono
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) (parisiGridMesh n).coe_nonneg
  have hcap (j : ℕ) : (c j:ℝ) ≤ 1 := by
    dsimp only [c,gridCDFCoefficient]
    rw [Real.coe_toNNReal _ (positiveGridCDF_bounds α ha n _).1]
    exact (positiveGridCDF_bounds α ha n _).2
  have hH : 0 < (H:ℝ) := by dsimp [H]; positivity [sq_pos_of_ne_zero hb,parisiGridMesh_pos n]
  have HH := finiteFeedback_postKernel_moment_ge W c hc hm hcap hH (n+1)
    (positiveGridIndex q n) hi (positiveGridIndex_lt hq01 n).le (hn _ le_rfl)
      (fun j hj _ => hn j hj) ht
  have he : (positiveGridIndex q n:ℝ≥0)*H = positiveGridPhysicalTime β q n := by
    dsimp [H,positiveGridPhysicalTime,positiveGridTime]
    ring
  rw [he] at HH
  exact HH

lemma actualParisiFullProcess_defect_pow_integral_continuous
    (W : BrownianSystem Ω) (β : ℝ) (k : ℕ) :
    Continuous (fun v : ℝ => ∫ w,scalarDefect
      (actualParisiFullScalarProcess W β v.toNNReal w)^k ∂W.law) := by
  apply continuous_of_dominated (bound := fun _ : Ω => (1:ℝ))
  · intro v
    exact ((measurable_scalarDefect.comp (measurable_actualParisiPreContinuationField W β _)).pow_const k).aestronglyMeasurable
  · intro v
    exact ae_of_all _ (fun w => by
      rw [norm_pow]
      simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _) (norm_scalarDefect_le_one _) k)
  · exact integrable_const _
  · filter_upwards [(actualParisiFullScalarDrift β).solution_continuous_ae W] with w hw
    exact (scalarDefect_boundedSmooth.smooth.continuous.comp
      (hw.comp (by fun_prop : Continuous Real.toNNReal))).pow k

theorem actualParisiFullProcess_post_third_moment_ge
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (s : ℝ)
    (hs : β^2*parisiEquilibriumSupportEndpoint β ≤ s) :
    (3/4:ℝ)*(∫ w,scalarDefect (actualParisiFullScalarProcess W β s.toNNReal w)^2 ∂W.law) ≤
      ∫ w,scalarDefect (actualParisiFullScalarProcess W β s.toNNReal w)^3 ∂W.law := by
  let Q := parisiEquilibriumSupportEndpoint β
  let V := β^2*Q
  have hb : 0 < β^2 := sq_pos_of_pos (zero_lt_one.trans hβ)
  have hQ := (parisiEquilibriumSupportEndpoint_spec β hβ).1
  have hi : Ioi V ⊆ {v : ℝ | (3/4:ℝ)*(∫ w,scalarDefect
      (actualParisiFullScalarProcess W β v.toNNReal w)^2 ∂W.law) ≤
        ∫ w,scalarDefect (actualParisiFullScalarProcess W β v.toNNReal w)^3 ∂W.law} := by
    intro v hv
    change V < v at hv
    have hmin : Q < min (v/β^2) 1 := lt_min
      ((lt_div_iff₀ hb).mpr (by simpa only [V,mul_comm] using hv)) hQ.2
    let q := (Q+min (v/β^2) 1)/2
    have hq : q ∈ Ioo Q 1 := by dsimp [q]; constructor <;> linarith [min_le_right (v/β^2) 1]
    have hqv : β^2*q < v := by
      rw [mul_comm]
      apply (lt_div_iff₀ hb).mp
      dsimp [q]
      linarith [min_le_left (v/β^2) 1]
    have hq0 : 0 < q := hQ.1.trans hq.1
    let a := Real.toNNReal (β^2*q)
    let T := Real.toNNReal v
    have hv0 : 0 ≤ v := (mul_pos hb hq0).le.trans hqv.le
    have haT : a ≤ T := Real.toNNReal_mono hqv.le
    have ha : (a:ℝ)=β^2*q := Real.coe_toNNReal _ (mul_pos hb hq0).le
    have hT : (T:ℝ)=v := Real.coe_toNNReal _ hv0
    have ht : 0 < (T:ℝ)-(a:ℝ) := by rw [hT,ha]; linarith
    have hmatch : ∀ r ∈ Ico (a:ℝ) T, ∀ x,
        (actualParisiFullScalarDrift β).f r x = deriv (varianceLogHeat 1 ((T:ℝ)-r) (softAbs 1)) x := by
      intro r hr x
      rw [actualParisiFullScalarDrift_eq_tanh_after_support β hβ r (by
        rw [ha] at hr
        change β^2*Q ≤ r
        nlinarith [hr.1,hq.1]),deriv_varianceLogHeat_one_softAbs (by linarith [hr.2])]
    have hf := regularDatum_softAbs (by norm_num : (1:ℝ)≠0)
    have hLip := softAbs_lipschitz (by norm_num : (1:ℝ)≠0)
    have he (k : ℕ) := expected_transition_tiltedMean W (actualParisiFullScalarDrift β)
      hf hLip (scalarDefect_boundedSmooth.pow k) (by norm_num : (0:ℝ)≤1) haT
      (by simpa only [one_mul] using hmatch)
    have H := actualParisiFullProcess_postKernel_moment_ge W β hβ hq ht
    change (3/4:ℝ)*(∫ w,scalarDefect
      ((actualParisiFullScalarDrift β).solution W.driver T w)^2 ∂W.law) ≤
        ∫ w,scalarDefect ((actualParisiFullScalarDrift β).solution W.driver T w)^3 ∂W.law
    rw [he 2,he 3]
    exact H
  have hc : IsClosed {v : ℝ | (3/4:ℝ)*(∫ w,scalarDefect
      (actualParisiFullScalarProcess W β v.toNNReal w)^2 ∂W.law) ≤
        ∫ w,scalarDefect (actualParisiFullScalarProcess W β v.toNNReal w)^3 ∂W.law} :=
    isClosed_le ((actualParisiFullProcess_defect_pow_integral_continuous W β 2).const_mul (3/4:ℝ))
      (actualParisiFullProcess_defect_pow_integral_continuous W β 3)
  have H := closure_minimal hi hc
  rw [closure_Ioi] at H
  exact H hs

end SKConstants
