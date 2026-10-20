module

public import SKConstants.ParisiCDFPositiveGrid

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace SKConstants.ParisiFullSupport

open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.SK.Analytic

def positiveGridFeedback (β : ℝ) (α : StieltjesFunction ℝ) (n : ℕ) : BoundedLipschitzDrift :=
  parisiGridFeedback β (positiveGridCDF α n) n

def positiveGridPhysicalTime (β q : ℝ) (n : ℕ) : ℝ≥0 :=
  Real.toNNReal (β^2)*positiveGridTime q n

lemma positiveGridPhysicalTime_le (β : ℝ) {q : ℝ} (hq0 : 0 ≤ q) (n : ℕ) :
    positiveGridPhysicalTime β q n ≤ Real.toNNReal (β^2*q) := by
  apply NNReal.coe_le_coe.mp
  rw [positiveGridPhysicalTime, NNReal.coe_mul, Real.coe_toNNReal _ (sq_nonneg β),
    Real.coe_toNNReal _ (mul_nonneg (sq_nonneg β) hq0)]
  exact mul_le_mul_of_nonneg_left (positiveGridTime_le hq0 n) (sq_nonneg β)

lemma positiveGridPhysicalTime_tendsto (β : ℝ) {q : ℝ} (hq0 : 0 ≤ q) :
    Tendsto (positiveGridPhysicalTime β q) atTop (𝓝 (Real.toNNReal (β^2*q))) := by
  apply tendsto_subtype_rng.mpr
  change Tendsto (fun n => ((Real.toNNReal (β^2)*positiveGridTime q n:ℝ≥0):ℝ)) atTop
    (𝓝 (Real.toNNReal (β^2*q):ℝ))
  simp only [NNReal.coe_mul,Real.coe_toNNReal _ (sq_nonneg β),
    Real.coe_toNNReal _ (mul_nonneg (sq_nonneg β) hq0)]
  exact (positiveGridTime_tendsto hq0).const_mul (β^2)

theorem positiveGridFeedback_uniform_error
    {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (β : ℝ) (hβ : β ≠ 0) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (h1 : α 1=1)
    (T : ℝ≥0) (hT : (T:ℝ)<β^2) (n : ℕ) (v : ℝ≥0) (hv : v ≤ T) (w : Ω) :
    |(positiveGridFeedback β α n).solution W.driver v w-
      finiteTemperatureCDFProcess W β α ha h1 v w| ≤
        2*(β^2*(parisiGridMesh n:ℝ)+(T:ℝ)*((parisiGridMesh n:ℝ)+
          2*(2*scalarTimeMassConstant β*Real.sqrt (parisiGridMesh n:ℝ)+
            2*Real.sqrt (parisiGridMesh n:ℝ))))*Real.exp (3*(T:ℝ)) := by
  let γ := positiveGridCDF α n
  let hγ := positiveGridCDF_bounds α ha n
  let hγ1 := positiveGridCDF_one α h1 n
  let η := Real.sqrt (parisiGridMesh n:ℝ)
  let D := 2*scalarTimeMassConstant β*η+2*η
  have hη : 0 < η := Real.sqrt_pos.mpr (by exact_mod_cast parisiGridMesh_pos n)
  have hD : 0 ≤ D := by dsimp [D]; positivity [scalarTimeMassConstant_nonneg β]
  have hquot : 2*(scalarTimeMassConstant β*(parisiGridMesh n:ℝ))/η+2*η=D := by
    have H : (parisiGridMesh n:ℝ)/η=η := by
      apply (div_eq_iff hη.ne').mpr
      dsimp only [η]
      nlinarith [Real.sq_sqrt (parisiGridMesh n).coe_nonneg]
    calc
      _ = 2*scalarTimeMassConstant β*((parisiGridMesh n:ℝ)/η)+2*η := by ring
      _ = _ := by rw [H]
  have HG := finiteFeedback_grid_solution_error W β hβ γ hγ hγ1
    (parisiGridMesh n) (parisiGridMesh_pos n) (n+1) (parisiGridMesh_horizon n)
    T hT η hη v hv w
  have HP := finiteTemperatureCDFProcess_error_of_uniform_coefficient W β α γ ha hγ h1 hγ1
    (parisiGridMesh n).coe_nonneg
    (positiveStieltjesCDF_error α ha (parisiGridMesh n) (parisiGridMesh n).coe_nonneg)
    η hη T v hv w
  rw [hquot] at HG
  have HP' : |finiteTemperatureCDFProcess W β γ hγ hγ1 v w-
      finiteTemperatureCDFProcess W β α ha h1 v w| ≤
        2*(T:ℝ)*((parisiGridMesh n:ℝ)+D)*Real.exp (3*(v:ℝ)) := by
    convert HP using 1
    have he : (parisiGridMesh n:ℝ)+2*(scalarTimeMassConstant β*(parisiGridMesh n:ℝ))/η+2*η =
        (parisiGridMesh n:ℝ)+D := by linarith [hquot]
    rw [he]
  have HG' : |(positiveGridFeedback β α n).solution W.driver v w-
      finiteTemperatureCDFProcess W β γ hγ hγ1 v w| ≤
        2*(β^2*(parisiGridMesh n:ℝ)+(T:ℝ)*D)*Real.exp (3*(T:ℝ)) := by
    apply HG.trans
    gcongr
  have HP'' : |finiteTemperatureCDFProcess W β γ hγ hγ1 v w-
      finiteTemperatureCDFProcess W β α ha h1 v w| ≤
        2*(T:ℝ)*((parisiGridMesh n:ℝ)+D)*Real.exp (3*(T:ℝ)) := by
    apply HP'.trans
    gcongr
  have H := (abs_sub_le ((positiveGridFeedback β α n).solution W.driver v w)
    (finiteTemperatureCDFProcess W β γ hγ hγ1 v w)
    (finiteTemperatureCDFProcess W β α ha h1 v w)).trans (add_le_add HG' HP'')
  convert H using 1
  dsimp only [D,η]
  ring

theorem positiveGridFeedback_sample_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (β : ℝ) (hβ : β ≠ 0) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (h1 : α 1=1) {q : ℝ} (hq : q ∈ Ico (0:ℝ) 1) :
    ∀ᵐ w ∂W.law,
      Tendsto (fun n => (positiveGridFeedback β α n).solution W.driver
        (positiveGridPhysicalTime β q n) w) atTop
        (𝓝 (finiteTemperatureCDFProcess W β α ha h1 (Real.toNNReal (β^2*q)) w)) := by
  let T := Real.toNNReal (β^2*q)
  have hT : (T:ℝ)<β^2 := by
    rw [Real.coe_toNNReal _ (mul_nonneg (sq_nonneg β) hq.1)]
    nlinarith [sq_pos_of_ne_zero hβ,hq.2]
  have hs : Tendsto (fun n => Real.sqrt (parisiGridMesh n:ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp parisiGridMesh_coe_tendsto
  have HE : Tendsto (fun n => 2*(β^2*(parisiGridMesh n:ℝ)+(T:ℝ)*((parisiGridMesh n:ℝ)+
      2*(2*scalarTimeMassConstant β*Real.sqrt (parisiGridMesh n:ℝ)+
        2*Real.sqrt (parisiGridMesh n:ℝ))))*Real.exp (3*(T:ℝ))) atTop (𝓝 0) := by
    convert ((parisiGridMesh_coe_tendsto.const_mul (β^2)).add
      ((parisiGridMesh_coe_tendsto.add
        (((hs.const_mul (2*scalarTimeMassConstant β)).add (hs.const_mul 2)).const_mul 2)).const_mul
        (T:ℝ))).const_mul 2 |>.mul_const (Real.exp (3*(T:ℝ))) using 1 <;> simp
  filter_upwards [finiteTemperatureCDFProcess_continuous_ae W β α ha h1] with w hw
  have HX := (hw.tendsto T).comp (positiveGridPhysicalTime_tendsto β hq.1)
  rw [Metric.tendsto_nhds] at HX ⊢
  intro ε hε
  filter_upwards [HE.eventually (gt_mem_nhds (show 0<ε/2 by positivity)),
    HX (ε/2) (by positivity)] with n hn hxn
  have H := positiveGridFeedback_uniform_error W β hβ α ha h1 T hT n
    (positiveGridPhysicalTime β q n) (positiveGridPhysicalTime_le β hq.1 n) w
  have HT := dist_triangle ((positiveGridFeedback β α n).solution W.driver
    (positiveGridPhysicalTime β q n) w)
    (finiteTemperatureCDFProcess W β α ha h1 (positiveGridPhysicalTime β q n) w)
    (finiteTemperatureCDFProcess W β α ha h1 T w)
  simp only [Real.dist_eq,Function.comp_def,T] at hxn HT ⊢
  linarith

end SKConstants.ParisiFullSupport
