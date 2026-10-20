module
public import SKConstants.ParisiGridApproximation

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants.ParisiFullSupport
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.SK.Analytic

def parisiGridMesh (n : ℕ) : ℝ≥0 := 1/((n:ℝ≥0)+1)

lemma parisiGridMesh_pos (n : ℕ) : 0 < parisiGridMesh n := by unfold parisiGridMesh; positivity
lemma parisiGridMesh_horizon (n : ℕ) : ((n+1:ℕ):ℝ≥0)*parisiGridMesh n=1 := by
  unfold parisiGridMesh
  push_cast
  exact mul_one_div_cancel (by positivity : (n:ℝ≥0)+1 ≠ 0)
lemma parisiGridMesh_coe_tendsto : Tendsto (fun n => (parisiGridMesh n:ℝ)) atTop (𝓝 0) := by
  simpa only [parisiGridMesh,NNReal.coe_div,NNReal.coe_add,NNReal.coe_one,NNReal.coe_natCast] using
    (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)) atTop (𝓝 0))

def parisiGridFeedback (β : ℝ) (α : ℝ → ℝ) (n : ℕ) : BoundedLipschitzDrift :=
  finiteFeedback (regularDatum_softAbs (by norm_num : (1:ℝ) ≠ 0))
    (softAbs_lipschitz (by norm_num : (1:ℝ) ≠ 0))
    (gridCDFCoefficient α (parisiGridMesh n)) (Real.toNNReal (β^2)*parisiGridMesh n) (n+1) 0

theorem parisiGridFeedback_solution_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (β : ℝ) (hβ : β ≠ 0) (α : StieltjesFunction ℝ)
    (ha : ∀ r, α r ∈ Icc (0:ℝ) 1) (h1 : α 1=1)
    (v : ℝ≥0) (hv : (v:ℝ)<β^2) (w : Ω) :
    Tendsto (fun n => (parisiGridFeedback β α n).solution W.driver v w) atTop
      (𝓝 (finiteTemperatureCDFProcess W β α ha h1 v w)) := by
  let C := scalarTimeMassConstant β
  have hh0 := parisiGridMesh_coe_tendsto
  have hs0 : Tendsto (fun n => Real.sqrt (parisiGridMesh n:ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hh0
  have hbound : Tendsto (fun n => 2*(β^2*(parisiGridMesh n:ℝ)+
      (v:ℝ)*(2*C*Real.sqrt (parisiGridMesh n:ℝ)+2*Real.sqrt (parisiGridMesh n:ℝ)))*Real.exp (3*(v:ℝ)))
      atTop (𝓝 0) := by
    convert ((hh0.const_mul (β^2)).add
      (((hs0.const_mul (2*C)).add (hs0.const_mul 2)).const_mul (v:ℝ))).const_mul 2 |>.mul_const (Real.exp (3*(v:ℝ))) using 1 <;> simp
  have he n := finiteFeedback_grid_solution_error W β hβ α ha h1
    (parisiGridMesh n) (parisiGridMesh_pos n) (n+1) (parisiGridMesh_horizon n)
    v hv (Real.sqrt (parisiGridMesh n:ℝ)) (Real.sqrt_pos.mpr (by exact_mod_cast parisiGridMesh_pos n)) v le_rfl w
  have hquot (n : ℕ) : (parisiGridMesh n:ℝ)/Real.sqrt (parisiGridMesh n:ℝ) = Real.sqrt (parisiGridMesh n:ℝ) := by
    apply (div_eq_iff (Real.sqrt_pos.mpr (by exact_mod_cast parisiGridMesh_pos n)).ne').mpr
    nlinarith [Real.sq_sqrt (parisiGridMesh n).coe_nonneg]
  have H : Tendsto (fun n => |(parisiGridFeedback β α n).solution W.driver v w-
      finiteTemperatureCDFProcess W β α ha h1 v w|) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => abs_nonneg _) _ hbound
    intro n
    have H := he n
    rw [show 2*(scalarTimeMassConstant β*(parisiGridMesh n:ℝ))/Real.sqrt (parisiGridMesh n:ℝ)=
      2*C*Real.sqrt (parisiGridMesh n:ℝ) by
        calc
          _ = 2*C*((parisiGridMesh n:ℝ)/Real.sqrt (parisiGridMesh n:ℝ)) := by dsimp [C]; ring
          _ = _ := by rw [hquot n]] at H
    exact H
  exact (tendsto_iff_dist_tendsto_zero).mpr (by simpa only [Real.dist_eq] using H)

end SKConstants.ParisiFullSupport
