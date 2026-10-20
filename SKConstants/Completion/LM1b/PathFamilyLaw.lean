module
public import SKConstants.ScalarUniformPathLaw

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators
namespace SKConstants.M1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {κ Ω A : Type*} [Fintype κ] [MeasurableSpace Ω] [MeasurableSpace A]

def pathFamilyIncrements (H : ℝ≥0) (n : ℕ) (p : κ → ScalarContinuousPath H) :
    κ × Fin (n+1) → ℝ := fun j =>
  IccExtend H.coe_nonneg (p j.1) (((j.2.val+1 : ℕ) : ℝ)*(scalarPathUniformStep H n : ℝ)) -
    IccExtend H.coe_nonneg (p j.1) ((j.2 : ℝ)*(scalarPathUniformStep H n : ℝ))

omit [Fintype κ] in
theorem measurable_pathFamilyIncrements (H : ℝ≥0) (n : ℕ) :
    Measurable (pathFamilyIncrements (κ := κ) H n) := by
  apply Measurable.of_eval
  intro j
  exact ((ContinuousMap.measurable_eval _).comp (measurable_pi_apply j.1)).sub
    ((ContinuousMap.measurable_eval _).comp (measurable_pi_apply j.1))

def pathFamilyDenseSamples (H : ℝ≥0) (p : κ → ScalarContinuousPath H) : κ × ℕ → ℝ :=
  fun j => scalarPathDenseSamples H (p j.1) j.2

theorem pathFamilyDenseSamples_measurableEmbedding (H : ℝ≥0) :
    MeasurableEmbedding (pathFamilyDenseSamples (κ := κ) H) := by
  apply Measurable.measurableEmbedding
  · exact Measurable.of_eval fun j =>
      (ContinuousMap.measurable_eval _).comp (measurable_pi_apply j.1)
  · intro p q he
    funext k
    apply (scalarPathDenseSamples_measurableEmbedding H).injective
    funext j
    exact congrFun he (k,j)

theorem pathFamily_law_of_uniform_increments
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure A) [IsProbabilityMeasure Q]
    (H : ℝ≥0) (hH : 0 < H)
    (X : Ω → κ → ScalarContinuousPath H) (Y : A → κ → ScalarContinuousPath H)
    (hX : Measurable X) (hY : Measurable Y)
    (hX0 : ∀ᵐ w ∂P, ∀ k, X w k ⟨0,le_rfl,H.coe_nonneg⟩ = 0)
    (hY0 : ∀ᵐ w ∂Q, ∀ k, Y w k ⟨0,le_rfl,H.coe_nonneg⟩ = 0)
    (hgrid : ∀ n, P.map (pathFamilyIncrements H n ∘ X) =
      Q.map (pathFamilyIncrements H n ∘ Y)) : P.map X = Q.map Y := by
  let S := pathFamilyDenseSamples (κ := κ) H
  have hS := pathFamilyDenseSamples_measurableEmbedding (κ := κ) H
  have he (I : Finset (κ × ℕ)) :
      P.map (fun w => I.restrict (S (X w))) = Q.map (fun w => I.restrict (S (Y w))) := by
    let t : I → Icc (0 : ℝ) (H : ℝ) := fun i => scalarPathDenseTimes H i.val.2
    let J (n : ℕ) (z : κ × Fin (n+1) → ℝ) : I → ℝ := fun i =>
      ∑ j : Fin (n+1), if j.val < ⌊(t i : ℝ)/(scalarPathUniformStep H n : ℝ)⌋₊
        then z (i.val.1,j) else 0
    have hJ (n : ℕ) : Measurable (J n) := by
      apply Measurable.of_eval
      intro i
      exact Finset.measurable_fun_sum _ (fun j _ => by split_ifs <;> fun_prop)
    have hlaw (n : ℕ) : P.map (J n ∘ pathFamilyIncrements H n ∘ X) =
        Q.map (J n ∘ pathFamilyIncrements H n ∘ Y) := by
      rw [← Measure.map_map (hJ n) ((measurable_pathFamilyIncrements H n).comp hX),
        hgrid n, Measure.map_map (hJ n) ((measurable_pathFamilyIncrements H n).comp hY)]
    have hlim (p : κ → ScalarContinuousPath H) (hp : ∀ k, p k ⟨0,le_rfl,H.coe_nonneg⟩ = 0) :
        Tendsto (fun n => J n (pathFamilyIncrements H n p)) atTop (𝓝 (I.restrict (S p))) := by
      apply tendsto_pi_nhds.mpr
      intro i
      simp only [J, pathFamilyIncrements]
      simp_rw [scalarPathUniformPrefix_sum H _ _ (scalarPathUniformIndex_bound hH _ (t i)), hp, sub_zero]
      have ht := ((p i.val.1).continuous.Icc_extend' (h := H.coe_nonneg)).continuousAt.tendsto.comp
        (scalarPathUniformFloorTime_tendsto hH (t i))
      simpa only [Function.comp_def, IccExtend, projIcc_of_mem _ (t i).property,
        Finset.restrict_def, S, pathFamilyDenseSamples, scalarPathDenseSamples, t] using ht
    exact scalarLaw_eq_of_ae_tendsto_comparison P Q
      (fun n => J n ∘ pathFamilyIncrements H n ∘ X)
      (fun n => J n ∘ pathFamilyIncrements H n ∘ Y)
      (fun w => I.restrict (S (X w))) (fun w => I.restrict (S (Y w)))
      (fun n => ((hJ n).comp ((measurable_pathFamilyIncrements H n).comp hX)).aemeasurable)
      (fun n => ((hJ n).comp ((measurable_pathFamilyIncrements H n).comp hY)).aemeasurable)
      hlaw
      ((Finset.measurable_restrict I).comp (hS.measurable.comp hX)).aemeasurable
      ((Finset.measurable_restrict I).comp (hS.measurable.comp hY)).aemeasurable
      (hX0.mono fun w hw => hlim (X w) hw) (hY0.mono fun w hw => hlim (Y w) hw)
  have hP : IsProjectiveLimit (P.map (S ∘ X))
      (fun I : Finset (κ × ℕ) => P.map (fun w => I.restrict (S (X w)))) :=
    isProjectiveLimit_map (hS.measurable.comp hX).aemeasurable
  have hQ : IsProjectiveLimit (Q.map (S ∘ Y))
      (fun I : Finset (κ × ℕ) => P.map (fun w => I.restrict (S (X w)))) := by
    intro I
    rw [Measure.map_map (Finset.measurable_restrict I) (hS.measurable.comp hY)]
    exact (he I).symm
  apply hS.map_injective
  rw [Measure.map_map hS.measurable hX, Measure.map_map hS.measurable hY]
  exact hP.unique hQ

end SKConstants.M1
