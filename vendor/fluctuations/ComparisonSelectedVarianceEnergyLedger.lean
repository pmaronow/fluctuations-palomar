module

public import ComparisonSelectedVarianceMiddle

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped BigOperators NNReal ENNReal Topology

theorem physical_selected_weight_variance_le_energy (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (J : Finset (Fin (steps.length+1)))
    {U : Type} [Fintype U] [DecidableEq U] (unit : Fin (steps.length+1) → U) (w : U → ℝ) :
    variance (fun z=>(physicalPinnedPair (uniformWeight n) (finiteFeature n) (spinSource n)
      steps 0 (fun k=>if k∈J then w (unit k) else 0) z.1 z.2).1)
      (rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps) ≤
      ∑u,(w u)^2*physicalSelectedUnitEnergy n steps q0 J unit u := by
  let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps
  let weight := fun k:Fin (steps.length+1)=>if k∈J then w (unit k) else 0
  let dim := Fintype.card (Fin (steps.length+1) × FeatureIndex n)
  let e : Fin dim ≃ Fin (steps.length+1) × FeatureIndex n := (Fintype.equivFin _).symm
  have h := physical_planted_variance_le q0 steps ha e weight
  dsimp only [Function.uncurry] at h
  change _ ≤ ∫z,(physicalPinnedPair (uniformWeight n) (finiteFeature n) (spinSource n)
    steps 0 weight z.1 z.2).2 ∂mu at h
  have hPair (z:PhysicalPathState (FeatureIndex n → ℝ) n steps) :
      (physicalPinnedPair (uniformWeight n) (finiteFeature n) (spinSource n)
        steps 0 weight z.1 z.2).2=
      ∑k,pathMassDifferences steps 0 k*(weight k)^2*physicalCutSusceptibility n steps id k.val z :=
    physicalPinnedPair_snd_eq_sum n steps ha weight id z
  simp_rw [hPair] at h
  have := rootedHierarchyPathLaw_probability (uniformWeight_pos n) (finiteFeature n) q0 steps ha
  have hI k : Integrable (fun z=>pathMassDifferences steps 0 k*(weight k)^2*
      physicalCutSusceptibility n steps id k.val z) mu :=
    ((physicalCutSusceptibility_memLp n steps ha id measurable_id mu k.val 1).integrable le_rfl).const_mul _
  rw [integral_finsetSum Finset.univ (fun k _=>hI k)] at h
  simp only [integral_const_mul] at h
  have heq : (∑k,pathMassDifferences steps 0 k*(weight k)^2*
      ∫z,physicalCutSusceptibility n steps id k.val z ∂mu)=
      ∑u,(w u)^2*physicalSelectedUnitEnergy n steps q0 J unit u := by
    unfold physicalSelectedUnitEnergy
    simp only [Finset.mul_sum,mul_ite,mul_zero]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk:k∈J
    · simp only [hk,true_and,weight,ite_true]
      rw [Finset.sum_ite_eq]
      simp only [Finset.mem_univ,ite_true]
      ring
    · simp only [hk,false_and,weight,ite_false,zero_pow (by norm_num : (2:ℕ)≠0),
        mul_zero,zero_mul,Finset.sum_const_zero]
  rw [heq] at h
  exact h

theorem physical_selected_weight_variance_integral_le_energy (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (J : Finset (Fin (steps.length+1)))
    {U : Type} [Fintype U] [DecidableEq U] (unit : Fin (steps.length+1) → U)
    (w : ℝ → U → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hw : ∀u,ContinuousOn (fun t=>w t u) (Icc a b)) :
    (∫t in a..b,variance (fun z=>(physicalPinnedPair (uniformWeight n) (finiteFeature n)
      (spinSource n) steps 0 (fun k=>if k∈J then w t (unit k) else 0) z.1 z.2).1)
        (rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps)) ≤
      ∑u,physicalSelectedUnitEnergy n steps q0 J unit u*(∫t in a..b,(w t u)^2) := by
  have hV := physical_selected_weight_variance_continuousOn n steps ha q0
    (fun t k=>if k∈J then w t (unit k) else 0) (Icc a b) (fun k=>by
      by_cases hk:k∈J
      · simpa only [hk,ite_true] using hw (unit k)
      · simp only [hk,ite_false]; exact continuousOn_const)
  have hVI : IntervalIntegrable (fun t=>variance (fun z=>(physicalPinnedPair
      (uniformWeight n) (finiteFeature n) (spinSource n) steps 0
      (fun k=>if k∈J then w t (unit k) else 0) z.1 z.2).1)
      (rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps)) volume a b := by
    apply ContinuousOn.intervalIntegrable (μ:=volume)
    simpa only [uIcc_of_le hab] using hV
  have hI u : IntervalIntegrable (fun t=>(w t u)^2*physicalSelectedUnitEnergy n steps q0 J unit u) volume a b := by
    apply ContinuousOn.intervalIntegrable (μ:=volume)
    simpa only [uIcc_of_le hab,Pi.pow_apply] using (hw u).pow 2 |>.mul_const (physicalSelectedUnitEnergy n steps q0 J unit u)
  have hSI : IntervalIntegrable (fun t=>∑u,(w t u)^2*physicalSelectedUnitEnergy n steps q0 J unit u) volume a b := by
    convert IntervalIntegrable.sum Finset.univ (fun u _=>hI u) using 1
    funext t
    simp only [Finset.sum_apply]
  have hmono := intervalIntegral.integral_mono_on hab hVI hSI
    (fun t _=>physical_selected_weight_variance_le_energy n steps ha q0 J unit (w t))
  rw [intervalIntegral.integral_finset_sum (fun u _=>hI u)] at hmono
  simp only [intervalIntegral.integral_mul_const] at hmono
  simpa only [mul_comm] using hmono

end OAI.SKFluctuations
