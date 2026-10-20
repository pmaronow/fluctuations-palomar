module

public import ComparisonWholeUnitPhysicalSampling
public import ComparisonWholeUnitCoupling

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped BigOperators NNReal ENNReal

def physicalSelectedUnitMass {ι U : Type} [Fintype U] [DecidableEq U]
    (steps : List (GaussianStep ι)) (J : Finset (Fin (steps.length+1)))
    (unit : Fin (steps.length+1) → U) (u : U) : ℝ :=
  ∑k,if k∈J ∧ unit k=u then pathMassDifferences steps 0 k else 0

def physicalSelectedUnitEnergy (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (q0 : FeatureIndex n → ℝ≥0)
    (J : Finset (Fin (steps.length+1))) {U : Type} [Fintype U] [DecidableEq U]
    (unit : Fin (steps.length+1) → U) (u : U) : ℝ :=
  ∑k,if k∈J ∧ unit k=u then pathMassDifferences steps 0 k*
    ∫z,physicalCutSusceptibility n steps id k.val z
      ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps else 0

theorem selected_mass_grouping {ι U : Type} [Fintype U] [DecidableEq U]
    (steps : List (GaussianStep ι)) (J : Finset (Fin (steps.length+1)))
    (unit : Fin (steps.length+1) → U) (F : U → ℝ) :
    (∑k,pathMassDifferences steps 0 k*(if k∈J then F (unit k) else 0))=
      ∑u,physicalSelectedUnitMass steps J unit u*F u := by
  unfold physicalSelectedUnitMass
  simp only [Finset.sum_mul,ite_mul,zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k∈J
  · simp only [hk,true_and,ite_true]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ,ite_true]
  · simp only [hk,false_and,ite_false,Finset.sum_const_zero,mul_zero]

theorem physical_selected_unit_weight_normalized {ι U : Type} [Fintype U] [DecidableEq U]
    (steps : List (GaussianStep ι)) (J : Finset (Fin (steps.length+1)))
    (unit : Fin (steps.length+1) → U) (part : U → ℝ) {m : ℝ}
    (hmass : ∀u,0 < physicalSelectedUnitMass steps J unit u)
    (hm : 0 < m) (hsum : ∑u,part u=m) :
    (∑k,pathMassDifferences steps 0 k*
      (if k∈J then part (unit k)/(m*physicalSelectedUnitMass steps J unit (unit k)) else 0))=1 := by
  rw [selected_mass_grouping steps J unit
    (fun u=>part u/(m*physicalSelectedUnitMass steps J unit u))]
  calc
    _ = ∑u,part u/m := Finset.sum_congr rfl (fun u _=>by field_simp [(hmass u).ne',hm.ne'])
    _ = _ := by rw [← Finset.sum_div,hsum,div_self hm.ne']

theorem physical_selected_unit_variance_le (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (J : Finset (Fin (steps.length+1)))
    {U : Type} [Fintype U] [DecidableEq U] (unit : Fin (steps.length+1) → U)
    (mass part : U → ℝ) {m tau : ℝ}
    (hmass : ∀u,0 < mass u) (hpart0 : ∀u,0 ≤ part u) (hpart : ∀u,part u ≤ mass u)
    (htau : 0 ≤ tau)
    (henergy : ∀u,physicalSelectedUnitEnergy n steps q0 J unit u ≤ tau*mass u)
    (hm : 0 < m) (hsum : ∑u,part u=m) :
    variance (fun z=>(physicalPinnedPair (uniformWeight n) (finiteFeature n) (spinSource n)
      steps 0 (fun k=>if k∈J then part (unit k)/(m*mass (unit k)) else 0) z.1 z.2).1)
      (rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps) ≤ tau/m := by
  let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps
  let w := fun u=>part u/(m*mass u)
  let weight := fun k:Fin (steps.length+1)=>if k∈J then w (unit k) else 0
  let d := Fintype.card (Fin (steps.length+1) × FeatureIndex n)
  let e : Fin d ≃ Fin (steps.length+1) × FeatureIndex n := (Fintype.equivFin _).symm
  have h := physical_planted_variance_le q0 steps ha e weight
  dsimp only [Function.uncurry] at h
  change _ ≤ ∫z,(physicalPinnedPair (uniformWeight n) (finiteFeature n) (spinSource n)
    steps 0 weight z.1 z.2).2 ∂mu at h
  have hPair (z : PhysicalPathState (FeatureIndex n → ℝ) n steps) :
      (physicalPinnedPair (uniformWeight n) (finiteFeature n) (spinSource n)
        steps 0 weight z.1 z.2).2=
      ∑k,pathMassDifferences steps 0 k*(weight k)^2*physicalCutSusceptibility n steps id k.val z :=
    physicalPinnedPair_snd_eq_sum n steps ha weight id z
  simp_rw [hPair] at h
  have := rootedHierarchyPathLaw_probability (uniformWeight_pos n) (finiteFeature n) q0 steps ha
  have hI (k : Fin (steps.length+1)) : Integrable
      (fun z=>pathMassDifferences steps 0 k*(weight k)^2*physicalCutSusceptibility n steps id k.val z) mu :=
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
    by_cases hk : k∈J
    · simp only [hk,true_and,weight,ite_true]
      rw [Finset.sum_ite_eq]
      simp only [Finset.mem_univ,ite_true]
      ring
    · simp only [hk,false_and,weight,ite_false,zero_pow (by norm_num : (2:ℕ)≠0),
        mul_zero,zero_mul,Finset.sum_const_zero]
  rw [heq] at h
  exact h.trans (whole_unit_side_energy_le mass part (physicalSelectedUnitEnergy n steps q0 J unit)
    hmass hpart0 hpart htau henergy hm hsum)

theorem physical_selected_weight_variance_continuousOn (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (weight : ℝ → Fin (steps.length+1) → ℝ)
    (A : Set ℝ) (hw : ∀k,ContinuousOn (fun i=>weight i k) A) :
    ContinuousOn (fun i=>variance (fun z=>(physicalPinnedPair (uniformWeight n) (finiteFeature n)
      (spinSource n) steps 0 (weight i) z.1 z.2).1)
      (rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps)) A := by
  let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps
  let X := actualSpinPath n steps id
  have := rootedHierarchyPathLaw_probability (uniformWeight_pos n) (finiteFeature n) q0 steps ha
  have hY (k : Fin (steps.length+1)) : MemLp (terminalScore X (steps.length+1) k.val) 2 mu :=
    terminalScore_memLp (actualSpinPath_rooted_martingale n steps ha q0)
      (R:=1) (fun j=>ae_of_all _ (fun z=>actualSpinPath_norm_le n steps ha id j z)) _ _ _
  have he (i : ℝ) :
      (fun z=>(physicalPinnedPair (uniformWeight n) (finiteFeature n) (spinSource n)
        steps 0 (weight i) z.1 z.2).1)=
      (fun z=>∑k:Fin (steps.length+1),(pathMassDifferences steps 0 k*weight i k)*
        terminalScore X (steps.length+1) k.val z) := by
    funext z
    have hh := physicalPinnedPair_fst_eq_window n steps ha (weight i) id z
    simpa only [terminalWindow,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,X,id_eq] using hh
  simp_rw [he]
  apply WholeUnitSideKernel.variance_linearCombination_continuousOn mu _ _ _ hY
  intro k
  exact continuousOn_const.mul (hw k)

end OAI.SKFluctuations
