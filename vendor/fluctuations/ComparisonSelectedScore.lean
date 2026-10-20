module

public import ComparisonEffectiveEvaluation

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped BigOperators NNReal ENNReal
namespace WholeUnitSideKernel

theorem weighted_mean_sub_abs_le {I : Type*} [Fintype I]
    (mass V : I → ℝ) {c eta : ℝ} (hmass : ∀i,0 ≤ mass i)
    (hnorm : ∑i,mass i=1) (hV : ∀i,mass i≠0 → |V i-c| ≤ eta) :
    |(∑i,mass i*V i)-c| ≤ eta := by
  have he : (∑i,mass i*V i)-c=∑i,mass i*(V i-c) := by
    simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,hnorm,one_mul]
  rw [he]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑i,mass i*eta := Finset.sum_le_sum (fun i _=>by
      rw [abs_mul,abs_of_nonneg (hmass i)]
      by_cases hz:mass i=0
      · simp only [hz,zero_mul]; exact le_rfl
      · exact mul_le_mul_of_nonneg_left (hV i hz) (hmass i))
    _ = eta := by rw [← Finset.sum_mul,hnorm,one_mul]

def selectedLeftWeight {ι : Type} {K : ℕ} (steps : List (GaussianStep ι))
    (J : Finset (Fin (steps.length+1))) (unit : Fin (steps.length+1) → Fin K)
    (x : ℕ → ℝ) (a t : ℝ) (k : Fin (steps.length+1)) : ℝ :=
  if k∈J then left a (x (unit k)) (x ((unit k).val+1)) t else 0

def selectedRightWeight {ι : Type} {K : ℕ} (steps : List (GaussianStep ι))
    (J : Finset (Fin (steps.length+1))) (unit : Fin (steps.length+1) → Fin K)
    (x : ℕ → ℝ) (b t : ℝ) (k : Fin (steps.length+1)) : ℝ :=
  if k∈J then right b (x (unit k)) (x ((unit k).val+1)) t else 0

def selectedScoreVariance (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    (q0 : FeatureIndex n → ℝ≥0) (weight : Fin (steps.length+1) → ℝ) : ℝ :=
  variance (fun z=>(physicalPinnedPair (uniformWeight n) (finiteFeature n) (spinSource n)
    steps 0 weight z.1 z.2).1) (rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps)

theorem selectedLeftCoefficient_eq {ι : Type} {K : ℕ} (steps : List (GaussianStep ι))
    (J : Finset (Fin (steps.length+1))) (unit : Fin (steps.length+1) → Fin K)
    (x : ℕ → ℝ) (a t : ℝ) (k : Fin (steps.length+1)) :
    pathMassDifferences steps 0 k*selectedLeftWeight steps J unit x a t k=
      physicalSelectedCellMass steps J k*left a (x (unit k)) (x ((unit k).val+1)) t := by
  by_cases hk:k∈J <;> simp [selectedLeftWeight,physicalSelectedCellMass,hk]

theorem selectedRightCoefficient_eq {ι : Type} {K : ℕ} (steps : List (GaussianStep ι))
    (J : Finset (Fin (steps.length+1))) (unit : Fin (steps.length+1) → Fin K)
    (x : ℕ → ℝ) (b t : ℝ) (k : Fin (steps.length+1)) :
    pathMassDifferences steps 0 k*selectedRightWeight steps J unit x b t k=
      physicalSelectedCellMass steps J k*right b (x (unit k)) (x ((unit k).val+1)) t := by
  by_cases hk:k∈J <;> simp [selectedRightWeight,physicalSelectedCellMass,hk]

theorem physical_selected_score_at_evaluation (n K : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (J : Finset (Fin (steps.length+1)))
    (unit : Fin (steps.length+1) → Fin K) (x : ℕ → ℝ) {a b t eta : ℝ}
    (hstart : x 0=a) (hend : x K=b) (hat : a < t) (htb : t < b)
    (hx : ∀u:Fin K,x u < x (u.val+1))
    (hmass : ∀u:Fin K,physicalSelectedUnitMass steps J unit u=x (u.val+1)-x u)
    (heta : 0 ≤ eta)
    (hS : ∀i∈J,∀j∈J,
      |physicalPathSecondMoment n steps q0 j.val-physicalPathSecondMoment n steps q0 i.val| ≤ eta)
    (i : Fin (steps.length+1)) (hi : i∈J) :
    let mass := physicalSelectedCellMass steps J
    let km := selectedLeftWeight steps J unit x a t
    let kp := selectedRightWeight steps J unit x b t
    let am := fun j=>mass j*left a (x (unit j)) (x ((unit j).val+1)) t
    let ap := fun j=>mass j*right b (x (unit j)) (x ((unit j).val+1)) t
    actualCutReplicaDefect n steps q0 i.val (physicalPathSecondMoment n steps q0 i.val) ≤
      24*selectedScoreVariance n steps q0 km+24*selectedScoreVariance n steps q0 kp+6*eta^2+
        32*(∑j,am j*physicalSideNoiseMoment n steps q0 i.val j.val)+
        32*(∑j,ap j*physicalSideNoiseMoment n steps q0 i.val j.val)+
        8*(∑j,am j*(if i.val < j.val then physicalSideMovementMoment n steps q0 i.val j.val else 0))+
        8*(∑j,ap j*(if j.val < i.val then physicalSideMovementMoment n steps q0 i.val j.val else 0))+
        actualCutCovarianceEnergy n steps q0 i.val := by
  dsimp only
  let km := selectedLeftWeight steps J unit x a t
  let kp := selectedRightWeight steps J unit x b t
  have hkm j : 0 ≤ km j := by
    by_cases hj:j∈J
    · simpa only [km,selectedLeftWeight,hj,ite_true] using (left_bounds (hx _) hat).1
    · simp only [km,selectedLeftWeight,hj,ite_false]; exact le_rfl
  have hkp j : 0 ≤ kp j := by
    by_cases hj:j∈J
    · simpa only [kp,selectedRightWeight,hj,ite_true] using (right_bounds (hx _) htb).1
    · simp only [kp,selectedRightWeight,hj,ite_false]; exact le_rfl
  have hnm := physical_selected_left_weight_normalized n K steps J unit x hstart hend hat htb.le hx hmass
  have hnp := physical_selected_right_weight_normalized n K steps J unit x hstart hend hat.le htb hx hmass
  have hmean (w : Fin (steps.length+1) → ℝ) (hw : ∀j,0 ≤ w j)
      (hwn : ∑j,pathMassDifferences steps 0 j*w j=1)
      (hsupport : ∀j,j∉J → w j=0) :
      |(∑j,(pathMassDifferences steps 0 j*w j)*physicalPathSecondMoment n steps q0 j.val)-
        physicalPathSecondMoment n steps q0 i.val| ≤ eta := by
    apply weighted_mean_sub_abs_le _ _
      (fun j=>mul_nonneg (pathMassDifferences_nonneg steps ha j) (hw j)) hwn
    intro j hj
    apply hS i hi j
    by_contra hjnot
    apply hj
    simp only [hsupport j hjnot,mul_zero]
  have hmm := hmean km hkm hnm (fun j hj=>by simp [km,selectedLeftWeight,hj])
  have hmp := hmean kp hkp hnp (fun j hj=>by simp [kp,selectedRightWeight,hj])
  have h := physical_two_sided_actual_cut_score_ledger n steps ha q0 i.val (by omega)
    km kp hkm hkp hnm hnp heta hmm hmp
  dsimp only at h
  simp only [km,kp,selectedLeftCoefficient_eq,selectedRightCoefficient_eq] at h
  exact h

end WholeUnitSideKernel
end OAI.SKFluctuations
