module

public import ComparisonIntegratedEvaluationLedger
public import ComparisonActualDefectBounds
public import ComparisonSelectedVarianceMiddle

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.WholeUnitSideKernel
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped BigOperators NNReal ENNReal

theorem weighted_affine_sum_eq {I : Type*} [Fintype I]
    (mass A B : I → ℝ) (c d : ℝ) :
    (∑i,mass i*(c*A i+d*B i))=c*(∑i,mass i*A i)+d*(∑i,mass i*B i) := by
  simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
  apply congrArg₂ (·+·)
  all_goals
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem physical_selected_integrated_score_ledger (n K : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (J : Finset (Fin (steps.length+1)))
    (unit : Fin (steps.length+1) → Fin K) (x : ℕ → ℝ) {a b δ p q eta : ℝ}
    (hstart : x 0=a) (hend : x K=b) (hδ : 0 < δ)
    (hp : a+δ ≤ p) (hpq : p ≤ q) (hq : q ≤ b-δ)
    (hx : ∀u:Fin K,x u < x (u.val+1))
    (hmass : ∀u:Fin K,physicalSelectedUnitMass steps J unit u=x (u.val+1)-x u)
    (heta : 0 ≤ eta)
    (hS : ∀i∈J,∀j∈J,
      |physicalPathSecondMoment n steps q0 j.val-physicalPathSecondMoment n steps q0 i.val| ≤ eta) :
    let mass := physicalSelectedCellMass steps J
    let D := fun i:Fin (steps.length+1)=>actualCutReplicaDefect n steps q0 i.val
      (physicalPathSecondMoment n steps q0 i.val)
    let C := fun i:Fin (steps.length+1)=>actualCutCovarianceEnergy n steps q0 i.val
    let PL := fineCoupling mass unit (fun u v=>coarseLeft x a p q u v)
    let PR := fineCoupling mass unit (fun u v=>coarseRight x b p q u v)
    let AL := fun i j:Fin (steps.length+1)=>32*physicalSideNoiseMoment n steps q0 i.val j.val+
      8*(if i.val < j.val then physicalSideMovementMoment n steps q0 i.val j.val else 0)
    let AR := fun i j:Fin (steps.length+1)=>32*physicalSideNoiseMoment n steps q0 i.val j.val+
      8*(if j.val < i.val then physicalSideMovementMoment n steps q0 i.val j.val else 0)
    (∑i,mass i*D i) ≤
      24*(∫t in p..q,selectedScoreVariance n steps q0 (selectedLeftWeight steps J unit x a t))+
      24*(∫t in p..q,selectedScoreVariance n steps q0 (selectedRightWeight steps J unit x b t))+
      6*eta^2*(q-p)+(∑i,∑j,PL i j*AL i j)+(∑i,∑j,PR i j*AR i j)+
      (∑i,mass i*C i)+4*(b-a-(q-p)) := by
  dsimp only
  let mass := physicalSelectedCellMass steps J
  let D := fun i:Fin (steps.length+1)=>actualCutReplicaDefect n steps q0 i.val
    (physicalPathSecondMoment n steps q0 i.val)
  let C := fun i:Fin (steps.length+1)=>actualCutCovarianceEnergy n steps q0 i.val
  let VL := fun t=>selectedScoreVariance n steps q0 (selectedLeftWeight steps J unit x a t)
  let VR := fun t=>selectedScoreVariance n steps q0 (selectedRightWeight steps J unit x b t)
  let AL := fun i j:Fin (steps.length+1)=>32*physicalSideNoiseMoment n steps q0 i.val j.val+
    8*(if i.val < j.val then physicalSideMovementMoment n steps q0 i.val j.val else 0)
  let AR := fun i j:Fin (steps.length+1)=>32*physicalSideNoiseMoment n steps q0 i.val j.val+
    8*(if j.val < i.val then physicalSideMovementMoment n steps q0 i.val j.val else 0)
  have hm0 := physicalSelectedCellMass_nonneg steps ha J
  have hmu u := (physicalSelectedCellMass_unitTotalMass steps J unit u).trans (hmass u)
  have hC i : 0 ≤ C i := actualCutCovarianceEnergy_nonneg n steps ha q0 i.val
  have hVL := physical_selected_left_variance_middle_integrable n K steps ha q0 J unit x hδ hp hpq hq hx
  have hVR := physical_selected_right_variance_middle_integrable n K steps ha q0 J unit x hδ hp hpq hq hx
  have hscore t (ht : t∈Icc p q) i (hi : mass i≠0) : D i ≤
      24*VL t+24*VR t+6*eta^2+
        (∑j,(mass j*left a (x (unit j)) (x ((unit j).val+1)) t)*AL i j)+
        (∑j,(mass j*right b (x (unit j)) (x ((unit j).val+1)) t)*AR i j)+C i := by
    have hiJ : i∈J := by
      by_contra hn
      exact hi (by simp [mass,physicalSelectedCellMass,hn])
    have h := physical_selected_score_at_evaluation n K steps ha q0 J unit x hstart hend
      (by linarith [ht.1] : a < t) (by linarith [ht.2] : t < b) hx hmass heta hS i hiJ
    dsimp only at h
    have heL := weighted_affine_sum_eq
      (fun j=>mass j*left a (x (unit j)) (x ((unit j).val+1)) t)
      (fun j=>physicalSideNoiseMoment n steps q0 i.val j.val)
      (fun j=>if i.val < j.val then physicalSideMovementMoment n steps q0 i.val j.val else 0) 32 8
    have heR := weighted_affine_sum_eq
      (fun j=>mass j*right b (x (unit j)) (x ((unit j).val+1)) t)
      (fun j=>physicalSideNoiseMoment n steps q0 i.val j.val)
      (fun j=>if j.val < i.val then physicalSideMovementMoment n steps q0 i.val j.val else 0) 32 8
    change _ ≤ _ at h
    dsimp only [AL,AR]
    rw [heL,heR]
    linarith
  have hi := integrated_evaluation_score_ledger mass D C unit x AL AR VL VR hstart hend hδ
    hp hpq hq hx hm0 hmu hC hVL hVR hscore
  have he := full_sum_le_evaluationIntegral_and_edges mass D unit x hstart hend hx hmu hm0
    (physicalSelectedCellMass_total n K steps J unit x hstart hend hmass)
    (fun i=>(actualCenteredCutReplicaDefect_mem_Icc n steps ha q0 i.val (by omega)).2)
    (by linarith : a < p) hpq (by linarith : q < b)
  exact he.trans (add_le_add hi le_rfl)

end OAI.SKFluctuations.WholeUnitSideKernel
