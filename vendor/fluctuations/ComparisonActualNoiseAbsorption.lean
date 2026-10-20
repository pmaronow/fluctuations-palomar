module

public import ComparisonActualCutLedger
public import ComparisonSelectedFineCoupling

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped BigOperators NNReal ENNReal
namespace WholeUnitSideKernel

theorem physical_noise_coupling_sum_le (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (P : Fin (steps.length+1) → Fin (steps.length+1) → ℝ)
    (mass : Fin (steps.length+1) → ℝ) {L eta v tau : ℝ}
    (hP : ∀i j,0 ≤ P i j) (hmass : ∀i,0 ≤ mass i)
    (hL : 0 ≤ L) (heta : 0 ≤ eta) (hv : 0 ≤ v) (htau : 0 ≤ tau)
    (hrow : ∀i,(∑j,P i j) ≤ mass i) (hcol : ∀j,(∑i,P i j) ≤ L*mass j)
    (hmassv : ∑i,mass i=v)
    (htrace : (∑i,mass i*actualCutCovarianceEnergy n steps q0 i.val) ≤ v*tau)
    (hS : ∀i j,P i j≠0 →
      |physicalPathSecondMoment n steps q0 j.val-physicalPathSecondMoment n steps q0 i.val| ≤ eta) :
    (∑i,∑j,P i j*physicalSideNoiseMoment n steps q0 i.val j.val) ≤
      (1+L)*v*(eta^2+tau)/2+
      4*(1+L)*Real.sqrt
        (∑i,mass i*actualCutReplicaDefect n steps q0 i.val (physicalPathSecondMoment n steps q0 i.val))*
        Real.sqrt (v*tau) := by
  let C := fun i:Fin (steps.length+1)=>actualCutCovarianceEnergy n steps q0 i.val
  let D := fun i:Fin (steps.length+1)=>actualCutReplicaDefect n steps q0 i.val
    (physicalPathSecondMoment n steps q0 i.val)
  let noise := fun i j:Fin (steps.length+1)=>
    if P i j=0 then 0 else physicalSideNoiseMoment n steps q0 i.val j.val
  have hC i : 0 ≤ C i := actualCutCovarianceEnergy_nonneg n steps ha q0 i.val
  have hD i : 0 ≤ D i := actualCutReplicaDefect_nonneg n steps ha q0 i.val _
  have hn i j : noise i j ≤ Real.sqrt (C i+C j)*(eta+4*Real.sqrt (D i+D j)) := by
    by_cases hzero : P i j=0
    · simp only [noise,hzero,ite_true]
      exact mul_nonneg (Real.sqrt_nonneg _) (by positivity)
    · simp only [noise,hzero,ite_false]
      exact physicalSideNoiseMoment_le_actual_cut_defects n steps ha q0
        (by omega : i.val ≤ steps.length) (by omega : j.val ≤ steps.length) heta (hS i j hzero)
  have h := joint_noise_sum_le P mass C D noise hP hmass hC hD hL hv htau hrow hcol
    hmassv htrace hn
  have he i j : P i j*noise i j=P i j*physicalSideNoiseMoment n steps q0 i.val j.val := by
    by_cases hz:P i j=0 <;> simp [noise,hz]
  simpa only [he,C,D] using h

theorem physicalSelectedCellMass_total (n K : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (J : Finset (Fin (steps.length+1)))
    (unit : Fin (steps.length+1) → Fin K) (x : ℕ → ℝ) {a b : ℝ}
    (hstart : x 0=a) (hend : x K=b)
    (hmass : ∀u:Fin K,physicalSelectedUnitMass steps J unit u=x (u.val+1)-x u) :
    (∑i,physicalSelectedCellMass steps J i)=b-a := by
  have h := sum_grouped_by_unit (physicalSelectedCellMass steps J) unit (fun _=>(1:ℝ))
  simp only [mul_one,physicalSelectedCellMass_unitTotalMass] at h
  rw [h]
  simp_rw [hmass]
  rw [Fin.sum_univ_eq_sum_range (fun u=>x (u+1)-x u),Finset.sum_range_sub,hstart,hend]

theorem physical_selected_coarseLeft_noise_sum_le (n K : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (J : Finset (Fin (steps.length+1)))
    (unit : Fin (steps.length+1) → Fin K) (x : ℕ → ℝ) {a b δ p q eta tau : ℝ}
    (hstart : x 0=a) (hend : x K=b) (hδ : 0 < δ)
    (hp : a+δ ≤ p) (hpq : p ≤ q) (hq : q ≤ b-δ)
    (hx : ∀u:Fin K,x u < x (u.val+1))
    (hmass : ∀u:Fin K,physicalSelectedUnitMass steps J unit u=x (u.val+1)-x u)
    (heta : 0 ≤ eta) (htau : 0 ≤ tau)
    (htrace : (∑i,physicalSelectedCellMass steps J i*actualCutCovarianceEnergy n steps q0 i.val) ≤ (b-a)*tau)
    (hS : ∀i∈J,∀j∈J,
      |physicalPathSecondMoment n steps q0 j.val-physicalPathSecondMoment n steps q0 i.val| ≤ eta) :
    let mass := physicalSelectedCellMass steps J
    let P := fineCoupling mass unit (fun u v=>coarseLeft x a p q u v)
    (∑i,∑j,P i j*physicalSideNoiseMoment n steps q0 i.val j.val) ≤
      (1+Real.log ((b-a)/δ))*(b-a)*(eta^2+tau)/2+
      4*(1+Real.log ((b-a)/δ))*Real.sqrt
        (∑i,mass i*actualCutReplicaDefect n steps q0 i.val (physicalPathSecondMoment n steps q0 i.val))*
        Real.sqrt ((b-a)*tau) := by
  dsimp only
  have hc := physical_selected_coarseLeft_marginals n K steps ha J unit x hstart hend hδ hp hpq hq hx hmass
  have hv : 0 ≤ b-a := by linarith
  have hL : 0 ≤ Real.log ((b-a)/δ) := Real.log_nonneg ((one_le_div hδ).mpr (by linarith))
  apply physical_noise_coupling_sum_le n steps ha q0 _ _ hc.1
    (physicalSelectedCellMass_nonneg steps ha J) hL heta hv htau hc.2.1 hc.2.2
    (physicalSelectedCellMass_total n K steps J unit x hstart hend hmass) htrace
  intro i j hij
  apply hS i _ j _
  all_goals
    by_contra hnot
    apply hij
    simp [fineCoupling,physicalSelectedCellMass,hnot]
theorem physical_selected_coarseRight_noise_sum_le (n K : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (J : Finset (Fin (steps.length+1)))
    (unit : Fin (steps.length+1) → Fin K) (x : ℕ → ℝ) {a b δ p q eta tau : ℝ}
    (hstart : x 0=a) (hend : x K=b) (hδ : 0 < δ)
    (hp : a+δ ≤ p) (hpq : p ≤ q) (hq : q ≤ b-δ)
    (hx : ∀u:Fin K,x u < x (u.val+1))
    (hmass : ∀u:Fin K,physicalSelectedUnitMass steps J unit u=x (u.val+1)-x u)
    (heta : 0 ≤ eta) (htau : 0 ≤ tau)
    (htrace : (∑i,physicalSelectedCellMass steps J i*actualCutCovarianceEnergy n steps q0 i.val) ≤ (b-a)*tau)
    (hS : ∀i∈J,∀j∈J,
      |physicalPathSecondMoment n steps q0 j.val-physicalPathSecondMoment n steps q0 i.val| ≤ eta) :
    let mass := physicalSelectedCellMass steps J
    let P := fineCoupling mass unit (fun u v=>coarseRight x b p q u v)
    (∑i,∑j,P i j*physicalSideNoiseMoment n steps q0 i.val j.val) ≤
      (1+Real.log ((b-a)/δ))*(b-a)*(eta^2+tau)/2+
      4*(1+Real.log ((b-a)/δ))*Real.sqrt
        (∑i,mass i*actualCutReplicaDefect n steps q0 i.val (physicalPathSecondMoment n steps q0 i.val))*
        Real.sqrt ((b-a)*tau) := by
  dsimp only
  have hc := physical_selected_coarseRight_marginals n K steps ha J unit x hstart hend hδ hp hpq hq hx hmass
  have hv : 0 ≤ b-a := by linarith
  have hL : 0 ≤ Real.log ((b-a)/δ) := Real.log_nonneg ((one_le_div hδ).mpr (by linarith))
  apply physical_noise_coupling_sum_le n steps ha q0 _ _ hc.1
    (physicalSelectedCellMass_nonneg steps ha J) hL heta hv htau hc.2.1 hc.2.2
    (physicalSelectedCellMass_total n K steps J unit x hstart hend hmass) htrace
  intro i j hij
  apply hS i _ j _
  all_goals
    by_contra hnot
    apply hij
    simp [fineCoupling,physicalSelectedCellMass,hnot]

end WholeUnitSideKernel
end OAI.SKFluctuations
