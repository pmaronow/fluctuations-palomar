module

public import ComparisonActualIntegratedDefect

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.WholeUnitSideKernel
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped BigOperators NNReal ENNReal

def actualBinSideVariance (n K : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (q0 : FeatureIndex n → ℝ≥0)
    (J : Finset (Fin (steps.length+1))) (unit : Fin (steps.length+1) → Fin K)
    (x : ℕ → ℝ) (δ width : ℝ) : ℝ :=
  (∫t in δ..width-δ,selectedScoreVariance n steps q0 (selectedLeftWeight steps J unit x 0 t))+
  (∫t in δ..width-δ,selectedScoreVariance n steps q0 (selectedRightWeight steps J unit x width t))

theorem physical_selected_bin_score_le_actual_variance (n K : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (J : Finset (Fin (steps.length+1)))
    (unit : Fin (steps.length+1) → Fin K) (x : ℕ → ℝ) {b δ eta : ℝ}
    (hstart : x 0=0) (hend : x K=b) (hδ : 0 < δ) (hwidth : 2*δ ≤ b)
    (hx : ∀u:Fin K,x u < x (u.val+1))
    (hmass : ∀u:Fin K,physicalSelectedUnitMass steps J unit u=x (u.val+1)-x u)
    (heta : 0 ≤ eta) (hS : ∀i∈J,∀j∈J,
      |physicalPathSecondMoment n steps q0 j.val-physicalPathSecondMoment n steps q0 i.val| ≤ eta) :
    let mass := physicalSelectedCellMass steps J
    let PL := fineCoupling mass unit (fun u v=>coarseLeft x 0 δ (b-δ) u v)
    let PR := fineCoupling mass unit (fun u v=>coarseRight x b δ (b-δ) u v)
    let noise := fun i j:Fin (steps.length+1)=>physicalSideNoiseMoment n steps q0 i.val j.val
    let revL := fun i j:Fin (steps.length+1)=>if i.val < j.val then physicalSideMovementMoment n steps q0 i.val j.val else 0
    let revR := fun i j:Fin (steps.length+1)=>if j.val < i.val then physicalSideMovementMoment n steps q0 i.val j.val else 0
    (∑i,mass i*actualCutReplicaDefect n steps q0 i.val (physicalPathSecondMoment n steps q0 i.val)) ≤
      24*actualBinSideVariance n K steps q0 J unit x δ b+6*eta^2*b+
      32*(∑i,∑j,PL i j*noise i j)+32*(∑i,∑j,PR i j*noise i j)+
      8*(∑i,∑j,PL i j*revL i j)+8*(∑i,∑j,PR i j*revR i j)+
      (∑i,mass i*actualCutCovarianceEnergy n steps q0 i.val)+8*δ := by
  dsimp only
  have hpq : δ ≤ b-δ := by linarith
  have hscore := physical_selected_integrated_score_ledger n K steps ha q0 J unit x
    hstart hend hδ (by simp) hpq le_rfl hx hmass heta hS
  dsimp only at hscore
  rw [joint_weighted_affine_sum_eq,joint_weighted_affine_sum_eq] at hscore
  simp only [zero_add,sub_zero] at hscore
  have hshort : 6*eta^2*((b-δ)-δ) ≤ 6*eta^2*b :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  dsimp only [actualBinSideVariance,selectedScoreVariance,selectedLeftWeight,selectedRightWeight] at *
  nlinarith

theorem physical_selected_bin_score_le_unit_energy (n K : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (J : Finset (Fin (steps.length+1)))
    (unit : Fin (steps.length+1) → Fin K) (x : ℕ → ℝ) {a b δ eta tauW : ℝ}
    (hstart : x 0=a) (hend : x K=b) (hδ : 0 < δ) (hwidth : 2*δ ≤ b-a)
    (hx : ∀u:Fin K,x u < x (u.val+1))
    (hmass : ∀u:Fin K,physicalSelectedUnitMass steps J unit u=x (u.val+1)-x u)
    (heta : 0 ≤ eta) (htauW : 0 ≤ tauW)
    (hS : ∀i∈J,∀j∈J,
      |physicalPathSecondMoment n steps q0 j.val-physicalPathSecondMoment n steps q0 i.val| ≤ eta)
    (henergy : ∀u:Fin K,physicalSelectedUnitEnergy n steps q0 J unit u ≤ tauW*(x (u.val+1)-x u)) :
    let mass := physicalSelectedCellMass steps J
    let PL := fineCoupling mass unit (fun u v=>coarseLeft x a (a+δ) (b-δ) u v)
    let PR := fineCoupling mass unit (fun u v=>coarseRight x b (a+δ) (b-δ) u v)
    let noise := fun i j:Fin (steps.length+1)=>physicalSideNoiseMoment n steps q0 i.val j.val
    let revL := fun i j:Fin (steps.length+1)=>if i.val < j.val then physicalSideMovementMoment n steps q0 i.val j.val else 0
    let revR := fun i j:Fin (steps.length+1)=>if j.val < i.val then physicalSideMovementMoment n steps q0 i.val j.val else 0
    (∑i,mass i*actualCutReplicaDefect n steps q0 i.val (physicalPathSecondMoment n steps q0 i.val)) ≤
      48*tauW*Real.log ((b-a)/δ)+6*eta^2*(b-a)+
      32*(∑i,∑j,PL i j*noise i j)+32*(∑i,∑j,PR i j*noise i j)+
      8*(∑i,∑j,PL i j*revL i j)+8*(∑i,∑j,PR i j*revR i j)+
      (∑i,mass i*actualCutCovarianceEnergy n steps q0 i.val)+8*δ := by
  dsimp only
  have hpq : a+δ ≤ b-δ := by linarith
  have hVL := physical_selected_left_variance_middle_le n K steps ha q0 J unit x
    hstart hend hδ le_rfl hpq le_rfl hx htauW henergy
  have hVR := physical_selected_right_variance_middle_le n K steps ha q0 J unit x
    hstart hend hδ le_rfl hpq le_rfl hx htauW henergy
  have hscore := physical_selected_integrated_score_ledger n K steps ha q0 J unit x
    hstart hend hδ le_rfl hpq le_rfl hx hmass heta hS
  dsimp only at hscore
  rw [joint_weighted_affine_sum_eq, joint_weighted_affine_sum_eq] at hscore
  have hshort : 6*eta^2*((b-δ)-(a+δ)) ≤ 6*eta^2*(b-a) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  nlinarith

end OAI.SKFluctuations.WholeUnitSideKernel
