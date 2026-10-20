module

public import ComparisonActualIntegratedScore
public import ComparisonReverseMovementScale

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.WholeUnitSideKernel
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped BigOperators NNReal ENNReal

theorem joint_cost_sum_le_constant {I : Type*} [Fintype I]
    (P cost : I → I → ℝ) (mass : I → ℝ) {R v : ℝ}
    (hP : ∀i j,0 ≤ P i j) (hR : 0 ≤ R)
    (hrow : ∀i,(∑j,P i j) ≤ mass i) (hmassv : ∑i,mass i=v)
    (hcost : ∀i j,P i j≠0 → cost i j ≤ R) :
    (∑i,∑j,P i j*cost i j) ≤ R*v := by
  calc
    _ ≤ ∑i,∑j,P i j*R := Finset.sum_le_sum (fun i _=>Finset.sum_le_sum (fun j _=>by
      by_cases hz:P i j=0
      · simp only [hz,zero_mul]; exact le_rfl
      · exact mul_le_mul_of_nonneg_left (hcost i j hz) (hP i j)))
    _ = R*(∑i,∑j,P i j) := by simp only [← Finset.sum_mul]; ring
    _ ≤ R*v := mul_le_mul_of_nonneg_left (by rw [← hmassv]; exact joint_total_mass_le P mass hrow) hR

theorem joint_weighted_affine_sum_eq {I : Type*} [Fintype I]
    (P A B : I → I → ℝ) (c d : ℝ) :
    (∑i,∑j,P i j*(c*A i j+d*B i j))=
      c*(∑i,∑j,P i j*A i j)+d*(∑i,∑j,P i j*B i j) := by
  simp_rw [weighted_affine_sum_eq]
  rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]

def actualBinBudget (v δ eta tauW tauC R L : ℝ) : ℝ :=
  48*tauW*L+6*eta^2*v+32*(1+L)*v*(eta^2+tauC)+16*R*v+v*tauC+8*δ

theorem physical_selected_bin_defect_le_linear_energy (n K : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (J : Finset (Fin (steps.length+1)))
    (unit : Fin (steps.length+1) → Fin K) (x : ℕ → ℝ) {a b δ eta tauW tauC R : ℝ}
    (hstart : x 0=a) (hend : x K=b) (hδ : 0 < δ) (hwidth : 2*δ ≤ b-a)
    (hx : ∀u:Fin K,x u < x (u.val+1))
    (hmass : ∀u:Fin K,physicalSelectedUnitMass steps J unit u=x (u.val+1)-x u)
    (heta : 0 ≤ eta) (htauW : 0 ≤ tauW) (htauC : 0 ≤ tauC) (hR : 0 ≤ R)
    (hS : ∀i∈J,∀j∈J,
      |physicalPathSecondMoment n steps q0 j.val-physicalPathSecondMoment n steps q0 i.val| ≤ eta)
    (henergy : ∀u:Fin K,physicalSelectedUnitEnergy n steps q0 J unit u ≤ tauW*(x (u.val+1)-x u))
    (htrace : (∑i,physicalSelectedCellMass steps J i*actualCutCovarianceEnergy n steps q0 i.val) ≤ (b-a)*tauC)
    (hreverseL : ∀i j:Fin (steps.length+1),i.val < j.val →
      fineCoupling (physicalSelectedCellMass steps J) unit
        (fun u v=>coarseLeft x a (a+δ) (b-δ) u v) i j≠0 →
      physicalSideMovementMoment n steps q0 i.val j.val ≤ R)
    (hreverseR : ∀i j:Fin (steps.length+1),j.val < i.val →
      fineCoupling (physicalSelectedCellMass steps J) unit
        (fun u v=>coarseRight x b (a+δ) (b-δ) u v) i j≠0 →
      physicalSideMovementMoment n steps q0 i.val j.val ≤ R) :
    let mass := physicalSelectedCellMass steps J
    let I := ∑i,mass i*actualCutReplicaDefect n steps q0 i.val (physicalPathSecondMoment n steps q0 i.val)
    let L := Real.log ((b-a)/δ)
    I ≤ 2*actualBinBudget (b-a) δ eta tauW tauC R L+
      (256*(1+L))^2*(b-a)*tauC := by
  dsimp only
  let mass := physicalSelectedCellMass steps J
  let D := fun i:Fin (steps.length+1)=>actualCutReplicaDefect n steps q0 i.val
    (physicalPathSecondMoment n steps q0 i.val)
  let noise := fun i j:Fin (steps.length+1)=>physicalSideNoiseMoment n steps q0 i.val j.val
  let revL := fun i j:Fin (steps.length+1)=>if i.val < j.val then physicalSideMovementMoment n steps q0 i.val j.val else 0
  let revR := fun i j:Fin (steps.length+1)=>if j.val < i.val then physicalSideMovementMoment n steps q0 i.val j.val else 0
  let PL := fineCoupling mass unit (fun u v=>coarseLeft x a (a+δ) (b-δ) u v)
  let PR := fineCoupling mass unit (fun u v=>coarseRight x b (a+δ) (b-δ) u v)
  let I := ∑i,mass i*D i
  let L := Real.log ((b-a)/δ)
  have hpq : a+δ ≤ b-δ := by linarith
  have hv : 0 ≤ b-a := by linarith
  have hm0 := physicalSelectedCellMass_nonneg steps ha J
  have hI : 0 ≤ I := Finset.sum_nonneg (fun i _=>mul_nonneg (hm0 i) (actualCutReplicaDefect_nonneg n steps ha q0 i.val _))
  have hm := physicalSelectedCellMass_total n K steps J unit x hstart hend hmass
  have hCL := physical_selected_coarseLeft_marginals n K steps ha J unit x hstart hend hδ le_rfl hpq le_rfl hx hmass
  have hCR := physical_selected_coarseRight_marginals n K steps ha J unit x hstart hend hδ le_rfl hpq le_rfl hx hmass
  have hmoveL : (∑i,∑j,PL i j*revL i j) ≤ R*(b-a) := by
    apply joint_cost_sum_le_constant PL revL mass hCL.1 hR hCL.2.1 hm
    intro i j hij
    by_cases hr:i.val < j.val
    · simpa only [revL,hr,ite_true] using hreverseL i j hr hij
    · simpa only [revL,hr,ite_false] using hR
  have hmoveR : (∑i,∑j,PR i j*revR i j) ≤ R*(b-a) := by
    apply joint_cost_sum_le_constant PR revR mass hCR.1 hR hCR.2.1 hm
    intro i j hij
    by_cases hr:j.val < i.val
    · simpa only [revR,hr,ite_true] using hreverseR i j hr hij
    · simpa only [revR,hr,ite_false] using hR
  have hNL := physical_selected_coarseLeft_noise_sum_le n K steps ha q0 J unit x
    hstart hend hδ le_rfl hpq le_rfl hx hmass heta htauC htrace hS
  have hNR := physical_selected_coarseRight_noise_sum_le n K steps ha q0 J unit x
    hstart hend hδ le_rfl hpq le_rfl hx hmass heta htauC htrace hS
  dsimp only at hNL hNR
  have hVL := physical_selected_left_variance_middle_le n K steps ha q0 J unit x
    hstart hend hδ le_rfl hpq le_rfl hx htauW henergy
  have hVR := physical_selected_right_variance_middle_le n K steps ha q0 J unit x
    hstart hend hδ le_rfl hpq le_rfl hx htauW henergy
  have hscore := physical_selected_integrated_score_ledger n K steps ha q0 J unit x
    hstart hend hδ le_rfl hpq le_rfl hx hmass heta hS
  dsimp only at hscore
  change I ≤ _ at hscore
  rw [joint_weighted_affine_sum_eq PL noise revL 32 8,
    joint_weighted_affine_sum_eq PR noise revR 32 8] at hscore
  have hshort : 6*eta^2*((b-δ)-(a+δ)) ≤ 6*eta^2*(b-a) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hbracket : I ≤ actualBinBudget (b-a) δ eta tauW tauC R L+
      (256*(1+L))*Real.sqrt (I*((b-a)*tauC)) := by
    rw [Real.sqrt_mul hI]
    dsimp only [actualBinBudget,L,I,D,mass,noise,revL,revR,PL,PR] at *
    nlinarith
  exact two_sided_defect_absorption hI hv htauC hbracket

end OAI.SKFluctuations.WholeUnitSideKernel
