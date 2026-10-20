module

public import ComparisonSelectedBinEnergyScore
public import ComparisonSelectedVarianceEnergyLedger
public import ComparisonBinCouplingSum

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.WholeUnitSideKernel
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped BigOperators NNReal ENNReal

def actualBinsVarianceBudget (B : ℕ) (v δ eta V tauC R L : ℝ) : ℝ :=
  24*V+6*eta^2*v+32*(1+L)*v*(eta^2+tauC)+
    16*R*v+v*tauC+8*(B:ℝ)*δ

theorem physical_selected_bins_defect_le_variance_budget (n B : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0)
    (K : Fin B → ℕ) (J : Fin B → Finset (Fin (steps.length+1)))
    (unit : ∀b:Fin B,Fin (steps.length+1) → Fin (K b))
    (x : Fin B → ℕ → ℝ) (width : Fin B → ℝ) {δ eta V tauC R L v : ℝ}
    (hstart : ∀b,x b 0=0) (hend : ∀b,x b (K b)=width b)
    (hδ : 0 < δ) (hwidth : ∀b,2*δ ≤ width b)
    (hx : ∀b,∀u:Fin (K b),x b u < x b (u.val+1))
    (hmass : ∀b,∀u:Fin (K b),physicalSelectedUnitMass steps (J b) (unit b) u=x b (u.val+1)-x b u)
    (heta : 0 ≤ eta) (htauC : 0 ≤ tauC) (hR : 0 ≤ R)
    (hL : 0 ≤ L) (hlog : ∀b,Real.log (width b/δ) ≤ L)
    (hv : ∑b,width b=v)
    (hS : ∀b,∀i∈J b,∀j∈J b,
      |physicalPathSecondMoment n steps q0 j.val-physicalPathSecondMoment n steps q0 i.val| ≤ eta)
    (hvariance : (∑b,actualBinSideVariance n (K b) steps q0 (J b) (unit b) (x b) δ (width b)) ≤ V)
    (htrace : (∑i,(∑b,physicalSelectedCellMass steps (J b) i)*actualCutCovarianceEnergy n steps q0 i.val) ≤ v*tauC)
    (hreverseL : ∀b,∀i j:Fin (steps.length+1),i.val < j.val →
      fineCoupling (physicalSelectedCellMass steps (J b)) (unit b)
        (fun u w=>coarseLeft (x b) 0 δ (width b-δ) u w) i j≠0 →
      physicalSideMovementMoment n steps q0 i.val j.val ≤ R)
    (hreverseR : ∀b,∀i j:Fin (steps.length+1),j.val < i.val →
      fineCoupling (physicalSelectedCellMass steps (J b)) (unit b)
        (fun u w=>coarseRight (x b) (width b) δ (width b-δ) u w) i j≠0 →
      physicalSideMovementMoment n steps q0 i.val j.val ≤ R) :
    let mass := fun i:Fin (steps.length+1)=>∑b,physicalSelectedCellMass steps (J b) i
    let I := ∑i,mass i*actualCutReplicaDefect n steps q0 i.val (physicalPathSecondMoment n steps q0 i.val)
    I ≤ 2*actualBinsVarianceBudget B v δ eta V tauC R L+(256*(1+L))^2*v*tauC := by
  dsimp only
  let bm := fun b:Fin B=>physicalSelectedCellMass steps (J b)
  let mass := fun i:Fin (steps.length+1)=>∑b,bm b i
  let PL := fun b:Fin B=>fineCoupling (bm b) (unit b)
    (fun u w=>coarseLeft (x b) 0 δ (width b-δ) u w)
  let PR := fun b:Fin B=>fineCoupling (bm b) (unit b)
    (fun u w=>coarseRight (x b) (width b) δ (width b-δ) u w)
  let gleft := fun i j:Fin (steps.length+1)=>∑b,PL b i j
  let gright := fun i j:Fin (steps.length+1)=>∑b,PR b i j
  let D := fun i:Fin (steps.length+1)=>actualCutReplicaDefect n steps q0 i.val
    (physicalPathSecondMoment n steps q0 i.val)
  let C := fun i:Fin (steps.length+1)=>actualCutCovarianceEnergy n steps q0 i.val
  let noise := fun i j:Fin (steps.length+1)=>physicalSideNoiseMoment n steps q0 i.val j.val
  let revL := fun i j:Fin (steps.length+1)=>if i.val < j.val then physicalSideMovementMoment n steps q0 i.val j.val else 0
  let revR := fun i j:Fin (steps.length+1)=>if j.val < i.val then physicalSideMovementMoment n steps q0 i.val j.val else 0
  let I := ∑i,mass i*D i
  have hpq b : δ ≤ width b-δ := by linarith [hwidth b]
  have hm0 b := physicalSelectedCellMass_nonneg steps ha (J b)
  have hmass0 i : 0 ≤ mass i := Finset.sum_nonneg (fun b _=>hm0 b i)
  have hbtotal b : (∑i,bm b i)=width b := by
    simpa using physicalSelectedCellMass_total n (K b) steps (J b) (unit b) (x b) (hstart b) (hend b) (hmass b)
  have htotal : ∑i,mass i=v := by
    dsimp only [mass]
    rw [Finset.sum_comm]
    simp_rw [hbtotal]
    exact hv
  have hv0 : 0 ≤ v := by rw [← htotal]; exact Finset.sum_nonneg (fun i _=>hmass0 i)
  have hI : 0 ≤ I := Finset.sum_nonneg (fun i _=>mul_nonneg (hmass0 i) (actualCutReplicaDefect_nonneg n steps ha q0 i.val _))
  have hCL b := physical_selected_coarseLeft_marginals n (K b) steps ha (J b) (unit b) (x b)
    (hstart b) (hend b) hδ (by simp) (hpq b) le_rfl (hx b) (hmass b)
  have hCR b := physical_selected_coarseRight_marginals n (K b) steps ha (J b) (unit b) (x b)
    (hstart b) (hend b) hδ (by simp) (hpq b) le_rfl (hx b) (hmass b)
  have hcolL b j : (∑i,PL b i j) ≤ L*bm b j := by
    have h := (hCL b).2.2 j
    have hl := mul_le_mul_of_nonneg_right (hlog b) (hm0 b j)
    dsimp only [PL,bm] at *
    simp only [sub_zero] at h
    exact h.trans hl
  have hcolR b j : (∑i,PR b i j) ≤ L*bm b j := by
    have h := (hCR b).2.2 j
    have hl := mul_le_mul_of_nonneg_right (hlog b) (hm0 b j)
    dsimp only [PR,bm] at *
    simp only [sub_zero] at h
    exact h.trans hl
  have hgleft := bin_coupling_sum_marginals PL bm (fun b=>(hCL b).1) (fun b=>(hCL b).2.1) hcolL
  have hgright := bin_coupling_sum_marginals PR bm (fun b=>(hCR b).1) (fun b=>(hCR b).2.1) hcolR
  have hSL (i j:Fin (steps.length+1)) (hij : gleft i j≠0) :
      |physicalPathSecondMoment n steps q0 j.val-physicalPathSecondMoment n steps q0 i.val| ≤ eta := by
    obtain ⟨b,hb⟩ := bin_sum_support (fun b=>PL b i j) hij
    apply hS b i _ j _
    all_goals
      by_contra hnot
      apply hb
      simp [PL,bm,fineCoupling,physicalSelectedCellMass,hnot]
  have hSR (i j:Fin (steps.length+1)) (hij : gright i j≠0) :
      |physicalPathSecondMoment n steps q0 j.val-physicalPathSecondMoment n steps q0 i.val| ≤ eta := by
    obtain ⟨b,hb⟩ := bin_sum_support (fun b=>PR b i j) hij
    apply hS b i _ j _
    all_goals
      by_contra hnot
      apply hb
      simp [PR,bm,fineCoupling,physicalSelectedCellMass,hnot]
  have hNL := physical_noise_coupling_sum_le n steps ha q0 gleft mass hgleft.1 hmass0 hL heta hv0 htauC
    hgleft.2.1 hgleft.2.2 htotal htrace hSL
  have hNR := physical_noise_coupling_sum_le n steps ha q0 gright mass hgright.1 hmass0 hL heta hv0 htauC
    hgright.2.1 hgright.2.2 htotal htrace hSR
  have hmoveL : (∑i,∑j,gleft i j*revL i j) ≤ R*v := by
    apply joint_cost_sum_le_constant gleft revL mass hgleft.1 hR hgleft.2.1 htotal
    intro i j hij
    by_cases hr:i.val < j.val
    · obtain ⟨b,hb⟩ := bin_sum_support (fun b=>PL b i j) hij
      simpa only [revL,hr,ite_true] using hreverseL b i j hr hb
    · simpa only [revL,hr,ite_false] using hR
  have hmoveR : (∑i,∑j,gright i j*revR i j) ≤ R*v := by
    apply joint_cost_sum_le_constant gright revR mass hgright.1 hR hgright.2.1 htotal
    intro i j hij
    by_cases hr:j.val < i.val
    · obtain ⟨b,hb⟩ := bin_sum_support (fun b=>PR b i j) hij
      simpa only [revR,hr,ite_true] using hreverseR b i j hr hb
    · simpa only [revR,hr,ite_false] using hR
  have hscore b := physical_selected_bin_score_le_actual_variance n (K b) steps ha q0 (J b) (unit b) (x b)
    (hstart b) (hend b) hδ (by simpa using hwidth b) (hx b) (hmass b) heta (hS b)
  dsimp only at hscore
  have hsum := Finset.sum_le_sum (fun b (_:b∈(Finset.univ:Finset (Fin B)))=>hscore b)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,sub_zero] at hsum
  rw [bin_mass_cost_sum_eq,bin_mass_cost_sum_eq,
    bin_joint_cost_sum_eq,bin_joint_cost_sum_eq,bin_joint_cost_sum_eq,bin_joint_cost_sum_eq,hv] at hsum
  have hbracket : I ≤ actualBinsVarianceBudget B v δ eta V tauC R L+
      (256*(1+L))*Real.sqrt (I*(v*tauC)) := by
    rw [Real.sqrt_mul hI]
    dsimp only [actualBinsVarianceBudget,I,D,C,mass,bm,gleft,gright,PL,PR,noise,revL,revR] at *
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,zero_add] at hsum
    nlinarith
  exact two_sided_defect_absorption hI hv0 htauC hbracket

end OAI.SKFluctuations.WholeUnitSideKernel
