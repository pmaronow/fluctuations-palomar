module

public import ComparisonPhysicalNoisePair

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped BigOperators NNReal ENNReal

def physicalSideNoiseMoment (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    (q0 : FeatureIndex n → ℝ≥0) (i j : ℕ) : ℝ :=
  ∫z,(orderedScoreNoise (actualSpinPath n steps id) (steps.length+1) i j z)^2
    ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps

def physicalSideMovementMoment (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    (q0 : FeatureIndex n → ℝ≥0) (i j : ℕ) : ℝ :=
  ∫z,‖actualSpinPath n steps id j z-actualSpinPath n steps id i z‖^4
    ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps

theorem physical_side_noise_square_integrable (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (i j : ℕ) :
    Integrable (fun z=>(orderedScoreNoise (actualSpinPath n steps id)
      (steps.length+1) i j z)^2)
      (rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps) := by
  let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps
  let X := actualSpinPath n steps id
  have := rootedHierarchyPathLaw_probability (uniformWeight_pos n) (finiteFeature n) q0 steps ha
  have hx (k : ℕ) : Measurable (X k) := actualSpinPath_measurable n steps ha id measurable_id k
  have hb (k l : ℕ) (z) : ‖X k z-X l z‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by
      have hk := actualSpinPath_norm_le n steps ha id k z
      have hl := actualSpinPath_norm_le n steps ha id l z
      linarith)
  apply Integrable.of_bound (((hx _).sub (hx _)).inner ((hx _).sub (hx _))
    |>.pow_const 2).aestronglyMeasurable 16
  filter_upwards [] with z
  change ‖(inner ℝ (X (steps.length+1) z-X (max i j) z) (X j z-X i z))^2‖ ≤ 16
  rw [norm_pow,Real.norm_eq_abs]
  have h := (abs_real_inner_le_norm _ _).trans (mul_le_mul
    (hb (steps.length+1) (max i j) z) (hb j i z) (norm_nonneg _) (by norm_num))
  nlinarith [abs_nonneg (inner ℝ (X (steps.length+1) z-X (max i j) z) (X j z-X i z))]

theorem physical_side_movement_fourth_integrable (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (i j : ℕ) :
    Integrable (fun z=>‖actualSpinPath n steps id j z-actualSpinPath n steps id i z‖^4)
      (rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps) := by
  let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps
  let X := actualSpinPath n steps id
  have := rootedHierarchyPathLaw_probability (uniformWeight_pos n) (finiteFeature n) q0 steps ha
  have hx (k : ℕ) : Measurable (X k) := actualSpinPath_measurable n steps ha id measurable_id k
  apply Integrable.of_bound (((hx j).sub (hx i)).norm.pow_const 4).aestronglyMeasurable 16
  filter_upwards [] with z
  change ‖‖X j z-X i z‖^4‖ ≤ 16
  rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)]
  have hb : ‖X j z-X i z‖ ≤ 2 := (norm_sub_le _ _).trans (by
    have hj := actualSpinPath_norm_le n steps ha id j z
    have hi := actualSpinPath_norm_le n steps ha id i z
    linarith)
  exact (pow_le_pow_left₀ (norm_nonneg _) hb 4).trans_eq (by norm_num)

theorem physical_side_score_error_integrable (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (i : ℕ) (alpha : Fin (steps.length+1) → ℝ)
    (reverse : Fin (steps.length+1) → Prop) [∀j,Decidable (reverse j)] :
    Integrable (fun z=>∑j,alpha j*(2*(orderedScoreNoise (actualSpinPath n steps id)
      (steps.length+1) i j.val z)^2+
        if reverse j then (1/2:ℝ)*‖actualSpinPath n steps id j.val z-
          actualSpinPath n steps id i z‖^4 else 0))
      (rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps) := by
  have := rootedHierarchyPathLaw_probability (uniformWeight_pos n) (finiteFeature n) q0 steps ha
  apply integrable_finsetSum
  intro j _
  apply Integrable.const_mul
  apply Integrable.add (physical_side_noise_square_integrable n steps ha q0 i j.val |>.const_mul 2)
  by_cases hr : reverse j
  · simpa only [if_pos hr] using physical_side_movement_fourth_integrable n steps ha q0 i j.val |>.const_mul (1/2:ℝ)
  · simpa only [if_neg hr] using (integrable_const (0:ℝ))

theorem physical_side_score_error_integral (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (i : ℕ) (alpha : Fin (steps.length+1) → ℝ)
    (reverse : Fin (steps.length+1) → Prop) [∀j,Decidable (reverse j)] :
    (∫z,∑j,alpha j*(2*(orderedScoreNoise (actualSpinPath n steps id)
      (steps.length+1) i j.val z)^2+
        if reverse j then (1/2:ℝ)*‖actualSpinPath n steps id j.val z-
          actualSpinPath n steps id i z‖^4 else 0)
      ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps)=
    2*(∑j,alpha j*physicalSideNoiseMoment n steps q0 i j.val)+
      (1/2:ℝ)*(∑j,alpha j*(if reverse j then physicalSideMovementMoment n steps q0 i j.val else 0)) := by
  let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps
  have := rootedHierarchyPathLaw_probability (uniformWeight_pos n) (finiteFeature n) q0 steps ha
  have hj (j : Fin (steps.length+1)) :
      Integrable (fun z=>alpha j*(2*(orderedScoreNoise (actualSpinPath n steps id)
        (steps.length+1) i j.val z)^2+
          if reverse j then (1/2:ℝ)*‖actualSpinPath n steps id j.val z-
            actualSpinPath n steps id i z‖^4 else 0)) mu := by
    apply Integrable.const_mul
    apply Integrable.add (physical_side_noise_square_integrable n steps ha q0 i j.val |>.const_mul 2)
    by_cases hr : reverse j
    · simpa only [if_pos hr] using physical_side_movement_fourth_integrable n steps ha q0 i j.val |>.const_mul (1/2:ℝ)
    · simpa only [if_neg hr] using (integrable_const (0:ℝ))
  rw [integral_finsetSum Finset.univ (fun j _=>hj j)]
  have he (j : Fin (steps.length+1)) :
      (∫z,alpha j*(2*(orderedScoreNoise (actualSpinPath n steps id)
        (steps.length+1) i j.val z)^2+
          if reverse j then (1/2:ℝ)*‖actualSpinPath n steps id j.val z-
            actualSpinPath n steps id i z‖^4 else 0) ∂mu)=
      2*(alpha j*physicalSideNoiseMoment n steps q0 i j.val)+
        (1/2:ℝ)*(alpha j*(if reverse j then physicalSideMovementMoment n steps q0 i j.val else 0)) := by
    rw [integral_const_mul]
    by_cases hr : reverse j
    · simp only [if_pos hr]
      rw [integral_add (physical_side_noise_square_integrable n steps ha q0 i j.val |>.const_mul 2)
        (physical_side_movement_fourth_integrable n steps ha q0 i j.val |>.const_mul (1/2:ℝ)),
        integral_const_mul,integral_const_mul]
      dsimp only [physicalSideNoiseMoment,physicalSideMovementMoment,mu]
      ring
    · simp only [if_neg hr,add_zero,mul_zero]
      rw [integral_const_mul]
      dsimp only [physicalSideNoiseMoment,mu]
      ring
  simp_rw [he,Finset.sum_add_distrib]
  rw [Finset.mul_sum,Finset.mul_sum]

theorem physical_two_sided_defect_score_ledger (n : ℕ)
    (pre tail : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 (pre++tail))
    (q0 : FeatureIndex n → ℝ≥0) (km kp : Fin ((pre++tail).length+1) → ℝ)
    (hkm : ∀j,0 ≤ km j) (hkp : ∀j,0 ≤ kp j)
    (hnormm : ∑j,pathMassDifferences (pre++tail) 0 j*km j=1)
    (hnormp : ∑j,pathMassDifferences (pre++tail) 0 j*kp j=1)
    {c eta : ℝ} (heta : 0 ≤ eta)
    (hmeanm : |(∑j,(pathMassDifferences (pre++tail) 0 j*km j)*
      physicalPathSecondMoment n (pre++tail) q0 j.val)-c| ≤ eta)
    (hmeanp : |(∑j,(pathMassDifferences (pre++tail) 0 j*kp j)*
      physicalPathSecondMoment n (pre++tail) q0 j.val)-c| ≤ eta) :
    let steps := pre++tail
    let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps
    let Am : PhysicalPathState (FeatureIndex n → ℝ) n steps → ℝ := fun z=>(physicalPinnedPair (uniformWeight n) (finiteFeature n)
      (spinSource n) steps 0 km z.1 z.2).1
    let Ap : PhysicalPathState (FeatureIndex n → ℝ) n steps → ℝ := fun z=>(physicalPinnedPair (uniformWeight n) (finiteFeature n)
      (spinSource n) steps 0 kp z.1 z.2).1
    let am := fun j=>pathMassDifferences steps 0 j*km j
    let ap := fun j=>pathMassDifferences steps 0 j*kp j
    physicalCutPairDefectSecond n pre tail q0 c ≤
      24*variance Am mu+24*variance Ap mu+6*eta^2+
        32*(∑j,am j*physicalSideNoiseMoment n steps q0 pre.length j.val)+
        32*(∑j,ap j*physicalSideNoiseMoment n steps q0 pre.length j.val)+
        8*(∑j,am j*(if pre.length < j.val then physicalSideMovementMoment n steps q0 pre.length j.val else 0))+
        8*(∑j,ap j*(if j.val < pre.length then physicalSideMovementMoment n steps q0 pre.length j.val else 0))+
        (∫z,physicalSpinTraceCovSq n tail (actualCutField pre tail z.1 z.2) ∂mu) := by
  dsimp only
  let steps := pre++tail
  let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps
  let X := actualSpinPath n steps id
  let Am : PhysicalPathState (FeatureIndex n → ℝ) n steps → ℝ := fun z=>(physicalPinnedPair (uniformWeight n) (finiteFeature n)
    (spinSource n) steps 0 km z.1 z.2).1
  let Ap : PhysicalPathState (FeatureIndex n → ℝ) n steps → ℝ := fun z=>(physicalPinnedPair (uniformWeight n) (finiteFeature n)
    (spinSource n) steps 0 kp z.1 z.2).1
  let am := fun j=>pathMassDifferences steps 0 j*km j
  let ap := fun j=>pathMassDifferences steps 0 j*kp j
  let cm := ∫z,Am z ∂mu
  let cp := ∫z,Ap z ∂mu
  let Fm := fun z=>(Am z-cm)^2
  let Fp := fun z=>(Ap z-cp)^2
  let F := fun z=>(terminalScore X (steps.length+1) pre.length z-c/2)^2
  let Qm := fun z=>∑j,am j*(2*(orderedScoreNoise X (steps.length+1) pre.length j.val z)^2+
    if pre.length < j.val then (1/2:ℝ)*‖X j.val z-X pre.length z‖^4 else 0)
  let Qp := fun z=>∑j,ap j*(2*(orderedScoreNoise X (steps.length+1) pre.length j.val z)^2+
    if j.val < pre.length then (1/2:ℝ)*‖X j.val z-X pre.length z‖^4 else 0)
  have := rootedHierarchyPathLaw_probability (uniformWeight_pos n) (finiteFeature n) q0 steps ha
  have hAm := physicalPinnedPair_fst_memLp n steps ha q0 km 2
  have hAp := physicalPinnedPair_fst_memLp n steps ha q0 kp 2
  have hFm : Integrable Fm mu := by
    simpa [Fm,Real.norm_eq_abs] using
      (hAm.sub (memLp_const cm)).integrable_norm_rpow (by norm_num) (by norm_num)
  have hFp : Integrable Fp mu := by
    simpa [Fp,Real.norm_eq_abs] using
      (hAp.sub (memLp_const cp)).integrable_norm_rpow (by norm_num) (by norm_num)
  have hF : Integrable F mu := by
    have hL := terminalScore_memLp (actualSpinPath_rooted_martingale n steps ha q0)
      (R:=1) (fun j=>ae_of_all _ (fun z=>actualSpinPath_norm_le n steps ha id j z))
      (steps.length+1) pre.length 2
    simpa [F,Real.norm_eq_abs] using
      (hL.sub (memLp_const (c/2))).integrable_norm_rpow (by norm_num) (by norm_num)
  have hQm : Integrable Qm mu := physical_side_score_error_integrable n steps ha q0 pre.length am
    (fun j=>pre.length < j.val)
  have hQp : Integrable Qp mu := physical_side_score_error_integrable n steps ha q0 pre.length ap
    (fun j=>j.val < pre.length)
  have hcm : |cm-c/2| ≤ eta/2 := by
    have hm := integral_physicalPinnedPair_fst n steps ha q0 km
    dsimp only at hm
    change cm=(1/2:ℝ)*(∑j,am j*physicalPathSecondMoment n steps q0 j.val) at hm
    rw [hm,show (1/2:ℝ)*(∑j,am j*physicalPathSecondMoment n steps q0 j.val)-c/2=
      ((∑j,am j*physicalPathSecondMoment n steps q0 j.val)-c)/2 by ring,
      abs_div,abs_of_pos (by norm_num : (0:ℝ) < 2)]
    exact div_le_div_of_nonneg_right hmeanm (by norm_num)
  have hcp : |cp-c/2| ≤ eta/2 := by
    have hp := integral_physicalPinnedPair_fst n steps ha q0 kp
    dsimp only at hp
    change cp=(1/2:ℝ)*(∑j,ap j*physicalPathSecondMoment n steps q0 j.val) at hp
    rw [hp,show (1/2:ℝ)*(∑j,ap j*physicalPathSecondMoment n steps q0 j.val)-c/2=
      ((∑j,ap j*physicalPathSecondMoment n steps q0 j.val)-c)/2 by ring,
      abs_div,abs_of_pos (by norm_num : (0:ℝ) < 2)]
    exact div_le_div_of_nonneg_right hmeanp (by norm_num)
  have heAm : Am=terminalWindow X (steps.length+1) Finset.univ Fin.val am := by
    funext z
    exact physicalPinnedPair_fst_eq_window n steps ha km id z
  have heAp : Ap=terminalWindow X (steps.length+1) Finset.univ Fin.val ap := by
    funext z
    exact physicalPinnedPair_fst_eq_window n steps ha kp id z
  have hpoint (z) : F z ≤ 6*Fm z+6*Fp z+6*(eta/2)^2+4*Qm z+4*Qp z := by
    have hp := terminalWindow_two_sided_score_square_bound (X:=X) (steps.length+1) pre.length
      Fin.val Fin.val am ap
      (fun j=>mul_nonneg (pathMassDifferences_nonneg steps ha j) (hkm j))
      (fun j=>mul_nonneg (pathMassDifferences_nonneg steps ha j) (hkp j))
      hnormm hnormp (by positivity : 0 ≤ eta/2) hcm hcp z
    rw [← heAm,← heAp] at hp
    exact hp
  have hR1 := (hFm.const_mul 6).add (hFp.const_mul 6)
  have hR2 := hR1.add (integrable_const (6*(eta/2)^2))
  have hR3 := hR2.add (hQm.const_mul 4)
  have hR4 := hR3.add (hQp.const_mul 4)
  have hInt := integral_mono hF hR4 hpoint
  simp only [Pi.add_apply] at hInt
  have hExpand : (∫z,6*Fm z+6*Fp z+6*(eta/2)^2+4*Qm z+4*Qp z ∂mu)=
      6*(∫z,Fm z ∂mu)+6*(∫z,Fp z ∂mu)+6*(eta/2)^2+
        4*(∫z,Qm z ∂mu)+4*(∫z,Qp z ∂mu) := by
    have he4 := integral_add hR3 (hQp.const_mul 4)
    have he3 := integral_add hR2 (hQm.const_mul 4)
    have he2 := integral_add hR1 (integrable_const (6*(eta/2)^2))
    have he1 := integral_add (hFm.const_mul 6) (hFp.const_mul 6)
    simp only [Pi.add_apply] at he4 he3 he2 he1
    rw [he4,he3,he2,he1]
    simp only [integral_const_mul,integral_const,probReal_univ,one_smul]
  have hVm : (∫z,Fm z ∂mu)=variance Am mu := by
    exact (variance_eq_integral hAm.aemeasurable).symm
  have hVp : (∫z,Fp z ∂mu)=variance Ap mu := by
    exact (variance_eq_integral hAp.aemeasurable).symm
  have hQmEq := physical_side_score_error_integral n steps ha q0 pre.length am (fun j=>pre.length < j.val)
  have hQpEq := physical_side_score_error_integral n steps ha q0 pre.length ap (fun j=>j.val < pre.length)
  change (∫z,Qm z ∂mu)=_ at hQmEq
  change (∫z,Qp z ∂mu)=_ at hQpEq
  rw [hExpand,hVm,hVp,hQmEq,hQpEq] at hInt
  have hD := physical_centered_overlap_integral_le_score n pre tail ha q0 c
  dsimp only at hD
  change physicalCutPairDefectSecond n pre tail q0 c ≤ 4*(∫z,F z ∂mu)+_ at hD
  linarith

theorem physicalSideNoiseMoment_comm (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (q0 : FeatureIndex n → ℝ≥0) (i j : ℕ) :
    physicalSideNoiseMoment n steps q0 i j=physicalSideNoiseMoment n steps q0 j i := by
  unfold physicalSideNoiseMoment
  congr 1
  funext z
  unfold orderedScoreNoise
  rw [max_comm j i]
  simp only [inner_sub_right]
  ring

theorem physicalSideNoiseMoment_le_two_defects (n : ℕ)
    (pre mid tail : List (GaussianStep (FeatureIndex n)))
    (ha : OrderedSteps 0 ((pre++mid)++tail)) (q0 : FeatureIndex n → ℝ≥0)
    {Si Sj Ci eta : ℝ} (hCi : 0 ≤ Ci) (heta : 0 ≤ eta) (hS : |Sj-Si| ≤ eta) :
    let steps := (pre++mid)++tail
    let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps
    let Cj := ∫z,physicalSpinTraceCovSq n tail (actualCutField (pre++mid) tail z.1 z.2) ∂mu
    let Di := physicalCutPairDefectSecond n pre (mid++tail) q0 Si
    let Dj := physicalCutPairDefectSecond n (pre++mid) tail q0 Sj
    physicalSideNoiseMoment n steps q0 pre.length (pre++mid).length ≤
      Real.sqrt (Ci+Cj)*(eta+4*Real.sqrt (Di+Dj)) := by
  have hi : pre.length ≤ (pre++mid).length := by simp
  simpa only [physicalSideNoiseMoment,orderedScoreNoise,max_eq_right hi] using
    physical_ordered_noise_le_two_defects n pre mid tail ha q0 hCi heta hS

end OAI.SKFluctuations
