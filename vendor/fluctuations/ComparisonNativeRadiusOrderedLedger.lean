module

public import ComparisonNativeRadiusCellLengths
public import ComparisonActualCutLedger
public import ComparisonActualDefectBounds
public import ComparisonPhysicalReverseMovement

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open LaplaceWindowFormalization WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 3000000
attribute [local instance] Classical.propDecidable

theorem radius_rootLevelPairMean_linear (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n→ℝ≥0) (K L : Spin n→Spin n→ℝ) (a b : ℝ) (i : ℕ) :
    rootLevelPairMean (uniformWeight n) (finiteFeature n) q0
      (fun s t=>a*K s t+b*L s t) steps i=
      a*rootLevelPairMean (uniformWeight n) (finiteFeature n) q0 K steps i+
      b*rootLevelPairMean (uniformWeight n) (finiteFeature n) q0 L steps i := by
  unfold rootLevelPairMean zeroContinuation
  simp_rw [levelPairMean_linear (uniformWeight_pos n) (finiteFeature n) K L steps ha a b]
  have hiK := (levelPairMean_smooth (uniformWeight_pos n) (finiteFeature n) K steps ha i 0).integrable_zero_shift (ν:=Measure.pi fun k=>gaussianReal 0 (q0 k)) 0
  have hiL := (levelPairMean_smooth (uniformWeight_pos n) (finiteFeature n) L steps ha i 0).integrable_zero_shift (ν:=Measure.pi fun k=>gaussianReal 0 (q0 k)) 0
  rw [integral_add (hiK.const_mul a) (hiL.const_mul b),integral_const_mul,integral_const_mul]

theorem radius_actualCenteredCutReplicaDefect_le_raw_overlap (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n→ℝ≥0) {i : ℕ} (hi : i ≤ steps.length) :
    actualCutReplicaDefect n steps q0 i (physicalPathSecondMoment n steps q0 i) ≤
      4*rootLevelPairMean (uniformWeight n) (finiteFeature n) q0
        (fun s t=>(orderedOverlap n s t)^2) steps i := by
  let S := physicalPathSecondMoment n steps q0 i
  let B := rootLevelPairMean (uniformWeight n) (finiteFeature n) q0
    (fun s t=>(orderedOverlap n s t)^2) steps i
  have hs : S^2 ≤ B := by
    have h := rootLevelPairMean_square (uniformWeight_pos n) (finiteFeature n) q0
      (orderedOverlap n) steps ha i
    rw [←physicalSecondMoment_eq_rootLevelPairMean n steps ha q0 i hi] at h
    exact h
  have h := rootLevelPairMean_mono (uniformWeight_pos n) (finiteFeature n) q0
    (K:=fun s t=>(orderedOverlap n s t-S)^2)
    (L:=fun s t=>2*(orderedOverlap n s t)^2+2*S^2)
    (fun s t=>by nlinarith [sq_nonneg (orderedOverlap n s t+S)]) steps ha i
  rw [radius_rootLevelPairMean_linear n steps ha q0
    (fun s t=>(orderedOverlap n s t)^2) (fun _ _=>S^2) 2 2 i,
    rootLevelPairMean_const (uniformWeight_pos n) (finiteFeature n) q0 steps ha i (S^2)] at h
  change actualCutReplicaDefect n steps q0 i S ≤ _ at h
  dsimp only [B] at hs
  linarith

theorem radius_physicalSideMovementMoment_le_raw (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n→ℝ≥0) {xs : ℝ} (hxs : 0 < xs)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ steps.length+1) :
    physicalSideMovementMoment n steps q0 i j ≤
      16*(physicalRawRatio n 2 steps 0 xs
        (Measure.pi fun k=>gaussianReal 0 (q0 k)) id measurable_id)^4*
        (xs+physicalCutMass 0 steps j)^2 := by
  have h := physicalRawRatio_increment_moment n 2 (by norm_num) steps ha hxs
    (Measure.pi fun k=>gaussianReal 0 (q0 k)) id measurable_id hij hj
  rw [←rootedHierarchyPathLaw_eq_physical] at h
  change physicalSideMovementMoment n steps q0 i j ≤ _ at h
  norm_num only at h
  convert h using 1 <;> ring

theorem radius_physicalSideNoiseMoment_le_raw_covariance (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n→ℝ≥0) {xs y : ℝ} (hxs : 0 < xs)
    {i j : ℕ} (hi : i ≤ steps.length) (hj : j ≤ steps.length)
    (hui : xs+physicalCutMass 0 steps i ≤ y)
    (huj : xs+physicalCutMass 0 steps j ≤ y) :
    physicalSideNoiseMoment n steps q0 i j ≤
      4*(physicalRawRatio n 2 steps 0 xs
        (Measure.pi fun k=>gaussianReal 0 (q0 k)) id measurable_id)^2*y*
        Real.sqrt (actualCutCovarianceEnergy n steps q0 i+
          actualCutCovarianceEnergy n steps q0 j) := by
  let Q := physicalRawRatio n 2 steps 0 xs
    (Measure.pi fun k=>gaussianReal 0 (q0 k)) id measurable_id
  have hy : 0 ≤ y := (add_nonneg hxs.le (physicalCutMass_mem steps ha i).1).trans hui
  have hordered {i j : ℕ} (hij : i ≤ j) (hj : j ≤ steps.length)
      (huj : xs+physicalCutMass 0 steps j ≤ y) :
      physicalSideNoiseMoment n steps q0 i j ≤
        4*Q^2*y*Real.sqrt (actualCutCovarianceEnergy n steps q0 i+
          actualCutCovarianceEnergy n steps q0 j) := by
    let pre := steps.take j
    let tail := steps.drop j
    have hfull : pre++tail=steps := List.take_append_drop j steps
    have hlen : pre.length=j := by simp [pre,min_eq_left hj]
    have ho : OrderedSteps 0 (pre++tail) := by simpa only [hfull] using ha
    have hnoise := physical_ordered_noise_integral_le_trace n pre tail ho q0
      (i:=i) (by simpa only [hlen] using hij)
    dsimp only at hnoise
    rw [←actualCutCovarianceEnergy_at_prefix] at hnoise
    have heN : physicalSideNoiseMoment n steps q0 i j ≤
        Real.sqrt (actualCutCovarianceEnergy n steps q0 j)*
          Real.sqrt (physicalSideMovementMoment n steps q0 i j) := by
      rw [hfull,hlen] at hnoise
      simpa only [physicalSideNoiseMoment,orderedScoreNoise,max_eq_right hij,
        physicalSideMovementMoment] using hnoise
    have hmove := radius_physicalSideMovementMoment_le_raw n steps ha q0 hxs hij
      (show j ≤ steps.length+1 by omega)
    have hyj : 0 ≤ xs+physicalCutMass 0 steps j :=
      add_nonneg hxs.le (physicalCutMass_mem steps ha j).1
    have hb : physicalSideMovementMoment n steps q0 i j ≤ (4*Q^2*y)^2 := by
      apply hmove.trans
      have hp := pow_le_pow_left₀ hyj huj 2
      have h := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 16*Q^4)
      dsimp only [Q] at h ⊢
      nlinarith
    have hs := Real.sqrt_le_sqrt hb
    rw [Real.sqrt_sq (by positivity : 0 ≤ 4*Q^2*y)] at hs
    have hc := Real.sqrt_le_sqrt
      (show actualCutCovarianceEnergy n steps q0 j ≤ actualCutCovarianceEnergy n steps q0 i+actualCutCovarianceEnergy n steps q0 j from le_add_of_nonneg_left (actualCutCovarianceEnergy_nonneg n steps ha q0 i))
    exact heN.trans (by
      have hm := mul_le_mul hc hs (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      simpa only [mul_comm,mul_left_comm,mul_assoc] using hm)
  by_cases hij : i ≤ j
  · exact hordered hij hj huj
  · rw [physicalSideNoiseMoment_comm]
    simpa only [add_comm] using hordered (le_of_not_ge hij) hi hui

namespace NativeRadiusSide

def before {N : ℕ} (mass : Fin N→ℝ) (i : Fin N) : ℝ :=
  ∑j,if j < i then mass j else 0
def after {N : ℕ} (mass : Fin N→ℝ) (i : Fin N) : ℝ :=
  ∑j,if i < j then mass j else 0
def leftProbability {N : ℕ} (mass : Fin N→ℝ) (i j : Fin N) : ℝ :=
  (if j < i then mass j else 0)/before mass i
def rightProbability {N : ℕ} (mass : Fin N→ℝ) (i j : Fin N) : ℝ :=
  (if i < j then mass j else 0)/after mass i
def leftCoefficient {N : ℕ} (duration mass : Fin N→ℝ) (i j : Fin N) : ℝ :=
  if mass j=0 then 0 else leftProbability mass i j/duration j
def rightCoefficient {N : ℕ} (duration mass : Fin N→ℝ) (i j : Fin N) : ℝ :=
  if mass j=0 then 0 else rightProbability mass i j/duration j
def leftJoint {N : ℕ} (mass : Fin N→ℝ) (G : Finset (Fin N)) (i j : Fin N) : ℝ :=
  if i∈G then mass i*leftProbability mass i j else 0
def rightJoint {N : ℕ} (mass : Fin N→ℝ) (G : Finset (Fin N)) (i j : Fin N) : ℝ :=
  if i∈G then mass i*rightProbability mass i j else 0

theorem before_nonneg {N : ℕ} (mass : Fin N→ℝ) (hm : ∀i,0 ≤ mass i) (i : Fin N) :
    0 ≤ before mass i := by
  unfold before
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact hm j
  · exact le_rfl
theorem after_nonneg {N : ℕ} (mass : Fin N→ℝ) (hm : ∀i,0 ≤ mass i) (i : Fin N) :
    0 ≤ after mass i := by
  unfold after
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact hm j
  · exact le_rfl

theorem leftProbability_nonneg {N : ℕ} (mass : Fin N→ℝ)
    (hm : ∀i,0 ≤ mass i) (i j : Fin N) : 0 ≤ leftProbability mass i j := by
  unfold leftProbability
  apply div_nonneg _ (before_nonneg mass hm i)
  split_ifs
  · exact hm j
  · exact le_rfl
theorem rightProbability_nonneg {N : ℕ} (mass : Fin N→ℝ)
    (hm : ∀i,0 ≤ mass i) (i j : Fin N) : 0 ≤ rightProbability mass i j := by
  unfold rightProbability
  apply div_nonneg _ (after_nonneg mass hm i)
  split_ifs
  · exact hm j
  · exact le_rfl

theorem leftProbability_sum {N : ℕ} (mass : Fin N→ℝ) (i : Fin N)
    (hi : 0 < before mass i) : ∑j,leftProbability mass i j=1 := by
  simp only [leftProbability,←Finset.sum_div]
  exact div_self hi.ne'
theorem rightProbability_sum {N : ℕ} (mass : Fin N→ℝ) (i : Fin N)
    (hi : 0 < after mass i) : ∑j,rightProbability mass i j=1 := by
  simp only [rightProbability,←Finset.sum_div]
  exact div_self hi.ne'

theorem duration_mul_leftCoefficient {N : ℕ} (duration mass : Fin N→ℝ)
    (hz : ∀j,duration j=0→mass j=0) (i j : Fin N) :
    duration j*leftCoefficient duration mass i j=leftProbability mass i j := by
  by_cases hm : mass j=0
  · simp [leftCoefficient,hm,leftProbability]
  · have hd : duration j≠0 := fun h=>hm (hz j h)
    simp only [leftCoefficient,hm,ite_eq_right]
    exact mul_div_cancel₀ _ hd
theorem duration_mul_rightCoefficient {N : ℕ} (duration mass : Fin N→ℝ)
    (hz : ∀j,duration j=0→mass j=0) (i j : Fin N) :
    duration j*rightCoefficient duration mass i j=rightProbability mass i j := by
  by_cases hm : mass j=0
  · simp [rightCoefficient,hm,rightProbability]
  · have hd : duration j≠0 := fun h=>hm (hz j h)
    simp only [rightCoefficient,hm,ite_eq_right]
    exact mul_div_cancel₀ _ hd

theorem leftCoefficient_nonneg {N : ℕ} (duration mass : Fin N→ℝ)
    (hd : ∀j,0 ≤ duration j) (hm : ∀j,0 ≤ mass j) (i j : Fin N) :
    0 ≤ leftCoefficient duration mass i j := by
  unfold leftCoefficient
  split_ifs
  · exact le_rfl
  · exact div_nonneg (leftProbability_nonneg mass hm i j) (hd j)
theorem rightCoefficient_nonneg {N : ℕ} (duration mass : Fin N→ℝ)
    (hd : ∀j,0 ≤ duration j) (hm : ∀j,0 ≤ mass j) (i j : Fin N) :
    0 ≤ rightCoefficient duration mass i j := by
  unfold rightCoefficient
  split_ifs
  · exact le_rfl
  · exact div_nonneg (rightProbability_nonneg mass hm i j) (hd j)

theorem left_reverse_sum_eq_zero {N : ℕ} (mass : Fin N→ℝ) (i : Fin N) (M : Fin N→ℝ) :
    (∑j,leftProbability mass i j*(if i.val < j.val then M j else 0))=0 := by
  apply Finset.sum_eq_zero
  intro j _
  by_cases h : j < i
  · simp only [leftProbability,h,ite_eq_left,ite_eq_right (show ¬i.val < j.val by exact not_lt_of_ge (le_of_lt h)),mul_zero]
  · simp [leftProbability,h]
theorem right_reverse_sum_eq_zero {N : ℕ} (mass : Fin N→ℝ) (i : Fin N) (M : Fin N→ℝ) :
    (∑j,rightProbability mass i j*(if j.val < i.val then M j else 0))=0 := by
  apply Finset.sum_eq_zero
  intro j _
  by_cases h : i < j
  · simp only [rightProbability,h,ite_eq_left,ite_eq_right (show ¬j.val < i.val by exact not_lt_of_ge (le_of_lt h)),mul_zero]
  · simp [rightProbability,h]

theorem leftJoint_nonneg {N : ℕ} (mass : Fin N→ℝ) (G : Finset (Fin N))
    (hm : ∀i,0 ≤ mass i) (i j : Fin N) : 0 ≤ leftJoint mass G i j := by
  unfold leftJoint
  split_ifs
  · exact mul_nonneg (hm i) (leftProbability_nonneg mass hm i j)
  · exact le_rfl
theorem rightJoint_nonneg {N : ℕ} (mass : Fin N→ℝ) (G : Finset (Fin N))
    (hm : ∀i,0 ≤ mass i) (i j : Fin N) : 0 ≤ rightJoint mass G i j := by
  unfold rightJoint
  split_ifs
  · exact mul_nonneg (hm i) (rightProbability_nonneg mass hm i j)
  · exact le_rfl

theorem leftJoint_row_le {N : ℕ} (mass : Fin N→ℝ) (G : Finset (Fin N))
    (hm : ∀i,0 ≤ mass i) (hG : ∀i∈G,0 < before mass i) (i : Fin N) :
    (∑j,leftJoint mass G i j) ≤ mass i := by
  by_cases hi : i∈G
  · simp [leftJoint,hi,←Finset.mul_sum,leftProbability_sum mass i (hG i hi)]
  · simpa [leftJoint,hi] using hm i
theorem rightJoint_row_le {N : ℕ} (mass : Fin N→ℝ) (G : Finset (Fin N))
    (hm : ∀i,0 ≤ mass i) (hG : ∀i∈G,0 < after mass i) (i : Fin N) :
    (∑j,rightJoint mass G i j) ≤ mass i := by
  by_cases hi : i∈G
  · simp [rightJoint,hi,←Finset.mul_sum,rightProbability_sum mass i (hG i hi)]
  · simpa [rightJoint,hi] using hm i

theorem leftJoint_column_le {N : ℕ} (mass : Fin N→ℝ) (G : Finset (Fin N))
    (hm : ∀i,0 ≤ mass i) {delta : ℝ} (hd : 0 < delta)
    (hG : ∀i∈G,delta ≤ before mass i) (j : Fin N) :
    (∑i,leftJoint mass G i j) ≤ ((∑i,mass i)/delta)*mass j := by
  have hp i : leftJoint mass G i j ≤ mass i*(mass j/delta) := by
    by_cases hi : i∈G
    · unfold leftJoint leftProbability
      simp only [hi,ite_eq_left]
      split_ifs
      · exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (hm j) hd (hG i hi)) (hm i)
      · simpa only [zero_div,mul_zero] using mul_nonneg (hm i) (div_nonneg (hm j) hd.le)
    · simp only [leftJoint,hi,ite_eq_right]
      exact mul_nonneg (hm i) (div_nonneg (hm j) hd.le)
  calc
    _ ≤ ∑i,mass i*(mass j/delta) := Finset.sum_le_sum (fun i _=>hp i)
    _ = _ := by rw [←Finset.sum_mul];ring
theorem rightJoint_column_le {N : ℕ} (mass : Fin N→ℝ) (G : Finset (Fin N))
    (hm : ∀i,0 ≤ mass i) {delta : ℝ} (hd : 0 < delta)
    (hG : ∀i∈G,delta ≤ after mass i) (j : Fin N) :
    (∑i,rightJoint mass G i j) ≤ ((∑i,mass i)/delta)*mass j := by
  have hp i : rightJoint mass G i j ≤ mass i*(mass j/delta) := by
    by_cases hi : i∈G
    · unfold rightJoint rightProbability
      simp only [hi,ite_eq_left]
      split_ifs
      · exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (hm j) hd (hG i hi)) (hm i)
      · simpa only [zero_div,mul_zero] using mul_nonneg (hm i) (div_nonneg (hm j) hd.le)
    · simp only [rightJoint,hi,ite_eq_right]
      exact mul_nonneg (hm i) (div_nonneg (hm j) hd.le)
  calc
    _ ≤ ∑i,mass i*(mass j/delta) := Finset.sum_le_sum (fun i _=>hp i)
    _ = _ := by rw [←Finset.sum_mul];ring

theorem joint_raw_noise_le {N : ℕ} (P : Fin N→Fin N→ℝ)
    (mass C : Fin N→ℝ) (pairNoise : Fin N→Fin N→ℝ)
    {L A : ℝ} (hP : ∀i j,0 ≤ P i j) (hm : ∀i,0 ≤ mass i)
    (hC : ∀i,0 ≤ C i) (hL : 0 ≤ L) (hA : 0 ≤ A)
    (hrow : ∀i,(∑j,P i j) ≤ mass i) (hcol : ∀j,(∑i,P i j) ≤ L*mass j)
    (hnoise : ∀i j,P i j≠0→pairNoise i j ≤ A*Real.sqrt (C i+C j)) :
    (∑i,∑j,P i j*pairNoise i j) ≤
      A*Real.sqrt ((1+L)*(∑i,mass i*C i))*Real.sqrt (∑i,mass i) := by
  have hmass : 0 ≤ ∑i,mass i := Finset.sum_nonneg (fun i _=>hm i)
  have henergy : 0 ≤ ∑i,∑j,P i j*(C i+C j) :=
    Finset.sum_nonneg (fun i _=>Finset.sum_nonneg (fun j _=>mul_nonneg (hP i j) (add_nonneg (hC i) (hC j))))
  have htotal : 0 ≤ ∑i,∑j,P i j :=
    Finset.sum_nonneg (fun i _=>Finset.sum_nonneg (fun j _=>hP i j))
  have h := weighted_sqrt_product_le (fun p:Fin N×Fin N=>P p.1 p.2)
    (fun p=>C p.1+C p.2) (fun _=>1)
    (fun p=>hP p.1 p.2) (fun p=>add_nonneg (hC p.1) (hC p.2)) (fun _=>by norm_num)
  simp only [Fintype.sum_prod_type,Real.sqrt_one,mul_one] at h
  have he := joint_marginal_energy_le P mass C hC hrow hcol
  have ht := joint_total_mass_le P mass hrow
  have hr := mul_le_mul (Real.sqrt_le_sqrt he) (Real.sqrt_le_sqrt ht)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hpoint i j : P i j*pairNoise i j ≤ P i j*(A*Real.sqrt (C i+C j)) := by
    by_cases hp : P i j=0
    · simp only [hp,zero_mul];exact le_rfl
    · exact mul_le_mul_of_nonneg_left (hnoise i j hp) (hP i j)
  calc
    _ ≤ ∑i,∑j,P i j*(A*Real.sqrt (C i+C j)) :=
      Finset.sum_le_sum (fun i _=>Finset.sum_le_sum (fun j _=>hpoint i j))
    _ = A*(∑i,∑j,P i j*Real.sqrt (C i+C j)) := by
      simp_rw [mul_left_comm _ A,←Finset.mul_sum]
    _ ≤ _ := by
      exact (mul_le_mul_of_nonneg_left (h.trans hr) hA).trans_eq (by ring)

end NativeRadiusSide

theorem radius_physical_ordered_score_ledger (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n→ℝ≥0) (mass : Fin (steps.length+1)→ℝ)
    (hmass : ∀j,0 ≤ mass j)
    (hzero : ∀j,pathMassDifferences steps 0 j=0→mass j=0)
    (i : Fin (steps.length+1)) (hi : mass i≠0)
    (hl : 0 < NativeRadiusSide.before mass i) (hr : 0 < NativeRadiusSide.after mass i)
    {eta : ℝ} (heta : 0 ≤ eta)
    (hS : ∀j,mass j≠0→
      |physicalPathSecondMoment n steps q0 j.val-physicalPathSecondMoment n steps q0 i.val| ≤ eta) :
    let km := NativeRadiusSide.leftCoefficient (pathMassDifferences steps 0) mass i
    let kp := NativeRadiusSide.rightCoefficient (pathMassDifferences steps 0) mass i
    actualCutReplicaDefect n steps q0 i.val (physicalPathSecondMoment n steps q0 i.val) ≤
      24*selectedScoreVariance n steps q0 km+24*selectedScoreVariance n steps q0 kp+6*eta^2+
      32*(∑j,NativeRadiusSide.leftProbability mass i j*physicalSideNoiseMoment n steps q0 i.val j.val)+
      32*(∑j,NativeRadiusSide.rightProbability mass i j*physicalSideNoiseMoment n steps q0 i.val j.val)+
      actualCutCovarianceEnergy n steps q0 i.val := by
  dsimp only
  let dm := pathMassDifferences steps 0
  let km := NativeRadiusSide.leftCoefficient dm mass i
  let kp := NativeRadiusSide.rightCoefficient dm mass i
  have hd j : 0 ≤ dm j := pathMassDifferences_nonneg steps ha j
  have hkm j := NativeRadiusSide.leftCoefficient_nonneg dm mass hd hmass i j
  have hkp j := NativeRadiusSide.rightCoefficient_nonneg dm mass hd hmass i j
  have hcl j := NativeRadiusSide.duration_mul_leftCoefficient dm mass hzero i j
  have hcr j := NativeRadiusSide.duration_mul_rightCoefficient dm mass hzero i j
  have hnorml : ∑j,dm j*km j=1 := by
    simp only [km,hcl]
    exact NativeRadiusSide.leftProbability_sum mass i hl
  have hnormr : ∑j,dm j*kp j=1 := by
    simp only [kp,hcr]
    exact NativeRadiusSide.rightProbability_sum mass i hr
  have hmeanl := weighted_mean_sub_abs_le (NativeRadiusSide.leftProbability mass i)
    (fun j=>physicalPathSecondMoment n steps q0 j.val)
    (fun j=>NativeRadiusSide.leftProbability_nonneg mass hmass i j)
    (NativeRadiusSide.leftProbability_sum mass i hl) (fun j hj=>by
      apply hS j
      intro hm
      exact hj (by simp [NativeRadiusSide.leftProbability,hm]))
  have hmeanr := weighted_mean_sub_abs_le (NativeRadiusSide.rightProbability mass i)
    (fun j=>physicalPathSecondMoment n steps q0 j.val)
    (fun j=>NativeRadiusSide.rightProbability_nonneg mass hmass i j)
    (NativeRadiusSide.rightProbability_sum mass i hr) (fun j hj=>by
      apply hS j
      intro hm
      exact hj (by simp [NativeRadiusSide.rightProbability,hm]))
  have hmeanl' : |(∑j,(dm j*km j)*physicalPathSecondMoment n steps q0 j.val)-
      physicalPathSecondMoment n steps q0 i.val| ≤ eta := by simpa only [km,hcl] using hmeanl
  have hmeanr' : |(∑j,(dm j*kp j)*physicalPathSecondMoment n steps q0 j.val)-
      physicalPathSecondMoment n steps q0 i.val| ≤ eta := by simpa only [kp,hcr] using hmeanr
  have h := physical_two_sided_actual_cut_score_ledger n steps ha q0 i.val
    (by omega) km kp hkm hkp hnorml hnormr heta hmeanl' hmeanr'
  dsimp only at h
  simp only [show pathMassDifferences steps 0=dm from rfl] at h
  simp only [km,kp,hcl,hcr,NativeRadiusSide.left_reverse_sum_eq_zero,
    NativeRadiusSide.right_reverse_sum_eq_zero,mul_zero,add_zero] at h
  exact h

theorem radius_physical_ordered_integrated_defect_le (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n→ℝ≥0) (mass : Fin (steps.length+1)→ℝ)
    (G : Finset (Fin (steps.length+1)))
    (hmass : ∀j,0 ≤ mass j)
    (hzero : ∀j,pathMassDifferences steps 0 j=0→mass j=0)
    {xs y delta eta V B : ℝ} (hxs : 0 < xs) (hy : 0 ≤ y) (hd : 0 < delta)
    (heta : 0 ≤ eta) (hV : 0 ≤ V) (hB : 0 ≤ B)
    (hl : ∀i∈G,delta ≤ NativeRadiusSide.before mass i)
    (hr : ∀i∈G,delta ≤ NativeRadiusSide.after mass i)
    (hband : ∀i,mass i≠0→xs+physicalCutMass 0 steps i.val ≤ y)
    (hS : ∀i,mass i≠0→∀j,mass j≠0→
      |physicalPathSecondMoment n steps q0 j.val-physicalPathSecondMoment n steps q0 i.val| ≤ eta)
    (hvarianceL : ∀i∈G,selectedScoreVariance n steps q0
      (NativeRadiusSide.leftCoefficient (pathMassDifferences steps 0) mass i) ≤ V)
    (hvarianceR : ∀i∈G,selectedScoreVariance n steps q0
      (NativeRadiusSide.rightCoefficient (pathMassDifferences steps 0) mass i) ≤ V)
    (hrawPair : ∀i,mass i≠0→i∉G→
      rootLevelPairMean (uniformWeight n) (finiteFeature n) q0
        (fun s t=>(orderedOverlap n s t)^2) steps i.val ≤ B) :
    let Q := physicalRawRatio n 2 steps 0 xs
      (Measure.pi fun k=>gaussianReal 0 (q0 k)) id measurable_id
    let v := ∑i,mass i
    let T := ∑i,mass i*actualCutCovarianceEnergy n steps q0 i.val
    (∑i,mass i*actualCutReplicaDefect n steps q0 i.val
      (physicalPathSecondMoment n steps q0 i.val)) ≤
      (48*V+6*eta^2)*v+
        256*Q^2*y*Real.sqrt ((1+v/delta)*T)*Real.sqrt v+T+
        4*B*(∑i,if i∈G then 0 else mass i) := by
  dsimp only
  let Q := physicalRawRatio n 2 steps 0 xs
    (Measure.pi fun k=>gaussianReal 0 (q0 k)) id measurable_id
  let C := fun i:Fin (steps.length+1)=>actualCutCovarianceEnergy n steps q0 i.val
  let D := fun i:Fin (steps.length+1)=>actualCutReplicaDefect n steps q0 i.val
    (physicalPathSecondMoment n steps q0 i.val)
  let noise := fun i j:Fin (steps.length+1)=>physicalSideNoiseMoment n steps q0 i.val j.val
  let PL := NativeRadiusSide.leftJoint mass G
  let PR := NativeRadiusSide.rightJoint mass G
  let v := ∑i,mass i
  let T := ∑i,mass i*C i
  let cost := 48*V+6*eta^2
  let A := 4*Q^2*y
  have hv : 0 ≤ v := Finset.sum_nonneg (fun i _=>hmass i)
  have hC i : 0 ≤ C i := actualCutCovarianceEnergy_nonneg n steps ha q0 i.val
  have hcost : 0 ≤ cost := by dsimp only [cost];positivity
  have hA : 0 ≤ A := by dsimp only [A];positivity
  have hLP i (hi : i∈G) : 0 < NativeRadiusSide.before mass i := by
    exact hd.trans_le (hl i hi)
  have hRP i (hi : i∈G) : 0 < NativeRadiusSide.after mass i := by
    exact hd.trans_le (hr i hi)
  have hPnL i j : 0 ≤ PL i j := NativeRadiusSide.leftJoint_nonneg mass G hmass i j
  have hPnR i j : 0 ≤ PR i j := NativeRadiusSide.rightJoint_nonneg mass G hmass i j
  have hNoiseL i j (hp : PL i j≠0) : noise i j ≤ A*Real.sqrt (C i+C j) := by
    have hmi : mass i≠0 := by
      intro hi
      exact hp (by simp [PL,NativeRadiusSide.leftJoint,hi])
    have hmj : mass j≠0 := by
      intro hj
      exact hp (by simp [PL,NativeRadiusSide.leftJoint,NativeRadiusSide.leftProbability,hj])
    exact radius_physicalSideNoiseMoment_le_raw_covariance n steps ha q0 hxs
      (by omega) (by omega) (hband i hmi) (hband j hmj)
  have hNoiseR i j (hp : PR i j≠0) : noise i j ≤ A*Real.sqrt (C i+C j) := by
    have hmi : mass i≠0 := by
      intro hi
      exact hp (by simp [PR,NativeRadiusSide.rightJoint,hi])
    have hmj : mass j≠0 := by
      intro hj
      exact hp (by simp [PR,NativeRadiusSide.rightJoint,NativeRadiusSide.rightProbability,hj])
    exact radius_physicalSideNoiseMoment_le_raw_covariance n steps ha q0 hxs
      (by omega) (by omega) (hband i hmi) (hband j hmj)
  have hNL := NativeRadiusSide.joint_raw_noise_le PL mass C noise hPnL hmass hC
    (div_nonneg hv hd.le) hA
    (NativeRadiusSide.leftJoint_row_le mass G hmass (fun i hi=>hLP i hi))
    (NativeRadiusSide.leftJoint_column_le mass G hmass hd hl) hNoiseL
  have hNR := NativeRadiusSide.joint_raw_noise_le PR mass C noise hPnR hmass hC
    (div_nonneg hv hd.le) hA
    (NativeRadiusSide.rightJoint_row_le mass G hmass (fun i hi=>hRP i hi))
    (NativeRadiusSide.rightJoint_column_le mass G hmass hd hr) hNoiseR
  have hpoint i : mass i*D i ≤ cost*mass i+
      32*(∑j,PL i j*noise i j)+32*(∑j,PR i j*noise i j)+mass i*C i+
      4*B*(if i∈G then 0 else mass i) := by
    by_cases hm : mass i=0
    · have hpl j : PL i j=0 := by simp [PL,NativeRadiusSide.leftJoint,hm]
      have hpr j : PR i j=0 := by simp [PR,NativeRadiusSide.rightJoint,hm]
      simp only [hm,mul_zero,zero_mul,hpl,hpr,Finset.sum_const_zero,add_zero]
      split_ifs <;> simp
    by_cases hi : i∈G
    · have h := radius_physical_ordered_score_ledger n steps ha q0 mass hmass hzero i hm
        (hLP i hi) (hRP i hi) heta (hS i hm)
      dsimp only at h
      have hV1 := hvarianceL i hi
      have hV2 := hvarianceR i hi
      have hmle := mul_le_mul_of_nonneg_left h (hmass i)
      have hV1m := mul_le_mul_of_nonneg_left hV1 (mul_nonneg (hmass i) (by norm_num : (0:ℝ)≤24))
      have hV2m := mul_le_mul_of_nonneg_left hV2 (mul_nonneg (hmass i) (by norm_num : (0:ℝ)≤24))
      have hpL : (∑j,PL i j*noise i j)=mass i*(∑j,NativeRadiusSide.leftProbability mass i j*noise i j) := by
        simp only [PL,NativeRadiusSide.leftJoint,hi,ite_eq_left,mul_assoc,←Finset.mul_sum]
      have hpR : (∑j,PR i j*noise i j)=mass i*(∑j,NativeRadiusSide.rightProbability mass i j*noise i j) := by
        simp only [PR,NativeRadiusSide.rightJoint,hi,ite_eq_left,mul_assoc,←Finset.mul_sum]
      rw [hpL,hpR,ite_eq_left hi]
      dsimp only [cost,D,C,noise] at *
      nlinarith
    · have h := radius_actualCenteredCutReplicaDefect_le_raw_overlap n steps ha q0 (i:=i.val) (by omega)
      have hb := hrawPair i hm hi
      have hD : D i ≤ 4*B := by dsimp only [D];linarith
      have hpl j : PL i j=0 := by simp [PL,NativeRadiusSide.leftJoint,hi]
      have hpr j : PR i j=0 := by simp [PR,NativeRadiusSide.rightJoint,hi]
      simp only [hpl,hpr,zero_mul,Finset.sum_const_zero,mul_zero,add_zero,ite_eq_right hi]
      have hh := mul_le_mul_of_nonneg_left hD (hmass i)
      have hc := mul_nonneg hcost (hmass i)
      have ht := mul_nonneg (hmass i) (hC i)
      nlinarith
  have hs := Finset.sum_le_sum (fun i (_ : i∈Finset.univ)=>hpoint i)
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at hs
  have hnL := mul_le_mul_of_nonneg_left hNL (by norm_num : 0 ≤ (32:ℝ))
  have hnR := mul_le_mul_of_nonneg_left hNR (by norm_num : 0 ≤ (32:ℝ))
  change (∑i,mass i*D i) ≤ _
  dsimp only [v,T,cost,A,Q] at hs hnL hnR ⊢
  nlinarith

end OAI.SKFluctuations
