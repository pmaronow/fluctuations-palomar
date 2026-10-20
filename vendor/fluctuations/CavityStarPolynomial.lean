module

public import CavityPhysicalStarClosure

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations
open Hierarchy

 theorem savedStarLedger_le_polynomial (l : ℕ) {epsilon v A S Z M P : ℝ}
    (hepsilon : 0 < epsilon) (he1 : epsilon ≤ 1) (hv : 0 ≤ v) (hA : 0 ≤ A)
    (hS : |S| ≤ A*v) (hZ0 : 0 ≤ Z) (hZ : Z ≤ 5*epsilon*v)
    (hM0 : 0 ≤ M) (hM : M ≤ 32*epsilon*v) (hP : P ≤ (epsilon*v)^(2*l)) :
    (3:ℝ)^(2*l-1)*(P+(2:ℝ)^(4*l-2)*
      (M^(2*l)/epsilon^l+epsilon^l*(|S|+Z)^(2*l))+Z^(2*l)) ≤
    ((3:ℝ)^(2*l-1)*(1+5^(2*l)+2^(4*l-2)*(32^(2*l)+(A+5)^(2*l))))*
      epsilon^l*v^(2*l) := by
  have he2 : epsilon^(2*l) ≤ epsilon^l := pow_le_pow_of_le_one hepsilon.le he1 (by omega)
  have hE : 0 < epsilon^l := pow_pos hepsilon _
  have hVp : 0 ≤ v^(2*l) := pow_nonneg hv _
  have hZp := pow_le_pow_left₀ hZ0 hZ (2*l)
  have hMp := div_le_div_of_nonneg_right (pow_le_pow_left₀ hM0 hM (2*l)) hE.le
  have hSp : |S|+Z ≤ (A+5)*v := by nlinarith
  have hSpow := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity : 0 ≤ |S|+Z) hSp (2*l)) hE.le
  have hP' : P ≤ epsilon^l*v^(2*l) := by
    calc P ≤ (epsilon*v)^(2*l) := hP
         _ = epsilon^(2*l)*v^(2*l) := mul_pow _ _ _
         _ ≤ _ := mul_le_mul_of_nonneg_right he2 hVp
  have hZ' : Z^(2*l) ≤ 5^(2*l)*epsilon^l*v^(2*l) := by
    calc _ ≤ (5*epsilon*v)^(2*l) := hZp
         _ = 5^(2*l)*epsilon^(2*l)*v^(2*l) := by rw [mul_pow,mul_pow]
         _ ≤ _ := mul_le_mul_of_nonneg_right
           (mul_le_mul_of_nonneg_left he2 (by positivity)) hVp
  have hM' : M^(2*l)/epsilon^l ≤ 32^(2*l)*epsilon^l*v^(2*l) := by
    calc _ ≤ (32*epsilon*v)^(2*l)/epsilon^l := hMp
         _ = _ := by
           simp only [mul_pow, show 2*l=l+l by omega,pow_add]
           field_simp
           <;> ring
  have hS' : epsilon^l*(|S|+Z)^(2*l) ≤ (A+5)^(2*l)*epsilon^l*v^(2*l) := by
    apply hSpow.trans_eq
    rw [mul_pow]
    ring
  have hsum := add_le_add (add_le_add hP'
    (mul_le_mul_of_nonneg_left (add_le_add hM' hS') (by positivity : 0 ≤ (2:ℝ)^(4*l-2)))) hZ'
  calc _ ≤ (3:ℝ)^(2*l-1)*
      (epsilon^l*v^(2*l)+(2:ℝ)^(4*l-2)*
        (32^(2*l)*epsilon^l*v^(2*l)+(A+5)^(2*l)*epsilon^l*v^(2*l))+
        5^(2*l)*epsilon^l*v^(2*l)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
       _ = _ := by ring

structure PhysicalStarBufferData (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n)))
    (q0 : FeatureIndex n → ℝ≥0) (fork t : ℕ) (S : ℝ) where
  km : Fin (steps.length+1) → ℝ
  kp : Fin (steps.length+1) → ℝ
  eta : ℝ
  nonnegm : ∀ j, 0 ≤ km j
  nonnegp : ∀ j, 0 ≤ kp j
  normalizedm : ∑ j, pathMassDifferences steps 0 j*km j = 1
  normalizedp : ∑ j, pathMassDifferences steps 0 j*kp j = 1
  forkBound : fork ≤ steps.length+1
  centralBound : t ≤ steps.length+1
  forkPast : ∀ j, pathMassDifferences steps 0 j*km j ≠ 0 → j.val ≤ fork
  centralPast : ∀ j, pathMassDifferences steps 0 j*km j ≠ 0 → j.val ≤ t
  forkFuture : ∀ j, pathMassDifferences steps 0 j*kp j ≠ 0 → fork ≤ j.val
  centralFuture : ∀ j, pathMassDifferences steps 0 j*kp j ≠ 0 → t ≤ j.val
  etaNonneg : 0 ≤ eta
  meanPast : |(∑ j, pathMassDifferences steps 0 j*km j*
    physicalPathSecondMoment n steps q0 j.val)-S| ≤ eta
  meanFuture : |(∑ j, pathMassDifferences steps 0 j*kp j*
    physicalPathSecondMoment n steps q0 j.val)-S| ≤ eta

 theorem physicalBufferCenteredNorm_nonneg (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (q0 : FeatureIndex n → ℝ≥0)
    (k : Fin (steps.length+1) → ℝ) (p : ℝ) :
    0 ≤ physicalBufferCenteredNorm n steps q0 k p := by
  exact momentNorm_nonneg _ _

theorem physical_star_from_buffer_data_polynomial (n l : ℕ) (hl : 0 < l)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (fork t : ℕ) (S : ℝ)
    (D : PhysicalStarBufferData n steps q0 fork t S)
    {epsilon v A : ℝ} (hepsilon : 0 < epsilon) (he1 : epsilon ≤ 1)
    (hv : 0 ≤ v) (hA : 0 ≤ A) (hS : |S| ≤ A*v)
    (hCm : physicalBufferCenteredNorm n steps q0 D.km (2*l:ℕ) ≤ epsilon*v)
    (hCp : physicalBufferCenteredNorm n steps q0 D.kp (2*l:ℕ) ≤ epsilon*v)
    (heta : D.eta ≤ epsilon*v)
    (hProj : physicalOverlapProjectionErrorMoment n l steps
      (Measure.pi fun i => gaussianReal 0 (q0 i)) id measurable_id fork t ≤
        (epsilon*v)^(2*l)) :
    physicalStarPairMoment n l steps (Measure.pi fun i => gaussianReal 0 (q0 i))
      id measurable_id fork S ≤
    ((3:ℝ)^(2*l-1)*(1+5^(2*l)+2^(4*l-2)*(32^(2*l)+(A+5)^(2*l))))*
      epsilon^l*v^(2*l) := by
  let Z := physicalBufferedNormBudget n steps q0 D.km D.kp (2*l:ℕ) D.eta
  let M := physicalBufferedMovementBudget n steps q0 D.km D.kp (2*l:ℕ) D.eta
  have hZ : Z ≤ 5*epsilon*v := by
    dsimp [Z,physicalBufferedNormBudget]
    linarith
  have hM : M ≤ 32*epsilon*v := by
    dsimp only [M,physicalBufferedMovementBudget]
    change 4*Z+8*physicalBufferCenteredNorm n steps q0 D.km (2*l:ℕ)+4*D.eta ≤ _
    linarith
  have hCm0 := physicalBufferCenteredNorm_nonneg n steps q0 D.km (2*l:ℕ)
  have hCp0 := physicalBufferCenteredNorm_nonneg n steps q0 D.kp (2*l:ℕ)
  have hZ0 : 0 ≤ Z := by dsimp [Z,physicalBufferedNormBudget]; linarith [D.etaNonneg]
  have hM0 : 0 ≤ M := by
    change 0 ≤ 4*Z+8*physicalBufferCenteredNorm n steps q0 D.km (2*l:ℕ)+4*D.eta
    linarith [D.etaNonneg]
  have H := physical_star_from_actual_buffers n l hl steps ha q0 D.km D.kp
    D.nonnegm D.nonnegp D.normalizedm D.normalizedp fork t D.forkBound D.centralBound
    D.forkPast D.centralPast D.forkFuture D.centralFuture D.etaNonneg
    (pow_pos hepsilon l) D.meanPast D.meanFuture
  dsimp only at H
  exact H.trans (savedStarLedger_le_polynomial l hepsilon he1 hv hA hS hZ0 hZ hM0 hM hProj)

end OAI.SKFluctuations
