module

public import PhysicalRetainedOverlapLimit
public import PhysicalFilledSourceDerivative
public import PhysicalSourceTraceBounds
public import HierarchyMixedHessianBound

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators
attribute [local instance] Classical.propDecidable
local instance (n : ℕ) : DecidableEq (FeatureIndex (n+1)) := fun _ _=>Classical.propDecidable _
set_option maxHeartbeats 1000000

theorem physicalJointGaussianDriver_column (n d : ℕ)
    (e : Fin (d+1) ≃ FeatureIndex n) (q : FeatureIndex n→ℝ≥0) (j : Fin (d+1)) :
    physicalJointGaussianDriver n d e q (Pi.single j 1)=
      Real.sqrt (q (e j):ℝ) • Pi.single (e j) 1 := by
  simp only [physicalJointGaussianDriver,ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe,coordinateEquiv_single]
  ext k
  by_cases hk : k=e j
  · subst k
    simp [scaleDriver_apply]
  · simp [scaleDriver_apply,Pi.single_apply,hk]

theorem physicalJointSpinJet_evolve_A₁_eq_response (n d : ℕ)
    (e : Fin (d+1) ≃ FeatureIndex n) (q : FeatureIndex n→ℝ≥0)
    (steps : List (GaussianStep (FeatureIndex n))) {a m : ℝ}
    (ha : OrderedSteps a steps) (hm : 0 < m) (T t : ℝ) (x : FeatureIndex n→ℝ)
    (i : Fin n) (j : Fin (d+1)) (z : Fin (d+1)→ℝ) :
    ((physicalSpinFeatureJet n d i (physicalJointGaussianDriver n d e q) steps ha x).evolve
      hm (T-t)).A₁ j z=
    gaussianHierarchyResponse (uniformWeight n) (finiteFeature n)
      (fun σ=>normalizedSpin n σ i) (physicalJointGaussianDriver n d e q (Pi.single j 1))
      ((m,fun k=>Real.toNNReal (T-t)*q k)::steps)
      (x+physicalJointGaussianDriver n d e q z) := by
  let L := physicalJointGaussianDriver n d e q
  let F := gaussianHierarchy (uniformWeight n) (finiteFeature n) steps
  let A := gaussianHierarchyMean (uniformWeight n) (finiteFeature n)
    (fun σ=>normalizedSpin n σ i) steps
  let G := gaussianHierarchyMean (uniformWeight n) (finiteFeature n)
    (fun σ=>finiteFeature n σ (L (Pi.single j 1))) steps
  let H := gaussianHierarchyResponse (uniformWeight n) (finiteFeature n)
    (fun σ=>normalizedSpin n σ i) (L (Pi.single j 1)) steps
  have hF := gaussianHierarchy_continuous (uniformWeight_pos n) (finiteFeature n) steps ha
  have hA := (gaussianHierarchyMean_smooth (uniformWeight_pos n) (finiteFeature n)
    (fun σ=>normalizedSpin n σ i) steps ha 0).continuous
  have hG := (gaussianHierarchyMean_smooth (uniformWeight_pos n) (finiteFeature n)
    (fun σ=>finiteFeature n σ (L (Pi.single j 1))) steps ha 0).continuous
  have hH := (gaussianHierarchyResponse_smooth (uniformWeight_pos n) (finiteFeature n)
    (fun σ=>normalizedSpin n σ i) (L (Pi.single j 1)) steps ha 0).continuous
  change clockGradient m (fun y=>F (x+L y)) (fun y=>G (x+L y)) (fun y=>A (x+L y))
    (fun y=>(physicalSpinFeatureJet n d i L steps ha x).A₁ j y) (T-t) z= _
  have he : (fun y=>(physicalSpinFeatureJet n d i L steps ha x).A₁ j y)=
      (fun y=>H (x+L y)) := by
    funext y
    exact gaussianFeatureJet_A₁ (uniformWeight_pos n) (finiteFeature n)
      (fun σ=>normalizedSpin n σ i) L steps ha x j y
  rw [he]
  change clockGradient m (fun y=>F (x+L y)) (fun y=>G (x+L y)) (fun y=>A (x+L y))
    (fun y=>H (x+L y)) (T-t) z= _
  unfold clockGradient
  rw [clockTest_affine_shift L hF hH,
    clockTest_affine_shift L hF (A:=fun y=>A y*G y) (hA.mul hG),
    clockTest_affine_shift L hF hA,clockTest_affine_shift L hF hG]
  simp only [L,F,A,G,H,linearClockTest,physicalJointGaussianDriver_linearGaussian,
    gaussianHierarchyResponse,gaussianHierarchyMean]

def physicalUniformCoordinateBound (n : ℕ) : ℝ :=
  ∑ k : FeatureIndex n,∑ σ,|finiteFeature n σ (Pi.single k 1)|

def physicalOverlapEnergyConstant (n : ℕ) : ℝ :=
  (n:ℝ)*((1+(physicalUniformCoordinateBound n)^2)/2)^2

theorem physicalUniformCoordinateBound_nonneg (n : ℕ) :
    0 ≤ physicalUniformCoordinateBound n :=
  Finset.sum_nonneg fun _ _=>Finset.sum_nonneg fun _ _=>abs_nonneg _

theorem physicalUniformCoordinateBound_bounds (n : ℕ) (σ : Spin n) (k : FeatureIndex n) :
    |finiteFeature n σ (Pi.single k 1)| ≤ physicalUniformCoordinateBound n := by
  exact (Finset.single_le_sum (fun τ _=>abs_nonneg (finiteFeature n τ (Pi.single k 1)))
    (Finset.mem_univ σ)).trans (Finset.single_le_sum
      (fun j _=>Finset.sum_nonneg fun τ _=>abs_nonneg (finiteFeature n τ (Pi.single j 1)))
      (Finset.mem_univ k))

theorem normalizedSpin_abs_le_one (n : ℕ) (σ : Spin n) (i : Fin n) :
    |normalizedSpin n σ i| ≤ 1 := by
  have hi := (Finset.single_le_sum (fun j _=>sq_nonneg (normalizedSpin n σ j))
    (Finset.mem_univ i)).trans (normalizedSpin_square_sum_le_one n σ)
  nlinarith [abs_nonneg (normalizedSpin n σ i),sq_abs (normalizedSpin n σ i)]

theorem physicalJointSpinJet_evolve_A₁_square_le (n d : ℕ)
    (e : Fin (d+1) ≃ FeatureIndex n) (q : FeatureIndex n→ℝ≥0)
    (steps : List (GaussianStep (FeatureIndex n))) {m : ℝ}
    (ha : OrderedSteps m steps) (hm : 0 < m) (T t : ℝ) (x : FeatureIndex n→ℝ)
    (i : Fin n) (j : Fin (d+1)) (z : Fin (d+1)→ℝ) :
    (((physicalSpinFeatureJet n d i (physicalJointGaussianDriver n d e q) steps ha x).evolve
      hm (T-t)).A₁ j z)^2 ≤
    (q (e j):ℝ)*((1+(physicalUniformCoordinateBound n)^2)/2)^2 := by
  let newsteps := (m,fun k=>Real.toNNReal (T-t)*q k)::steps
  have hn : OrderedSteps m newsteps := ⟨hm.le,le_rfl,hm,ha⟩
  rw [physicalJointSpinJet_evolve_A₁_eq_response,physicalJointGaussianDriver_column]
  have he : (fun σ=>normalizedSpin n σ i)=
      (fun σ=>finiteFeature n σ (physicalNormalizedSourceMap n (Pi.single i 1))) := by
    funext σ
    exact (physicalNormalizedSourceMap_feature n σ i).symm
  rw [he]
  change (gaussianHierarchyHessian (uniformWeight n) (finiteFeature n) newsteps
    (x+physicalJointGaussianDriver n d e q z)
    (physicalNormalizedSourceMap n (Pi.single i 1))
    (Real.sqrt (q (e j):ℝ) • Pi.single (e j) 1))^2 ≤ _
  rw [gaussianHierarchyHessian_smul_right (uniformWeight_pos n) (finiteFeature n) newsteps hn,
    mul_pow,Real.sq_sqrt (q (e j)).coe_nonneg]
  apply mul_le_mul_of_nonneg_left ?_ (q (e j)).coe_nonneg
  have hb := gaussianHierarchyHessian_mixed_abs_le (uniformWeight_pos n) (finiteFeature n)
    (physicalNormalizedSourceMap n (Pi.single i 1)) (Pi.single (e j) 1)
    (fun σ=>by simpa only [physicalNormalizedSourceMap_feature] using normalizedSpin_abs_le_one n σ i)
    (fun σ=>physicalUniformCoordinateBound_bounds n σ (e j)) newsteps hn
    (x+physicalJointGaussianDriver n d e q z)
  have hp : 0 ≤ (1+(physicalUniformCoordinateBound n)^2)/2 := by positivity
  simp only [one_pow] at hb
  simpa only [one_pow,sq_abs] using (sq_le_sq₀ (abs_nonneg _) hp).mpr hb

theorem physicalJointSpinJet_evolve_energy_le (n d : ℕ)
    (e : Fin (d+1) ≃ FeatureIndex n) (q : FeatureIndex n→ℝ≥0)
    (steps : List (GaussianStep (FeatureIndex n))) {m : ℝ}
    (ha : OrderedSteps m steps) (hm : 0 < m) (T t : ℝ) (x : FeatureIndex n→ℝ)
    (i : Fin n) (z : Fin (d+1)→ℝ) :
    ((physicalSpinFeatureJet n d i (physicalJointGaussianDriver n d e q) steps ha x).evolve
      hm (T-t)).energy z ≤
    ((1+(physicalUniformCoordinateBound n)^2)/2)^2 *∑ k,(q k:ℝ) := by
  unfold HeatJet.energy
  calc
    _ ≤ ∑ j,(q (e j):ℝ)*((1+(physicalUniformCoordinateBound n)^2)/2)^2 :=
      Finset.sum_le_sum fun j _=>physicalJointSpinJet_evolve_A₁_square_le n d e q steps ha hm T t x i j z
    _ = ((1+(physicalUniformCoordinateBound n)^2)/2)^2 *∑ k,(q k:ℝ) := by
      rw [←Finset.sum_mul]
      have hs : (∑ j : Fin (d+1),(q (e j):ℝ))=∑ k : FeatureIndex n,(q k:ℝ) :=
        Equiv.sum_comp e (fun k=>(q k:ℝ))
      rw [hs]
      ring

theorem physicalFilledOverlapEnergy_le_variance (n d : ℕ)
    (e : Fin (d+1) ≃ FeatureIndex n) (q : FeatureIndex n→ℝ≥0)
    (steps : List (GaussianStep (FeatureIndex n))) {m : ℝ}
    (ha : OrderedSteps m steps) (hm : 0 < m) (T t : ℝ) (x : FeatureIndex n→ℝ) :
    physicalFilledOverlapEnergy n d (physicalJointGaussianDriver n d e q) steps ha hm T t x ≤
      physicalOverlapEnergyConstant n*∑ k,(q k:ℝ) := by
  unfold physicalFilledOverlapEnergy
  calc
    _ ≤ ∑ i : Fin n,((1+(physicalUniformCoordinateBound n)^2)/2)^2 *∑ k,(q k:ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      let J := (physicalSpinFeatureJet n d i (physicalJointGaussianDriver n d e q) steps ha x).evolve hm (T-t)
      have hi := (exponentialIncrement_gaussian (fun _ : Fin (d+1)=>Real.toNNReal t)).integrable_shift J.lipschitz m 0
      have hh := shiftedMean_mono J.smoothEnergy (BddSmooth.const 0
        (((1+(physicalUniformCoordinateBound n)^2)/2)^2 *∑ k,(q k:ℝ)))
        (physicalJointSpinJet_evolve_energy_le n d e q steps ha hm T t x i) hi
      rw [shiftedMean_const _ hi] at hh
      exact hh
    _ = physicalOverlapEnergyConstant n*∑ k,(q k:ℝ) := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,physicalOverlapEnergyConstant]
      ring

end OAI.SKFluctuations.LaplaceWindowFormalization
