module

public import SKBarriers2.Interfaces
public import SKBarriers2.Overshoot.Defs
public import OAI.Probability.SKBarriers.Replicas.TripleTailValue
public import OAI.Probability.SKBarriers.Hierarchy.TimeChainRepresentation
public import OAI.Probability.SKBarriers.Scalar.ScalarSymmetry
public import OAI.Probability.SKBarriers.Scalar.ScalarListBounds
public import OAI.Probability.SKBarriers.Hierarchy.IncrementListAnalytic
public import OAI.Probability.SKBarriers.Hierarchy.TimeIncrementBridge
public import OAI.Probability.SKBarriers.Replicas.TripleTailSchedule
public import OAI.Probability.SKBarriers.Replicas.TripleScheduleEndpoint

@[expose] public section

noncomputable section
open scoped BigOperators Matrix NNReal Topology
open MeasureTheory ProbabilityTheory Set
open OAI.SK.Analytic

namespace SKBarriers2.OW

def windowGrid (α : ℝ → ℝ) (s h : ℝ) (N : ℕ) (a len c : ℝ)
    (vs : List (Fin 3 → ℝ)) : List (ℝ × (Fin 3 → ℝ)) :=
  (List.range N).flatMap fun (j : ℕ) => vs.map fun v =>
    (α (s + h * (a + len * (j : ℝ) / (N : ℝ))) / c,
      Real.sqrt (h * len / (N : ℝ)) • v)

def repairLength (p k : ℝ) : ℝ :=
  4 * k ^ 2 * SKOptimized.Overshoot.varianceCoefficient p

def windowRepairGrid (α : ℝ → ℝ) (p s h k : ℝ) (N : ℕ)
    (vs : List (Fin 3 → ℝ)) : List (ℝ × (Fin 3 → ℝ)) :=
  (List.range N).flatMap fun (j : ℕ) => vs.map fun v =>
    (α (s + h * (2 + repairLength p k * (j : ℝ) / (N : ℝ))) / 1,
      (k * Real.sqrt (h * (4 * SKOptimized.Overshoot.varianceCoefficient p) / (N : ℝ))) • v)

theorem window_eq (α : ℝ → ℝ) (p s h k : ℝ) (N : ℕ) :
    window α p s h k N =
      windowGrid α s h N 0 1 3 [SKOptimized.Overshoot.commonVector p k] ++
      windowGrid α s h N 1 p 2 [SKOptimized.Overshoot.sharedVector p k] ++
      windowGrid α s h N 1 p 1 [SKOptimized.Overshoot.rampVector p k] ++
      windowGrid α s h N (1 + p) (1 - p) 1
        [SKOptimized.Overshoot.rampVector p k, SKOptimized.Overshoot.postXVector p k,
          SKOptimized.Overshoot.postYVector p k] ++
      windowRepairGrid α p s h k N
        [SKOptimized.Overshoot.rampVector p 0,
          (1 / Real.sqrt 2) • SKOptimized.Overshoot.sharedVector p 0,
          (1 / 2 : ℝ) • SKOptimized.Overshoot.contrast] ++
      windowGrid α s h N (2 + repairLength p k) (2 - repairLength p k) 1
        [Pi.single 0 1, Pi.single 1 1, Pi.single 2 1] := by
  simp only [window, windowGrid, windowRepairGrid, repairLength, bind_pure_comp, Functor.map, List.flatMap_map]

private theorem covariance_vectors (m : ℝ) (vs : List (Fin 3 → ℝ)) :
    matrixChainCovariance (vs.map fun v => (m, v)) =
      (vs.map rankOneMatrix).sum := by
  induction vs with
  | nil => simp
  | cons v vs ih => simp only [List.map_cons, matrixChainCovariance_cons, ih, List.sum_cons]

private theorem covariance_flatMap {ι : Type} (ms : List ι) (mass : ι → ℝ)
    (vs : List (Fin 3 → ℝ)) :
    matrixChainCovariance (ms.flatMap fun j => vs.map fun v => (mass j, v)) =
      (ms.length : ℝ) • (vs.map rankOneMatrix).sum := by
  induction ms with
  | nil => simp [matrixChainCovariance, chainSum]
  | cons j ms ih =>
    simp only [List.flatMap_cons, matrixChainCovariance_append, covariance_vectors, ih,
      List.length_cons, Nat.cast_add, Nat.cast_one, add_smul, one_smul]
    exact add_comm _ _

private theorem rankOneMatrix_smul (c : ℝ) (v : Fin 3 → ℝ) :
    rankOneMatrix (c • v) = c ^ 2 • rankOneMatrix v := by
  ext i j
  simp only [rankOneMatrix, Pi.smul_apply, smul_eq_mul]
  ring

private theorem sum_rankOne_smul (a : ℝ) (vs : List (Fin 3 → ℝ)) :
    (vs.map (fun v => a • rankOneMatrix v)).sum = a • (vs.map rankOneMatrix).sum := by
  induction vs with
  | nil => simp
  | cons v vs ih => simp only [List.map_cons, List.sum_cons, ih, smul_add]

theorem windowGrid_covariance (α : ℝ → ℝ) (s h : ℝ) {N : ℕ} (hN : 0 < N)
    (a len c : ℝ) (vs : List (Fin 3 → ℝ)) (hd : 0 ≤ h * len) :
    matrixChainCovariance (windowGrid α s h N a len c vs) =
      (h * len) • (vs.map rankOneMatrix).sum := by
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hs : Real.sqrt (h * len / (N : ℝ)) ^ 2 = h * len / (N : ℝ) :=
    Real.sq_sqrt (div_nonneg hd (Nat.cast_nonneg N))
  unfold windowGrid
  have he (j : ℕ) :
      vs.map (fun v => (α (s + h * (a + len * (j : ℝ) / (N : ℝ))) / c,
        Real.sqrt (h * len / (N : ℝ)) • v)) =
      (vs.map (fun v => Real.sqrt (h * len / (N : ℝ)) • v)).map
        (fun v => (α (s + h * (a + len * (j : ℝ) / (N : ℝ))) / c, v)) := by
    rw [List.map_map]
    rfl
  simp_rw [he]
  rw [covariance_flatMap, List.length_range]
  simp_rw [List.map_map, Function.comp_def, rankOneMatrix_smul, hs]
  rw [sum_rankOne_smul, smul_smul]
  congr 1
  field_simp

theorem windowRepairGrid_covariance (α : ℝ → ℝ) (p s h k : ℝ) {N : ℕ}
    (hN : 0 < N) (vs : List (Fin 3 → ℝ))
    (hd : 0 ≤ h * (4 * SKOptimized.Overshoot.varianceCoefficient p)) :
    matrixChainCovariance (windowRepairGrid α p s h k N vs) =
      (h * repairLength p k) • (vs.map rankOneMatrix).sum := by
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hs : (k * Real.sqrt
      (h * (4 * SKOptimized.Overshoot.varianceCoefficient p) / (N : ℝ))) ^ 2 =
      k ^ 2 * (h * (4 * SKOptimized.Overshoot.varianceCoefficient p) / (N : ℝ)) := by
    rw [mul_pow, Real.sq_sqrt (div_nonneg hd (Nat.cast_nonneg N))]
  unfold windowRepairGrid
  simp_rw [show ∀ j : ℕ,
      vs.map (fun v => (α (s + h * (2 + repairLength p k * (j : ℝ) / (N : ℝ))) / 1,
        (k * Real.sqrt (h * (4 * SKOptimized.Overshoot.varianceCoefficient p) / (N : ℝ))) • v)) =
      (vs.map (fun v =>
        (k * Real.sqrt (h * (4 * SKOptimized.Overshoot.varianceCoefficient p) / (N : ℝ))) • v)).map
        (fun v => (α (s + h * (2 + repairLength p k * (j : ℝ) / (N : ℝ))) / 1, v))
      from fun _ => (List.map_map ..).symm]
  rw [covariance_flatMap, List.length_range]
  simp_rw [List.map_map, Function.comp_def, rankOneMatrix_smul, hs]
  rw [sum_rankOne_smul, smul_smul]
  congr 1
  unfold repairLength
  field_simp

private theorem repair_vectors (p : ℝ) :
    ([SKOptimized.Overshoot.rampVector p 0,
      (1 / Real.sqrt 2) • SKOptimized.Overshoot.sharedVector p 0,
      (1 / 2 : ℝ) • SKOptimized.Overshoot.contrast].map rankOneMatrix).sum =
      SKOptimized.Overshoot.repairMatrix := by
  have hs : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rankOneMatrix, SKOptimized.Overshoot.rampVector,
      SKOptimized.Overshoot.sharedVector, SKOptimized.Overshoot.contrast,
      SKOptimized.Overshoot.repairMatrix, SKOptimized.Overshoot.contrastMatrix,
      SKOptimized.Overshoot.outer] <;>
    field_simp <;> nlinarith

private theorem axis_vectors :
    ([Pi.single 0 1, Pi.single 1 1, Pi.single 2 1].map rankOneMatrix).sum =
      (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [rankOneMatrix, Pi.single_apply]

theorem window_covariance_blocks (α : ℝ → ℝ) (p s h k : ℝ) {N : ℕ}
    (hN : 0 < N) (hh : 0 ≤ h) (hp : p ∈ Icc (0 : ℝ) 1)
    (hl : repairLength p k ∈ Icc (0 : ℝ) 2) :
    matrixChainCovariance (window α p s h k N) =
      h • rankOneMatrix (SKOptimized.Overshoot.commonVector p k) +
      (h * p) • rankOneMatrix (SKOptimized.Overshoot.sharedVector p k) +
      (h * p) • rankOneMatrix (SKOptimized.Overshoot.rampVector p k) +
      (h * (1 - p)) •
        (rankOneMatrix (SKOptimized.Overshoot.rampVector p k) +
          rankOneMatrix (SKOptimized.Overshoot.postXVector p k) +
          rankOneMatrix (SKOptimized.Overshoot.postYVector p k)) +
      (h * repairLength p k) • (fun i j => SKOptimized.Overshoot.repairMatrix i j) +
      (h * (2 - repairLength p k)) • (fun i j => (1 : Matrix (Fin 3) (Fin 3) ℝ) i j) := by
  rw [window_eq]
  simp only [matrixChainCovariance_append]
  rw [windowGrid_covariance α s h hN 0 1 3 _ (by simpa using hh),
    windowGrid_covariance α s h hN 1 p 2 _ (mul_nonneg hh hp.1),
    windowGrid_covariance α s h hN 1 p 1 _ (mul_nonneg hh hp.1),
    windowGrid_covariance α s h hN (1 + p) (1 - p) 1 _
      (mul_nonneg hh (sub_nonneg.mpr hp.2)),
    windowRepairGrid_covariance α p s h k hN _ (mul_nonneg hh (mul_nonneg (by norm_num)
      (by
        unfold SKOptimized.Overshoot.varianceCoefficient
        have ht : 0 ≤ (3 : ℝ) - p := by linarith [hp.2]
        positivity))),
    windowGrid_covariance α s h hN (2 + repairLength p k) (2 - repairLength p k) 1 _
      (mul_nonneg hh (sub_nonneg.mpr hl.2)), repair_vectors, axis_vectors]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, mul_one]
  rw [add_assoc (rankOneMatrix _) (rankOneMatrix _) (rankOneMatrix _)]

theorem window_full_covariance (α : ℝ → ℝ) (p s h k : ℝ) {N : ℕ}
    (hN : 0 < N) (hh : 0 ≤ h) (hp : p ∈ Icc (0 : ℝ) 1)
    (hl : repairLength p k ∈ Icc (0 : ℝ) 2) :
    (fun _ _ => s) + matrixChainCovariance (window α p s h k N) +
      (1 - s - 4 * h) • (fun i j => (1 : Matrix (Fin 3) (Fin 3) ℝ) i j) =
        tripleGram (s + h) (h * k) (s + (1 + p) * h) := by
  have hp2 : p ≠ 2 := by linarith [hp.2]
  have he := SKOptimized.Overshoot.repaired_local_covariance_endpoint p k hp2
  rw [window_covariance_blocks α p s h k hN hh hp hl]
  have hb :
      h • rankOneMatrix (SKOptimized.Overshoot.commonVector p k) +
      (h * p) • rankOneMatrix (SKOptimized.Overshoot.sharedVector p k) +
      (h * p) • rankOneMatrix (SKOptimized.Overshoot.rampVector p k) +
      (h * (1 - p)) •
        (rankOneMatrix (SKOptimized.Overshoot.rampVector p k) +
          rankOneMatrix (SKOptimized.Overshoot.postXVector p k) +
          rankOneMatrix (SKOptimized.Overshoot.postYVector p k)) +
      (h * repairLength p k) • (fun i j => SKOptimized.Overshoot.repairMatrix i j) =
      h • (fun i j => (SKOptimized.Overshoot.rawLocalCovariance p k +
        (4 * (k ^ 2 * SKOptimized.Overshoot.varianceCoefficient p)) •
          SKOptimized.Overshoot.repairMatrix) i j) := by
    ext i j
    simp only [rankOneMatrix, SKOptimized.Overshoot.rawLocalCovariance,
      SKOptimized.Overshoot.q0, SKOptimized.Overshoot.q1, SKOptimized.Overshoot.outer,
      Matrix.add_apply, Matrix.smul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      repairLength]
    ring
  rw [hb, he]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tripleGram, Matrix.one_apply, repairLength] <;> ring

def diagonalEmbedding : ℝ →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℝ ℝ

@[simp] theorem diagonalEmbedding_apply (z : ℝ) (i : Fin 3) :
    diagonalEmbedding z i = z := by
  rfl

theorem vectorStep_diagonal (m c : ℝ) (f : (Fin 3 → ℝ) → ℝ) (φ : ℝ → ℝ)
    (hf : ∀ z, f (fun _ => z) = 3 * φ z) (z : ℝ) :
    vectorStep (m / 3) (fun _ : Fin 3 => c) f (fun _ => z) =
      3 * scalarStep m c φ z := by
  have he : f ∘ diagonalEmbedding = fun z => 3 * φ z := funext hf
  have H := congrFun (vectorStep_pullback diagonalEmbedding (m / 3) c f) z
  rw [he, vectorStep_div_scale m 3 (by norm_num), vectorStep_real] at H
  exact H.symm

theorem tail_factorization (l : List (ℝ × ℝ)) {φ : ℝ → ℝ}
    (hφ : BoundedDerivs φ) (x : Fin 3 → ℝ) :
    vectorIncrementChain (tripleTailSchedule l) (fun y => ∑ i : Fin 3, φ (y i)) x =
      ∑ i : Fin 3, scalarIncrementChain l φ (x i) := by
  simpa [Fin.sum_univ_succ, add_assoc] using
    congrFun (tripleTailSchedule_value hφ hφ hφ l) x

theorem boundary_eq_Phi (β : ℝ) (α : ℝ → ℝ) (p s h k : ℝ) (N : ℕ) (z : ℝ) :
    boundary β α p s h k N z =
      vectorIncrementChain ((window α p s h k N).map (fun step => (step.1, β • step.2)))
        (fun x => ∑ i : Fin 3, Phi β α (s + 4 * h) (x i)) (fun _ => z) := by
  rfl

section EqualMass
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

private def jointDirection (v w : E) : (ℝ × ℝ) →L[ℝ] E :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight w

private theorem joint_regular {f : E → ℝ} (hf : BoundedDerivs f) (v w x : E) :
    BoundedDerivs (fun y : ℝ × ℝ => f (x + y.1 • v + y.2 • w)) := by
  simpa only [Function.comp_def, jointDirection, add_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', add_assoc] using
      (hf.translate x).compCLM (jointDirection v w)

theorem exp_mul_vectorStep {f : E → ℝ} (hf : BoundedDerivs f)
    {m : ℝ} (hm : m ≠ 0) (v x : E) :
    Real.exp (m * vectorStep m v f x) =
      ∫ y, Real.exp (m * f (x + y • v)) ∂gaussianReal 0 1 := by
  have hi : Integrable (fun y => Real.exp (m * f (x + y • v))) (gaussianReal 0 1) :=
    (hf.compCLM (vectorTranslation v)).exp_integrable m x
  simp only [vectorStep, gaussianStep, ite_eq_right hm, positiveGaussianLogStep]
  rw [mul_div_cancel₀ _ hm, Real.exp_log (integral_exp_pos hi)]

theorem vectorStep_equal_mass_merge {f : E → ℝ} (hf : BoundedDerivs f)
    {m : ℝ} (hm : m ≠ 0) (v w x : E) :
    vectorStep m v (vectorStep m w f) x =
      Real.log (∫ y : ℝ × ℝ, Real.exp (m * f (x + y.1 • v + y.2 • w))
        ∂(gaussianReal 0 1).prod (gaussianReal 0 1)) / m := by
  have hr := joint_regular hf v w x
  have hi : Integrable (fun y : ℝ × ℝ => Real.exp (m * f (x + y.1 • v + y.2 • w)))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    (hr.exp_growths m).1.integrable_gaussianMeasure
      (Real.continuous_exp.comp (continuous_const.mul hr.1.continuous))
  rw [vectorStep, gaussianStep, ite_eq_right hm, positiveGaussianLogStep]
  simp_rw [exp_mul_vectorStep hf hm]
  rw [← integral_prod _ hi]

theorem vectorStep_zero_mass_merge {f : E → ℝ} (hf : BoundedDerivs f) (v w x : E) :
    vectorStep 0 v (vectorStep 0 w f) x =
      ∫ y : ℝ × ℝ, f (x + y.1 • v + y.2 • w)
        ∂(gaussianReal 0 1).prod (gaussianReal 0 1) := by
  have hr := joint_regular hf v w x
  have hi : Integrable (fun y : ℝ × ℝ => f (x + y.1 • v + y.2 • w))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    hr.hasExpGrowth.integrable_gaussianMeasure hr.1.continuous
  simp only [vectorStep, gaussianStep, ite_true]
  exact (integral_prod _ hi).symm

private theorem joint_integral_swap (g : E → ℝ) (v w x : E) :
    (∫ y : ℝ × ℝ, g (x + y.1 • v + y.2 • w)
      ∂(gaussianReal 0 1).prod (gaussianReal 0 1)) =
    ∫ y : ℝ × ℝ, g (x + y.1 • w + y.2 • v)
      ∂(gaussianReal 0 1).prod (gaussianReal 0 1) := by
  rw [← integral_prod_swap]
  apply integral_congr_ae
  exact ae_of_all _ fun y => by
    simp only [Prod.swap]
    congr 1
    exact add_right_comm x _ _

theorem vectorStep_equal_mass_comm {f : E → ℝ} (hf : BoundedDerivs f)
    (m : ℝ) (v w : E) :
    vectorStep m v (vectorStep m w f) = vectorStep m w (vectorStep m v f) := by
  funext x
  by_cases hm : m = 0
  · subst m
    rw [vectorStep_zero_mass_merge hf, vectorStep_zero_mass_merge hf]
    exact joint_integral_swap f v w x
  · rw [vectorStep_equal_mass_merge hf hm, vectorStep_equal_mass_merge hf hm]
    rw [joint_integral_swap (fun y => Real.exp (m * f y)) v w x]

theorem vectorStep_neg_direction (m : ℝ) (v : E) (f : E → ℝ) :
    vectorStep m (-v) f = vectorStep m v f := by
  funext x
  have hi (g : ℝ → ℝ) : (∫ y, g (-y) ∂gaussianReal 0 1) =
      ∫ y, g y ∂gaussianReal 0 1 := by
    simpa only [scalarSign_true] using
      (scalarSign_gaussian true).integral_comp (scalarSignEquiv true).measurableEmbedding g
  have he (y : ℝ) : y • (-v) = (-y) • v := by
    rw [smul_neg, neg_smul]
  simp only [vectorStep, gaussianStep, positiveGaussianLogStep, he]
  rw [hi (fun y => f (x + y • v)), hi (fun y => Real.exp (m * f (x + y • v)))]

end EqualMass

theorem windowGrid_mass_mem (α : ℝ → ℝ) (hα : ∀ t, α t ∈ Icc (0 : ℝ) 1)
    (s h : ℝ) (N : ℕ) (a len c : ℝ) (hc : 1 ≤ c) (vs : List (Fin 3 → ℝ))
    (step : ℝ × (Fin 3 → ℝ)) (hstep : step ∈ windowGrid α s h N a len c vs) :
    step.1 ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨j, _, hs⟩ := List.mem_flatMap.mp hstep
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hs
  exact ⟨div_nonneg (hα _).1 (by linarith),
    (div_le_one (by linarith : 0 < c)).mpr ((hα _).2.trans hc)⟩

theorem window_mass_mem (α : ℝ → ℝ) (hα : ∀ t, α t ∈ Icc (0 : ℝ) 1)
    (p s h k : ℝ) (N : ℕ) (step : ℝ × (Fin 3 → ℝ))
    (hstep : step ∈ window α p s h k N) : step.1 ∈ Icc (0 : ℝ) 1 := by
  rw [window_eq] at hstep
  simp only [List.mem_append] at hstep
  rcases hstep with ((((hs | hs) | hs) | hs) | hs) | hs
  all_goals first
    | exact windowGrid_mass_mem α hα s h N _ _ _ (by norm_num) _ step hs
    | obtain ⟨j, _, hv⟩ := List.mem_flatMap.mp hs
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hv
      simpa only [div_one] using hα _

private def MassOrderedBetween (l : List (ℝ × (Fin 3 → ℝ))) (a b : ℝ) : Prop :=
  l.Pairwise (fun u v => u.1 ≤ v.1) ∧ ∀ u ∈ l, a ≤ u.1 ∧ u.1 ≤ b

private theorem MassOrderedBetween.append {l r : List (ℝ × (Fin 3 → ℝ))}
    {a b c d : ℝ} (hl : MassOrderedBetween l a b) (hr : MassOrderedBetween r c d)
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    MassOrderedBetween (l ++ r) a d := by
  refine ⟨List.pairwise_append.mpr ⟨hl.1, hr.1, ?_⟩, ?_⟩
  · intro u hu v hv
    exact (hl.2 u hu).2.trans (hbc.trans (hr.2 v hv).1)
  · intro u hu
    rcases List.mem_append.mp hu with hu | hu
    · exact ⟨(hl.2 u hu).1, (hl.2 u hu).2.trans (hbc.trans hcd)⟩
    · exact ⟨hab.trans (hbc.trans (hr.2 u hu).1), (hr.2 u hu).2⟩

private theorem windowGrid_ordered (α : ℝ → ℝ) (hα : Monotone α)
    (s h : ℝ) (N : ℕ) (a len c : ℝ) (hh : 0 ≤ h) (hlen : 0 ≤ len)
    (hc : 0 < c) (vs : List (Fin 3 → ℝ)) :
    MassOrderedBetween (windowGrid α s h N a len c vs)
      (α (s + h * a) / c) (α (s + h * (a + len)) / c) := by
  have htime (j : ℕ) (hj : j ∈ List.range N) :
      s + h * a ≤ s + h * (a + len * (j : ℝ) / (N : ℝ)) ∧
      s + h * (a + len * (j : ℝ) / (N : ℝ)) ≤ s + h * (a + len) := by
    have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le j) (List.mem_range.mp hj)
    have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    have hjr : (j : ℝ) ≤ N := Nat.cast_le.mpr (Nat.le_of_lt (List.mem_range.mp hj))
    have hfrac : 0 ≤ len * (j : ℝ) / (N : ℝ) ∧ len * (j : ℝ) / (N : ℝ) ≤ len :=
      ⟨by positivity, (div_le_iff₀ hNr).mpr (mul_le_mul_of_nonneg_left hjr hlen)⟩
    constructor <;> nlinarith [mul_nonneg hh hfrac.1,
      mul_nonneg hh (sub_nonneg.mpr hfrac.2)]
  constructor
  · rw [windowGrid, List.pairwise_flatMap]
    constructor
    · intro j _
      rw [List.pairwise_map]
      induction vs with
      | nil => exact List.Pairwise.nil
      | cons v vs ih => exact List.pairwise_cons.mpr ⟨fun _ _ => le_rfl, ih⟩
    · apply List.pairwise_le_range.imp
      intro i j hij u hu v hv
      obtain ⟨u, _, rfl⟩ := List.mem_map.mp hu
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hv
      apply div_le_div_of_nonneg_right (hα ?_) hc.le
      have hijr : (i : ℝ) ≤ j := Nat.cast_le.mpr hij
      have H := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hijr hlen)
        (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
      nlinarith [mul_nonneg hh (sub_nonneg.mpr H)]
  · intro step hstep
    obtain ⟨j, hj, hs⟩ := List.mem_flatMap.mp hstep
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hs
    exact ⟨div_le_div_of_nonneg_right (hα (htime j hj).1) hc.le,
      div_le_div_of_nonneg_right (hα (htime j hj).2) hc.le⟩

private theorem MassOrderedBetween.of_masses_eq
    {l r : List (ℝ × (Fin 3 → ℝ))} {a b : ℝ}
    (hl : MassOrderedBetween l a b) (he : r.map Prod.fst = l.map Prod.fst) :
    MassOrderedBetween r a b := by
  refine ⟨List.pairwise_map.mp (he.symm ▸ List.pairwise_map.mpr hl.1), ?_⟩
  intro u hu
  have hm : u.1 ∈ l.map Prod.fst := he ▸ List.mem_map.mpr ⟨u, hu, rfl⟩
  obtain ⟨v, hv, heq⟩ := List.mem_map.mp hm
  exact heq ▸ hl.2 v hv

theorem window_mass_sorted (α : ℝ → ℝ) (hα : Monotone α)
    (_ha : ∀ t, 0 ≤ α t) (p s h k : ℝ) (N : ℕ) (hh : 0 ≤ h)
    (hp : p ∈ Icc (0 : ℝ) 1) (hl : repairLength p k ∈ Icc (0 : ℝ) 2)
    (hsep : α (s + h * (1 + p)) / 2 ≤ α (s + h)) :
    (window α p s h k N).Pairwise (fun u v => u.1 ≤ v.1) := by
  have hm01 : α s ≤ α (s + h) := hα (by linarith)
  have hm12 : α (s + h) ≤ α (s + h * (1 + p)) :=
    hα (by nlinarith [mul_nonneg hh hp.1])
  have hm23 : α (s + h * (1 + p)) ≤ α (s + h * 2) :=
    hα (by nlinarith [mul_nonneg hh (sub_nonneg.mpr hp.2)])
  have hm34 : α (s + h * 2) ≤ α (s + h * (2 + repairLength p k)) :=
    hα (by nlinarith [mul_nonneg hh hl.1])
  have hm45 : α (s + h * (2 + repairLength p k)) ≤ α (s + h * 4) :=
    hα (by nlinarith [mul_nonneg hh (sub_nonneg.mpr hl.2)])
  have H0 := windowGrid_ordered α hα s h N 0 1 3 hh (by norm_num)
    (by norm_num) [SKOptimized.Overshoot.commonVector p k]
  simp only [mul_zero, add_zero, zero_add, mul_one] at H0
  have H1 := windowGrid_ordered α hα s h N 1 p 2 hh hp.1
    (by norm_num) [SKOptimized.Overshoot.sharedVector p k]
  simp only [mul_one] at H1
  have H2 := windowGrid_ordered α hα s h N 1 p 1 hh hp.1
    (by norm_num) [SKOptimized.Overshoot.rampVector p k]
  simp only [mul_one, div_one] at H2
  have H3 := windowGrid_ordered α hα s h N (1 + p) (1 - p) 1 hh
    (sub_nonneg.mpr hp.2) (by norm_num)
    [SKOptimized.Overshoot.rampVector p k, SKOptimized.Overshoot.postXVector p k,
      SKOptimized.Overshoot.postYVector p k]
  rw [show (1 + p) + (1 - p) = (2 : ℝ) by ring] at H3
  simp only [div_one] at H3
  let repairVs := [SKOptimized.Overshoot.rampVector p 0,
    (1 / Real.sqrt 2) • SKOptimized.Overshoot.sharedVector p 0,
    (1 / 2 : ℝ) • SKOptimized.Overshoot.contrast]
  have H4 := windowGrid_ordered α hα s h N 2 (repairLength p k) 1 hh hl.1
    (by norm_num) repairVs
  simp only [div_one] at H4
  have H4' : MassOrderedBetween (windowRepairGrid α p s h k N repairVs)
      (α (s + h * 2)) (α (s + h * (2 + repairLength p k))) :=
    H4.of_masses_eq (by
      simp only [windowRepairGrid, windowGrid, List.map_flatMap, List.map_map,
        Function.comp_def])
  have H5 := windowGrid_ordered α hα s h N (2 + repairLength p k)
    (2 - repairLength p k) 1 hh (sub_nonneg.mpr hl.2) (by norm_num)
    [Pi.single 0 1, Pi.single 1 1, Pi.single 2 1]
  rw [show (2 + repairLength p k) + (2 - repairLength p k) = (4 : ℝ) by ring] at H5
  simp only [div_one] at H5
  have H01 := H0.append H1 (by linarith) (by linarith [_ha (s + h)]) (by linarith)
  have H012 := H01.append H2 (by linarith [_ha s]) hsep hm12
  have H0123 := H012.append H3 (by linarith [_ha s]) le_rfl hm23
  have H01234 := H0123.append H4' (by linarith [_ha s]) le_rfl hm34
  have H := H01234.append H5 (by linarith [_ha s]) le_rfl hm45
  rw [window_eq]
  exact H.1

theorem exists_window_mass_sorted_cutoff (α : ℝ → ℝ) (hα : Monotone α)
    (ha : ∀ t, 0 ≤ α t) (s : ℝ) (hs : 0 < α s) (hc : ContinuousAt α s) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h ∈ Icc (0 : ℝ) h₀, ∀ p k : ℝ, ∀ N : ℕ,
      p ∈ Icc (0 : ℝ) 1 → repairLength p k ∈ Icc (0 : ℝ) 2 →
      (window α p s h k N).Pairwise (fun u v => u.1 ≤ v.1) := by
  obtain ⟨ε, hε, hclose⟩ := Metric.continuousAt_iff.mp hc (α s) hs
  refine ⟨ε / 8, by positivity, ?_⟩
  intro h hh p k N hp hl
  apply window_mass_sorted α hα ha p s h k N hh.1 hp hl
  have hd : dist (s + h * (1 + p)) s < ε := by
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_nonneg (mul_nonneg hh.1 (by linarith [hp.1]))]
    nlinarith [mul_nonneg hh.1 (sub_nonneg.mpr hp.2), hh.2]
  have H := hclose hd
  rw [Real.dist_eq] at H
  have HM := hα (show s ≤ s + h by linarith [hh.1])
  linarith [(abs_lt.mp H).2]

theorem common_chain_diagonal (l : List (ℝ × ℝ)) (f : (Fin 3 → ℝ) → ℝ)
    (φ : ℝ → ℝ) (hf : ∀ z, f (fun _ => z) = 3 * φ z) (z : ℝ) :
    vectorIncrementChain (tripleCommonSchedule l) f (fun _ => z) =
      3 * scalarIncrementChain l φ z := by
  induction l generalizing z with
  | nil => exact hf z
  | cons a l ih =>
    have hv : (![a.2, a.2, a.2] : Fin 3 → ℝ) = fun _ => a.2 := by
      ext i
      fin_cases i <;> rfl
    simp only [tripleCommonSchedule, List.map_cons, vectorIncrementChain, hv,
      scalarIncrementChain]
    exact vectorStep_diagonal a.1 a.2 _ _ ih z

def pairEmbedding : (ℝ × ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.fst ℝ ℝ ℝ,
    ContinuousLinearMap.snd ℝ ℝ ℝ, ContinuousLinearMap.snd ℝ ℝ ℝ]

@[simp] theorem pairEmbedding_apply (x : ℝ × ℝ) :
    pairEmbedding x = ![x.1, x.2, x.2] := by
  ext i
  fin_cases i <;> rfl

theorem shared_ramp_diagonal (l : List (ℝ × ℝ)) {φ : ℝ → ℝ}
    (hφ : BoundedDerivs φ) (z : ℝ) :
    vectorIncrementChain
      (l.map (fun a => (a.1 / 2, ![0, a.2, a.2])) ++
        l.map (fun a => (a.1, ![a.2, 0, 0])))
      (fun x : Fin 3 → ℝ => φ (x 0) + φ (x 1) + φ (x 2)) (fun _ => z) =
      3 * scalarIncrementChain l φ z := by
  let tagged : List (ProductIncrement (E := ℝ) (F := ℝ)) :=
    l.map Sum.inr ++ l.map Sum.inl
  have hleft : productLeft tagged = l := by
    simp [tagged, productLeft, List.filterMap_append, List.filterMap_map]
  have hright : productRight tagged = l := by
    simp [tagged, productRight, List.filterMap_append, List.filterMap_map]
  have H := congrFun (vectorIncrementChain_pullback pairEmbedding
    (tagged.map (fun a => (productMass a, productVector a)))
    (fun x : Fin 3 → ℝ => φ (x 0) + φ (x 1) + φ (x 2))) (z, z)
  have hterminal :
      (fun x : Fin 3 → ℝ => φ (x 0) + φ (x 1) + φ (x 2)) ∘ pairEmbedding =
        fun x : ℝ × ℝ => φ x.1 + 2 * φ x.2 := by
    funext x
    simp only [Function.comp_apply, pairEmbedding_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two]
    change φ x.1 + φ x.2 + φ x.2 = φ x.1 + 2 * φ x.2
    ring
  rw [hterminal] at H
  change productBranchChain tagged (fun x : ℝ × ℝ => φ x.1 + 2 * φ x.2) (z, z) = _ at H
  rw [productBranchChain_factor tagged hφ hφ, hleft, hright,
    vectorIncrementChain_real] at H
  have hsched :
      (tagged.map (fun a => (productMass a, productVector a))).map
        (fun a => (a.1, pairEmbedding a.2)) =
      l.map (fun a => (a.1 / 2, ![0, a.2, a.2])) ++
        l.map (fun a => (a.1, ![a.2, 0, 0])) := by
    simp [tagged, List.map_append, List.map_map, Function.comp_def, productMass, productVector]
  rw [hsched] at H
  have hz : pairEmbedding (z, z) = fun _ => z := by
    ext i
    fin_cases i <;> rfl
  simp only [Function.comp_apply] at H
  rw [hz] at H
  rw [← H]
  ring

def scalarGrid (β : ℝ) (α : ℝ → ℝ) (s h : ℝ) (N : ℕ) (a len : ℝ) :
    List (ℝ × ℝ) :=
  (List.range N).map fun (j : ℕ) =>
    (α (s + h * (a + len * (j : ℝ) / (N : ℝ))),
      β * Real.sqrt (h * len / (N : ℝ)))

private theorem windowGrid_scaled (β : ℝ) (α : ℝ → ℝ) (s h : ℝ) (N : ℕ)
    (a len c : ℝ) (vs : List (Fin 3 → ℝ)) :
    (windowGrid α s h N a len c vs).map (fun u => (u.1, β • u.2)) =
      (scalarGrid β α s h N a len).flatMap fun u =>
        vs.map fun v => (u.1 / c, u.2 • v) := by
  simp only [windowGrid, scalarGrid, List.map_flatMap, List.flatMap_map,
    List.map_map, Function.comp_def, smul_smul]

private theorem chain_zero_vectors {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (l : List (ℝ × E)) (hl : ∀ a ∈ l, a.2 = 0) (f : E → ℝ) :
    vectorIncrementChain l f = f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [vectorIncrementChain, hl a List.mem_cons_self,
      ih (fun b hb => hl b (List.mem_cons_of_mem a hb)), vectorStep_zero]

private theorem repair_zero_chain (β : ℝ) (α : ℝ → ℝ) (p s h : ℝ) (N : ℕ)
    (f : (Fin 3 → ℝ) → ℝ) :
    vectorIncrementChain
      ((windowRepairGrid α p s h 0 N [SKOptimized.Overshoot.rampVector p 0,
        (1 / Real.sqrt 2) • SKOptimized.Overshoot.sharedVector p 0,
        (1 / 2 : ℝ) • SKOptimized.Overshoot.contrast]).map (fun u => (u.1, β • u.2))) f = f := by
  apply chain_zero_vectors
  intro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  obtain ⟨j, _, hv⟩ := List.mem_flatMap.mp hb
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hv
  simp only [zero_mul, zero_smul, smul_zero]

private theorem smul_axes (c : ℝ) :
    c • (Pi.single 0 (1 : ℝ) : Fin 3 → ℝ) = ![c, 0, 0] ∧
    c • (Pi.single 1 (1 : ℝ) : Fin 3 → ℝ) = ![0, c, 0] ∧
    c • (Pi.single 2 (1 : ℝ) : Fin 3 → ℝ) = ![0, 0, c] := by
  constructor
  · ext i
    fin_cases i <;> simp
  · constructor <;> ext i <;> fin_cases i <;> simp

private theorem zero_common_grid (β : ℝ) (α : ℝ → ℝ) (p s h : ℝ) (N : ℕ) :
    (windowGrid α s h N 0 1 3 [SKOptimized.Overshoot.commonVector p 0]).map
      (fun u => (u.1, β • u.2)) = tripleCommonSchedule (scalarGrid β α s h N 0 1) := by
  rw [windowGrid_scaled]
  simp only [SKOptimized.Overshoot.commonVector, mul_zero, add_zero, sub_zero,
    List.map_cons, List.map_nil, ← List.map_eq_flatMap, tripleCommonSchedule]
  apply List.map_congr_left
  intro a _
  congr 1
  ext i
  fin_cases i <;> simp

private theorem zero_shared_grid (β : ℝ) (α : ℝ → ℝ) (p s h : ℝ) (N : ℕ) :
    (windowGrid α s h N 1 p 2 [SKOptimized.Overshoot.sharedVector p 0]).map
      (fun u => (u.1, β • u.2)) =
      (scalarGrid β α s h N 1 p).map (fun a => (a.1 / 2, ![0, a.2, a.2])) := by
  rw [windowGrid_scaled]
  simp only [SKOptimized.Overshoot.sharedVector, mul_zero, add_zero, sub_zero,
    List.map_cons, List.map_nil, ← List.map_eq_flatMap]
  apply List.map_congr_left
  intro a _
  congr 1
  ext i
  fin_cases i <;> simp

private theorem zero_ramp_grid (β : ℝ) (α : ℝ → ℝ) (p s h : ℝ) (N : ℕ) :
    (windowGrid α s h N 1 p 1 [SKOptimized.Overshoot.rampVector p 0]).map
      (fun u => (u.1, β • u.2)) =
      (scalarGrid β α s h N 1 p).map (fun a => (a.1, ![a.2, 0, 0])) := by
  rw [windowGrid_scaled]
  simp only [SKOptimized.Overshoot.rampVector, mul_zero, div_one,
    List.map_cons, List.map_nil, ← List.map_eq_flatMap]
  apply List.map_congr_left
  intro a _
  congr 1
  ext i
  fin_cases i <;> simp

private theorem smul_vec3 (c a b d : ℝ) :
    c • (![a, b, d] : Fin 3 → ℝ) = ![c * a, c * b, c * d] := by
  ext i
  fin_cases i <;> rfl

private theorem zero_post_grid (β : ℝ) (α : ℝ → ℝ) (p s h : ℝ) (N : ℕ) :
    (windowGrid α s h N (1 + p) (1 - p) 1
      [SKOptimized.Overshoot.rampVector p 0, SKOptimized.Overshoot.postXVector p 0,
        SKOptimized.Overshoot.postYVector p 0]).map (fun u => (u.1, β • u.2)) =
      tripleTailSchedule (scalarGrid β α s h N (1 + p) (1 - p)) := by
  rw [windowGrid_scaled]
  unfold tripleTailSchedule
  apply List.flatMap_congr
  intro a _
  simp only [SKOptimized.Overshoot.rampVector, SKOptimized.Overshoot.postXVector,
    SKOptimized.Overshoot.postYVector, mul_zero, add_zero, sub_zero,
    div_one, List.map_cons, List.map_nil, tripleTailBlock, smul_vec3, mul_one]

private theorem axis_grid (β : ℝ) (α : ℝ → ℝ) (s h : ℝ) (N : ℕ) (a len : ℝ) :
    (windowGrid α s h N a len 1 [Pi.single 0 1, Pi.single 1 1, Pi.single 2 1]).map
      (fun u => (u.1, β • u.2)) = tripleTailSchedule (scalarGrid β α s h N a len) := by
  rw [windowGrid_scaled]
  unfold tripleTailSchedule
  apply List.flatMap_congr
  intro u _
  simp only [List.map_cons, List.map_nil, div_one, tripleTailBlock,
    (smul_axes u.2).1, (smul_axes u.2).2.1, (smul_axes u.2).2.2]

def scalarWindow (β : ℝ) (α : ℝ → ℝ) (p s h : ℝ) (N : ℕ) : List (ℝ × ℝ) :=
  scalarGrid β α s h N 0 1 ++ scalarGrid β α s h N 1 p ++
    scalarGrid β α s h N (1 + p) (1 - p) ++ scalarGrid β α s h N 2 2

theorem window_zero_factorization (β : ℝ) (α : ℝ → ℝ) (p s h : ℝ) (N : ℕ)
    {φ : ℝ → ℝ} (hφ : BoundedDerivs φ) (z : ℝ) :
    vectorIncrementChain ((window α p s h 0 N).map (fun u => (u.1, β • u.2)))
      (fun x : Fin 3 → ℝ => φ (x 0) + φ (x 1) + φ (x 2)) (fun _ => z) =
      3 * scalarIncrementChain (scalarWindow β α p s h N) φ z := by
  rw [window_eq]
  simp only [List.map_append, vectorIncrementChain_append]
  rw [repair_zero_chain]
  simp only [repairLength, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_mul,
    add_zero, sub_zero]
  rw [zero_common_grid, zero_shared_grid, zero_ramp_grid, zero_post_grid, axis_grid]
  rw [tripleTailSchedule_value hφ hφ hφ,
    tripleTailSchedule_value (scalarIncrementChain_regular _ hφ)
      (scalarIncrementChain_regular _ hφ) (scalarIncrementChain_regular _ hφ)]
  rw [← vectorIncrementChain_append
    ((scalarGrid β α s h N 1 p).map (fun a => (a.1 / 2, ![0, a.2, a.2])))
    ((scalarGrid β α s h N 1 p).map (fun a => (a.1, ![a.2, 0, 0])))]
  unfold scalarWindow
  simp only [scalarIncrementChain_append]
  apply common_chain_diagonal
  intro y
  exact shared_ramp_diagonal _
    (scalarIncrementChain_regular _ (scalarIncrementChain_regular _ hφ)) y

theorem boundary_zero_factorization (β : ℝ) (α : ℝ → ℝ) (p s h : ℝ) (N : ℕ)
    (hΦ : BoundedDerivs (Phi β α (s + 4 * h))) (z : ℝ) :
    boundary β α p s h 0 N z =
      3 * scalarIncrementChain (scalarWindow β α p s h N)
        (Phi β α (s + 4 * h)) z := by
  rw [boundary_eq_Phi]
  simpa [Fin.sum_univ_succ, add_assoc] using
    window_zero_factorization β α p s h N hΦ z

def relativeGridProfile (α : ℝ → ℝ) (a len : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  α (a + len * (⌊(t - a) * (N : ℝ) / len⌋₊ : ℝ) / (N : ℝ))

def relativeWindowProfile (α : ℝ → ℝ) (p s h : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  if t < s then α t
  else if t < s + h then relativeGridProfile α s h N t
  else if t < s + (1 + p) * h then relativeGridProfile α (s + h) (p * h) N t
  else if t < s + 2 * h then
    relativeGridProfile α (s + (1 + p) * h) ((1 - p) * h) N t
  else if t < s + 4 * h then relativeGridProfile α (s + 2 * h) (2 * h) N t
  else α t

def joinedWindowProfile (γ α : ℝ → ℝ) (p s h : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  if t < s then γ t else relativeWindowProfile α p s h N t

theorem matrixChainPenalty_eq_sum {d : ℕ} (l : List (ℝ × (Fin d → ℝ)))
    (Q : Fin d → Fin d → ℝ) :
    matrixChainPenalty l Q =
      ∑ i : Fin l.length, (l.get i).1 *
        (matrixSquare d (Q + strictPrefix (fun j => rankOneMatrix (l.get j).2) i +
          rankOneMatrix (l.get i).2) -
        matrixSquare d (Q + strictPrefix (fun j => rankOneMatrix (l.get j).2) i)) := by
  unfold matrixChainPenalty
  have he : l.map (fun p => (p.1, rankOneMatrix p.2)) =
      List.ofFn (fun i : Fin l.length => ((l.get i).1, rankOneMatrix (l.get i).2)) := by
    conv_lhs => rw [← List.ofFn_get l, List.map_ofFn]
    rfl
  rw [he, chainPotentialPenalty_ofFn]

theorem penalty_eq_sum (γ α : ℝ → ℝ) (p s h k : ℝ) (N : ℕ) :
    penalty γ α p s h k N =
      6 * (∫ t in Icc (0 : ℝ) s, t * γ t) +
      (∑ i : Fin (window α p s h k N).length,
        ((window α p s h k N).get i).1 *
          (matrixSquare 3 ((fun _ _ => s) +
            strictPrefix (fun j => rankOneMatrix ((window α p s h k N).get j).2) i +
            rankOneMatrix ((window α p s h k N).get i).2) -
          matrixSquare 3 ((fun _ _ => s) +
            strictPrefix (fun j => rankOneMatrix ((window α p s h k N).get j).2) i))) +
      6 * (∫ t in Icc (s + 4 * h) 1, t * α t) := by
  rw [penalty, matrixChainPenalty_eq_sum]

theorem varianceCoefficient_le_two {p : ℝ} (hp : p ∈ Icc (0 : ℝ) (1 / 2)) :
    SKOptimized.Overshoot.varianceCoefficient p ≤ 2 := by
  have hd : 0 < 2 - p := by linarith [hp.2]
  have he : SKOptimized.Overshoot.varianceCoefficient p =
      ((3 - p) + (1 - p) ^ 2) / (2 - p) ^ 2 := by
    unfold SKOptimized.Overshoot.varianceCoefficient SKOptimized.Overshoot.tentWeight
      SKOptimized.Overshoot.rampWeight
    simp only [div_pow, one_pow]
    field_simp [hd.ne']
    ring
  rw [he]
  apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
  nlinarith [mul_nonneg (show 0 ≤ 1 - p by linarith [hp.2])
    (show 0 ≤ 4 - p by linarith [hp.2])]

theorem repairLength_mem {p k : ℝ} (hp : p ∈ Icc (0 : ℝ) (1 / 2))
    (hk : |k| ≤ (1 / 2 : ℝ)) : repairLength p k ∈ Icc (0 : ℝ) 2 := by
  have hL := (SKOptimized.Overshoot.varianceCoefficient_pos hp.2).le
  have hk2 : 4 * k ^ 2 ≤ 1 := by
    have H := sq_le_sq₀ (abs_nonneg k) (by norm_num : (0 : ℝ) ≤ 1 / 2) |>.mpr hk
    rw [sq_abs] at H
    nlinarith
  unfold repairLength
  exact ⟨mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg k)) hL,
    (mul_le_mul_of_nonneg_right hk2 hL).trans
      (by simpa only [one_mul] using varianceCoefficient_le_two hp)⟩

theorem window_full_covariance_admissible (α : ℝ → ℝ) (p s h k : ℝ) {N : ℕ}
    (hN : 0 < N) (hh : 0 ≤ h) (hp : p ∈ Icc (0 : ℝ) (1 / 2))
    (hk : |k| ≤ (1 / 2 : ℝ)) :
    (fun _ _ => s) + matrixChainCovariance (window α p s h k N) +
      (1 - s - 4 * h) • (fun i j => (1 : Matrix (Fin 3) (Fin 3) ℝ) i j) =
        tripleGram (s + h) (h * k) (s + (1 + p) * h) := by
  exact window_full_covariance α p s h k hN hh
    ⟨hp.1, by linarith [hp.2]⟩ (repairLength_mem hp hk)

theorem tail_factorization_tendsto (β : ℝ) (α : ℝ → ℝ)
    (hα : ∀ t, α t ∈ Icc (0 : ℝ) 1) (hm : Monotone α)
    (T : ℝ) (hT : T ∈ Icc (0 : ℝ) 1) (x : Fin 3 → ℝ) :
    Filter.Tendsto (fun n : ℕ =>
      vectorIncrementChain
        (tripleTailSchedule (scaleIncrementChain β
          (rawTimeChain (dyadicIntervals α n T (Real.toNNReal (1 - T))))))
        (fun y => ∑ i : Fin 3, scalarSpinTerminal (y i)) x)
      Filter.atTop (nhds (∑ i : Fin 3, Phi β α T (x i))) := by
  have ht : Real.toNNReal (1 - T) ≤ 1 := by
    exact Real.toNNReal_le_one.mpr (by linarith [hT.1])
  have hv (i : Fin 3) :=
    (dyadicScalar_value_uniform β hα hm T (Real.toNNReal (1 - T)) ht).tendsto_at (x i)
  have H := tendsto_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ => hv i)
  convert H using 1
  funext n
  rw [tail_factorization _ scalarSpinTerminal_regular]
  simp only [scalarIncrementChain_rawTimeChain]
  all_goals rfl

@[simp] theorem window_zero_mesh (α : ℝ → ℝ) (p s h k : ℝ) :
    window α p s h k 0 = [] := by
  rw [window_eq]
  simp only [windowGrid, windowRepairGrid, List.range_zero, List.flatMap_nil, List.nil_append]

theorem boundary_zero_mesh (β : ℝ) (α : ℝ → ℝ) (p s h k z : ℝ) :
    boundary β α p s h k 0 z = 3 * Phi β α (s + 4 * h) z := by
  rw [boundary_eq_Phi, window_zero_mesh]
  simp only [List.map_nil, vectorIncrementChain]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  ring

theorem penalty_zero_mesh (γ α : ℝ → ℝ) (p s h k : ℝ) :
    penalty γ α p s h k 0 =
      6 * (∫ t in Icc (0 : ℝ) s, t * γ t) +
      6 * (∫ t in Icc (s + 4 * h) 1, t * α t) := by
  simp only [penalty, window_zero_mesh, matrixChainPenalty_nil, add_zero]

theorem trialValue_zero_mesh (β : ℝ) (γ α : ℝ → ℝ) (r d δ : ℝ) :
    trialValue β γ α r d δ 0 =
      scalarCDFOperator β (fun t => γ t / 3) 0 (Real.toNNReal (r - 2 * d))
        (fun z => 3 * Phi β α (r + 6 * d) z) 0 -
      (3 * β ^ 2 / 2) *
        ((∫ t in Icc (0 : ℝ) (r - 2 * d), t * γ t) +
          ∫ t in Icc (r + 6 * d) 1, t * α t) := by
  have hb (p s h k : ℝ) : boundary β α p s h k 0 =
      fun z => 3 * Phi β α (s + 4 * h) z :=
    funext fun z => boundary_zero_mesh β α p s h k z
  unfold trialValue
  rw [hb, penalty_zero_mesh]
  rw [show r - 2 * d + 4 * (2 * d) = r + 6 * d by ring]
  ring

theorem trialValue_zero_mesh_even (β : ℝ) (γ α : ℝ → ℝ) (r d δ : ℝ) :
    trialValue β γ α r d (-δ) 0 = trialValue β γ α r d δ 0 := by
  rw [trialValue_zero_mesh, trialValue_zero_mesh]

theorem dyadicScalar_div_three (β : ℝ) (α : ℝ → ℝ) (n : ℕ)
    (s : ℝ) (t : ℝ≥0) (f : ℝ → ℝ) :
    dyadicScalar β (fun u => α u / 3) n s t (fun x => 3 * f x) =
      fun x => 3 * dyadicScalar β α n s t f x := by
  induction n generalizing s t f with
  | zero =>
    simp only [dyadicScalar_zero, scalarTimeStep]
    exact gaussianStep_div_scale (α s) 3 (by norm_num) _
  | succ n ih =>
    rw [dyadicScalar_succ, ih, ih, dyadicScalar_succ]

theorem scalarCDFOperator_div_three (β : ℝ) (α : ℝ → ℝ)
    (hα : ∀ u, α u ∈ Icc (0 : ℝ) 1) (hm : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) {f : ℝ → ℝ} (hf : BoundedDerivs f)
    {K : ℝ≥0} (hLip : LipschitzWith K f) (x : ℝ) :
    scalarCDFOperator β (fun u => α u / 3) s t (fun y => 3 * f y) x =
      3 * scalarCDFOperator β α s t f x := by
  have hb : ∀ u, α u / 3 ∈ Icc (0 : ℝ) 1 := by
    intro u
    constructor <;> linarith [(hα u).1, (hα u).2]
  have hmono : Monotone (fun u => α u / 3) :=
    fun a b hab => div_le_div_of_nonneg_right (hm hab) (by norm_num)
  have hLip3 : LipschitzWith (3 * K) (fun y => 3 * f y) := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    calc
      dist (3 * f u) (3 * f v) = 3 * dist (f u) (f v) := by
        simp only [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
      _ ≤ 3 * ((K : ℝ) * dist u v) :=
        mul_le_mul_of_nonneg_left (hLip.dist_le_mul u v) (by norm_num)
      _ = ((3 * K : ℝ≥0) : ℝ) * dist u v := by
        change (3 : ℝ) * ((K : ℝ) * dist u v) = 3 * (K : ℝ) * dist u v
        ring
  have h₁ := (dyadicScalar_general_uniform (hf.const_mul 3) hLip3
    β hb hmono s t ht).tendsto_at x
  have h₂ := ((dyadicScalar_general_uniform hf hLip β hα hm s t ht).tendsto_at x).const_mul 3
  simp only [dyadicScalar_div_three] at h₁
  exact tendsto_nhds_unique h₁ h₂

theorem trialValue_zero_finite (β : ℝ) (γ α : ℝ → ℝ)
    (hγ : ∀ u, γ u ∈ Icc (0 : ℝ) 1) (hmγ : Monotone γ)
    (r d : ℝ) (N : ℕ) (hs : r - 2 * d ∈ Icc (0 : ℝ) 1)
    (hΦ : BoundedDerivs (Phi β α (r - 2 * d + 4 * (2 * d))))
    {K : ℝ≥0} (hLip : LipschitzWith K
      (scalarIncrementChain (scalarWindow β α (1 / 2) (r - 2 * d) (2 * d) N)
        (Phi β α (r - 2 * d + 4 * (2 * d))))) :
    trialValue β γ α r d 0 N =
      3 * scalarCDFOperator β γ 0 (Real.toNNReal (r - 2 * d))
        (scalarIncrementChain (scalarWindow β α (1 / 2) (r - 2 * d) (2 * d) N)
          (Phi β α (r - 2 * d + 4 * (2 * d)))) 0 -
      β ^ 2 / 4 * penalty γ α (1 / 2) (r - 2 * d) (2 * d) 0 N := by
  unfold trialValue
  rw [zero_div]
  have he : boundary β α (1 / 2) (r - 2 * d) (2 * d) 0 N =
      fun z => 3 * scalarIncrementChain
        (scalarWindow β α (1 / 2) (r - 2 * d) (2 * d) N)
          (Phi β α (r - 2 * d + 4 * (2 * d))) z :=
    funext (boundary_zero_factorization β α (1 / 2) (r - 2 * d) (2 * d) N hΦ)
  rw [he, scalarCDFOperator_div_three β γ hγ hmγ 0 _
    (Real.toNNReal_le_one.mpr hs.2) (scalarIncrementChain_regular _ hΦ) hLip]

theorem scalarWindow_mass_mem (β : ℝ) (α : ℝ → ℝ)
    (hα : ∀ t, α t ∈ Icc (0 : ℝ) 1) (p s h : ℝ) (N : ℕ)
    (u : ℝ × ℝ) (hu : u ∈ scalarWindow β α p s h N) :
    u.1 ∈ Icc (0 : ℝ) 1 := by
  simp only [scalarWindow, List.mem_append] at hu
  rcases hu with ((hu | hu) | hu) | hu
  all_goals
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hu
    exact hα _

theorem trialValue_zero_finite_admissible (β : ℝ) (γ α : ℝ → ℝ)
    (hγ : ∀ t, γ t ∈ Icc (0 : ℝ) 1) (hmγ : Monotone γ)
    (hα : ∀ t, α t ∈ Icc (0 : ℝ) 1) (hmα : Monotone α)
    (r d : ℝ) (N : ℕ) (hs : r - 2 * d ∈ Icc (0 : ℝ) 1)
    (hT : r - 2 * d + 4 * (2 * d) ∈ Icc (0 : ℝ) 1) :
    trialValue β γ α r d 0 N =
      3 * scalarCDFOperator β γ 0 (Real.toNNReal (r - 2 * d))
        (scalarIncrementChain (scalarWindow β α (1 / 2) (r - 2 * d) (2 * d) N)
          (Phi β α (r - 2 * d + 4 * (2 * d)))) 0 -
      β ^ 2 / 4 * penalty γ α (1 / 2) (r - 2 * d) (2 * d) 0 N := by
  have ht : Real.toNNReal (1 - (r - 2 * d + 4 * (2 * d))) ≤ 1 :=
    Real.toNNReal_le_one.mpr (by linarith [hT.1])
  have hΦ : BoundedDerivs (Phi β α (r - 2 * d + 4 * (2 * d))) :=
    scalarCDFValue_regular β hα hmα _ _ ht
  apply trialValue_zero_finite β γ α hγ hmγ r d N hs hΦ
  apply scalarIncrementChain_lipschitz _ (fun u hu =>
    (scalarWindow_mass_mem β α hα _ _ _ N u hu).1) hΦ
  exact scalarCDFValue_lipschitz β hα hmα _ _ ht

def swap23 : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 0,
    ContinuousLinearMap.proj 2, ContinuousLinearMap.proj 1]

@[simp] theorem swap23_apply (x : Fin 3 → ℝ) : swap23 x = ![x 0, x 2, x 1] := by
  ext i
  fin_cases i <;> rfl

private theorem rankOne_neg (v : Fin 3 → ℝ) : rankOneMatrix (-v) = rankOneMatrix v := by
  ext i j
  simp only [rankOneMatrix, Pi.neg_apply, neg_mul_neg]

private theorem penalty_vectors (m : ℝ) (vs : List (Fin 3 → ℝ))
    (Q : Fin 3 → Fin 3 → ℝ) :
    matrixChainPenalty (vs.map (fun v => (m, v))) Q =
      m * (matrixSquare 3 (Q + (vs.map rankOneMatrix).sum) - matrixSquare 3 Q) := by
  induction vs generalizing Q with
  | nil => simp
  | cons v vs ih =>
    simp only [List.map_cons, matrixChainPenalty_cons, ih, List.sum_cons, add_assoc]
    ring

private structure ScheduleEquivalent (l r : List (ℝ × (Fin 3 → ℝ))) : Prop where
  covariance : matrixChainCovariance l = matrixChainCovariance r
  penalty : ∀ Q, matrixChainPenalty l Q = matrixChainPenalty r Q
  value : ∀ f, BoundedDerivs f → vectorIncrementChain l f = vectorIncrementChain r f

private theorem ScheduleEquivalent.refl (l : List (ℝ × (Fin 3 → ℝ))) :
    ScheduleEquivalent l l := ⟨rfl, fun _ => rfl, fun _ _ => rfl⟩

private theorem ScheduleEquivalent.append {l₁ l₂ r₁ r₂ : List (ℝ × (Fin 3 → ℝ))}
    (hl : ScheduleEquivalent l₁ l₂) (hr : ScheduleEquivalent r₁ r₂) :
    ScheduleEquivalent (l₁ ++ r₁) (l₂ ++ r₂) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [matrixChainCovariance_append, matrixChainCovariance_append, hl.covariance, hr.covariance]
  · intro Q
    rw [matrixChainPenalty_append, matrixChainPenalty_append, hl.penalty,
      hl.covariance, hr.penalty]
  · intro f hf
    rw [vectorIncrementChain_append, vectorIncrementChain_append,
      hl.value _ (vectorIncrementChain_regular _ hf), hr.value f hf]

private theorem ScheduleEquivalent.flatMap {ι : Type} (js : List ι)
    (l r : ι → List (ℝ × (Fin 3 → ℝ)))
    (he : ∀ j ∈ js, ScheduleEquivalent (l j) (r j)) :
    ScheduleEquivalent (js.flatMap l) (js.flatMap r) := by
  induction js with
  | nil => exact .refl []
  | cons j js ih =>
    exact (he j List.mem_cons_self).append
      (ih (fun a ha => he a (List.mem_cons_of_mem j ha)))

private theorem equivalent_block (m : ℝ) (vs ws : List (Fin 3 → ℝ))
    (hc : (vs.map rankOneMatrix).sum = (ws.map rankOneMatrix).sum)
    (hv : ∀ f, BoundedDerivs f →
      vectorIncrementChain (vs.map (fun v => (m, v))) f =
      vectorIncrementChain (ws.map (fun v => (m, v))) f) :
    ScheduleEquivalent (vs.map (fun v => (m, v))) (ws.map (fun v => (m, v))) := by
  refine ⟨?_, ?_, hv⟩
  · rw [covariance_vectors, covariance_vectors, hc]
  · intro Q
    rw [penalty_vectors, penalty_vectors, hc]

private theorem equivalent_neg (m : ℝ) (v : Fin 3 → ℝ) :
    ScheduleEquivalent [(m, -v)] [(m, v)] := by
  apply equivalent_block m [-v] [v]
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, rankOne_neg]
  · intro f _
    simp only [List.map_cons, List.map_nil, vectorIncrementChain, vectorStep_neg_direction]

private theorem equivalent_swap (m : ℝ) (v w : Fin 3 → ℝ) :
    ScheduleEquivalent [(m, v), (m, w)] [(m, w), (m, v)] := by
  apply equivalent_block m [v, w] [w, v]
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    exact add_comm _ _
  · intro f hf
    simp only [List.map_cons, List.map_nil, vectorIncrementChain]
    exact vectorStep_equal_mass_comm hf m v w

private theorem equivalent_swap_last (m : ℝ) (u v w : Fin 3 → ℝ) :
    ScheduleEquivalent [(m, u), (m, v), (m, w)] [(m, u), (m, w), (m, v)] :=
  (ScheduleEquivalent.refl [(m, u)]).append (equivalent_swap m v w)

private theorem swap_vectors (p k : ℝ) :
    swap23 (SKOptimized.Overshoot.commonVector p k) = SKOptimized.Overshoot.commonVector p (-k) ∧
    swap23 (SKOptimized.Overshoot.sharedVector p k) = SKOptimized.Overshoot.sharedVector p (-k) ∧
    swap23 (SKOptimized.Overshoot.rampVector p k) = SKOptimized.Overshoot.rampVector p (-k) ∧
    swap23 (SKOptimized.Overshoot.postXVector p k) = SKOptimized.Overshoot.postYVector p (-k) ∧
    swap23 (SKOptimized.Overshoot.postYVector p k) = SKOptimized.Overshoot.postXVector p (-k) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals ext i; fin_cases i <;>
    simp [swap23_apply, SKOptimized.Overshoot.commonVector, SKOptimized.Overshoot.sharedVector,
      SKOptimized.Overshoot.rampVector, SKOptimized.Overshoot.postXVector,
      SKOptimized.Overshoot.postYVector] <;> ring

private theorem swap_contrast : swap23 SKOptimized.Overshoot.contrast = -SKOptimized.Overshoot.contrast := by
  ext i
  fin_cases i <;> norm_num [swap23_apply, SKOptimized.Overshoot.contrast]

private theorem swap_axes :
    swap23 (Pi.single 0 (1 : ℝ)) = Pi.single 0 1 ∧
    swap23 (Pi.single 1 (1 : ℝ)) = Pi.single 2 1 ∧
    swap23 (Pi.single 2 (1 : ℝ)) = Pi.single 1 1 := by
  refine ⟨?_, ?_, ?_⟩
  all_goals ext i; fin_cases i <;> simp [swap23_apply]

private theorem grid_equivalent (β : ℝ) (α : ℝ → ℝ) (s h : ℝ) (N : ℕ)
    (a len c : ℝ) (vs ws : List (Fin 3 → ℝ))
    (he : ∀ m b : ℝ, ScheduleEquivalent
      (vs.map (fun v => (m, b • v))) (ws.map (fun v => (m, b • swap23 v)))) :
    ScheduleEquivalent
      ((windowGrid α s h N a len c vs).map (fun u => (u.1, β • u.2)))
      (((windowGrid α s h N a len c ws).map (fun u => (u.1, β • u.2))).map
        (fun u => (u.1, swap23 u.2))) := by
  rw [windowGrid_scaled, windowGrid_scaled]
  simp only [List.map_flatMap, List.map_map, Function.comp_def, map_smul]
  exact ScheduleEquivalent.flatMap _ _ _ (fun u _ => he (u.1 / c) u.2)

theorem exists_window_admissible_cutoff (α : ℝ → ℝ)
    (hα : ∀ t, α t ∈ Icc (0 : ℝ) 1) (hm : Monotone α)
    (s : ℝ) (hs : 0 < α s) (hc : ContinuousAt α s) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h ∈ Icc (0 : ℝ) h₀, ∀ p k : ℝ, ∀ N : ℕ,
      p ∈ Icc (0 : ℝ) (1 / 2) → |k| ≤ (1 / 2 : ℝ) →
      (∀ u ∈ window α p s h k N, u.1 ∈ Icc (0 : ℝ) 1) ∧
      (window α p s h k N).Pairwise (fun u v => u.1 ≤ v.1) := by
  obtain ⟨h₀, hh₀, H⟩ := exists_window_mass_sorted_cutoff α hm (fun t => (hα t).1) s hs hc
  refine ⟨h₀, hh₀, ?_⟩
  intro h hh p k N hp hk
  exact ⟨fun u hu => window_mass_mem α hα p s h k N u hu,
    H h hh p k N ⟨hp.1, by linarith [hp.2]⟩ (repairLength_mem hp hk)⟩

@[simp] theorem repairLength_neg (p k : ℝ) : repairLength p (-k) = repairLength p k := by
  simp only [repairLength, neg_sq]

private theorem repair_equivalent (β : ℝ) (α : ℝ → ℝ) (p s h k : ℝ) (N : ℕ) :
    ScheduleEquivalent
      ((windowRepairGrid α p s h (-k) N [SKOptimized.Overshoot.rampVector p 0,
        (1 / Real.sqrt 2) • SKOptimized.Overshoot.sharedVector p 0,
        (1 / 2 : ℝ) • SKOptimized.Overshoot.contrast]).map (fun u => (u.1, β • u.2)))
      (((windowRepairGrid α p s h k N [SKOptimized.Overshoot.rampVector p 0,
        (1 / Real.sqrt 2) • SKOptimized.Overshoot.sharedVector p 0,
        (1 / 2 : ℝ) • SKOptimized.Overshoot.contrast]).map (fun u => (u.1, β • u.2))).map
          (fun u => (u.1, swap23 u.2))) := by
  have h₀ : swap23 (SKOptimized.Overshoot.rampVector p 0) = SKOptimized.Overshoot.rampVector p 0 := by
    simpa only [neg_zero] using (swap_vectors p 0).2.2.1
  have h₁ : swap23 ((1 / Real.sqrt 2) • SKOptimized.Overshoot.sharedVector p 0) =
      (1 / Real.sqrt 2) • SKOptimized.Overshoot.sharedVector p 0 := by
    rw [map_smul]
    simpa only [neg_zero] using congrArg (fun v => (1 / Real.sqrt 2) • v) (swap_vectors p 0).2.1
  have h₂ : swap23 ((1 / 2 : ℝ) • SKOptimized.Overshoot.contrast) =
      -((1 / 2 : ℝ) • SKOptimized.Overshoot.contrast) := by
    rw [map_smul, swap_contrast, smul_neg]
  simp only [windowRepairGrid, List.map_flatMap, List.map_map, Function.comp_def,
    repairLength_neg]
  apply ScheduleEquivalent.flatMap
  intro j _
  simp only [List.map_cons, List.map_nil, map_smul, h₀, h₁, h₂, smul_smul,
    neg_mul, neg_smul, smul_neg]
  exact (equivalent_neg _ _).append ((equivalent_neg _ _).append (.refl [_]))

private theorem window_neg_equivalent (β : ℝ) (α : ℝ → ℝ) (p s h k : ℝ) (N : ℕ) :
    ScheduleEquivalent
      ((window α p s h (-k) N).map (fun u => (u.1, β • u.2)))
      (((window α p s h k N).map (fun u => (u.1, β • u.2))).map
        (fun u => (u.1, swap23 u.2))) := by
  have H0 := grid_equivalent β α s h N 0 1 3
    [SKOptimized.Overshoot.commonVector p (-k)] [SKOptimized.Overshoot.commonVector p k]
    (by
      intro m b
      simp only [List.map_cons, List.map_nil, (swap_vectors p k).1]
      exact .refl _)
  have H1 := grid_equivalent β α s h N 1 p 2
    [SKOptimized.Overshoot.sharedVector p (-k)] [SKOptimized.Overshoot.sharedVector p k]
    (by
      intro m b
      simp only [List.map_cons, List.map_nil, (swap_vectors p k).2.1]
      exact .refl _)
  have H2 := grid_equivalent β α s h N 1 p 1
    [SKOptimized.Overshoot.rampVector p (-k)] [SKOptimized.Overshoot.rampVector p k]
    (by
      intro m b
      simp only [List.map_cons, List.map_nil, (swap_vectors p k).2.2.1]
      exact .refl _)
  have H3 := grid_equivalent β α s h N (1 + p) (1 - p) 1
    [SKOptimized.Overshoot.rampVector p (-k), SKOptimized.Overshoot.postXVector p (-k),
      SKOptimized.Overshoot.postYVector p (-k)]
    [SKOptimized.Overshoot.rampVector p k, SKOptimized.Overshoot.postXVector p k,
      SKOptimized.Overshoot.postYVector p k]
    (by
      intro m b
      simp only [List.map_cons, List.map_nil, (swap_vectors p k).2.2.1,
        (swap_vectors p k).2.2.2.1, (swap_vectors p k).2.2.2.2]
      exact equivalent_swap_last m _ _ _)
  have H4 := repair_equivalent β α p s h k N
  have H5 := grid_equivalent β α s h N (2 + repairLength p k) (2 - repairLength p k) 1
    [Pi.single 0 1, Pi.single 1 1, Pi.single 2 1]
    [Pi.single 0 1, Pi.single 1 1, Pi.single 2 1]
    (by
      intro m b
      simp only [List.map_cons, List.map_nil, swap_axes.1, swap_axes.2.1, swap_axes.2.2]
      exact equivalent_swap_last m _ _ _)
  rw [window_eq, window_eq]
  simp only [List.map_append, repairLength_neg]
  exact ((((H0.append H1).append H2).append H3).append H4).append H5

@[simp] theorem swap23_diagonal (z : ℝ) : swap23 (fun _ => z) = fun _ => z := by
  ext i
  fin_cases i <;> rfl

theorem window_chain_even (β : ℝ) (α : ℝ → ℝ) (p s h k : ℝ) (N : ℕ)
    {f : (Fin 3 → ℝ) → ℝ} (hf : BoundedDerivs f) (hsym : f ∘ swap23 = f) (z : ℝ) :
    vectorIncrementChain ((window α p s h (-k) N).map (fun u => (u.1, β • u.2))) f (fun _ => z) =
    vectorIncrementChain ((window α p s h k N).map (fun u => (u.1, β • u.2))) f (fun _ => z) := by
  have he := congrFun ((window_neg_equivalent β α p s h k N).value f hf) (fun _ => z)
  have hp := congrFun (vectorIncrementChain_pullback swap23
    ((window α p s h k N).map (fun u => (u.1, β • u.2))) f) (fun _ => z)
  rw [hsym] at hp
  simp only [Function.comp_apply, swap23_diagonal] at hp
  exact he.trans hp.symm

def covarianceSwap23 (Q : Fin 3 → Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun i j => swap23 (fun a => swap23 (Q a) j) i

private theorem covarianceSwap23_add (Q R : Fin 3 → Fin 3 → ℝ) :
    covarianceSwap23 (Q + R) = covarianceSwap23 Q + covarianceSwap23 R := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem rankOne_swap23 (v : Fin 3 → ℝ) :
    rankOneMatrix (swap23 v) = covarianceSwap23 (rankOneMatrix v) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem matrixSquare_swap23 (Q : Fin 3 → Fin 3 → ℝ) :
    matrixSquare 3 (covarianceSwap23 Q) = matrixSquare 3 Q := by
  simp [matrixSquare, Fin.sum_univ_succ, covarianceSwap23, swap23_apply]
  ring

theorem matrixChainPenalty_swap23 (l : List (ℝ × (Fin 3 → ℝ)))
    (Q : Fin 3 → Fin 3 → ℝ) :
    matrixChainPenalty (l.map (fun u => (u.1, swap23 u.2))) (covarianceSwap23 Q) =
      matrixChainPenalty l Q := by
  induction l generalizing Q with
  | nil => rfl
  | cons u l ih =>
    simp only [List.map_cons, matrixChainPenalty_cons, rankOne_swap23,
      ← covarianceSwap23_add, matrixSquare_swap23, ih]

theorem window_penalty_even (α : ℝ → ℝ) (p s h k : ℝ) (N : ℕ) :
    matrixChainPenalty (window α p s h (-k) N) (fun _ _ => s) =
      matrixChainPenalty (window α p s h k N) (fun _ _ => s) := by
  have he := (window_neg_equivalent 1 α p s h k N).penalty (fun _ _ => s)
  simp only [one_smul, Prod.mk.eta, List.map_id_fun', id_eq] at he
  have hq : covarianceSwap23 (fun _ _ => s) = fun _ _ => s := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have H := matrixChainPenalty_swap23 (window α p s h k N) (fun _ _ => s)
  rw [hq] at H
  exact he.trans H

theorem penalty_even (γ α : ℝ → ℝ) (p s h k : ℝ) (N : ℕ) :
    penalty γ α p s h (-k) N = penalty γ α p s h k N := by
  rw [penalty, penalty, window_penalty_even]

theorem boundary_even (β : ℝ) (α : ℝ → ℝ) (p s h k : ℝ) (N : ℕ)
    (hΦ : BoundedDerivs (Phi β α (s + 4 * h))) (z : ℝ) :
    boundary β α p s h (-k) N z = boundary β α p s h k N z := by
  have hf : BoundedDerivs (fun x : Fin 3 → ℝ => ∑ i, Phi β α (s + 4 * h) (x i)) := by
    simpa [Fin.sum_univ_succ, add_assoc] using
      ((hΦ.compCLM (tripleCoordinate 0)).add
        (hΦ.compCLM (tripleCoordinate 1))).add
          (hΦ.compCLM (tripleCoordinate 2))
  have hsym : (fun x : Fin 3 → ℝ => ∑ i, Phi β α (s + 4 * h) (x i)) ∘ swap23 =
      fun x : Fin 3 → ℝ => ∑ i, Phi β α (s + 4 * h) (x i) := by
    funext x
    simp [swap23_apply, Fin.sum_univ_succ]
    ring
  rw [boundary_eq_Phi, boundary_eq_Phi]
  exact window_chain_even β α p s h k N hf hsym z

theorem trialValue_even (β : ℝ) (γ α : ℝ → ℝ) (r d δ : ℝ) (N : ℕ)
    (hΦ : BoundedDerivs (Phi β α (r - 2 * d + 4 * (2 * d)))) :
    trialValue β γ α r d (-δ) N = trialValue β γ α r d δ N := by
  have hb : boundary β α (1 / 2) (r - 2 * d) (2 * d) (-(δ / (2 * d))) N =
      boundary β α (1 / 2) (r - 2 * d) (2 * d) (δ / (2 * d)) N :=
    funext (boundary_even β α (1 / 2) (r - 2 * d) (2 * d) (δ / (2 * d)) N hΦ)
  unfold trialValue
  rw [neg_div, hb, penalty_even]

theorem trialValue_even_admissible (β : ℝ) (γ α : ℝ → ℝ)
    (hα : ∀ t, α t ∈ Icc (0 : ℝ) 1) (hmα : Monotone α) (r d δ : ℝ) (N : ℕ)
    (hT : r - 2 * d + 4 * (2 * d) ∈ Icc (0 : ℝ) 1) :
    trialValue β γ α r d (-δ) N = trialValue β γ α r d δ N := by
  apply trialValue_even
  exact scalarCDFValue_regular β hα hmα _ _ (Real.toNNReal_le_one.mpr (by linarith [hT.1]))

private def baselineMiddle (l : List (ℝ × ℝ)) : List TripleMiddleIncrement :=
  l.map Sum.inr ++ l.map (fun u => Sum.inl (u.1, (u.2, 0)))

private theorem baselineMiddle_left (l : List (ℝ × ℝ)) :
    weightedUnderlying (productLeft (baselineMiddle l)) = l := by
  simp [baselineMiddle, productLeft, weightedUnderlying, List.filterMap_append,
    List.filterMap_map, List.map_map, Function.comp_def]

private theorem baselineMiddle_right (l : List (ℝ × ℝ)) :
    productRight (baselineMiddle l) = l := by
  simp [baselineMiddle, productRight, List.filterMap_append, List.filterMap_map]

private theorem baselineMiddle_schedule (l : List (ℝ × ℝ)) :
    tripleMiddleSchedule 0 (baselineMiddle l) =
      l.map (fun u => (u.1 / 2, ![0, u.2, u.2])) ++
      l.map (fun u => (u.1, ![u.2, 0, 0])) := by
  simp [baselineMiddle, tripleMiddleSchedule, List.map_append, List.map_map,
    Function.comp_def, productMass, tripleMiddleVector]

private theorem baseline_schedule_penalty (c m t : List (ℝ × ℝ)) (s : ℝ) :
    matrixChainPenalty (tripleCommonSchedule c ++
      tripleMiddleSchedule 0 (baselineMiddle m) ++ tripleTailSchedule t)
      (fun _ _ => s) = 3 * rawPenalty (c ++ m ++ t) s := by
  have hconst : (fun _ _ : Fin 3 => s) = tripleClockMatrix s s s s s := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hc := tripleCommonSchedule_covariance c s
  have hm := tripleMiddleSchedule_covariance 0 (baselineMiddle m)
    (s + rawVariance c) (s + rawVariance c) (s + rawVariance c) 0 0
  have hp := tripleMiddleSchedule_penalty 0 (baselineMiddle m)
    (s + rawVariance c) (s + rawVariance c) (s + rawVariance c) 0 0
  simp only [baselineMiddle_left, baselineMiddle_right, tripleClockPerturbed_zero,
    zero_pow (by norm_num : 2 ≠ 0), zero_pow (by norm_num : 4 ≠ 0), mul_zero,
    zero_mul, add_zero] at hm hp
  have hcm : tripleClockMatrix s s s s s +
      matrixChainCovariance (tripleCommonSchedule c ++ tripleMiddleSchedule 0 (baselineMiddle m)) =
      tripleClockPerturbed (s + rawVariance c + rawVariance m)
        (s + rawVariance c + rawVariance m) (s + rawVariance c + rawVariance m)
        (s + rawVariance c) (s + rawVariance c + rawVariance m) 0
        (0 + weightedCross (productLeft (baselineMiddle m)))
        (0 + weightedVariance (productLeft (baselineMiddle m))) := by
    rw [matrixChainCovariance_append, ← add_assoc, hc, hm]
  rw [hconst, matrixChainPenalty_append, hcm, matrixChainPenalty_append,
    tripleCommonSchedule_penalty, hc, hp, tripleTailSchedule_penalty]
  simp only [zero_pow (by norm_num : 2 ≠ 0), rawPenalty_append, rawVariance_append]
  ring_nf

private theorem matrixChainPenalty_zero_vectors
    (l : List (ℝ × (Fin 3 → ℝ))) (hl : ∀ u ∈ l, u.2 = 0)
    (Q : Fin 3 → Fin 3 → ℝ) : matrixChainPenalty l Q = 0 := by
  induction l generalizing Q with
  | nil => rfl
  | cons u l ih =>
    have hz : rankOneMatrix u.2 = 0 := by
      rw [hl u List.mem_cons_self]
      ext i j
      simp only [rankOneMatrix, Pi.zero_apply, zero_mul]
    rw [matrixChainPenalty_cons, hz, add_zero, sub_self, mul_zero, zero_add]
    exact ih (fun v hv => hl v (List.mem_cons_of_mem u hv)) Q

private theorem matrixChainCovariance_zero_vectors
    (l : List (ℝ × (Fin 3 → ℝ))) (hl : ∀ u ∈ l, u.2 = 0) :
    matrixChainCovariance l = 0 := by
  induction l with
  | nil => rfl
  | cons u l ih =>
    have hz : rankOneMatrix u.2 = 0 := by
      rw [hl u List.mem_cons_self]
      ext i j
      simp only [rankOneMatrix, Pi.zero_apply, zero_mul]
    rw [matrixChainCovariance_cons, hz, zero_add]
    exact ih (fun v hv => hl v (List.mem_cons_of_mem u hv))

private theorem penalty_remove_zero_vectors
    (l z r : List (ℝ × (Fin 3 → ℝ))) (hz : ∀ u ∈ z, u.2 = 0)
    (Q : Fin 3 → Fin 3 → ℝ) :
    matrixChainPenalty ((l ++ z) ++ r) Q = matrixChainPenalty (l ++ r) Q := by
  simp only [matrixChainPenalty_append, matrixChainCovariance_append,
    matrixChainPenalty_zero_vectors z hz, matrixChainCovariance_zero_vectors z hz,
    add_zero]

theorem window_zero_penalty (α : ℝ → ℝ) (p s h : ℝ) (N : ℕ) :
    matrixChainPenalty (window α p s h 0 N) (fun _ _ => s) =
      3 * rawPenalty (scalarWindow 1 α p s h N) s := by
  have hmap : window α p s h 0 N =
      (window α p s h 0 N).map (fun u => (u.1, (1 : ℝ) • u.2)) := by
    simp only [one_smul, Prod.mk.eta, List.map_id_fun', id_eq]
  rw [hmap, window_eq]
  simp only [List.map_append]
  rw [zero_common_grid, zero_shared_grid, zero_ramp_grid, zero_post_grid]
  simp only [repairLength, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_mul,
    add_zero, sub_zero]
  rw [axis_grid]
  rw [penalty_remove_zero_vectors]
  · simpa only [baselineMiddle_schedule, tripleTailSchedule, List.flatMap_append,
      scalarWindow, List.append_assoc] using
      baseline_schedule_penalty (scalarGrid 1 α s h N 0 1) (scalarGrid 1 α s h N 1 p)
        (scalarGrid 1 α s h N (1 + p) (1 - p) ++ scalarGrid 1 α s h N 2 2) s
  · intro u hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
    obtain ⟨j, _, hj⟩ := List.mem_flatMap.mp hv
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hj
    simp only [zero_mul, zero_smul, smul_zero]

theorem penalty_zero_scalar (γ α : ℝ → ℝ) (p s h : ℝ) (N : ℕ) :
    penalty γ α p s h 0 N =
      6 * (∫ t in Icc (0 : ℝ) s, t * γ t) +
      3 * rawPenalty (scalarWindow 1 α p s h N) s +
      6 * (∫ t in Icc (s + 4 * h) 1, t * α t) := by
  rw [penalty, window_zero_penalty]

end SKBarriers2.OW
