module

public import SKBarriers2.Corner.Evenness
public import SKBarriers2.Corner.WindowAlgebra
public import OAI.Probability.SKBarriers.Scalar.ScalarSemigroup

@[expose] public section

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Set OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

section Merge
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem scalarStep_line (m c : ℝ) (v x : E) (f : E → ℝ) :
    scalarStep m c (fun t => f (x + t • v)) =
      fun t => vectorStep m (c • v) f (x + t • v) := by
  have he (t y : ℝ) : x + (t + c * y) • v = (x + t • v) + y • (c • v) := by
    simp only [add_smul, smul_smul]
    rw [mul_comm c y, add_assoc]
  funext t
  simp only [scalarStep, vectorStep, gaussianStep, positiveGaussianLogStep, he]

theorem vectorStep_collinear_merge {f : E → ℝ} (hf : BoundedDerivs f)
    (m c d e : ℝ) (v : E) (he : e ^ 2 = c ^ 2 + d ^ 2) :
    vectorStep m (c • v) (vectorStep m (d • v) f) = vectorStep m (e • v) f := by
  funext x
  let L : ℝ →L[ℝ] E := ContinuousLinearMap.toSpanSingleton ℝ v
  have hline : BoundedDerivs (fun t : ℝ => f (x + t • v)) := by
    simpa only [L, ContinuousLinearMap.toSpanSingleton_apply, Function.comp_def]
      using (hf.translate x).compCLM L
  have H := congrFun (scalarStep_semigroup hline m c d e he) 0
  rw [scalarStep_line, scalarStep_line, scalarStep_line] at H
  simpa only [zero_smul, add_zero] using H

private theorem chain_commute_step (vs : List E) (m : ℝ) (v : E)
    {f : E → ℝ} (hf : BoundedDerivs f) :
    vectorIncrementChain (vs.map fun w => (m, w)) (vectorStep m v f) =
      vectorStep m v (vectorIncrementChain (vs.map fun w => (m, w)) f) := by
  induction vs with
  | nil => rfl
  | cons w vs ih =>
    simp only [List.map_cons, vectorIncrementChain, ih]
    exact OW.vectorStep_equal_mass_comm (vectorIncrementChain_regular _ hf) m w v

private theorem block_merge (vs : List E) {f : E → ℝ} (hf : BoundedDerivs f)
    (m c d e : ℝ) (he : e ^ 2 = c ^ 2 + d ^ 2) :
    vectorIncrementChain (vs.map fun v => (m, c • v))
      (vectorIncrementChain (vs.map fun v => (m, d • v)) f) =
        vectorIncrementChain (vs.map fun v => (m, e • v)) f := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    change vectorStep m (c • v)
      (vectorIncrementChain (vs.map fun w => (m, c • w))
        (vectorStep m (d • v) (vectorIncrementChain (vs.map fun w => (m, d • w)) f))) = _
    have hc := chain_commute_step (vs.map fun w => c • w) m (d • v)
      (vectorIncrementChain_regular (vs.map fun w => (m, d • w)) hf)
    simp only [List.map_map, Function.comp_def] at hc
    rw [hc, ih]
    exact vectorStep_collinear_merge (vectorIncrementChain_regular _ hf) m c d e v he

private theorem chain_zero_directions (vs : List E) (m : ℝ) (f : E → ℝ) :
    vectorIncrementChain (vs.map fun _ => (m, (0 : E))) f = f := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp only [List.map_cons, vectorIncrementChain, ih, vectorStep_zero]

theorem repeated_block_merge (vs : List E) (m c : ℝ) (N : ℕ)
    {f : E → ℝ} (hf : BoundedDerivs f) (e : ℝ) (he : e ^ 2 = (N : ℝ) * c ^ 2) :
    vectorIncrementChain ((List.range N).flatMap fun _ => vs.map fun v => (m, c • v)) f =
      vectorIncrementChain (vs.map fun v => (m, e • v)) f := by
  induction N generalizing f e with
  | zero =>
    have he₀ : e = 0 := by simpa only [Nat.cast_zero, zero_mul, sq_eq_zero_iff] using he
    subst e
    simp only [List.range_zero, List.flatMap_nil, vectorIncrementChain, zero_smul]
    exact (chain_zero_directions vs m f).symm
  | succ N ih =>
    let d := Real.sqrt (N : ℝ) * c
    have hd : d ^ 2 = (N : ℝ) * c ^ 2 := by
      dsimp only [d]
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
    have he' : e ^ 2 = d ^ 2 + c ^ 2 := by
      rw [hd]
      simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using he
    rw [List.range_succ, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [vectorIncrementChain_append, ih (vectorIncrementChain_regular _ hf) d hd]
    exact block_merge vs hf m d c e he'

private def RegularEquivalent (l r : List (ℝ × E)) : Prop :=
  ∀ f : E → ℝ, BoundedDerivs f → vectorIncrementChain l f = vectorIncrementChain r f

private theorem RegularEquivalent.append {l r l' r' : List (ℝ × E)}
    (hl : RegularEquivalent l l') (hr : RegularEquivalent r r') :
    RegularEquivalent (l ++ r) (l' ++ r') := by
  intro f hf
  rw [vectorIncrementChain_append, vectorIncrementChain_append, hr f hf]
  exact hl _ (vectorIncrementChain_regular _ hf)

end Merge

private theorem grid_merge (β a s h t len c : ℝ) {N : ℕ} (hN : 0 < N)
    (vs : List Vec3) (hd : 0 ≤ h * len) :
    RegularEquivalent
      ((OW.windowGrid (fun _ => a) s h N t len c vs).map (fun u => (u.1, β • u.2)))
      (vs.map fun v => (a / c, (β * Real.sqrt (h * len)) • v)) := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  intro f hf
  simp only [OW.windowGrid, List.map_flatMap, List.map_map, Function.comp_def, smul_smul]
  apply repeated_block_merge vs (a / c) (β * Real.sqrt (h * len / (N : ℝ))) N hf
  rw [mul_pow, mul_pow, Real.sq_sqrt hd,
    Real.sq_sqrt (div_nonneg hd (Nat.cast_nonneg N))]
  field_simp

private theorem repair_merge (β a p s h k : ℝ) {N : ℕ} (hN : 0 < N)
    (vs : List Vec3) (hd : 0 ≤ h * (4 * varianceCoefficient p)) :
    RegularEquivalent
      ((OW.windowRepairGrid (fun _ => a) p s h k N vs).map (fun u => (u.1, β • u.2)))
      (vs.map fun v => (a, (β * (k * Real.sqrt (h * (4 * varianceCoefficient p)))) • v)) := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  intro f hf
  simp only [OW.windowRepairGrid, List.map_flatMap, List.map_map, Function.comp_def, smul_smul, div_one]
  apply repeated_block_merge vs a (β * (k * Real.sqrt (h * (4 * varianceCoefficient p) / (N : ℝ)))) N hf
  rw [mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hd,
    Real.sq_sqrt (div_nonneg hd (Nat.cast_nonneg N))]
  field_simp

def frozenCommon (β a p h k : ℝ) : List (ℝ × Vec3) :=
  [(a / 3, (β * Real.sqrt h) • commonVector p k)]

def frozenShared (β a p h k : ℝ) : List (ℝ × Vec3) :=
  [(a / 2, (β * Real.sqrt (h * p)) • sharedVector p k)]

def frozenInner (β a p h k : ℝ) : List (ℝ × Vec3) :=
  [(a, (β * Real.sqrt (h * p)) • rampVector p k)] ++
    [rampVector p k, postXVector p k, postYVector p k].map
      (fun v => (a, (β * Real.sqrt (h * (1 - p))) • v)) ++
    [rampVector p 0, (1 / Real.sqrt 2) • sharedVector p 0, (1 / 2 : ℝ) • contrast].map
      (fun v => (a, (β * (k * Real.sqrt (h * (4 * varianceCoefficient p)))) • v)) ++
    [Pi.single 0 1, Pi.single 1 1, Pi.single 2 1].map
      (fun v => (a, (β * Real.sqrt (h * (2 - OW.repairLength p k))) • v))

def frozenSchedule (β a p h k : ℝ) : List (ℝ × Vec3) :=
  frozenCommon β a p h k ++ frozenShared β a p h k ++ frozenInner β a p h k

theorem frozenSchedule_length (β a p h k : ℝ) : (frozenSchedule β a p h k).length = 12 := by
  simp [frozenSchedule, frozenCommon, frozenShared, frozenInner]

theorem frozenSchedule_eq_window_one (β a p s h k : ℝ) :
    frozenSchedule β a p h k =
      (OW.window (fun _ => a) p s h k 1).map (fun u => (u.1, β • u.2)) := by
  rw [OW.window_eq]
  norm_num [frozenSchedule, frozenCommon, frozenShared, frozenInner,
    OW.windowGrid, OW.windowRepairGrid, List.map_append, List.map_map, Function.comp_def, smul_smul]
  simp [mul_assoc]

private theorem covariance_scaled (l : List (ℝ × Vec3)) (β : ℝ) :
    matrixChainCovariance (l.map (fun u => (u.1, β • u.2))) = β ^ 2 • matrixChainCovariance l := by
  induction l with
  | nil => simp
  | cons u l ih =>
    simp only [List.map_cons, matrixChainCovariance_cons, ih, smul_add]
    congr 1
    ext i j
    simp only [rankOneMatrix, Pi.smul_apply, smul_eq_mul]
    ring

theorem frozenCommon_covariance (β a p h k : ℝ) (hh : 0 ≤ h) :
    matrixChainCovariance (frozenCommon β a p h k) =
      (β ^ 2 * h) • (fun i j => q0 p k i j) := by
  ext i j
  simp only [frozenCommon, matrixChainCovariance_cons, matrixChainCovariance_nil,
    Pi.add_apply, Pi.zero_apply, add_zero, rankOneMatrix, Pi.smul_apply, smul_eq_mul,
    q0, outer]
  calc
    _ = (β ^ 2 * Real.sqrt h ^ 2) * (commonVector p k i * commonVector p k j) := by ring
    _ = _ := by rw [Real.sq_sqrt hh]

theorem frozenShared_covariance (β a p h k : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p) :
    matrixChainCovariance (frozenShared β a p h k) =
      (β ^ 2 * h) • (fun i j => q1 p k i j) := by
  ext i j
  simp only [frozenShared, matrixChainCovariance_cons, matrixChainCovariance_nil,
    Pi.add_apply, Pi.zero_apply, add_zero, rankOneMatrix, Pi.smul_apply, smul_eq_mul,
    q1, outer, Matrix.smul_apply]
  calc
    _ = (β ^ 2 * Real.sqrt (h * p) ^ 2) * (sharedVector p k i * sharedVector p k j) := by ring
    _ = (β ^ 2 * (h * p)) * (sharedVector p k i * sharedVector p k j) := by rw [Real.sq_sqrt (mul_nonneg hh hp)]
    _ = _ := by ring

def frozenInnerCovariance (p k : ℝ) : Mat3 := q2 p k + (4 : ℝ) • (1 : Mat3)

theorem frozenInnerCovariance_physical (p k : ℝ) (hp : p ≠ 2) :
    frozenInnerCovariance p k = outer (rampVector p k) +
      (1 - p) • (outer (postXVector p k) + outer (postYVector p k)) +
      (2 : ℝ) • (1 : Mat3) - (k ^ 2 * varianceCoefficient p) • contrastMatrix := by
  rw [frozenInnerCovariance, q2_physical_decomposition p k hp]
  module

theorem frozenInner_covariance (β a p s h k : ℝ) (hh : 0 ≤ h)
    (hp : p ∈ Icc (0 : ℝ) 1) (hl : OW.repairLength p k ∈ Icc (0 : ℝ) 2) :
    matrixChainCovariance (frozenInner β a p h k) =
      (β ^ 2 * h) • (fun i j => frozenInnerCovariance p k i j) := by
  have hp₂ : p ≠ 2 := by linarith [hp.2]
  have he : q0 p k + q1 p k + frozenInnerCovariance p k =
      (!![4, 1 + k, 1 - k; 1 + k, 4, 1 + p; 1 - k, 1 + p, 4] : Mat3) := by
    rw [frozenInnerCovariance, ← add_assoc, covariance_total p k hp₂]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.one_apply]
  have H : matrixChainCovariance (frozenSchedule β a p h k) =
      (β ^ 2 * h) • (fun i j => (q0 p k + q1 p k + frozenInnerCovariance p k) i j) := by
    rw [frozenSchedule_eq_window_one β a p s h k]
    ext i j
    have hs := congrFun (congrFun (covariance_scaled (OW.window (fun _ => a) p s h k 1) β) i) j
    have hw := congrFun (congrFun (window_covariance (fun _ => a) p s h k (N := 1) (by decide) hh hp hl) i) j
    change matrixChainCovariance ((OW.window (fun _ => a) p s h k 1).map (fun u => (u.1, β • u.2))) i j =
      β ^ 2 * matrixChainCovariance (OW.window (fun _ => a) p s h k 1) i j at hs
    change matrixChainCovariance (OW.window (fun _ => a) p s h k 1) i j =
      h * (!![4, 1 + k, 1 - k; 1 + k, 4, 1 + p; 1 - k, 1 + p, 4] : Mat3) i j at hw
    change _ = (β ^ 2 * h) * (q0 p k + q1 p k + frozenInnerCovariance p k) i j
    rw [hs, hw, he]
    ring
  rw [frozenSchedule, matrixChainCovariance_append, matrixChainCovariance_append,
    frozenCommon_covariance β a p h k hh, frozenShared_covariance β a p h k hh hp.1] at H
  ext i j
  have Hij := congrFun (congrFun H i) j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.add_apply] at Hij ⊢
  linarith only [Hij]

theorem frozenSchedule_covariance (β a p h k : ℝ) (hh : 0 ≤ h)
    (hp : p ∈ Icc (0 : ℝ) 1) (hl : OW.repairLength p k ∈ Icc (0 : ℝ) 2) :
    matrixChainCovariance (frozenSchedule β a p h k) = (β ^ 2 * h) •
      (fun i j => (!![4, 1 + k, 1 - k; 1 + k, 4, 1 + p; 1 - k, 1 + p, 4] : Mat3) i j) := by
  rw [frozenSchedule, matrixChainCovariance_append, matrixChainCovariance_append,
    frozenCommon_covariance β a p h k hh, frozenShared_covariance β a p h k hh hp.1,
    frozenInner_covariance β a p 0 h k hh hp hl]
  have he := covariance_total p k (by linarith [hp.2] : p ≠ 2)
  ext i j
  have hij := congrFun (congrFun he i) j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, frozenInnerCovariance, Matrix.add_apply,
    Matrix.smul_apply] at hij ⊢
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.one_apply] at hij ⊢ <;>
    linear_combination (β ^ 2 * h) * hij

theorem frozen_window_merge (β a p s h k : ℝ) {N : ℕ} (hN : 0 < N)
    (hh : 0 ≤ h) (hp : p ∈ Icc (0 : ℝ) 1)
    (hl : OW.repairLength p k ∈ Icc (0 : ℝ) 2)
    {f : Vec3 → ℝ} (hf : BoundedDerivs f) :
    vectorIncrementChain ((OW.window (fun _ => a) p s h k N).map (fun u => (u.1, β • u.2))) f =
      vectorIncrementChain (frozenSchedule β a p h k) f := by
  have hL : 0 ≤ h * (4 * varianceCoefficient p) := by
    unfold varianceCoefficient
    have ht : 0 ≤ (3 : ℝ) - p := by linarith [hp.2]
    positivity
  have h₀ := grid_merge β a s h 0 1 3 hN [commonVector p k] (by simpa using hh)
  have h₁ := grid_merge β a s h 1 p 2 hN [sharedVector p k] (mul_nonneg hh hp.1)
  have h₂ := grid_merge β a s h 1 p 1 hN [rampVector p k] (mul_nonneg hh hp.1)
  have h₃ := grid_merge β a s h (1 + p) (1 - p) 1 hN
    [rampVector p k, postXVector p k, postYVector p k] (mul_nonneg hh (sub_nonneg.mpr hp.2))
  have h₄ := repair_merge β a p s h k hN
    [rampVector p 0, (1 / Real.sqrt 2) • sharedVector p 0, (1 / 2 : ℝ) • contrast] hL
  have h₅ := grid_merge β a s h (2 + OW.repairLength p k) (2 - OW.repairLength p k) 1 hN
    [Pi.single 0 1, Pi.single 1 1, Pi.single 2 1] (mul_nonneg hh (sub_nonneg.mpr hl.2))
  have H := ((((h₀.append h₁).append h₂).append h₃).append h₄).append h₅
  rw [OW.window_eq]
  simp only [List.map_append]
  convert H f hf using 1
  simp [frozenSchedule, frozenCommon, frozenShared, frozenInner]

def frozenTerminal (β : ℝ) (α : ℝ → ℝ) (s h : ℝ) : Vec3 → ℝ :=
  fun x => ∑ i, Phi β α (s + 4 * h) (x i)

def frozenBoundary (β : ℝ) (α : ℝ → ℝ) (a p s h k : ℝ) (N : ℕ) (z : ℝ) : ℝ :=
  vectorIncrementChain ((OW.window (fun _ => a) p s h k N).map (fun u => (u.1, β • u.2)))
    (frozenTerminal β α s h) (fun _ => z)

theorem frozenBoundary_eq_lambda_zero (β : ℝ) (α : ℝ → ℝ) (a p s h k : ℝ) (N : ℕ) (z : ℝ) :
    frozenBoundary β α a p s h k N z =
      vectorIncrementChain ((OW.window (interpolatedProfile α a 0) p s h k N).map
        (fun u => (u.1, β • u.2))) (frozenTerminal β α s h) (fun _ => z) := by
  have hprofile : interpolatedProfile α a 0 = fun _ => a := by
    funext t
    simp only [interpolatedProfile, zero_mul, add_zero]
  rw [hprofile]
  rfl

theorem frozenTerminal_regular (β : ℝ) (α : ℝ → ℝ) (s h : ℝ)
    (hΦ : BoundedDerivs (Phi β α (s + 4 * h))) : BoundedDerivs (frozenTerminal β α s h) := by
  unfold frozenTerminal
  simpa [Fin.sum_univ_succ, add_assoc] using
    ((hΦ.compCLM (tripleCoordinate 0)).add (hΦ.compCLM (tripleCoordinate 1))).add
      (hΦ.compCLM (tripleCoordinate 2))

theorem frozenTerminal_swap (β : ℝ) (α : ℝ → ℝ) (s h : ℝ) :
    frozenTerminal β α s h ∘ OW.swap23 = frozenTerminal β α s h := by
  funext x
  simp [frozenTerminal, OW.swap23_apply, Fin.sum_univ_succ]
  ring

theorem frozenBoundary_even (β : ℝ) (α : ℝ → ℝ) (a p s h k : ℝ) (N : ℕ)
    (hΦ : BoundedDerivs (Phi β α (s + 4 * h))) (z : ℝ) :
    frozenBoundary β α a p s h (-k) N z = frozenBoundary β α a p s h k N z := by
  exact OW.window_chain_even β (fun _ => a) p s h k N
    (frozenTerminal_regular β α s h hΦ) (frozenTerminal_swap β α s h) z

def frozenDifference (β : ℝ) (α : ℝ → ℝ) (a s h k z : ℝ) : ℝ :=
  vectorIncrementChain (frozenSchedule β a (1 / 2) h k) (frozenTerminal β α s h) (fun _ => z) -
    vectorIncrementChain (frozenSchedule β a (1 / 2) h 0) (frozenTerminal β α s h) (fun _ => z)

theorem frozenDifference_zero (β : ℝ) (α : ℝ → ℝ) (a s h z : ℝ) :
    frozenDifference β α a s h 0 z = 0 := by
  exact sub_self _

theorem frozenDifference_even (β : ℝ) (α : ℝ → ℝ) (a s h k z : ℝ)
    (hΦ : BoundedDerivs (Phi β α (s + 4 * h))) :
    frozenDifference β α a s h (-k) z = frozenDifference β α a s h k z := by
  unfold frozenDifference
  rw [frozenSchedule_eq_window_one β a (1 / 2) s h (-k),
    frozenSchedule_eq_window_one β a (1 / 2) s h k]
  exact congrArg (fun t => t - vectorIncrementChain (frozenSchedule β a (1 / 2) h 0)
    (frozenTerminal β α s h) (fun _ => z)) (frozenBoundary_even β α a (1 / 2) s h k 1 hΦ z)

theorem frozen_boundary_merge (β : ℝ) (α : ℝ → ℝ) (a s h k : ℝ) {N : ℕ} (hN : 0 < N)
    (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2) (hΦ : BoundedDerivs (Phi β α (s + 4 * h))) (z : ℝ) :
    frozenBoundary β α a (1 / 2) s h k N z =
      vectorIncrementChain (frozenCommon β a (1 / 2) h k)
        (vectorIncrementChain (frozenShared β a (1 / 2) h k)
          (vectorIncrementChain (frozenInner β a (1 / 2) h k) (frozenTerminal β α s h))) (fun _ => z) := by
  unfold frozenBoundary
  rw [frozen_window_merge β a (1 / 2) s h k hN hh (by norm_num)
    (OW.repairLength_mem (by norm_num) hk) (frozenTerminal_regular β α s h hΦ),
    frozenSchedule, vectorIncrementChain_append, vectorIncrementChain_append]

theorem frozenDifference_eq_boundary_sub (β : ℝ) (α : ℝ → ℝ) (a s h k z : ℝ)
    {N : ℕ} (hN : 0 < N) (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2)
    (hΦ : BoundedDerivs (Phi β α (s + 4 * h))) :
    frozenDifference β α a s h k z =
      frozenBoundary β α a (1 / 2) s h k N z - frozenBoundary β α a (1 / 2) s h 0 N z := by
  unfold frozenDifference frozenBoundary
  rw [frozen_window_merge β a (1 / 2) s h k hN hh (by norm_num)
      (OW.repairLength_mem (by norm_num) hk) (frozenTerminal_regular β α s h hΦ),
    frozen_window_merge β a (1 / 2) s h 0 hN hh (by norm_num)
      (by norm_num [OW.repairLength]) (frozenTerminal_regular β α s h hΦ)]

end SKBarriers2.Corner
