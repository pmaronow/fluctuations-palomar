module

public import PressureBridge
public import FullMassComparisonMinimum
public import SKFluctuationsOAI.Probability.SKFluctuations.CompletedFeatureKernel

@[expose] public section

namespace OAI.SKFluctuations.LaplaceWindowFormalization
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

def physicalCompletedFeature (beta : ℝ) (n : ℕ) (σ : Spin n) :
    (StandardCompletedDisorder n) →L[ℝ] ℝ :=
  ∑ i, liftedCoefficients beta n σ i • ContinuousLinearMap.proj i

@[simp] theorem physicalCompletedFeature_apply (beta : ℝ) (n : ℕ)
    (σ : Spin n) (x : StandardCompletedDisorder n) :
    physicalCompletedFeature beta n σ x = liftedHamiltonian beta n x σ := by
  simp [physicalCompletedFeature, liftedHamiltonian_eq_sum]

@[simp] theorem physicalCompletedFeature_single (beta : ℝ) (n : ℕ)
    (σ : Spin n) (i : CompletedIndex n) :
    physicalCompletedFeature beta n σ (Pi.single i 1) = liftedCoefficients beta n σ i := by
  classical
  rw [physicalCompletedFeature_apply, liftedHamiltonian_eq_sum]
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_eq_left]

theorem physicalCompletedFeature_terminal (beta : ℝ) (n : ℕ)
    (x : StandardCompletedDisorder n) :
    spinLogPartition (uniformWeight n) (physicalCompletedFeature beta n) x =
      liftedFreeEnergy beta n x := by
  unfold spinLogPartition spinPartition
  simp only [physicalCompletedFeature_apply, uniformWeight]
  rw [← Finset.mul_sum, ← exp_liftedFreeEnergy, Real.log_exp]

theorem ordered_physicalCompleted_featureLaw (beta : ℝ) (n : ℕ) (hn : 0 < n) :
    featureLaw (orderedFeature n)
        (Sum.elim (fun _ => (0 : ℝ≥0)) (fun _ => (beta ^ 2).toNNReal)) =
      featureLaw (physicalCompletedFeature beta n) (fun _ => 1) := by
  classical
  rw [ordered_completed_featureLaw n hn]
  apply Subtype.ext
  apply featureVector_law_eq
  intro σ τ
  have hsingle (ρ : Spin n) (i : FeatureIndex n) :
      finiteFeature n ρ (Pi.single i 1) = featureCoefficient n ρ i := by
    simp [finiteFeature_apply, Pi.single_apply]
  simp only [hsingle, physicalCompletedFeature_single, NNReal.coe_one, one_mul]
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, NNReal.coe_zero, zero_mul,
    Finset.sum_const_zero, zero_add, Real.coe_toNNReal _ (sq_nonneg beta), featureCoefficient]
  apply Finset.sum_congr rfl
  intro i _
  cases i <;> simp only [liftedCoefficients] <;> ring

def physicalShellPressure (n : ℕ) (T s epsilon : ℝ) : ℝ :=
  realOrderedSKPathPressure n (initialShellMatrixClock T epsilon s) (fun _ => 0) 0

theorem physicalShellPressure_eq_oneStep (n : ℕ) (hn : 0 < n)
    {T s epsilon : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (he : 0 ≤ epsilon) (heT : epsilon ≤ T) :
    physicalShellPressure n T s epsilon =
      stepDisorderPressure (uniformWeight n) (orderedFeature n)
        (fun i => (orderedAmplitude n i) ^ 2)
        (Sum.elim (fun _ => 0) (fun _ => (T - epsilon).toNNReal))
        [(s, Sum.elim (fun _ => 0) (fun _ => epsilon.toNNReal))] 0 / (n : ℝ) := by
  classical
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let q₀ : OrderedFeatureIndex n → ℝ≥0 :=
    Sum.elim (fun _ => 0) (fun _ => (T - epsilon).toNNReal)
  let L : List (GaussianStep (OrderedFeatureIndex n)) :=
    [(s, Sum.elim (fun _ => 0) (fun _ => epsilon.toNNReal))]
  let q : ℝ → OrderedFeatureIndex n → ℝ≥0 :=
    orderedPathClock n (fun u => (initialShellMatrixClock T epsilon s u).toNNReal)
      (fun _ => 0)
  have ho : OrderedSteps 0 L := by
    exact ⟨le_rfl, hs.le, hs, hs.le, hs1⟩
  have hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0 : ℝ) 1) :=
    orderedPathClock_monotone n
      (toNNReal_monotoneOn ((initialShellMatrixClock_monotone T s he).monotoneOn _))
      (fun _ _ _ _ _ => le_rfl)
  have hclock (u : ℝ) (i : OrderedFeatureIndex n) :
      stepClockFunction (fun i => (q₀ i : ℝ)) L u i = (q u i : ℝ) := by
    cases i with
    | inl i => simp [q₀, L, q, stepClockFunction, orderedPathClock]
    | inr i =>
      have hT : 0 ≤ T := he.trans heT
      by_cases hu : u < s
      · simp [q₀, L, q, stepClockFunction, orderedPathClock,
          initialShellMatrixClock, hu, not_le.mpr hu, sub_nonneg.mpr heT]
      · have hsu : s ≤ u := le_of_not_gt hu
        simp [q₀, L, q, stepClockFunction, orderedPathClock,
          initialShellMatrixClock, hu, hsu, sub_nonneg.mpr heT, he, hT]
  have hdist : stepPathClockDistance (orderedAmplitude n) q₀ L q = 0 := by
    simp [stepPathClockDistance, hclock]
  have h := stepDisorderPressure_path_comparison (uniformWeight_pos n)
    (orderedFeature n) (fun i => (orderedAmplitude n i) ^ 2) (orderedAmplitude n)
    (orderedFeature_square n) (fun i σ => (orderedFeature_abs n σ i).le)
    q₀ L ho q hq 0
  rw [hdist] at h
  have heq := sub_eq_zero.mp (abs_nonpos_iff.mp h)
  simpa only [physicalShellPressure, realOrderedSKPathPressure, orderedSKPathPressure,
    Real.toNNReal_zero] using congrArg (fun v : ℝ => v / (n : ℝ)) heq.symm

theorem physicalShellPressure_mono (n : ℕ) (hn : 0 < n)
    {T s e₁ e₂ : ℝ} (hs : 0 < s) (he₁ : 0 ≤ e₁)
    (he12 : e₁ ≤ e₂) (he₂T : e₂ ≤ T) :
    physicalShellPressure n T s e₁ ≤ physicalShellPressure n T s e₂ := by
  let d (e u : ℝ) := if u < s then e else 0
  have hb (e : ℝ) (he : 0 ≤ e) :
      MonotoneOn (fun u => T - d e u) (Icc (0 : ℝ) 1) :=
    (initialShellMatrixClock_monotone T s he).monotoneOn _
  have h := pathCompensatedPressure_mono n hn (fun _ => T) (fun _ => 0)
    (d e₁) (d e₂) (fun _ => 0)
    (fun u _ => by dsimp [d]; split_ifs; exact he12; exact le_rfl)
    (hb e₁ he₁) (by intro u hu v hv huv; simp)
    (hb e₂ (he₁.trans he12)) (by intro u hu v hv huv; simp)
    (by simp [d, hs]; linarith) (by simp)
    (by simp [d, hs]; linarith) (by simp)
    (by simp; exact fun _ _ _ _ _ => le_rfl)
    (by simp; exact fun _ _ _ _ _ => le_rfl) 0
  unfold physicalShellPressure initialShellMatrixClock
  simpa [pathCompensatedPressure, d] using h

theorem initialShellMatrixClock_l1 {T s e₁ e₂ : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (he12 : e₁ ≤ e₂) :
    (∫ u in (0 : ℝ)..1,
      |initialShellMatrixClock T e₁ s u - initialShellMatrixClock T e₂ s u|) =
      s * (e₂ - e₁) := by
  have heq : (∫ u in (0 : ℝ)..1,
      |initialShellMatrixClock T e₁ s u - initialShellMatrixClock T e₂ s u|) =
      ∫ u in (0 : ℝ)..1, (Iic s).indicator (fun _ : ℝ => e₂ - e₁) u := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne s] with u hu hui
    by_cases hus : u < s
    · simp [initialShellMatrixClock, hus, hus.le,
        show T - e₁ - (T - e₂) = e₂ - e₁ by ring,
        abs_of_nonneg (sub_nonneg.mpr he12)]
    · have hsu : s < u := lt_of_le_of_ne (le_of_not_gt hus) (Ne.symm hu)
      simp [initialShellMatrixClock, hus, not_le.mpr hsu]
  rw [heq]
  change (∫ u in (0 : ℝ)..1, {u : ℝ | u ≤ s}.indicator (fun _ => e₂ - e₁) u) = _
  rw [intervalIntegral.integral_indicator (show s ∈ Icc (0 : ℝ) 1 from ⟨hs, hs1⟩)]
  simp
  ring

theorem physicalShellPressure_interval_bound (n : ℕ) (hn : 0 < n)
    {T s e₁ e₂ : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (he₁ : 0 ≤ e₁)
    (he12 : e₁ ≤ e₂) (he₂T : e₂ ≤ T) :
    physicalShellPressure n T s e₁ ≤ physicalShellPressure n T s e₂ ∧
      physicalShellPressure n T s e₂ ≤
        physicalShellPressure n T s e₁ + s * (e₂ - e₁) / 4 := by
  refine ⟨physicalShellPressure_mono n hn hs he₁ he12 he₂T, ?_⟩
  have h := realOrderedSKPathPressure_l1_comparison n hn
    (initialShellMatrixClock T e₂ s) (fun _ => 0)
    (initialShellMatrixClock T e₁ s) (fun _ => 0)
    ((initialShellMatrixClock_monotone T s (he₁.trans he12)).monotoneOn _)
    (fun _ _ _ _ _ => le_rfl)
    ((initialShellMatrixClock_monotone T s he₁).monotoneOn _)
    (fun _ _ _ _ _ => le_rfl)
    (by simp [initialShellMatrixClock, hs]; linarith) (le_refl 0)
    (by simp [initialShellMatrixClock, hs]; linarith) (le_refl 0) 0
  simp only [sub_self, abs_zero, intervalIntegral.integral_zero, mul_zero, add_zero] at h
  have hi := initialShellMatrixClock_l1 (T := T) hs.le hs1 he12
  simp_rw [abs_sub_comm (initialShellMatrixClock T e₂ s _) _] at h
  rw [hi] at h
  change |physicalShellPressure n T s e₂ - physicalShellPressure n T s e₁| ≤ _ at h
  linarith [(le_abs_self (physicalShellPressure n T s e₂ - physicalShellPressure n T s e₁)).trans h]

theorem integral_ordered_terminal_eq_completed (beta : ℝ) (n : ℕ) (hn : 0 < n)
    (F : ℝ → ℝ) (hF : Measurable F) :
    (∫ y, F (spinLogPartition (uniformWeight n) (orderedFeature n) y)
      ∂(Measure.pi fun i : OrderedFeatureIndex n => gaussianReal 0
        (Sum.elim (fun _ => (0 : ℝ≥0)) (fun _ => (beta ^ 2).toNNReal) i))) =
    ∫ g, F (completedFreeEnergy beta n g) ∂completedLaw beta n := by
  let A : (Spin n → ℝ) → ℝ := fun y => F (hamiltonianHierarchy (uniformWeight n) [] y)
  have hA : Measurable A := hF.comp (hamiltonianHierarchy_measurable (uniformWeight n) [])
  have ho := featureLaw_integral (orderedFeature n)
    (Sum.elim (fun _ => (0 : ℝ≥0)) (fun _ => (beta ^ 2).toNNReal)) A hA
  have hp := featureLaw_integral (physicalCompletedFeature beta n) (fun _ => 1) A hA
  rw [ordered_physicalCompleted_featureLaw beta n hn] at ho
  have ht (y : OrderedFeatureIndex n → ℝ) :
      A (featureVector (orderedFeature n) y) =
        F (spinLogPartition (uniformWeight n) (orderedFeature n) y) := by
    dsimp only [A]
    exact congrArg F (by
      simpa only [featureSteps, List.map_nil, gaussianHierarchy] using
        (gaussianHierarchy_featureLaw (uniformWeight n) (orderedFeature n) [] y).symm)
  have ht' (x : StandardCompletedDisorder n) :
      A (featureVector (physicalCompletedFeature beta n) x) = F (liftedFreeEnergy beta n x) := by
    dsimp only [A]
    apply congrArg F
    calc
      _ = spinLogPartition (uniformWeight n) (physicalCompletedFeature beta n) x := by
        simpa only [featureSteps, List.map_nil, gaussianHierarchy] using
          (gaussianHierarchy_featureLaw (uniformWeight n) (physicalCompletedFeature beta n) [] x).symm
      _ = _ := physicalCompletedFeature_terminal beta n x
  simp_rw [ht] at ho
  simp_rw [ht'] at hp
  calc
    _ = ∫ x, F (liftedFreeEnergy beta n x) ∂standardCompletedLaw n := ho.symm.trans hp
    _ = ∫ g, F (completedFreeEnergy beta n g) ∂completedLaw beta n := by
      have hm := measurePreserving_toCompletedDisorder beta n
      rw [← hm.map_eq]
      exact (integral_map hm.measurable.aemeasurable
        (hF.comp (continuous_freeEnergy beta n |>.measurable |>.comp
          (measurable_fst : Measurable (Prod.fst : Disorder n × ℝ → Disorder n))
          |>.add measurable_snd)).aestronglyMeasurable).symm

theorem ordered_matrix_selfCorrection (n : ℕ) (hn : 0 < n) (T : ℝ) (hT : 0 ≤ T) :
    (∑ i : OrderedFeatureIndex n,
      (((Sum.elim (fun _ => (0 : ℝ≥0)) (fun _ => T.toNNReal) i : ℝ≥0) : ℝ) *
        (orderedAmplitude n i) ^ 2)) = (n : ℝ) * T / 2 := by
  convert orderedAmplitude_sum n hn T 0 using 1
  · apply Finset.sum_congr rfl
    intro i _
    cases i <;> simp [hT]
  · ring

theorem physicalShellPressure_zero_eq_quenched (beta : ℝ) (n : ℕ) (hn : 0 < n)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    physicalShellPressure n (beta ^ 2) s 0 = quenchedPressure beta n := by
  rw [physicalShellPressure_eq_oneStep n hn hs hs1 (le_refl 0) (sq_nonneg beta)]
  have hzero : Sum.elim (fun _ : Fin n => (0 : ℝ≥0))
      (fun _ : Fin n × Fin n => (0 : ℝ).toNNReal) = (0 : OrderedFeatureIndex n → ℝ≥0) := by
    ext i; cases i <;> simp
  simp only [sub_zero, hzero, stepDisorderPressure, gaussianHierarchy,
    Pi.zero_apply, shiftedContinuation_zero_clock _ hs.ne',
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, NNReal.coe_zero, add_zero]
  rw [ordered_matrix_selfCorrection n hn (beta ^ 2) (sq_nonneg beta)]
  have hm := integral_ordered_terminal_eq_completed beta n hn id measurable_id
  simp only [id_eq] at hm
  change ((∫ y, spinLogPartition (uniformWeight n) (orderedFeature n) (0 + y)
    ∂(Measure.pi fun i : OrderedFeatureIndex n => gaussianReal 0
      (Sum.elim (fun _ => 0) (fun _ => (beta ^ 2).toNNReal) i))) -
    (1 / 2 : ℝ) * ((n : ℝ) * beta ^ 2 / 2)) / (n : ℝ) = _
  simp only [zero_add]
  rw [hm, mean_completedFreeEnergy]
  unfold quenchedPressure
  have hn0 : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  field_simp
  ring

theorem physicalShellPressure_full_eq_positiveMass (beta : ℝ) (n : ℕ) (hn : 0 < n)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    physicalShellPressure n (beta ^ 2) s (beta ^ 2) = positiveMassPressure beta s n := by
  rw [physicalShellPressure_eq_oneStep n hn hs hs1 (sq_nonneg beta) le_rfl]
  have hzero : Sum.elim (fun _ : Fin n => (0 : ℝ≥0))
      (fun _ : Fin n × Fin n => (0 : ℝ).toNNReal) = (0 : OrderedFeatureIndex n → ℝ≥0) := by
    ext i; cases i <;> simp
  simp only [sub_self, hzero, stepDisorderPressure, Pi.zero_apply, isotropicGaussian_zero,
    zeroContinuation, integral_dirac, zero_add, gaussianHierarchy,
    shiftedContinuation, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, NNReal.coe_zero, zero_add, add_zero]
  rw [ordered_matrix_selfCorrection n hn (beta ^ 2) (sq_nonneg beta)]
  rw [integral_ordered_terminal_eq_completed beta n hn (fun z => Real.exp (s * z)) (by fun_prop)]
  unfold positiveMassPressure
  change (Real.log (mgf (completedFreeEnergy beta n) (completedLaw beta n) s) / s -
      (1 / 2 : ℝ) * ((n : ℝ) * beta ^ 2 / 2)) / (n : ℝ) = _
  have hn0 : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  field_simp [hn0, hs.ne']
  ring

theorem completedCenteredLogLaplace_eq_physicalShell_gap (beta : ℝ) (n : ℕ) (hn : 0 < n)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    completedCenteredLogLaplace beta s n = (n : ℝ) * s *
      (physicalShellPressure n (beta ^ 2) s (beta ^ 2) -
        physicalShellPressure n (beta ^ 2) s 0) := by
  rw [physicalShellPressure_full_eq_positiveMass beta n hn hs hs1,
    physicalShellPressure_zero_eq_quenched beta n hn hs hs1]
  exact completedCenteredLogLaplace_eq_pressure_gap beta s hn hs.ne'

theorem laplaceScale_le_one {m : ℝ} (hm : m < 1 / 300) (n : ℕ) (hn : 0 < n) :
    laplaceScale m n ≤ 1 := by
  unfold laplaceScale
  exact Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast hn) (by linarith)

theorem pressureIncrement_eq_physicalShell_gap (beta : ℝ) {m : ℝ}
    (hm : m < 1 / 300) (n : ℕ) (hn : 0 < n) :
    pressureIncrement beta m n =
      physicalShellPressure n (beta ^ 2) (laplaceScale m n) (beta ^ 2) -
        physicalShellPressure n (beta ^ 2) (laplaceScale m n) 0 := by
  rw [physicalShellPressure_full_eq_positiveMass beta n hn (laplaceScale_pos m hn)
      (laplaceScale_le_one hm n hn),
    physicalShellPressure_zero_eq_quenched beta n hn (laplaceScale_pos m hn)
      (laplaceScale_le_one hm n hn)]
  rfl

end
end OAI.SKFluctuations.LaplaceWindowFormalization
