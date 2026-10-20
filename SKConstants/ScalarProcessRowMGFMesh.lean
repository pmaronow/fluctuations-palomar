module
public import SKConstants.ScalarObservationSquareMGF
public import SKConstants.ScalarProcessPosteriorItoLimit
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Chebyshev

public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
set_option backward.isDefEq.respectTransparency false
namespace SKConstants

@[expose] def scalarRowMeshWeight (m : ℕ → ℕ) (a : ℕ → ℝ) (d k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range d, if m i ≤ k ∧ k < m (i+1) then a i else 0

lemma scalarRowMeshIntervals_disjoint (m : ℕ → ℕ) (hm : Monotone m) (k i j : ℕ)
    (hi : m i ≤ k ∧ k < m (i+1)) (hj : m j ≤ k ∧ k < m (j+1)) : i = j := by
  by_contra h
  rcases lt_or_gt_of_ne h with h | h
  · have := hm (show i+1 ≤ j by omega)
    omega
  · have := hm (show j+1 ≤ i by omega)
    omega

lemma scalarRowMeshWeight_sq (m : ℕ → ℕ) (hm : Monotone m) (a : ℕ → ℝ) (d k : ℕ) :
    scalarRowMeshWeight m a d k ^ 2 =
      ∑ i ∈ Finset.range d, if m i ≤ k ∧ k < m (i+1) then (a i)^2 else 0 := by
  unfold scalarRowMeshWeight
  by_cases h : ∃ i ∈ Finset.range d, m i ≤ k ∧ k < m (i+1)
  · obtain ⟨i, hid, hi⟩ := h
    have hother (j : ℕ) (hj : j ∈ Finset.range d) (hji : j ≠ i) :
        ¬ (m j ≤ k ∧ k < m (j+1)) := by
      intro hj'
      exact hji (scalarRowMeshIntervals_disjoint m hm k j i hj' hi)
    rw [Finset.sum_eq_single i, Finset.sum_eq_single i]
    · simp [hi]
    · intro j hj hji
      simp [hother j hj hji]
    · exact fun h => (h hid).elim
    · intro j hj hji
      simp [hother j hj hji]
    · exact fun h => (h hid).elim
  · have hnone : ∀ i ∈ Finset.range d, ¬ (m i ≤ k ∧ k < m (i+1)) := by
      simpa only [not_exists, not_and] using h
    simp only [Finset.sum_eq_zero (fun i hi => ite_eq_right (hnone i hi)), zero_pow (by decide : (2 : ℕ) ≠ 0)]

lemma scalarRowMesh_interval_sum {R : Type*} [AddCommMonoid R]
    (m : ℕ → ℕ) (hm : Monotone m) (d i : ℕ) (hi : i < d) (f : ℕ → R) :
    (∑ k ∈ Finset.range (m d), if m i ≤ k ∧ k < m (i+1) then f k else 0) =
      ∑ k ∈ Finset.Ico (m i) (m (i+1)), f k := by
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  exact ⟨fun h => h.2, fun h => ⟨h.2.trans_le (hm (by omega)), h⟩⟩

lemma scalarRowMeshWeight_energy (m : ℕ → ℕ) (hm : Monotone m) (a : ℕ → ℝ) (d : ℕ) :
    (∑ k ∈ Finset.range (m d), scalarRowMeshWeight m a d k ^ 2) =
      ∑ i ∈ Finset.range d, (a i)^2 * ((m (i+1) - m i : ℕ) : ℝ) := by
  simp_rw [scalarRowMeshWeight_sq m hm a]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [scalarRowMesh_interval_sum m hm d i (Finset.mem_range.mp hi)]
  simp [mul_comm]

lemma scalarRowMeshWeight_sum (m : ℕ → ℕ) (hm : Monotone m) (a f : ℕ → ℝ) (d : ℕ) :
    (∑ k ∈ Finset.range (m d), scalarRowMeshWeight m a d k * f k) =
      ∑ i ∈ Finset.range d, a i *
        ((∑ k ∈ Finset.range (m (i+1)), f k) - (∑ k ∈ Finset.range (m i), f k)) := by
  unfold scalarRowMeshWeight
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp_rw [ite_mul, zero_mul]
  rw [scalarRowMesh_interval_sum m hm d i (Finset.mem_range.mp hi)]
  rw [← Finset.mul_sum]
  congr 1
  exact Finset.sum_Ico_eq_sub _ (hm (Nat.le_succ i))

@[expose] def scalarRowPosteriorCoefficient (n : ℕ) (m : ℕ → ℕ) (a : ℕ → ℝ)
    (d : ℕ) : ScalarObservationPredictableCoefficient (scalarUniformTime n) :=
  fun k w => scalarRowMeshWeight m a d k *
    scalarDefect (w ⟨scalarUniformTime n k, Set.mem_Iic.mpr le_rfl⟩)

lemma measurable_scalarRowPosteriorCoefficient (n : ℕ) (m : ℕ → ℕ) (a : ℕ → ℝ)
    (d k : ℕ) : Measurable (scalarRowPosteriorCoefficient n m a d k) :=
  (measurable_scalarDefect.comp (measurable_pi_apply _)).const_mul _

lemma scalarRowPosteriorCoefficient_sum {Ω : Type*} (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (n : ℕ) (m : ℕ → ℕ) (hm : Monotone m)
    (a : ℕ → ℝ) (d : ℕ) (u : Bool × Ω) :
    scalarObservationPredictableSum z B (scalarUniformTime n)
      (scalarRowPosteriorCoefficient n m a d) (m d) u =
      ∑ i ∈ Finset.range d, a i *
        (scalarWeightedBrownianMeshSum scalarDefect z B n (m (i+1)) u -
          scalarWeightedBrownianMeshSum scalarDefect z B n (m i) u) := by
  rw [scalarObservationPredictableSum, predictableGaussianSum_eq_range_sum]
  simp only [scalarObservationCoefficient, scalarRowPosteriorCoefficient,
    scalarActualObservationPast, brownianMeshIncrement]
  simp_rw [mul_assoc]
  exact scalarRowMeshWeight_sum m hm a
    (fun k => scalarDefect (scalarHiddenContinuousField z B (scalarUniformTime n k) u) *
      (scalarContinuousInnovation z B (scalarUniformTime n (k+1)) u -
        scalarContinuousInnovation z B (scalarUniformTime n k) u)) d

lemma scalarRowPosteriorCoefficient_variation_le {Ω : Type*} (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (n : ℕ) (m : ℕ → ℕ) (hm : Monotone m)
    (a : ℕ → ℝ) (d : ℕ) (u : Bool × Ω) :
    scalarObservationPredictableVariation z B (scalarUniformTime n)
      (scalarRowPosteriorCoefficient n m a d) (m d) u ≤
      ∑ i ∈ Finset.range d, (a i)^2 *
        ((scalarUniformTime n (m (i+1)) : ℝ) - (scalarUniformTime n (m i) : ℝ)) := by
  rw [scalarObservationPredictableVariation, predictableGaussianVariation_eq_range_sum]
  calc
    _ ≤ ∑ k ∈ Finset.range (m d), scalarRowMeshWeight m a d k ^ 2 *
        (1 / ((n : ℝ) + 1)) := by
      apply Finset.sum_le_sum
      intro k hk
      simp only [scalarObservationCoefficient, scalarRowPosteriorCoefficient,
        scalarActualObservationPast, mul_pow, brownianMeshVariance_scalarUniformTime,
        NNReal.coe_div, NNReal.coe_one, NNReal.coe_add, NNReal.coe_natCast]
      have hsq := pow_le_pow_left₀ (scalarDefect_pos
        (scalarHiddenContinuousField z B (scalarUniformTime n k) u)).le
        (scalarDefect_le_one _) 2
      simpa using mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsq (sq_nonneg (scalarRowMeshWeight m a d k)))
        (by positivity : 0 ≤ (1 : ℝ) / ((n : ℝ) + 1))
    _ = _ := by
      rw [← Finset.sum_mul, scalarRowMeshWeight_energy m hm a, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [scalarUniformTime_coe, scalarUniformTime_coe,
        Nat.cast_sub (hm (Nat.le_succ i))]
      ring

lemma scalarRowPosteriorMesh_hasSubgaussianMGF {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (n : ℕ) (m : ℕ → ℕ) (hm : Monotone m)
    (a : ℕ → ℝ) (d : ℕ) :
    HasSubgaussianMGF
      (fun u => ∑ i ∈ Finset.range d, a i *
        (scalarWeightedBrownianMeshSum scalarDefect z B n (m (i+1)) u -
          scalarWeightedBrownianMeshSum scalarDefect z B n (m i) u))
      (∑ i ∈ Finset.range d, ‖a i‖₊ ^ 2 *
        (scalarUniformTime n (m (i+1)) - scalarUniformTime n (m i)))
      (scalarHiddenBrownianLaw z P) := by
  have h := scalarObservationPredictableSum_hasSubgaussianMGF P z B hB
    (scalarUniformTime n) (scalarUniformTime_monotone n)
    (scalarRowPosteriorCoefficient n m a d) (measurable_scalarRowPosteriorCoefficient n m a d)
    (m d) (∑ i ∈ Finset.range d, ‖a i‖₊ ^ 2 *
      (scalarUniformTime n (m (i+1)) - scalarUniformTime n (m i))) ?_
  · exact h.congr (ae_of_all _ (scalarRowPosteriorCoefficient_sum z B n m hm a d))
  · apply ae_of_all
    intro u
    convert scalarRowPosteriorCoefficient_variation_le z B n m hm a d u using 1
    push_cast
    apply Finset.sum_congr rfl
    intro i hi
    rw [NNReal.coe_sub (scalarUniformTime_monotone n (hm (Nat.le_succ i))),
      Real.norm_eq_abs, sq_abs]

lemma norm_scalarRowMeshWeight_le (m : ℕ → ℕ) (a : ℕ → ℝ) (d k : ℕ) :
    ‖scalarRowMeshWeight m a d k‖ ≤ ∑ i ∈ Finset.range d, ‖a i‖ := by
  unfold scalarRowMeshWeight
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  split_ifs <;> simp

lemma scalarRowPosteriorCoefficient_variation_eq {Ω : Type*} (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (n : ℕ) (m : ℕ → ℕ) (hm : Monotone m)
    (a : ℕ → ℝ) (d : ℕ) (u : Bool × Ω) :
    scalarObservationPredictableVariation z B (scalarUniformTime n)
      (scalarRowPosteriorCoefficient n m a d) (m d) u =
      ∑ i ∈ Finset.range d, a i ^ 2 *
        (scalarObservationPredictableVariation z B (scalarUniformTime n)
            (scalarCurrentObservationCoefficient (scalarUniformTime n) scalarDefect) (m (i+1)) u -
          scalarObservationPredictableVariation z B (scalarUniformTime n)
            (scalarCurrentObservationCoefficient (scalarUniformTime n) scalarDefect) (m i) u) := by
  simp only [scalarObservationPredictableVariation, predictableGaussianVariation_eq_range_sum,
    scalarObservationCoefficient, scalarRowPosteriorCoefficient, scalarCurrentObservationCoefficient,
    scalarActualObservationPast, mul_pow]
  simp_rw [mul_assoc, scalarRowMeshWeight_sq m hm a]
  change (∑ k ∈ Finset.range (m d),
    scalarRowMeshWeight m (fun i => a i ^ 2) d k *
      (scalarDefect (scalarHiddenContinuousField z B (scalarUniformTime n k) u) ^ 2 *
        (brownianMeshVariance (scalarUniformTime n) k : ℝ))) = _
  exact scalarRowMeshWeight_sum m hm (fun i => a i ^ 2) _ d

lemma scalarRowPosteriorMesh_secondMoment_eq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (n : ℕ) (m : ℕ → ℕ) (hm : Monotone m)
    (a : ℕ → ℝ) (d : ℕ) :
    (∫ u, (∑ i ∈ Finset.range d, a i *
        (scalarWeightedBrownianMeshSum scalarDefect z B n (m (i+1)) u -
          scalarWeightedBrownianMeshSum scalarDefect z B n (m i) u)) ^ 2
      ∂scalarHiddenBrownianLaw z P) =
      ∑ i ∈ Finset.range d, a i ^ 2 *
        ((∫ u, scalarWeightedBrownianMeshSum scalarDefect z B n (m (i+1)) u ^ 2
          ∂scalarHiddenBrownianLaw z P) -
        (∫ u, scalarWeightedBrownianMeshSum scalarDefect z B n (m i) u ^ 2
          ∂scalarHiddenBrownianLaw z P)) := by
  let H := scalarRowPosteriorCoefficient n m a d
  let G := scalarCurrentObservationCoefficient (scalarUniformTime n) scalarDefect
  have hHm : ∀ k, Measurable (H k) := measurable_scalarRowPosteriorCoefficient n m a d
  have hHbound (k : ℕ) (w) : ‖H k w‖ ≤ ∑ i ∈ Finset.range d, ‖a i‖ := by
    dsimp [H, scalarRowPosteriorCoefficient]
    rw [abs_mul]
    have hd : |scalarDefect (w ⟨scalarUniformTime n k, Set.mem_Iic.mpr le_rfl⟩)| ≤ 1 := by
      simpa only [Real.norm_eq_abs] using norm_scalarDefect_le_one
        (w ⟨scalarUniformTime n k, Set.mem_Iic.mpr le_rfl⟩)
    calc
      _ ≤ |scalarRowMeshWeight m a d k| * 1 :=
        mul_le_mul_of_nonneg_left hd (abs_nonneg _)
      _ ≤ _ := by
        simpa only [mul_one, Real.norm_eq_abs] using norm_scalarRowMeshWeight_le m a d k
  have hHs := integrable_scalarObservationCoefficient_sq_of_bounded P z B hB
    (scalarUniformTime n) H hHm (∑ i ∈ Finset.range d, ‖a i‖) hHbound
  have hi := scalarObservationPredictableSum_L2_isometry P z B hB
    (scalarUniformTime n) (scalarUniformTime_monotone n) H hHm hHs (m d)
  have hGm : ∀ k, Measurable (G k) := measurable_scalarCurrentObservationCoefficient _ _ measurable_scalarDefect
  have hGs := integrable_scalarObservationCoefficient_sq_of_bounded P z B hB
    (scalarUniformTime n) G hGm 1 (fun k w => norm_scalarDefect_le_one _)
  have hgi (j : ℕ) := scalarObservationPredictableSum_L2_isometry P z B hB
    (scalarUniformTime n) (scalarUniformTime_monotone n) G hGm hGs j
  have he (j : ℕ) : (∫ u, scalarWeightedBrownianMeshSum scalarDefect z B n j u ^ 2
      ∂scalarHiddenBrownianLaw z P) =
      ∫ u, scalarObservationPredictableVariation z B (scalarUniformTime n) G j u
        ∂scalarHiddenBrownianLaw z P := by
    simpa only [G, scalarObservationPredictableSum_current_uniform] using (hgi j).2.2
  calc
    _ = ∫ u, scalarObservationPredictableSum z B (scalarUniformTime n) H (m d) u ^ 2
        ∂scalarHiddenBrownianLaw z P := by
      apply integral_congr_ae
      exact ae_of_all _ (fun u => congrArg (fun x : ℝ => x ^ 2)
        (scalarRowPosteriorCoefficient_sum z B n m hm a d u).symm)
    _ = ∫ u, scalarObservationPredictableVariation z B (scalarUniformTime n) H (m d) u
        ∂scalarHiddenBrownianLaw z P := hi.2.2
    _ = ∫ u, ∑ i ∈ Finset.range d, a i ^ 2 *
        (scalarObservationPredictableVariation z B (scalarUniformTime n) G (m (i+1)) u -
          scalarObservationPredictableVariation z B (scalarUniformTime n) G (m i) u)
        ∂scalarHiddenBrownianLaw z P := by
      apply integral_congr_ae
      exact ae_of_all _ (scalarRowPosteriorCoefficient_variation_eq z B n m hm a d)
    _ = _ := by
      have hInt (i : ℕ) : Integrable (fun u => a i^2 *
          (scalarObservationPredictableVariation z B (scalarUniformTime n) G (m (i+1)) u -
            scalarObservationPredictableVariation z B (scalarUniformTime n) G (m i) u))
          (scalarHiddenBrownianLaw z P) := by
        simpa only [Pi.sub_apply] using
          (((hgi (m (i+1))).2.1).sub ((hgi (m i)).2.1)).const_mul (a i^2)
      rw [integral_finsetSum (Finset.range d) (fun i hi => hInt i)]
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_const_mul, integral_sub (hgi (m (i+1))).2.1 (hgi (m i)).2.1,
        ← he, ← he]

end SKConstants
