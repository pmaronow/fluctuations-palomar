module
public import SKConstants.ScalarProcessCharacteristic
public import SKConstants.BrownianGaussianHistory
public import SKConstants.ScalarProcessSampledHistory
public import Mathlib.Tactic

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
set_option backward.isDefEq.respectTransparency false
namespace SKConstants

@[expose] def scalarHistoryTruncate : (N m : ℕ) → (m ≤ N) →
    ScalarObservationHistory N → ScalarObservationHistory m := by
  intro N
  induction N with
  | zero =>
    intro m hm H
    have he : m = 0 := Nat.eq_zero_of_le_zero hm
    subst m
    exact H
  | succ N ih =>
    intro m hm H
    by_cases hmN : m ≤ N
    · exact ih m hmN H.1
    · have he : m = N + 1 := by omega
      subst m
      exact H

lemma scalarHistoryTruncate_self (N : ℕ) (H : ScalarObservationHistory N) :
    scalarHistoryTruncate N N (le_refl N) H = H := by
  cases N with
  | zero => rfl
  | succ N => simp [scalarHistoryTruncate, Nat.recAux]

lemma scalarHistoryTruncate_succ (N m : ℕ) (hm : m ≤ N)
    (H : ScalarObservationHistory (N + 1)) :
    scalarHistoryTruncate (N + 1) m (by omega) H = scalarHistoryTruncate N m hm H.1 := by
  simp [scalarHistoryTruncate, Nat.recAux, hm]

lemma measurable_scalarHistoryTruncate (N m : ℕ) (hm : m ≤ N) :
    Measurable (scalarHistoryTruncate N m hm) := by
  induction N with
  | zero =>
    have he : m = 0 := Nat.eq_zero_of_le_zero hm
    subst m
    exact measurable_id
  | succ N ih =>
    by_cases hmN : m ≤ N
    · have he : scalarHistoryTruncate (N + 1) m hm =
          fun H => scalarHistoryTruncate N m hmN H.1 := by
        funext H
        exact scalarHistoryTruncate_succ N m hmN H
      rw [he]
      exact (ih hmN).comp measurable_fst
    · have he : m = N + 1 := by omega
      subst m
      have hfun : scalarHistoryTruncate (N + 1) (N + 1) hm = id := by
        funext H
        exact scalarHistoryTruncate_self (N + 1) H
      rw [hfun]
      exact measurable_id

@[expose] def scalarHistoryInnovationPrefixSum (z : ℝ) (dt : ℕ → ℝ≥0) (m : ℕ) :
    (N : ℕ) → ScalarObservationHistory N → ℝ
  | 0, _ => 0
  | N + 1, H => scalarHistoryInnovationPrefixSum z dt m N H.1 +
      if N < m then scalarInnovation (scalarLastField z N H.1) (dt N) H.2 else 0

lemma scalarHistoryInnovationPrefixSum_full (z : ℝ) (dt : ℕ → ℝ≥0)
    (N m : ℕ) (hm : N ≤ m) (H : ScalarObservationHistory N) :
    scalarHistoryInnovationPrefixSum z dt m N H = scalarHistoryInnovationSum z dt N H := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [scalarHistoryInnovationPrefixSum, scalarHistoryInnovationSum,
      ite_eq_left (show N < m by omega)]
    rw [ih (by omega)]

lemma scalarHistoryInnovationPrefixSum_eq_truncate (z : ℝ) (dt : ℕ → ℝ≥0)
    (N m : ℕ) (hm : m ≤ N) (H : ScalarObservationHistory N) :
    scalarHistoryInnovationPrefixSum z dt m N H =
      scalarHistoryInnovationSum z dt m (scalarHistoryTruncate N m hm H) := by
  induction N with
  | zero =>
    have he : m = 0 := Nat.eq_zero_of_le_zero hm
    subst m
    rfl
  | succ N ih =>
    by_cases hmN : m ≤ N
    · rw [scalarHistoryInnovationPrefixSum, ite_eq_right (show ¬ N < m by omega), add_zero,
        scalarHistoryTruncate_succ N m hmN H]
      exact ih hmN H.1
    · have he : m = N + 1 := by omega
      subst m
      rw [scalarHistoryInnovationPrefixSum_full z dt (N + 1) (N + 1) (le_refl _) H,
        scalarHistoryTruncate_self]

@[expose] def scalarPrefixCoefficient {ι : Type*} [Fintype ι]
    (theta : ι → ℝ) (ends : ι → ℕ) (k : ℕ) : ℝ :=
  ∑ i, theta i * if k < ends i then 1 else 0

lemma scalarHistoryWeightedInnovationSum_eq_prefixes {ι : Type*} [Fintype ι]
    (z : ℝ) (dt : ℕ → ℝ≥0) (theta : ι → ℝ) (ends : ι → ℕ)
    (N : ℕ) (H : ScalarObservationHistory N) :
    scalarHistoryWeightedInnovationSum z dt (scalarPrefixCoefficient theta ends) N H =
      ∑ i, theta i * scalarHistoryInnovationPrefixSum z dt (ends i) N H := by
  induction N with
  | zero => simp [scalarHistoryWeightedInnovationSum, scalarHistoryInnovationPrefixSum]
  | succ N ih =>
    simp only [scalarHistoryWeightedInnovationSum, scalarHistoryInnovationPrefixSum]
    rw [ih H.1]
    simp only [mul_add, Finset.sum_add_distrib]
    congr 1
    rw [scalarPrefixCoefficient, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hp : N < ends i <;> simp [hp]

lemma scalarHistoryWeightedInnovationSum_eq_truncated_prefixes {ι : Type*} [Fintype ι]
    (z : ℝ) (dt : ℕ → ℝ≥0) (theta : ι → ℝ) (ends : ι → ℕ)
    (N : ℕ) (hp : ∀ i, ends i ≤ N) (H : ScalarObservationHistory N) :
    scalarHistoryWeightedInnovationSum z dt (scalarPrefixCoefficient theta ends) N H =
      ∑ i, theta i * scalarHistoryInnovationSum z dt (ends i)
        (scalarHistoryTruncate N (ends i) (hp i) H) := by
  rw [scalarHistoryWeightedInnovationSum_eq_prefixes]
  apply Finset.sum_congr rfl
  intro i hi
  rw [scalarHistoryInnovationPrefixSum_eq_truncate z dt N (ends i) (hp i) H]

lemma integral_char_deterministicGaussianSum (dt : ℕ → ℝ≥0) (a : ℕ → ℝ) (N : ℕ) :
    (∫ H, Complex.exp ((adaptedGaussianSum (fun k _ => a k) N H : ℂ) * Complex.I)
      ∂gaussianHistoryLaw dt N) =
      Complex.exp (-((∑ k ∈ Finset.range N, (a k) ^ 2 * (dt k : ℝ) / 2 : ℝ) : ℂ)) := by
  induction N with
  | zero => simp [adaptedGaussianSum, gaussianHistoryLaw]
  | succ N ih =>
    change (∫ p : GaussianHistory N × ℝ,
      Complex.exp ((adaptedGaussianSum (fun k _ => a k) (N + 1) p : ℂ) * Complex.I)
      ∂(gaussianHistoryLaw dt N).prod (gaussianReal 0 (dt N))) = _
    have he : (fun p : GaussianHistory N × ℝ =>
        Complex.exp ((adaptedGaussianSum (fun k _ => a k) (N + 1) p : ℂ) * Complex.I)) =
        fun p => Complex.exp ((adaptedGaussianSum (fun k _ => a k) N p.1 : ℂ) * Complex.I) *
          Complex.exp (((a N * p.2 : ℝ) : ℂ) * Complex.I) := by
      funext p
      simp only [adaptedGaussianSum, Complex.ofReal_add, add_mul, Complex.exp_add]
    rw [he, integral_prod_mul
      (fun H : GaussianHistory N =>
        Complex.exp ((adaptedGaussianSum (fun k _ => a k) N H : ℂ) * Complex.I))
      (fun y : ℝ => Complex.exp (((a N * y : ℝ) : ℂ) * Complex.I)), ih]
    have hg : (∫ y : ℝ, Complex.exp (((a N * y : ℝ) : ℂ) * Complex.I)
        ∂gaussianReal 0 (dt N)) =
        Complex.exp (-(((dt N : ℝ) * (a N) ^ 2 / 2 : ℝ) : ℂ)) := by
      simpa only [sub_zero, sub_self, mul_zero, Complex.ofReal_zero, zero_mul, zero_sub] using
        gaussianReal_integral_char_shift 0 0 (a N) (dt N)
    rw [hg, ← Complex.exp_add, Finset.sum_range_succ]
    congr 1
    push_cast
    ring

lemma adaptedGaussianSum_deterministic_sequence (a xi : ℕ → ℝ) (N : ℕ) :
    adaptedGaussianSum (fun k _ => a k) N (gaussianHistoryOfSequence xi N) =
      ∑ k ∈ Finset.range N, a k * xi k := by
  induction N with
  | zero => simp [adaptedGaussianSum]
  | succ N ih =>
    change adaptedGaussianSum (fun k _ => a k) N (gaussianHistoryOfSequence xi N) +
      a N * xi N = _
    rw [ih, Finset.sum_range_succ]

lemma integral_char_brownianDeterministicWeightedSum {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (a : ℕ → ℝ) (N : ℕ) :
    (∫ ω, Complex.exp ((∑ k ∈ Finset.range N,
      a k * brownianMeshIncrement B t k ω : ℝ) * Complex.I) ∂P) =
      Complex.exp (-((∑ k ∈ Finset.range N,
        (a k) ^ 2 * (brownianMeshVariance t k : ℝ) / 2 : ℝ) : ℂ)) := by
  have hLaw := brownianGaussianHistory_hasLaw hB t ht N
  have hm : Measurable (adaptedGaussianSum (fun k _ => a k) N) :=
    measurable_adaptedGaussianSum _ (fun k => measurable_const) N
  have h := hLaw.integral_comp
    (f := fun H => Complex.exp ((adaptedGaussianSum (fun k _ => a k) N H : ℂ) * Complex.I))
    (by fun_prop)
  simp only [Function.comp_def, brownianGaussianHistory,
    adaptedGaussianSum_deterministic_sequence] at h
  rw [h, integral_char_deterministicGaussianSum]

lemma scalarPrefixCoefficient_abs_le {ι : Type*} [Fintype ι]
    (theta : ι → ℝ) (ends : ι → ℕ) (k : ℕ) :
    |scalarPrefixCoefficient theta ends k| ≤ ∑ i, |theta i| := by
  unfold scalarPrefixCoefficient
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  by_cases hk : k < ends i <;> simp [hk]

lemma scalarPrefixCoefficient_energy_le {ι : Type*} [Fintype ι]
    (theta : ι → ℝ) (ends : ι → ℕ) (dt : ℕ → ℝ≥0) (N : ℕ) :
    (∑ k ∈ Finset.range N, (scalarPrefixCoefficient theta ends k) ^ 2 * (dt k : ℝ)) ≤
      (∑ i, |theta i|) ^ 2 * ∑ k ∈ Finset.range N, (dt k : ℝ) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  apply mul_le_mul_of_nonneg_right _ (dt k).property
  have h := scalarPrefixCoefficient_abs_le theta ends k
  have hA : 0 ≤ ∑ i, |theta i| := Finset.sum_nonneg (fun i hi => abs_nonneg _)
  nlinarith [sq_abs (scalarPrefixCoefficient theta ends k),
    abs_nonneg (scalarPrefixCoefficient theta ends k)]

lemma sum_scalarPrefixCoefficient_mul {ι : Type*} [Fintype ι]
    (theta : ι → ℝ) (ends : ι → ℕ) (xi : ℕ → ℝ) (N : ℕ) (hp : ∀ i, ends i ≤ N) :
    (∑ k ∈ Finset.range N, scalarPrefixCoefficient theta ends k * xi k) =
      ∑ i, theta i * ∑ k ∈ Finset.range (ends i), xi k := by
  simp only [scalarPrefixCoefficient, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have hfilter : (Finset.range N).filter (fun k => k < ends i) = Finset.range (ends i) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    have hN := hp i
    omega
  calc
    _ = theta i * (∑ k ∈ Finset.range N, if k < ends i then xi k else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      by_cases he : k < ends i <;> simp [he]
    _ = _ := by rw [← Finset.sum_filter, hfilter]

lemma sum_scalarPrefixCoefficient_brownianMeshIncrement {ι Ω : Type*} [Fintype ι]
    (theta : ι → ℝ) (ends : ι → ℕ) (B : ℝ≥0 → Ω → ℝ)
    (t : ℕ → ℝ≥0) (N : ℕ) (hp : ∀ i, ends i ≤ N) (ω : Ω) :
    (∑ k ∈ Finset.range N,
      scalarPrefixCoefficient theta ends k * brownianMeshIncrement B t k ω) =
      ∑ i, theta i * (B (t (ends i)) ω - B (t 0) ω) := by
  rw [sum_scalarPrefixCoefficient_mul theta ends (fun k => brownianMeshIncrement B t k ω) N hp]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [brownianMeshIncrement]
  rw [Finset.sum_range_sub (fun k => B (t k) ω)]

lemma integral_char_brownianPrefixes {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (theta : ι → ℝ) (ends : ι → ℕ) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (N : ℕ) (hp : ∀ i, ends i ≤ N) :
    (∫ ω, Complex.exp ((∑ i, theta i * (B (t (ends i)) ω - B (t 0) ω) : ℝ) *
      Complex.I) ∂P) =
      Complex.exp (-((∑ k ∈ Finset.range N,
        (scalarPrefixCoefficient theta ends k) ^ 2 * (brownianMeshVariance t k : ℝ) / 2 : ℝ) : ℂ)) := by
  have h := integral_char_brownianDeterministicWeightedSum hB t ht
    (scalarPrefixCoefficient theta ends) N
  simpa only [sum_scalarPrefixCoefficient_brownianMeshIncrement theta ends B t N hp] using h

lemma scalarHistoryTruncate_sampled {Ω : Type*} (Y : ℕ → Ω → ℝ)
    (N m : ℕ) (hm : m ≤ N) (ω : Ω) :
    scalarHistoryTruncate N m hm (scalarSampledFieldHistory Y N ω) =
      scalarSampledFieldHistory Y m ω := by
  induction N with
  | zero =>
    have he : m = 0 := Nat.eq_zero_of_le_zero hm
    subst m
    rfl
  | succ N ih =>
    by_cases hmN : m ≤ N
    · rw [scalarHistoryTruncate_succ N m hmN]
      exact ih hmN
    · have he : m = N + 1 := by omega
      subst m
      exact scalarHistoryTruncate_self (N + 1) _

lemma scalarHistoryWeightedInnovationSum_sampled_eq_prefixes {ι Ω : Type*} [Fintype ι]
    (z : ℝ) (dt : ℕ → ℝ≥0) (theta : ι → ℝ) (ends : ι → ℕ)
    (Y : ℕ → Ω → ℝ) (N : ℕ) (hp : ∀ i, ends i ≤ N) (ω : Ω) :
    scalarHistoryWeightedInnovationSum z dt (scalarPrefixCoefficient theta ends) N
      (scalarSampledFieldHistory Y N ω) =
      ∑ i, theta i * scalarHistoryInnovationSum z dt (ends i)
        (scalarSampledFieldHistory Y (ends i) ω) := by
  rw [scalarHistoryWeightedInnovationSum_eq_truncated_prefixes z dt theta ends N hp]
  apply Finset.sum_congr rfl
  intro i hi
  rw [scalarHistoryTruncate_sampled]

end SKConstants
