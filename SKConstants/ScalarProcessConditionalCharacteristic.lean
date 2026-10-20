module
public import SKConstants.ScalarProcessInnovationPrefixes
public import Mathlib.Tactic

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
set_option backward.isDefEq.respectTransparency false
namespace SKConstants

@[expose] def scalarFutureCoefficient (a : ℕ → ℝ) (m k : ℕ) : ℝ :=
  if m ≤ k then a k else 0

lemma scalarHistoryFutureInnovationSum_zero (z : ℝ) (dt : ℕ → ℝ≥0) (a : ℕ → ℝ)
    (m N : ℕ) (hNm : N ≤ m) (H : ScalarObservationHistory N) :
    scalarHistoryWeightedInnovationSum z dt (scalarFutureCoefficient a m) N H = 0 := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [scalarHistoryWeightedInnovationSum, scalarFutureCoefficient,
      ite_eq_right (show ¬m ≤ N by omega), zero_mul, add_zero]
    exact ih (by omega) H.1

@[expose] def scalarHistoryConditionalInnovationChar (z : ℝ) (dt : ℕ → ℝ≥0)
    (a : ℕ → ℝ) (m N : ℕ) (hmN : m ≤ N) (Phi : ScalarObservationHistory m → ℂ) : ℂ :=
  ∫ H, Phi (scalarHistoryTruncate N m hmN H) *
    Complex.exp ((scalarHistoryWeightedInnovationSum z dt (scalarFutureCoefficient a m) N H : ℂ) *
      Complex.I) ∂scalarObservationHistoryLaw z dt N

lemma integrable_scalarHistoryConditionalChar (z : ℝ) (dt : ℕ → ℝ≥0)
    (a : ℕ → ℝ) (m N : ℕ) (hmN : m ≤ N) (Phi : ScalarObservationHistory m → ℂ)
    (hPhi : Measurable Phi) (C : ℝ) (hbound : ∀ H, ‖Phi H‖ ≤ C) :
    Integrable (fun H => Phi (scalarHistoryTruncate N m hmN H) *
      Complex.exp ((scalarHistoryWeightedInnovationSum z dt (scalarFutureCoefficient a m) N H : ℂ) *
        Complex.I)) (scalarObservationHistoryLaw z dt N) := by
  have hm := hPhi.comp (measurable_scalarHistoryTruncate N m hmN)
  apply Integrable.of_bound (hm.mul (by fun_prop)).aestronglyMeasurable C
  apply ae_of_all
  intro H
  change ‖Phi (scalarHistoryTruncate N m hmN H) *
    Complex.exp ((scalarHistoryWeightedInnovationSum z dt (scalarFutureCoefficient a m) N H : ℂ) *
      Complex.I)‖ ≤ C
  simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  exact hbound _

lemma scalarHistoryConditionalInnovationChar_succ (z : ℝ) (dt : ℕ → ℝ≥0)
    (a : ℕ → ℝ) (m N : ℕ) (hmN : m ≤ N) (Phi : ScalarObservationHistory m → ℂ)
    (hPhi : Measurable Phi) (C : ℝ) (hbound : ∀ H, ‖Phi H‖ ≤ C) :
    scalarHistoryConditionalInnovationChar z dt a m (N + 1) (by omega) Phi =
      ∫ H, (Phi (scalarHistoryTruncate N m hmN H) *
        Complex.exp ((scalarHistoryWeightedInnovationSum z dt (scalarFutureCoefficient a m) N H : ℂ) *
          Complex.I)) * scalarInnovationChar (scalarLastField z N H) (dt N) (a N)
            ∂scalarObservationHistoryLaw z dt N := by
  unfold scalarHistoryConditionalInnovationChar
  change (∫ p : ScalarObservationHistory N × ℝ,
    Phi (scalarHistoryTruncate (N + 1) m (by omega) p) *
      Complex.exp ((scalarHistoryWeightedInnovationSum z dt (scalarFutureCoefficient a m)
        (N + 1) p : ℂ) * Complex.I)
      ∂scalarObservationHistoryLaw z dt N ⊗ₘ scalarObservationStepKernel z (dt N) N) = _
  rw [Measure.integral_compProd
    (integrable_scalarHistoryConditionalChar z dt a m (N + 1) (by omega) Phi hPhi C hbound)]
  congr 1
  funext H
  have he : (fun y => Phi (scalarHistoryTruncate (N + 1) m (by omega) (H, y)) *
      Complex.exp ((scalarHistoryWeightedInnovationSum z dt (scalarFutureCoefficient a m)
        (N + 1) (H, y) : ℂ) * Complex.I)) =
      fun y => (Phi (scalarHistoryTruncate N m hmN H) *
        Complex.exp ((scalarHistoryWeightedInnovationSum z dt (scalarFutureCoefficient a m) N H : ℂ) *
          Complex.I)) * Complex.exp (((a N *
            scalarInnovation (scalarLastField z N H) (dt N) y : ℝ) : ℂ) * Complex.I) := by
    funext y
    rw [scalarHistoryTruncate_succ N m hmN, scalarHistoryWeightedInnovationSum]
    simp only [scalarFutureCoefficient, ite_eq_left hmN, Complex.ofReal_add,
      add_mul, Complex.exp_add]
    ring
  rw [he, integral_const_mul]
  rfl

private lemma stronglyMeasurable_historyScalarInnovationChar
    (z : ℝ) (dt : ℕ → ℝ≥0) (a : ℕ → ℝ) (N : ℕ) :
    StronglyMeasurable (fun H : ScalarObservationHistory N =>
      scalarInnovationChar (scalarLastField z N H) (dt N) (a N)) := by
  have hJ := measurable_scalarHistoryInnovationStep z (dt N) N
  have hm : StronglyMeasurable (fun p : ScalarObservationHistory N × ℝ =>
      Complex.exp (((a N * scalarInnovation (scalarLastField z N p.1) (dt N) p.2 : ℝ) : ℂ) *
        Complex.I)) := (by fun_prop : Measurable _).stronglyMeasurable
  exact hm.integral_kernel_prod_right' (κ := scalarObservationStepKernel z (dt N) N)

lemma scalarHistoryConditionalInnovationChar_succ_error (z : ℝ) (dt : ℕ → ℝ≥0)
    (a : ℕ → ℝ) (m N : ℕ) (hmN : m ≤ N) (Phi : ScalarObservationHistory m → ℂ)
    (hPhi : Measurable Phi) (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ H, ‖Phi H‖ ≤ C) :
    ‖scalarHistoryConditionalInnovationChar z dt a m (N + 1) (by omega) Phi -
      Complex.exp (-(((dt N : ℝ) * (a N) ^ 2 / 2 : ℝ) : ℂ)) *
        scalarHistoryConditionalInnovationChar z dt a m N hmN Phi‖ ≤
      C * ((a N) ^ 2 * (dt N : ℝ) ^ 2 * Real.exp (2 * |a N| * dt N)) := by
  let E : ScalarObservationHistory N → ℂ := fun H =>
    Phi (scalarHistoryTruncate N m hmN H) *
      Complex.exp ((scalarHistoryWeightedInnovationSum z dt (scalarFutureCoefficient a m) N H : ℂ) *
        Complex.I)
  let S : ScalarObservationHistory N → ℂ := fun H =>
    scalarInnovationChar (scalarLastField z N H) (dt N) (a N)
  let G : ℂ := Complex.exp (-(((dt N : ℝ) * (a N) ^ 2 / 2 : ℝ) : ℂ))
  have hE : StronglyMeasurable E := by
    have hm := hPhi.comp (measurable_scalarHistoryTruncate N m hmN)
    dsimp [E]
    exact (hm.mul (by fun_prop)).stronglyMeasurable
  have hS : StronglyMeasurable S := stronglyMeasurable_historyScalarInnovationChar z dt a N
  have hEnorm (H : ScalarObservationHistory N) : ‖E H‖ ≤ C := by
    simp only [E, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    exact hbound _
  have hiF : Integrable (fun H => E H * S H) (scalarObservationHistoryLaw z dt N) := by
    apply Integrable.of_bound (hE.mul hS).aestronglyMeasurable C
    apply ae_of_all
    intro H
    change ‖E H * S H‖ ≤ C
    rw [norm_mul]
    exact (mul_le_mul (hEnorm H) (scalarInnovationChar_norm_le_one _ _ _)
      (norm_nonneg _) hC).trans_eq (mul_one C)
  have hiG : Integrable (fun H => G * E H) (scalarObservationHistoryLaw z dt N) :=
    (integrable_scalarHistoryConditionalChar z dt a m N hmN Phi hPhi C hbound).const_mul G
  have he : scalarHistoryConditionalInnovationChar z dt a m (N + 1) (by omega) Phi -
      G * scalarHistoryConditionalInnovationChar z dt a m N hmN Phi =
      ∫ H, E H * S H - G * E H ∂scalarObservationHistoryLaw z dt N := by
    rw [integral_sub hiF hiG, integral_const_mul,
      scalarHistoryConditionalInnovationChar_succ z dt a m N hmN Phi hPhi C hbound]
    rfl
  change ‖scalarHistoryConditionalInnovationChar z dt a m (N + 1) (by omega) Phi -
    G * scalarHistoryConditionalInnovationChar z dt a m N hmN Phi‖ ≤ _
  rw [he]
  have hb : ∀ᵐ H ∂scalarObservationHistoryLaw z dt N,
      ‖E H * S H - G * E H‖ ≤ C *
        ((a N) ^ 2 * (dt N : ℝ) ^ 2 * Real.exp (2 * |a N| * dt N)) := by
    apply ae_of_all
    intro H
    have hid : E H * S H - G * E H = E H * (S H - G) := by ring
    rw [hid, norm_mul]
    exact mul_le_mul (hEnorm H) (scalarInnovationChar_gaussian_error _ _ _)
      (norm_nonneg _) hC
  exact (norm_integral_le_of_norm_le_const hb).trans_eq (by simp)

lemma scalarHistoryConditionalInnovationChar_gaussian_error (z : ℝ) (dt : ℕ → ℝ≥0)
    (a : ℕ → ℝ) (m N : ℕ) (hmN : m ≤ N) (Phi : ScalarObservationHistory m → ℂ)
    (hPhi : Measurable Phi) (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ H, ‖Phi H‖ ≤ C) :
    ‖scalarHistoryConditionalInnovationChar z dt a m N hmN Phi -
      Complex.exp (-((∑ k ∈ Finset.Ico m N, (a k) ^ 2 * (dt k : ℝ) / 2 : ℝ) : ℂ)) *
        (∫ H, Phi H ∂scalarObservationHistoryLaw z dt m)‖ ≤
      C * ∑ k ∈ Finset.Ico m N,
        (a k) ^ 2 * (dt k : ℝ) ^ 2 * Real.exp (2 * |a k| * dt k) := by
  induction N, hmN using Nat.le_induction with
  | base =>
    have hb : scalarHistoryConditionalInnovationChar z dt a m m (le_refl m) Phi =
        ∫ H, Phi H ∂scalarObservationHistoryLaw z dt m := by
      unfold scalarHistoryConditionalInnovationChar
      congr 1
      funext H
      rw [scalarHistoryTruncate_self,
        scalarHistoryFutureInnovationSum_zero z dt a m m (le_refl m) H]
      simp
    rw [hb]
    simp
  | succ N hmN ih =>
    let G : ℂ := Complex.exp (-(((dt N : ℝ) * (a N) ^ 2 / 2 : ℝ) : ℂ))
    let H : ℂ := Complex.exp (-((∑ k ∈ Finset.Ico m N,
      (a k) ^ 2 * (dt k : ℝ) / 2 : ℝ) : ℂ))
    let mean : ℂ := ∫ H, Phi H ∂scalarObservationHistoryLaw z dt m
    have hG : ‖G‖ ≤ 1 := norm_exp_neg_ofReal_le_one _ (by positivity)
    have hnew : Complex.exp (-((∑ k ∈ Finset.Ico m (N + 1),
        (a k) ^ 2 * (dt k : ℝ) / 2 : ℝ) : ℂ)) = G * H := by
      dsimp [G, H]
      have hn : (a N) ^ 2 * (dt N : ℝ) / 2 = (dt N : ℝ) * (a N) ^ 2 / 2 := by ring
      rw [Finset.sum_Ico_succ_top hmN, hn, Complex.ofReal_add, neg_add, Complex.exp_add]
      exact mul_comm _ _
    rw [hnew, Finset.sum_Ico_succ_top hmN]
    change ‖scalarHistoryConditionalInnovationChar z dt a m (N + 1) _ Phi - (G * H) * mean‖ ≤ _
    calc
      _ = ‖(scalarHistoryConditionalInnovationChar z dt a m (N + 1) _ Phi -
          G * scalarHistoryConditionalInnovationChar z dt a m N hmN Phi) +
        G * (scalarHistoryConditionalInnovationChar z dt a m N hmN Phi - H * mean)‖ := by
        congr 1
        ring
      _ ≤ ‖scalarHistoryConditionalInnovationChar z dt a m (N + 1) _ Phi -
          G * scalarHistoryConditionalInnovationChar z dt a m N hmN Phi‖ +
        ‖G * (scalarHistoryConditionalInnovationChar z dt a m N hmN Phi - H * mean)‖ :=
        norm_add_le _ _
      _ ≤ C * ((a N) ^ 2 * (dt N : ℝ) ^ 2 * Real.exp (2 * |a N| * dt N)) +
        C * ∑ k ∈ Finset.Ico m N,
          (a k) ^ 2 * (dt k : ℝ) ^ 2 * Real.exp (2 * |a k| * dt k) := by
        apply add_le_add
          (scalarHistoryConditionalInnovationChar_succ_error z dt a m N hmN Phi hPhi C hC hbound)
        rw [norm_mul]
        exact (mul_le_mul_of_nonneg_right hG (norm_nonneg _)).trans
          (by simpa only [H, mean, one_mul] using ih)
      _ = _ := by ring

lemma scalarHistoryConditionalInnovationChar_mesh_error (z : ℝ) (dt : ℕ → ℝ≥0)
    (a : ℕ → ℝ) (m N : ℕ) (hmN : m ≤ N) (Phi : ScalarObservationHistory m → ℂ)
    (hPhi : Measurable Phi) (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ H, ‖Phi H‖ ≤ C)
    (A h : ℝ) (hA : 0 ≤ A) (hh : h ≤ 1)
    (hdt : ∀ k ∈ Finset.Ico m N, (dt k : ℝ) ≤ h)
    (ha : ∀ k ∈ Finset.Ico m N, |a k| ≤ A) :
    ‖scalarHistoryConditionalInnovationChar z dt a m N hmN Phi -
      Complex.exp (-((∑ k ∈ Finset.Ico m N, (a k) ^ 2 * (dt k : ℝ) / 2 : ℝ) : ℂ)) *
        (∫ H, Phi H ∂scalarObservationHistoryLaw z dt m)‖ ≤
      C * (Real.exp (2 * A) * h *
        ∑ k ∈ Finset.Ico m N, (a k) ^ 2 * (dt k : ℝ)) := by
  apply (scalarHistoryConditionalInnovationChar_gaussian_error z dt a m N hmN Phi
    hPhi C hC hbound).trans
  apply mul_le_mul_of_nonneg_left _ hC
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  have ht : (dt k : ℝ) ≤ h := hdt k hk
  have ht1 : (dt k : ℝ) ≤ 1 := ht.trans hh
  have hh0 : 0 ≤ h := (dt k).property.trans ht
  have hab : |a k| ≤ A := ha k hk
  have hexp : 2 * |a k| * (dt k : ℝ) ≤ 2 * A := by
    calc
      _ ≤ 2 * A * (dt k : ℝ) := by gcongr
      _ ≤ 2 * A := by nlinarith
  have hsq : (dt k : ℝ) ^ 2 ≤ h * (dt k : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_right ht (dt k).property]
  calc
    _ ≤ (a k) ^ 2 * (h * (dt k : ℝ)) * Real.exp (2 * A) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
      · exact Real.exp_le_exp.mpr hexp
      · positivity
      · positivity
    _ = _ := by ring

end SKConstants
