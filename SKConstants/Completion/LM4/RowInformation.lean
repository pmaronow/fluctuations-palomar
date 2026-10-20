module

public import SKConstants.Completion.LM4.FactorialBernstein
public import SKConstants.Completion.LM4.IntegralMoments
public import SKConstants.Completion.LM4.RowTailMoments

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

namespace SKConstants.Completion.LM4

open Concentration
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

def rowInformation (ell J Q : Ω → ℝ) (ω : Ω) : ℝ :=
  Real.log (ell ω) - J ω + Q ω / 2

theorem measurable_rowInformation {ell J Q : Ω → ℝ}
    (hell : Measurable ell) (hJ : Measurable J) (hQ : Measurable Q) :
    Measurable (rowInformation ell J Q) := (hell.log.sub hJ).add (hQ.div_const 2)

theorem rowInformation_raw_moments [IsProbabilityMeasure μ]
    {ell J Q : Ω → ℝ} (hell : Measurable ell) (hJm : Measurable J) (hQm : Measurable Q)
    (hbound : ∀ᵐ ω ∂μ, 0 ≤ ell ω ∧ ell ω ≤ 2)
    (hnorm : ∫ ω, ell ω ∂μ = 1)
    (V : ℝ≥0) (hJ : HasSubgaussianMGF J (4 * V) μ)
    (hQ : ∀ᵐ ω ∂μ, 0 ≤ Q ω ∧ Q ω ≤ 4 * (V : ℝ)) :
    (∀ p : ℕ, Integrable (fun ω => |rowInformation ell J Q ω| ^ p) (linkedRowLaw μ ell)) ∧
    (∀ p : ℕ, 2 ≤ p →
      (∫ ω, |rowInformation ell J Q ω| ^ p ∂linkedRowLaw μ ell) ≤
        (p.factorial : ℝ) * (8 * (1 + (V : ℝ))) ^ p) := by
  let ν := linkedRowLaw μ ell
  let S := 1 + (V : ℝ)
  have hS : 1 ≤ S := by dsimp [S]; linarith [V.coe_nonneg]
  have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have : IsProbabilityMeasure ν := linkedRowLaw_isProbability hell hbound hnorm
  have hL (p : ℕ) := linkedRowLaw_log_moments hell hbound hnorm p
  have hM (p : ℕ) := linkedRowLaw_integral_moments hell hJm hbound hnorm V hJ p
  have hQν : ∀ᵐ ω ∂ν, 0 ≤ Q ω ∧ Q ω ≤ 4 * (V : ℝ) :=
    (linkedRowLaw_absolutelyContinuous (μ := μ) ell).ae_le hQ
  have hQabs : ∀ᵐ ω ∂ν, |Q ω / 2| ≤ 2 * S := by
    filter_upwards [hQν] with ω hω
    rw [abs_of_nonneg (div_nonneg hω.1 (by norm_num))]
    dsimp [S]
    linarith
  have hQI (p : ℕ) : Integrable (fun ω => |Q ω / 2| ^ p) ν := by
    apply Integrable.of_bound (by fun_prop) ((2 * S) ^ p)
    filter_upwards [hQabs] with ω hω
    simpa only [Real.norm_eq_abs, abs_pow, abs_abs] using
      pow_le_pow_left₀ (abs_nonneg _) hω p
  have hQM (p : ℕ) : (∫ ω, |Q ω / 2| ^ p ∂ν) ≤ (p.factorial : ℝ) * (2 * S) ^ p := by
    have hf : 1 ≤ (p.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos p
    calc
      _ ≤ ∫ _ω, (2 * S) ^ p ∂ν := integral_mono_ae (hQI p) (integrable_const _)
        (hQabs.mono (fun _ hω => pow_le_pow_left₀ (abs_nonneg _) hω p))
      _ = (2 * S) ^ p := by simp
      _ ≤ _ := by nlinarith [pow_nonneg (by positivity : 0 ≤ 2 * S) p]
  have hI (p : ℕ) : Integrable (fun ω => |rowInformation ell J Q ω| ^ p) ν := by
    have hLM := integrable_abs_add_pow (f := fun ω => Real.log (ell ω))
      (g := fun ω => -J ω) hell.log hJm.neg p (hL p).1
      (by simpa only [abs_neg] using (hM p).1)
    simpa only [rowInformation, sub_eq_add_neg] using
      integrable_abs_add_pow (f := fun ω => Real.log (ell ω) + -J ω)
        (g := fun ω => Q ω / 2) (hell.log.add hJm.neg) (hQm.div_const 2) p hLM (hQI p)
  refine ⟨hI, fun p hp => ?_⟩
  have hLscale : (∫ ω, |Real.log (ell ω)| ^ p ∂ν) ≤
      (p.factorial : ℝ) * ((3 / 2 : ℝ) * S) ^ p := by
    have hpow : 2 ≤ ((3 / 2 : ℝ) * S) ^ p := calc
      (2 : ℝ) ≤ (3 / 2 : ℝ) ^ 2 := by norm_num
      _ ≤ (3 / 2 : ℝ) ^ p := pow_le_pow_right₀ (by norm_num) hp
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) (by nlinarith : (3 / 2 : ℝ) ≤ (3 / 2) * S) p
    have hh := mul_le_mul_of_nonneg_left hpow (show (0 : ℝ) ≤ (p.factorial : ℝ) by positivity)
    exact (hL p).2.trans (by nlinarith)
  have hJscale : (∫ ω, |-J ω| ^ p ∂ν) ≤
      (p.factorial : ℝ) * ((9 / 2 : ℝ) * S) ^ p := by
    have hpow : (5 : ℝ) ≤ (9 / 4 : ℝ) ^ p := calc
      (5 : ℝ) ≤ (9 / 4 : ℝ) ^ 2 := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) hp
    calc
      _ = ∫ ω, |J ω| ^ p ∂ν := by simp only [abs_neg]
      _ ≤ 5 * (p.factorial : ℝ) * (2 * S) ^ p := (hM p).2
      _ ≤ (p.factorial : ℝ) * ((2 * S) ^ p * (9 / 4 : ℝ) ^ p) := by
        have hh := mul_le_mul_of_nonneg_left hpow
          (show (0 : ℝ) ≤ (p.factorial : ℝ) * (2 * S) ^ p by positivity)
        nlinarith
      _ = _ := by rw [← mul_pow]; congr 2; ring
  have hLM := integral_abs_add_pow_le (f := fun ω => Real.log (ell ω)) (g := fun ω => -J ω)
    hell.log hJm.neg
    (by positivity : 0 < (3 / 2 : ℝ) * S) (by positivity : 0 < (9 / 2 : ℝ) * S)
    (hL p).1 (by simpa only [abs_neg] using (hM p).1) hLscale hJscale
  have hLMscale : (∫ ω, |Real.log (ell ω) + -J ω| ^ p ∂ν) ≤
      (p.factorial : ℝ) * (6 * S) ^ p := by
    simpa only [show (3 / 2 : ℝ) * S + (9 / 2 : ℝ) * S = 6 * S by ring] using hLM.2
  have hAll := integral_abs_add_pow_le (f := fun ω => Real.log (ell ω) + -J ω)
    (g := fun ω => Q ω / 2) (hell.log.add hJm.neg) (hQm.div_const 2)
    (by positivity : 0 < 6 * S) (by positivity : 0 < 2 * S)
    hLM.1 (hQI p) hLMscale (hQM p)
  convert hAll.2 using 1
  · simp only [rowInformation, sub_eq_add_neg]
  · congr 2
    dsimp [S]
    ring

theorem rowInformation_centered_moments [IsProbabilityMeasure μ]
    {ell J Q : Ω → ℝ} (hell : Measurable ell) (hJm : Measurable J) (hQm : Measurable Q)
    (hbound : ∀ᵐ ω ∂μ, 0 ≤ ell ω ∧ ell ω ≤ 2)
    (hnorm : ∫ ω, ell ω ∂μ = 1)
    (V : ℝ≥0) (hJ : HasSubgaussianMGF J (4 * V) μ)
    (hQ : ∀ᵐ ω ∂μ, 0 ≤ Q ω ∧ Q ω ≤ 4 * (V : ℝ)) :
    let ν := linkedRowLaw μ ell
    let X := centeredObservable ν (rowInformation ell J Q)
    (∀ p : ℕ, Integrable (fun ω => X ω ^ p) ν) ∧
    (∫ ω, X ω ∂ν = 0) ∧
    (∀ p : ℕ, 2 ≤ p → (∫ ω, |X ω| ^ p ∂ν) ≤
      (p.factorial : ℝ) * (16 * (1 + (V : ℝ))) ^ p) := by
  let ν := linkedRowLaw μ ell
  let Y := rowInformation ell J Q
  have : IsProbabilityMeasure ν := linkedRowLaw_isProbability hell hbound hnorm
  have hY : Measurable Y := measurable_rowInformation hell hJm hQm
  have hm := rowInformation_raw_moments hell hJm hQm hbound hnorm V hJ hQ
  have hI : Integrable Y ν :=
    (integrable_norm_iff hY.aestronglyMeasurable).mp (by simpa only [pow_one, Real.norm_eq_abs] using hm.1 1)
  have hX : Measurable (centeredObservable ν Y) := hY.sub_const _
  refine ⟨fun p => ?_, ?_, fun p hp => ?_⟩
  · have hc := integrable_abs_add_pow hY measurable_const p (hm.1 p)
      (integrable_const (|-∫ u, Y u ∂ν| ^ p))
    apply hc.mono' (hX.pow_const p).aestronglyMeasurable
    exact .of_forall (fun ω => by simp only [Real.norm_eq_abs, abs_pow, centeredObservable, sub_eq_add_neg, le_refl])
  · change ∫ ω, Y ω - ∫ u, Y u ∂ν ∂ν = 0
    rw [integral_sub hI (integrable_const _)]
    simp
  · have hc := integral_abs_centered_pow_le hY hI (by omega : 1 ≤ p) (hm.1 p)
    calc
      _ ≤ 2 ^ p * (∫ ω, |Y ω| ^ p ∂ν) := hc.2
      _ ≤ 2 ^ p * ((p.factorial : ℝ) * (8 * (1 + (V : ℝ))) ^ p) := by
        gcongr
        exact hm.2 p hp
      _ = _ := by rw [mul_left_comm, ← mul_pow]; congr 2; ring

theorem rowInformation_localMGF [IsProbabilityMeasure μ]
    {ell J Q : Ω → ℝ} (hell : Measurable ell) (hJm : Measurable J) (hQm : Measurable Q)
    (hbound : ∀ᵐ ω ∂μ, 0 ≤ ell ω ∧ ell ω ≤ 2)
    (hnorm : ∫ ω, ell ω ∂μ = 1)
    (V : ℝ≥0) (hJ : HasSubgaussianMGF J (4 * V) μ)
    (hQ : ∀ᵐ ω ∂μ, 0 ≤ Q ω ∧ Q ω ≤ 4 * (V : ℝ)) :
    LocalQuadraticMGF
      (centeredObservable (linkedRowLaw μ ell) (rowInformation ell J Q)) (linkedRowLaw μ ell)
      (512 * (1 + (V : ℝ)) ^ 2) (1 / (32 * (1 + (V : ℝ)))) := by
  have := linkedRowLaw_isProbability hell hbound hnorm
  have hc := rowInformation_centered_moments hell hJm hQm hbound hnorm V hJ hQ
  convert localMGF_of_centered_factorial
    (X := centeredObservable (linkedRowLaw μ ell) (rowInformation ell J Q))
    ((measurable_rowInformation hell hJm hQm).sub_const _)
    (by positivity : 0 < 16 * (1 + (V : ℝ))) hc.1 hc.2.1 hc.2.2 using 1 <;> ring

theorem iid_rowInformation_upper [IsProbabilityMeasure μ]
    {ell J Q : Ω → ℝ} (hell : Measurable ell) (hJm : Measurable J) (hQm : Measurable Q)
    (hbound : ∀ᵐ ω ∂μ, 0 ≤ ell ω ∧ ell ω ≤ 2)
    (hnorm : ∫ ω, ell ω ∂μ = 1)
    (V : ℝ≥0) (hJ : HasSubgaussianMGF J (4 * V) μ)
    (hQ : ∀ᵐ ω ∂μ, 0 ≤ Q ω ∧ Q ω ≤ 4 * (V : ℝ))
    {n : ℕ} (hn : 0 < n) {η : ℝ} (hη : 0 < η) :
    let ν := linkedRowLaw μ ell
    (Measure.pi (fun _ : Fin n => ν)).real
      {ω | (n : ℝ) * η ≤ ∑ i : Fin n,
        centeredObservable ν (rowInformation ell J Q) (ω i)} ≤
      Real.exp (-(n : ℝ) * min
        (η ^ 2 / (2048 * (1 + (V : ℝ)) ^ 2)) (η / (64 * (1 + (V : ℝ))))) := by
  have := linkedRowLaw_isProbability hell hbound hnorm
  have hRow := rowInformation_localMGF hell hJm hQm hbound hnorm V hJ hQ
  convert iid_sum_upper_of_localMGF (linkedRowLaw μ ell)
    ((measurable_rowInformation hell hJm hQm).sub_const _) hRow
    (by positivity) (by positivity) hn hη using 1 <;> congr 3 <;> field_simp <;> ring

theorem iid_rowInformation_abs [IsProbabilityMeasure μ]
    {ell J Q : Ω → ℝ} (hell : Measurable ell) (hJm : Measurable J) (hQm : Measurable Q)
    (hbound : ∀ᵐ ω ∂μ, 0 ≤ ell ω ∧ ell ω ≤ 2)
    (hnorm : ∫ ω, ell ω ∂μ = 1)
    (V : ℝ≥0) (hJ : HasSubgaussianMGF J (4 * V) μ)
    (hQ : ∀ᵐ ω ∂μ, 0 ≤ Q ω ∧ Q ω ≤ 4 * (V : ℝ))
    {n : ℕ} (hn : 0 < n) {η : ℝ} (hη : 0 < η) :
    let ν := linkedRowLaw μ ell
    (Measure.pi (fun _ : Fin n => ν)).real
      {ω | (n : ℝ) * η ≤ |∑ i : Fin n,
        centeredObservable ν (rowInformation ell J Q) (ω i)|} ≤
      2 * Real.exp (-(n : ℝ) * min
        (η ^ 2 / (2048 * (1 + (V : ℝ)) ^ 2)) (η / (64 * (1 + (V : ℝ))))) := by
  have := linkedRowLaw_isProbability hell hbound hnorm
  have hRow := rowInformation_localMGF hell hJm hQm hbound hnorm V hJ hQ
  convert iid_sum_abs_of_localMGF (linkedRowLaw μ ell)
    ((measurable_rowInformation hell hJm hQm).sub_const _) hRow
    (by positivity) (by positivity) hn hη using 1 <;> congr 4 <;> field_simp <;> ring

theorem iid_rowInformation_strict_upper [IsProbabilityMeasure μ]
    {ell J Q : Ω → ℝ} (hell : Measurable ell) (hJm : Measurable J) (hQm : Measurable Q)
    (hbound : ∀ᵐ ω ∂μ, 0 ≤ ell ω ∧ ell ω ≤ 2)
    (hnorm : ∫ ω, ell ω ∂μ = 1)
    (V : ℝ≥0) (hJ : HasSubgaussianMGF J (4 * V) μ)
    (hQ : ∀ᵐ ω ∂μ, 0 ≤ Q ω ∧ Q ω ≤ 4 * (V : ℝ))
    {n : ℕ} (hn : 0 < n) {η : ℝ} (hη : 0 < η) :
    let ν := linkedRowLaw μ ell
    (Measure.pi (fun _ : Fin n => ν)).real
      {ω | (n : ℝ) * η < ∑ i : Fin n,
        centeredObservable ν (rowInformation ell J Q) (ω i)} ≤
      Real.exp (-((n : ℝ) / 2048) *
        min (η ^ 2 / (1 + (V : ℝ)) ^ 2) (η / (1 + (V : ℝ)))) := by
  let ν := linkedRowLaw μ ell
  have := linkedRowLaw_isProbability hell hbound hnorm
  have ht := iid_rowInformation_upper hell hJm hQm hbound hnorm V hJ hQ hn hη
  apply (measureReal_mono
    (s₁ := {ω : Fin n → Ω | (n : ℝ) * η < ∑ i : Fin n,
      centeredObservable ν (rowInformation ell J Q) (ω i)})
    (s₂ := {ω : Fin n → Ω | (n : ℝ) * η ≤ ∑ i : Fin n,
      centeredObservable ν (rowInformation ell J Q) (ω i)}) (by
        intro ω h
        change (n : ℝ) * η < _ at h
        change (n : ℝ) * η ≤ _
        exact h.le)).trans
    (ht.trans ?_)
  apply Real.exp_le_exp.mpr
  let S := 1 + (V : ℝ)
  have hS : 0 < S := by dsimp [S]; positivity
  have hmin : (1 / 2048 : ℝ) * min (η ^ 2 / S ^ 2) (η / S) ≤
      min (η ^ 2 / (2048 * S ^ 2)) (η / (64 * S)) := by
    rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2048)]
    apply min_le_min
    · field_simp
      norm_num
    · have hnonneg : 0 ≤ η / S := by positivity
      nlinarith [show η / (64 * S) = (η / S) / 64 by rw [div_div, mul_comm S]]
  have hnR : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hh := mul_le_mul_of_nonneg_left hmin hnR
  dsimp [S] at hh
  nlinarith

end SKConstants.Completion.LM4
