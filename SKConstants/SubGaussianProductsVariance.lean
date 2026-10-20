module

public import SKConstants.SubGaussianProducts
public import SKConstants.SubGaussianSquaresVariance

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal ENNReal
namespace SKConstants.Concentration
set_option backward.isDefEq.respectTransparency true

lemma subGaussian_product_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (V : ℝ≥0) (hV : 0 < V) (hX : HasSubgaussianMGF X V μ)
    (hY : HasSubgaussianMGF Y V μ) (a : ℝ) (ha : 0 ≤ a) :
    μ.real {ω | a < |X ω*Y ω|} ≤ 4*Real.exp (-a/(2*(V:ℝ))) := by
  have hsub : {ω | a < |X ω*Y ω|} ⊆ {ω | a < X ω^2} ∪ {ω | a < Y ω^2} := by
    intro ω hω
    by_contra hh
    simp only [mem_union, mem_ofPred_eq, not_or, not_lt] at hh
    have hab : |X ω*Y ω| ≤ (X ω^2+Y ω^2)/2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|X ω|-|Y ω|), sq_abs (X ω), sq_abs (Y ω)]
    exact (not_lt_of_ge (hab.trans (by linarith))) hω
  have h := (measureReal_mono (μ := μ) hsub).trans (measureReal_union_le _ _)
  exact h.trans (by linarith [subGaussian_square_tail μ X V hV hX a ha,
    subGaussian_square_tail μ Y V hV hY a ha])

lemma subGaussian_product_high_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hXm : Measurable X) (hYm : Measurable Y) (V : ℝ≥0) (hV : 0 < V)
    (hX : HasSubgaussianMGF X V μ) (hY : HasSubgaussianMGF Y V μ)
    (a : ℝ) (ha : 0 ≤ a) (p : ℕ) :
    (∫ ω, {ω | a < |X ω*Y ω|}.indicator (fun ω => |X ω*Y ω|^p) ω ∂μ) ≤
      2*(p.factorial:ℝ)*(4*Real.exp 1*(V:ℝ))^p*Real.exp (-a/(4*(V:ℝ))) := by
  let F : Ω → ℝ := fun ω => |X ω*Y ω|^p
  let A := {ω | a < |X ω*Y ω|}
  have hA : MeasurableSet A := measurableSet_lt measurable_const (continuous_abs.measurable.comp (hXm.mul hYm))
  have hm := subGaussian_product_factorial_moments μ X Y V hV hX hY
  have hF2 : Integrable (fun ω => F ω^2) μ := by
    simpa only [F, ← pow_mul, show p*2=2*p by omega] using hm.1 (2*p)
  have hM0 : 0 ≤ ∫ ω, F ω^2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  have hM : (∫ ω, F ω^2 ∂μ) ≤ ((2*p).factorial:ℝ)*(2*Real.exp 1*(V:ℝ))^(2*p) := by
    simpa only [F, ← pow_mul, show p*2=2*p by omega] using hm.2 (2*p)
  have hP := subGaussian_product_tail μ X Y V hV hX hY a ha
  have hCS := integral_indicator_le_sqrt_square μ F (by dsimp [F]; fun_prop)
    (fun ω => pow_nonneg (abs_nonneg _) p) hF2 A hA
  have hfac := factorial_two_mul_le_square p
  let C := 2*(p.factorial:ℝ)*(4*Real.exp 1*(V:ℝ))^p*Real.exp (-a/(4*(V:ℝ)))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hExp : Real.exp (-a/(2*(V:ℝ))) = Real.exp (-a/(4*(V:ℝ)))^2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    field_simp
    ring
  have hProd : (∫ ω, F ω^2 ∂μ)*μ.real A ≤ C^2 := by
    calc
      _ ≤ (((2*p).factorial:ℝ)*(2*Real.exp 1*(V:ℝ))^(2*p)) *
          (4*Real.exp (-a/(2*(V:ℝ)))) := mul_le_mul hM hP measureReal_nonneg (by positivity)
      _ ≤ ((2:ℝ)^(2*p)*(p.factorial:ℝ)^2*(2*Real.exp 1*(V:ℝ))^(2*p)) *
          (4*Real.exp (-a/(2*(V:ℝ)))) := by gcongr
      _ = C^2 := by
        rw [hExp]
        dsimp [C]
        rw [show 4*Real.exp 1*(V:ℝ) = 2*(2*Real.exp 1*(V:ℝ)) by ring]
        simp only [mul_pow, ← pow_mul]
        rw [show p*2=2*p by omega]
        ring
  rw [← Real.sqrt_mul hM0] at hCS
  exact hCS.trans (Real.sqrt_le_iff.mpr ⟨hC,hProd⟩)

lemma subGaussian_product_truncated_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hXm : Measurable X) (hYm : Measurable Y) (V : ℝ≥0) (hV : 0 < V)
    (hX : HasSubgaussianMGF X V μ) (hY : HasSubgaussianMGF Y V μ)
    (s : ℝ) (hSecond : (∫ ω, (X ω*Y ω)^2 ∂μ) ≤ s)
    (a : ℝ) (ha : 0 ≤ a) (p : ℕ) (hp : 2 ≤ p) :
    (∫ ω, |X ω*Y ω|^p ∂μ) ≤ s*a^(p-2) +
      2*(p.factorial:ℝ)*(4*Real.exp 1*(V:ℝ))^p*Real.exp (-a/(4*(V:ℝ))) := by
  let F : Ω → ℝ := fun ω => |X ω*Y ω|^p
  let A := {ω | a < |X ω*Y ω|}
  have hA : MeasurableSet A := measurableSet_lt measurable_const (continuous_abs.measurable.comp (hXm.mul hYm))
  have hm := subGaussian_product_factorial_moments μ X Y V hV hX hY
  have hSq : Integrable (fun ω => (X ω*Y ω)^2) μ := by
    simpa only [sq_abs] using hm.1 2
  have hHigh := (hm.1 p).indicator hA
  have hDom (ω : Ω) : F ω ≤ a^(p-2)*(X ω*Y ω)^2+A.indicator F ω := by
    by_cases hω : ω ∈ A
    · rw [indicator_of_mem hω]
      exact le_add_of_nonneg_left (mul_nonneg (pow_nonneg ha _) (sq_nonneg _))
    · rw [indicator_of_notMem hω, add_zero]
      have hl : |X ω*Y ω| ≤ a := le_of_not_gt hω
      dsimp [F]
      calc
        _ = |X ω*Y ω|^(p-2)*(X ω*Y ω)^2 := by
          rw [← sq_abs, ← pow_add]; congr 1; omega
        _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hl _) (sq_nonneg _)
  have H := integral_mono (hm.1 p) ((hSq.const_mul (a^(p-2))).add hHigh) hDom
  simp only [Pi.add_apply] at H
  rw [integral_add (hSq.const_mul _) hHigh, integral_const_mul] at H
  have hh := subGaussian_product_high_moment μ X Y hXm hYm V hV hX hY a ha p
  exact H.trans (by
    have hl := mul_le_mul_of_nonneg_left hSecond (pow_nonneg ha (p-2))
    nlinarith)

lemma subGaussian_product_variance_factorial_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hXm : Measurable X) (hYm : Measurable Y) (V : ℝ≥0) (hV : 0 < V)
    (hX : HasSubgaussianMGF X V μ) (hY : HasSubgaussianMGF Y V μ)
    (s : ℝ) (hs : 0 < s) (hSecond : (∫ ω, (X ω*Y ω)^2 ∂μ) ≤ s)
    (a B : ℝ) (ha : 0 ≤ a) (hB : 0 < B) (haB : a ≤ B)
    (hVB : 4*Real.exp 1*(V:ℝ) ≤ B)
    (hCutoff : (4*Real.exp 1*(V:ℝ))^2*Real.exp (-a/(4*(V:ℝ))) ≤ s) :
    ∀ p, 2 ≤ p → (∫ ω, |X ω*Y ω|^p ∂μ) ≤ (p.factorial:ℝ)*(3*s)*B^(p-2) := by
  intro p hp
  have hh := subGaussian_product_truncated_moment μ X Y hXm hYm V hV hX hY s hSecond a ha p hp
  have hf : 1 ≤ (p.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos p
  have hb0 : 0 ≤ 4*Real.exp 1*(V:ℝ) := by positivity
  have hhigh : (4*Real.exp 1*(V:ℝ))^p*Real.exp (-a/(4*(V:ℝ))) ≤ s*B^(p-2) := by
    calc
      _ = (4*Real.exp 1*(V:ℝ))^(p-2)*
          ((4*Real.exp 1*(V:ℝ))^2*Real.exp (-a/(4*(V:ℝ)))) := by
        rw [← mul_assoc, ← pow_add, show p-2+2=p by omega]
      _ ≤ (4*Real.exp 1*(V:ℝ))^(p-2)*s := mul_le_mul_of_nonneg_left hCutoff (pow_nonneg hb0 _)
      _ ≤ B^(p-2)*s := by gcongr
      _ = _ := by ring
  have hlow : s*a^(p-2) ≤ (p.factorial:ℝ)*s*B^(p-2) := by
    calc
      _ ≤ s*B^(p-2) := by gcongr
      _ ≤ _ := by nlinarith [mul_nonneg hs.le (pow_nonneg hB.le (p-2))]
  have hh' := mul_le_mul_of_nonneg_left hhigh (show 0 ≤ 2*(p.factorial:ℝ) by positivity)
  nlinarith

lemma subGaussian_product_variance_localMGF {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hXm : Measurable X) (hYm : Measurable Y) (V : ℝ≥0) (hV : 0 < V)
    (hX : HasSubgaussianMGF X V μ) (hY : HasSubgaussianMGF Y V μ)
    (s : ℝ) (hs : 0 < s) (hSecond : (∫ ω, (X ω*Y ω)^2 ∂μ) ≤ s)
    (hMean : (∫ ω, X ω*Y ω ∂μ) = 0)
    (a B : ℝ) (ha : 0 ≤ a) (hB : 0 < B) (haB : a ≤ B)
    (hVB : 4*Real.exp 1*(V:ℝ) ≤ B)
    (hCutoff : (4*Real.exp 1*(V:ℝ))^2*Real.exp (-a/(4*(V:ℝ))) ≤ s) :
    LocalQuadraticMGF (fun ω => X ω*Y ω) μ (6*s) (1/(2*B)) := by
  have hm := subGaussian_product_factorial_moments μ X Y V hV hX hY
  have hGoal : 6*s = 2*(3*s) := by ring
  rw [hGoal]
  exact localQuadraticMGF_of_factorial_moments (X := fun ω => X ω*Y ω) (v := 3*s)
    (hXm.mul hYm) (by positivity) hB
    (fun p => (hm.1 p).mono' ((hXm.mul hYm).pow_const p).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => by simp [Real.norm_eq_abs]))) hMean
    (subGaussian_product_variance_factorial_moments μ X Y hXm hYm V hV hX hY
      s hs hSecond a B ha hB haB hVB hCutoff)

def productVarianceCutoff (v s : ℝ) : ℝ :=
  4*v*max 0 (Real.log ((4*Real.exp 1*v)^2/s))

def productVarianceScale (v s : ℝ) : ℝ :=
  max (Real.sqrt s) (max (4*Real.exp 1*v) (productVarianceCutoff v s))

lemma productVarianceCutoff_exponential_bound {v s : ℝ} (hv : 0 < v) (hs : 0 < s) :
    (4*Real.exp 1*v)^2*Real.exp (-productVarianceCutoff v s/(4*v)) ≤ s := by
  have hr : 0 < (4*Real.exp 1*v)^2/s := by positivity
  have hn : -productVarianceCutoff v s/(4*v) =
      -max 0 (Real.log ((4*Real.exp 1*v)^2/s)) := by
    unfold productVarianceCutoff
    field_simp
  rw [hn]
  calc
    _ ≤ (4*Real.exp 1*v)^2*Real.exp (-Real.log ((4*Real.exp 1*v)^2/s)) := by
      gcongr
      exact le_max_right _ _
    _ = s := by rw [Real.exp_neg, Real.exp_log hr]; field_simp

lemma productVarianceScale_pos {v s : ℝ} (hv : 0 < v) : 0 < productVarianceScale v s := by
  exact (show 0 < 4*Real.exp 1*v by positivity).trans_le
    ((le_max_left _ _).trans (le_max_right _ _))

lemma subGaussian_product_logarithmic_variance_localMGF
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hXm : Measurable X) (hYm : Measurable Y) (V : ℝ≥0) (hV : 0 < V)
    (hX : HasSubgaussianMGF X V μ) (hY : HasSubgaussianMGF Y V μ)
    (s : ℝ) (hs : 0 < s) (hSecond : (∫ ω, (X ω*Y ω)^2 ∂μ) ≤ s)
    (hMean : (∫ ω, X ω*Y ω ∂μ) = 0) :
    LocalQuadraticMGF (fun ω => X ω*Y ω) μ (6*s)
      (1/(2*productVarianceScale (V:ℝ) s)) := by
  exact subGaussian_product_variance_localMGF μ X Y hXm hYm V hV hX hY s hs hSecond hMean
    (productVarianceCutoff (V:ℝ) s) (productVarianceScale (V:ℝ) s)
    (by unfold productVarianceCutoff; positivity)
    (productVarianceScale_pos (NNReal.coe_pos.mpr hV))
    ((le_max_right _ _).trans (le_max_right _ _)) ((le_max_left _ _).trans (le_max_right _ _))
    (productVarianceCutoff_exponential_bound (NNReal.coe_pos.mpr hV) hs)

lemma centered_signed_variance_factorial_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → ℝ) (hZ : Measurable Z)
    (s B : ℝ) (hs : 0 < s) (hB : 0 < B) (hsB : Real.sqrt s ≤ B)
    (hSecond : (∫ ω, Z ω^2 ∂μ) ≤ s)
    (hInt : ∀ p, Integrable (fun ω => |Z ω|^p) μ)
    (hMom : ∀ p, 2 ≤ p → (∫ ω, |Z ω|^p ∂μ) ≤ (p.factorial:ℝ)*(3*s)*B^(p-2)) :
    (∀ p, Integrable (fun ω => centeredObservable μ Z ω^p) μ) ∧
      (∫ ω, centeredObservable μ Z ω ∂μ) = 0 ∧
      (∀ p, 2 ≤ p → (∫ ω, |centeredObservable μ Z ω|^p ∂μ) ≤
        (p.factorial:ℝ)*(8*s)*(2*B)^(p-2)) := by
  let m := ∫ ω, Z ω ∂μ
  have hZInt : Integrable Z μ := (hInt 1).mono' hZ.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω => by simp [Real.norm_eq_abs]))
  have hZLp : MemLp Z 2 μ := (memLp_two_iff_integrable_sq hZ.aestronglyMeasurable).mpr (by
    simpa only [sq_abs] using hInt 2)
  have hm2 : m^2 ≤ s := by
    have hv := variance_nonneg Z μ
    rw [variance_eq_sub hZLp] at hv
    change 0 ≤ (∫ ω, Z ω^2 ∂μ)-m^2 at hv
    linarith
  have hmB : |m| ≤ B := (Real.le_sqrt_of_sq_le (by simpa only [sq_abs] using hm2)).trans hsB
  have hMeanPow (p : ℕ) (hp : 2 ≤ p) : |m|^p ≤ s*B^(p-2) := by
    calc
      _ = m^2*|m|^(p-2) := by rw [← sq_abs, ← pow_add]; congr 1; omega
      _ ≤ s*B^(p-2) := mul_le_mul hm2 (pow_le_pow_left₀ (abs_nonneg _) hmB _)
        (pow_nonneg (abs_nonneg _) _) hs.le
  have hdom (p : ℕ) (ω : Ω) : |centeredObservable μ Z ω|^p ≤
      2^(p-1)*(|Z ω|^p+|m|^p) := by
    unfold centeredObservable
    apply (pow_le_pow_left₀ (abs_nonneg _) (abs_sub _ _) p).trans
    exact add_pow_le (abs_nonneg _) (abs_nonneg _) p
  have hAbsInt (p : ℕ) : Integrable (fun ω => |centeredObservable μ Z ω|^p) μ := by
    apply (((hInt p).add (integrable_const (|m|^p))).const_mul (2^(p-1))).mono'
      ((continuous_abs.measurable.comp (hZ.sub_const _)).pow_const p).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω => by
      simpa only [Real.norm_eq_abs, abs_pow, abs_abs, centeredObservable, Function.comp_def, Pi.add_apply] using hdom p ω)
  refine ⟨fun p => (hAbsInt p).mono' ((hZ.sub_const _).pow_const p).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω => by simp [Real.norm_eq_abs])), ?_, ?_⟩
  · unfold centeredObservable
    rw [integral_sub hZInt (integrable_const _)]
    simp
  · intro p hp
    have hf : 1 ≤ (p.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos p
    have hmp : |m|^p ≤ (p.factorial:ℝ)*s*B^(p-2) := (hMeanPow p hp).trans (by
      nlinarith [mul_nonneg hs.le (pow_nonneg hB.le (p-2))])
    calc
      _ ≤ ∫ ω, 2^(p-1)*(|Z ω|^p+|m|^p) ∂μ := integral_mono (hAbsInt p)
        (((hInt p).add (integrable_const (|m|^p))).const_mul _) (hdom p)
      _ = 2^(p-1)*((∫ ω, |Z ω|^p ∂μ)+|m|^p) := by
        rw [integral_const_mul, integral_add (hInt p) (integrable_const _)]
        simp
      _ ≤ 2^(p-1)*((p.factorial:ℝ)*(4*s)*B^(p-2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith [hMom p hp]
      _ = _ := by
        rw [show p-1=(p-2)+1 by omega, pow_succ, mul_pow]
        ring

lemma subGaussian_centered_product_logarithmic_variance_localMGF
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hXm : Measurable X) (hYm : Measurable Y) (V : ℝ≥0) (hV : 0 < V)
    (hX : HasSubgaussianMGF X V μ) (hY : HasSubgaussianMGF Y V μ)
    (s : ℝ) (hs : 0 < s) (hSecond : (∫ ω, (X ω*Y ω)^2 ∂μ) ≤ s) :
    LocalQuadraticMGF (centeredObservable μ (fun ω => X ω*Y ω)) μ (16*s)
      (1/(4*productVarianceScale (V:ℝ) s)) := by
  have hm := subGaussian_product_factorial_moments μ X Y V hV hX hY
  have hRaw := subGaussian_product_variance_factorial_moments μ X Y hXm hYm V hV hX hY
    s hs hSecond (productVarianceCutoff (V:ℝ) s) (productVarianceScale (V:ℝ) s)
    (by unfold productVarianceCutoff; positivity) (productVarianceScale_pos (NNReal.coe_pos.mpr hV))
    ((le_max_right _ _).trans (le_max_right _ _)) ((le_max_left _ _).trans (le_max_right _ _))
    (productVarianceCutoff_exponential_bound (NNReal.coe_pos.mpr hV) hs)
  obtain ⟨hPowers,hMean,hMoments⟩ := centered_signed_variance_factorial_moments μ
    (fun ω => X ω*Y ω) (hXm.mul hYm) s (productVarianceScale (V:ℝ) s) hs
    (productVarianceScale_pos (NNReal.coe_pos.mpr hV)) (le_max_left _ _) hSecond hm.1 hRaw
  convert localQuadraticMGF_of_factorial_moments (X := centeredObservable μ (fun ω => X ω*Y ω))
    (v := 8*s) (B := 2*productVarianceScale (V:ℝ) s)
    ((hXm.mul hYm).sub_const _) (by positivity)
    (by have := productVarianceScale_pos (v := (V:ℝ)) (s := s) (NNReal.coe_pos.mpr hV); positivity)
    hPowers hMean hMoments using 1 <;> ring

end SKConstants.Concentration
