module
public import SKConstants.SubGaussianSquares
public import SKConstants.SubGaussianVarianceCutoff
public import SKConstants.VarianceCentering
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic

public section
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal ENNReal
namespace SKConstants.Concentration

lemma factorial_two_mul_le_square (p : ℕ) :
    ((2*p).factorial : ℝ) ≤ (2 : ℝ) ^ (2*p) * (p.factorial : ℝ) ^ 2 := by
  have he := Nat.choose_mul_factorial_mul_factorial (n := 2*p) (k := p) (by omega)
  have hsub : 2*p-p=p := by omega
  rw [hsub] at he
  have hh := Nat.mul_le_mul_right (p.factorial * p.factorial) (Nat.choose_le_two_pow (2*p) p)
  have hn : (2*p).factorial ≤ 2^(2*p) * (p.factorial * p.factorial) := by
    simpa only [← Nat.mul_assoc, he] using hh
  simpa only [pow_two] using (show ((2*p).factorial : ℝ) ≤ (2:ℝ)^(2*p) * ((p.factorial : ℝ) * (p.factorial : ℝ)) by exact_mod_cast hn)

lemma integral_indicator_le_sqrt_square {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (F : Ω → ℝ) (hFm : Measurable F)
    (hFnonneg : ∀ ω, 0 ≤ F ω) (hF2 : Integrable (fun ω => F ω ^ 2) μ)
    (A : Set Ω) (hA : MeasurableSet A) :
    (∫ ω, A.indicator F ω ∂μ) ≤
      Real.sqrt (∫ ω, F ω ^ 2 ∂μ) * Real.sqrt (μ.real A) := by
  let I : Ω → ℝ := A.indicator (fun _ => 1)
  have hIm : Measurable I := measurable_const.indicator hA
  have hI2 : (fun ω => I ω ^ 2) = I := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [I, hω]
  have hIint : Integrable I μ := (integrable_const (1:ℝ)).indicator hA
  have hIF : (fun ω => F ω * I ω) = A.indicator F := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [I, hω]
  have hf : MemLp F 2 μ := (memLp_two_iff_integrable_sq hFm.aestronglyMeasurable).mpr hF2
  have hi : MemLp I 2 μ := (memLp_two_iff_integrable_sq hIm.aestronglyMeasurable).mpr (by rwa [hI2])
  have H := integral_mul_le_Lp_mul_Lq_of_nonneg (p := 2) (q := 2)
    (Real.holderConjugate_iff.mpr ⟨(by norm_num : (1:ℝ)<2), by norm_num⟩)
    (f := F) (g := I) (μ := μ) (Filter.Eventually.of_forall hFnonneg)
    (Filter.Eventually.of_forall fun ω => by by_cases hω : ω ∈ A <;> simp [I, hω]) (by simpa using hf) (by simpa using hi)
  simp only [Real.rpow_two, one_div] at H
  rw [hIF, hI2] at H
  have hIe : (∫ ω, I ω ∂μ) = μ.real A := integral_indicator_one hA
  rw [hIe] at H
  simpa only [Real.sqrt_eq_rpow, one_div] using H

lemma subGaussian_square_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (L : Ω → ℝ) (K : ℝ≥0)
    (_hK : 0 < K) (hMGF : HasSubgaussianMGF L K μ) (a : ℝ) (ha : 0 ≤ a) :
    μ.real {ω | a < L ω ^ 2} ≤ 2 * Real.exp (-a/(2*(K:ℝ))) := by
  have hp := hMGF.measure_ge_le (Real.sqrt_nonneg a)
  have hn := hMGF.neg.measure_ge_le (Real.sqrt_nonneg a)
  have hsub : {ω | a < L ω ^ 2} ⊆
      {ω | Real.sqrt a ≤ L ω} ∪ {ω | Real.sqrt a ≤ -L ω} := by
    intro ω hω
    change a < L ω ^ 2 at hω
    have habs : Real.sqrt a ≤ |L ω| := Real.sqrt_le_iff.mpr
      ⟨abs_nonneg _, by simpa only [sq_abs] using hω.le⟩
    exact le_abs.mp habs
  have hb := (measureReal_mono (μ := μ) hsub).trans (measureReal_union_le _ _)
  rw [Real.sq_sqrt ha] at hp hn
  change μ.real {ω | Real.sqrt a ≤ -L ω} ≤ _ at hn
  exact hb.trans (by linarith)

lemma subGaussian_square_high_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (L : Ω → ℝ) (hMeas : Measurable L)
    (K : ℝ≥0) (hK : 0 < K) (hMGF : HasSubgaussianMGF L K μ)
    (a : ℝ) (ha : 0 ≤ a) (p : ℕ) :
    (∫ ω, {ω | a < L ω ^ 2}.indicator (fun ω => (L ω ^ 2) ^ p) ω ∂μ) ≤
      2 * (p.factorial : ℝ) * (2 * Real.exp 1 * (K : ℝ)) ^ p *
        Real.exp (-a / (4 * (K : ℝ))) := by
  let F : Ω → ℝ := fun ω => (L ω ^ 2) ^ p
  let A : Set Ω := {ω | a < L ω ^ 2}
  have hA : MeasurableSet A := measurableSet_lt measurable_const (hMeas.pow_const 2)
  have hFeq : (fun ω => F ω ^ 2) = fun ω => |L ω| ^ (2*(2*p)) := by
    funext ω
    dsimp [F]
    rw [← sq_abs (L ω), ← pow_mul, ← pow_mul]
    congr 1
    omega
  have hF2 : Integrable (fun ω => F ω ^ 2) μ := by
    rw [hFeq]
    exact subGaussian_integrable_abs_pow μ L K hMGF (2*(2*p))
  have hM0 : 0 ≤ ∫ ω, F ω ^ 2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  have hM : (∫ ω, F ω ^ 2 ∂μ) ≤
      2 * ((2*p).factorial : ℝ) * (Real.exp 1 * (K : ℝ)) ^ (2*p) := by
    rw [hFeq]
    exact subGaussian_even_moment_bound μ L K hK hMGF (2*p)
  have hP := subGaussian_square_tail μ L K hK hMGF a ha
  have hCS := integral_indicator_le_sqrt_square μ F (by dsimp [F]; fun_prop)
    (fun ω => pow_nonneg (sq_nonneg _) p) hF2 A hA
  have hfac := factorial_two_mul_le_square p
  let C := 2 * (p.factorial : ℝ) * (2 * Real.exp 1 * (K : ℝ)) ^ p *
    Real.exp (-a / (4 * (K : ℝ)))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hExp : Real.exp (-a/(2*(K:ℝ))) = Real.exp (-a/(4*(K:ℝ))) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    have hk : (K:ℝ) ≠ 0 := (NNReal.coe_pos.mpr hK).ne'
    field_simp
    ring
  have hProd : (∫ ω, F ω ^ 2 ∂μ) * μ.real A ≤ C ^ 2 := by
    calc
      _ ≤ (2 * ((2*p).factorial : ℝ) * (Real.exp 1 * (K : ℝ)) ^ (2*p)) *
          (2 * Real.exp (-a/(2*(K:ℝ)))) :=
        mul_le_mul hM hP (measureReal_nonneg) (by positivity)
      _ ≤ (2 * ((2:ℝ)^(2*p) * (p.factorial : ℝ)^2) * (Real.exp 1 * (K : ℝ)) ^ (2*p)) *
          (2 * Real.exp (-a/(2*(K:ℝ)))) := by gcongr
      _ = C ^ 2 := by
        rw [hExp]
        dsimp [C]
        simp only [mul_pow, ← pow_mul]
        rw [show p*2=2*p by omega]
        ring
  rw [← Real.sqrt_mul hM0] at hCS
  exact hCS.trans (Real.sqrt_le_iff.mpr ⟨hC, hProd⟩)

lemma subGaussian_square_truncated_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (L : Ω → ℝ) (hMeas : Measurable L)
    (K : ℝ≥0) (hK : 0 < K) (hMGF : HasSubgaussianMGF L K μ)
    (s : ℝ) (_hs : 0 < s) (hSecond : (∫ ω, L ω ^ 2 ∂μ) ≤ s)
    (a : ℝ) (ha : 0 ≤ a) (p : ℕ) (hp : 1 ≤ p) :
    (∫ ω, |L ω ^ 2| ^ p ∂μ) ≤
      s * a ^ (p - 1) +
        2 * (p.factorial : ℝ) * (2 * Real.exp 1 * (K : ℝ)) ^ p *
          Real.exp (-a / (4 * (K : ℝ))) := by
  let F : Ω → ℝ := fun ω => (L ω ^ 2) ^ p
  let A : Set Ω := {ω | a < L ω ^ 2}
  have hA : MeasurableSet A := measurableSet_lt measurable_const (hMeas.pow_const 2)
  have hFInt : Integrable F μ := by
    simpa only [F, pow_mul, sq_abs] using subGaussian_integrable_abs_pow μ L K hMGF (2*p)
  have hSqInt : Integrable (fun ω => L ω ^ 2) μ := by
    simpa only [sq_abs] using subGaussian_integrable_abs_pow μ L K hMGF 2
  have hHighInt : Integrable (A.indicator F) μ := hFInt.indicator hA
  have hDom (ω : Ω) : F ω ≤ a ^ (p-1) * L ω ^ 2 + A.indicator F ω := by
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω]
      exact le_add_of_nonneg_left (mul_nonneg (pow_nonneg ha _) (sq_nonneg _))
    · rw [Set.indicator_of_notMem hω, add_zero]
      have hlow : L ω ^ 2 ≤ a := le_of_not_gt hω
      dsimp [F]
      have he : p-1+1=p := by omega
      calc
        _ = (L ω ^ 2) ^ (p-1) * L ω ^ 2 := by conv_lhs => rw [← he, pow_succ]
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (sq_nonneg _) hlow (p-1)) (sq_nonneg _)
  have H := integral_mono hFInt ((hSqInt.const_mul (a^(p-1))).add hHighInt) hDom
  simp only [Pi.add_apply] at H
  rw [integral_add (hSqInt.const_mul _) hHighInt, integral_const_mul] at H
  have hlow := mul_le_mul_of_nonneg_left hSecond (pow_nonneg ha (p-1))
  have hhigh := subGaussian_square_high_moment μ L hMeas K hK hMGF a ha p
  have htarget := H.trans (add_le_add hlow hhigh)
  have habs : (fun ω => |L ω ^ 2| ^ p) = F := by
    funext ω
    simp only [abs_of_nonneg (sq_nonneg (L ω)), F]
  rw [habs]
  simpa only [mul_comm (a^(p-1)) s] using htarget

lemma subGaussian_square_variance_factorial_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (L : Ω → ℝ) (hMeas : Measurable L)
    (K : ℝ≥0) (hK : 0 < K) (hMGF : HasSubgaussianMGF L K μ)
    (s : ℝ) (hs : 0 < s) (hSecond : (∫ ω, L ω ^ 2 ∂μ) ≤ s)
    (a B : ℝ) (ha : 0 ≤ a) (hB : 0 < B) (hsB : s ≤ B) (haB : a ≤ B)
    (hkB : 2 * Real.exp 1 * (K : ℝ) ≤ B)
    (hCutoff : (2 * Real.exp 1 * (K : ℝ)) * Real.exp (-a / (4 * (K : ℝ))) ≤ s)
    (p : ℕ) (hp : 1 ≤ p) :
    (∫ ω, |L ω ^ 2| ^ p ∂μ) ≤ 3 * s * (p.factorial : ℝ) * B ^ (p - 1) :=
  (subGaussian_square_truncated_moment μ L hMeas K hK hMGF s hs hSecond a ha p hp).trans
    (square_truncated_moment_cutoff_bound (NNReal.coe_pos.mpr hK) hs ha hB hsB haB
      hkB hCutoff p hp)

lemma subGaussian_centered_square_variance_localMGF {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (L : Ω → ℝ) (hMeas : Measurable L)
    (K : ℝ≥0) (hK : 0 < K) (hMGF : HasSubgaussianMGF L K μ)
    (s : ℝ) (hs : 0 < s) (hSecond : (∫ ω, L ω ^ 2 ∂μ) ≤ s)
    (a B : ℝ) (ha : 0 ≤ a) (hB : 0 < B) (hsB : s ≤ B) (haB : a ≤ B)
    (hkB : 2 * Real.exp 1 * (K : ℝ) ≤ B)
    (hCutoff : (2 * Real.exp 1 * (K : ℝ)) * Real.exp (-a / (4 * (K : ℝ))) ≤ s) :
    LocalQuadraticMGF (centeredObservable μ (fun ω => L ω ^ 2)) μ
      (16 * s * B) (1 / (4 * B)) := by
  apply centered_variance_localMGF_of_factorial_moments μ (fun ω => L ω ^ 2)
    (hMeas.pow_const 2) (fun ω => sq_nonneg _) s B hs hB hsB hSecond
  · intro p
    simpa only [abs_pow, ← pow_mul] using
      subGaussian_integrable_abs_pow μ L K hMGF (2 * p)
  · intro p hp
    exact subGaussian_square_variance_factorial_moments μ L hMeas K hK hMGF s hs
      hSecond a B ha hB hsB haB hkB hCutoff p hp

lemma subGaussian_centered_square_logarithmic_variance_localMGF
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (L : Ω → ℝ) (hMeas : Measurable L)
    (K : ℝ≥0) (hK : 0 < K) (hMGF : HasSubgaussianMGF L K μ)
    (s : ℝ) (hs : 0 < s) (hSecond : (∫ ω, L ω ^ 2 ∂μ) ≤ s) :
    LocalQuadraticMGF (centeredObservable μ (fun ω => L ω ^ 2)) μ
      (16 * s * squareVarianceScale (K : ℝ) s)
      (1 / (4 * squareVarianceScale (K : ℝ) s)) := by
  obtain ⟨ha, hB, hsB, haB, hkB, hCutoff⟩ :=
    squareVarianceCutoff_conditions (NNReal.coe_pos.mpr hK) hs
  exact subGaussian_centered_square_variance_localMGF μ L hMeas K hK hMGF s hs
    hSecond (squareVarianceCutoff (K : ℝ) s) (squareVarianceScale (K : ℝ) s)
    ha hB hsB haB hkB hCutoff

end SKConstants.Concentration
