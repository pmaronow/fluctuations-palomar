module
public import SKConstants.ScalarProcessInnovationPrefixes
public import SKConstants.ScalarProcessUniformMesh
public import Mathlib.Tactic

public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
set_option backward.isDefEq.respectTransparency false
namespace SKConstants

lemma integral_char_scalarUniformPrefixes (z : ℝ) {ι Ω : Type*} [Fintype ι]
    [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (theta : ι → ℝ) (ends : ι → ℕ) (n N : ℕ) (hp : ∀ i, ends i ≤ N) :
    (∫ u, Complex.exp ((∑ i, theta i *
      scalarEulerInnovation z B (scalarUniformTime n (ends i)) n u : ℝ) * Complex.I)
        ∂scalarHiddenBrownianLaw z P) =
      scalarHistoryWeightedInnovationChar z (brownianMeshVariance (scalarUniformTime n))
        (scalarPrefixCoefficient theta ends) N := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hLaw := scalarUniformObservationHistory_hasLaw hB z n N
  have h := hLaw.integral_comp
    (f := fun H => Complex.exp ((scalarHistoryWeightedInnovationSum z
      (brownianMeshVariance (scalarUniformTime n)) (scalarPrefixCoefficient theta ends) N H : ℂ) *
        Complex.I)) (by fun_prop)
  have hzero : ∀ᵐ u ∂scalarHiddenBrownianLaw z P, B 0 u.2 = 0 :=
    (measurePreserving_snd (μ := scalarHiddenPriorBool z) (ν := P)).quasiMeasurePreserving.ae
      hB.eval_zero_ae_eq_zero
  have he : (fun u => Complex.exp ((scalarHistoryWeightedInnovationSum z
      (brownianMeshVariance (scalarUniformTime n)) (scalarPrefixCoefficient theta ends) N
        (scalarUniformObservationHistory z B n N u) : ℂ) * Complex.I)) =ᵐ[scalarHiddenBrownianLaw z P]
      (fun u => Complex.exp ((∑ i, theta i *
        scalarEulerInnovation z B (scalarUniformTime n (ends i)) n u : ℝ) * Complex.I)) := by
    filter_upwards [hzero] with u hu
    rw [scalarUniformObservationHistory, scalarHistoryWeightedInnovationSum_sampled_eq_prefixes
      z (brownianMeshVariance (scalarUniformTime n)) theta ends _ N hp u]
    congr 2
    apply congrArg Complex.ofReal
    apply Finset.sum_congr rfl
    intro i hi
    rw [← scalarUniformObservationHistory, scalarHistoryInnovationSum_uniform_eq z B n (ends i) u hu]
  have h' := integral_congr_ae he
  simpa only [Function.comp_def, scalarHistoryWeightedInnovationChar] using h'.symm.trans h

lemma integral_char_brownianPrefixes_hidden (z : ℝ) {ι Ω : Type*} [Fintype ι]
    [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (theta : ι → ℝ) (ends : ι → ℕ) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (N : ℕ) (hp : ∀ i, ends i ≤ N) :
    (∫ u : Bool × Ω, Complex.exp ((∑ i, theta i * (B (t (ends i)) u.2 - B (t 0) u.2) : ℝ) *
      Complex.I) ∂scalarHiddenBrownianLaw z P) =
      Complex.exp (-((∑ k ∈ Finset.range N,
        (scalarPrefixCoefficient theta ends k) ^ 2 * (brownianMeshVariance t k : ℝ) / 2 : ℝ) : ℂ)) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hsnd : HasLaw (Prod.snd : Bool × Ω → Ω) P (scalarHiddenBrownianLaw z P) := by
    constructor
    · exact measurable_snd.aemeasurable
    · exact measurePreserving_snd.map_eq
  have hm : AEMeasurable (fun ω => ∑ i, theta i * (B (t (ends i)) ω - B (t 0) ω)) P := by
    apply Finset.aemeasurable_fun_sum
    intro i hi
    exact ((hB.aemeasurable _).sub (hB.aemeasurable _)).const_mul _
  have h := hsnd.integral_comp
    (f := fun ω => Complex.exp ((∑ i, theta i * (B (t (ends i)) ω - B (t 0) ω) : ℝ) * Complex.I))
    ((Complex.measurable_exp.comp_aemeasurable
      ((Complex.continuous_ofReal.measurable.comp_aemeasurable hm).mul_const
        Complex.I)).aestronglyMeasurable)
  rw [show (fun u : Bool × Ω => Complex.exp ((∑ i,
      theta i * (B (t (ends i)) u.2 - B (t 0) u.2) : ℝ) * Complex.I)) =
      (fun ω => Complex.exp ((∑ i, theta i * (B (t (ends i)) ω - B (t 0) ω) : ℝ) * Complex.I)) ∘
        Prod.snd from rfl, h]
  exact integral_char_brownianPrefixes hB theta ends t ht N hp

lemma scalarUniformPrefixes_characteristic_error (z : ℝ) {ι Ω : Type*} [Fintype ι]
    [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (theta : ι → ℝ) (T : ι → ℝ≥0) (n : ℕ) :
    ‖(∫ u, Complex.exp ((∑ i, theta i * scalarEulerInnovation z B
        (scalarUniformTime n ⌊((n : ℝ) + 1) * (T i : ℝ)⌋₊) n u : ℝ) * Complex.I)
        ∂scalarHiddenBrownianLaw z P) -
      (∫ u : Bool × Ω, Complex.exp ((∑ i, theta i *
        (B (scalarUniformTime n ⌊((n : ℝ) + 1) * (T i : ℝ)⌋₊) u.2 - B 0 u.2) : ℝ) *
        Complex.I) ∂scalarHiddenBrownianLaw z P)‖ ≤
      Real.exp (2 * ∑ i, |theta i|) / ((n : ℝ) + 1) *
        (∑ i, |theta i|) ^ 2 * (∑ i, (T i : ℝ)) := by
  let A : ℝ := ∑ i, |theta i|
  let total : ℝ := ∑ i, (T i : ℝ)
  let ends : ι → ℕ := fun i => ⌊((n : ℝ) + 1) * (T i : ℝ)⌋₊
  let N : ℕ := ⌊((n : ℝ) + 1) * total⌋₊
  let dt : ℕ → ℝ≥0 := brownianMeshVariance (scalarUniformTime n)
  let h : ℝ := 1 / ((n : ℝ) + 1)
  have hA : 0 ≤ A := Finset.sum_nonneg (fun i hi => abs_nonneg _)
  have ht : 0 ≤ total := Finset.sum_nonneg (fun i hi => (T i).property)
  have hp : ∀ i, ends i ≤ N := by
    intro i
    apply Nat.floor_mono
    have hi : (T i : ℝ) ≤ total := Finset.single_le_sum
      (fun j hj => (T j).property) (Finset.mem_univ i)
    exact mul_le_mul_of_nonneg_left hi (by positivity)
  have hwidth (k : ℕ) : (dt k : ℝ) = h := by
    dsimp [dt, h]
    rw [brownianMeshVariance_scalarUniformTime]
    simp only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_add, NNReal.coe_natCast]
  have hh0 : 0 ≤ h := by dsimp [h]; positivity
  have hh1 : h ≤ 1 := by
    dsimp [h]
    apply (div_le_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have htotal : ∑ k ∈ Finset.range N, (dt k : ℝ) ≤ total := by
    simp only [hwidth, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    dsimp [h]
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr
    have hN : (N : ℝ) ≤ ((n : ℝ) + 1) * total := Nat.floor_le (by positivity)
    nlinarith
  have hs := integral_char_scalarUniformPrefixes z hB theta ends n N hp
  have hg := integral_char_brownianPrefixes_hidden z hB theta ends
    (scalarUniformTime n) (scalarUniformTime_monotone n) N hp
  rw [scalarUniformTime_zero n] at hg
  change ‖(∫ u, Complex.exp ((∑ i, theta i *
      scalarEulerInnovation z B (scalarUniformTime n (ends i)) n u : ℝ) * Complex.I)
        ∂scalarHiddenBrownianLaw z P) -
    (∫ u : Bool × Ω, Complex.exp ((∑ i, theta i *
      (B (scalarUniformTime n (ends i)) u.2 - B 0 u.2) : ℝ) * Complex.I)
      ∂scalarHiddenBrownianLaw z P)‖ ≤ _
  rw [hs, hg]
  calc
    _ ≤ Real.exp (2 * A) * h * ∑ k ∈ Finset.range N,
        (scalarPrefixCoefficient theta ends k) ^ 2 * (dt k : ℝ) :=
      scalarHistoryWeightedInnovationChar_mesh_error z dt
        (scalarPrefixCoefficient theta ends) N A h hA hh1
        (fun k hk => (hwidth k).le) (fun k hk => scalarPrefixCoefficient_abs_le theta ends k)
    _ ≤ Real.exp (2 * A) * h * (A ^ 2 * ∑ k ∈ Finset.range N, (dt k : ℝ)) :=
      mul_le_mul_of_nonneg_left (scalarPrefixCoefficient_energy_le theta ends dt N)
        (mul_nonneg (Real.exp_pos _).le hh0)
    _ ≤ Real.exp (2 * A) * h * (A ^ 2 * total) := by gcongr
    _ = _ := by dsimp [A, h, total]; ring

end SKConstants
