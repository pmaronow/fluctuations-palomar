module
public import SKConstants.ScalarProcessConditionalCharacteristic
public import SKConstants.ScalarProcessInnovationBrownian
public import Mathlib.Tactic

public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
set_option backward.isDefEq.respectTransparency false
namespace SKConstants

lemma scalarHistoryFutureInnovationSum_const (z : ℝ) (dt : ℕ → ℝ≥0) (theta : ℝ)
    (m N : ℕ) (hmN : m ≤ N) (H : ScalarObservationHistory N) :
    scalarHistoryWeightedInnovationSum z dt (scalarFutureCoefficient (fun _ => theta) m) N H =
      theta * (scalarHistoryInnovationSum z dt N H -
        scalarHistoryInnovationSum z dt m (scalarHistoryTruncate N m hmN H)) := by
  induction N, hmN using Nat.le_induction with
  | base =>
    rw [scalarHistoryFutureInnovationSum_zero z dt (fun _ => theta) m m (le_refl m),
      scalarHistoryTruncate_self, sub_self, mul_zero]
  | succ N hmN ih =>
    rw [scalarHistoryWeightedInnovationSum, scalarHistoryInnovationSum,
      scalarHistoryTruncate_succ N m hmN]
    simp only [scalarFutureCoefficient, ite_eq_left hmN]
    rw [ih H.1]
    ring

@[expose] def scalarUniformPastFieldTest {ι : Type*} [Fintype ι]
    (z : ℝ) (eta : ι → ℝ) (ends : ι → ℕ) (m : ℕ) (hp : ∀ i, ends i ≤ m)
    (H : ScalarObservationHistory m) : ℂ :=
  Complex.exp ((∑ i, eta i * scalarLastField z (ends i)
    (scalarHistoryTruncate m (ends i) (hp i) H) : ℝ) * Complex.I)

lemma measurable_scalarUniformPastFieldTest {ι : Type*} [Fintype ι]
    (z : ℝ) (eta : ι → ℝ) (ends : ι → ℕ) (m : ℕ) (hp : ∀ i, ends i ≤ m) :
    Measurable (scalarUniformPastFieldTest z eta ends m hp) := by
  have hm : Measurable (fun H : ScalarObservationHistory m => ∑ i, eta i *
      scalarLastField z (ends i) (scalarHistoryTruncate m (ends i) (hp i) H)) := by
    apply Finset.measurable_fun_sum
    intro i hi
    exact ((measurable_scalarLastField z (ends i)).comp
      (measurable_scalarHistoryTruncate m (ends i) (hp i))).const_mul _
  exact Complex.measurable_exp.comp
    ((Complex.continuous_ofReal.measurable.comp hm).mul_const Complex.I)

lemma scalarUniformPastFieldTest_norm {ι : Type*} [Fintype ι]
    (z : ℝ) (eta : ι → ℝ) (ends : ι → ℕ) (m : ℕ) (hp : ∀ i, ends i ≤ m)
    (H : ScalarObservationHistory m) : ‖scalarUniformPastFieldTest z eta ends m hp H‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

lemma scalarUniformPastFieldTest_sampled {ι Ω : Type*} [Fintype ι]
    (z : ℝ) (eta : ι → ℝ) (ends : ι → ℕ) (m : ℕ) (hp : ∀ i, ends i ≤ m)
    (B : ℝ≥0 → Ω → ℝ) (n : ℕ) (u : Bool × Ω) (hzero : B 0 u.2 = 0) :
    scalarUniformPastFieldTest z eta ends m hp (scalarUniformObservationHistory z B n m u) =
      Complex.exp ((∑ i, eta i * scalarHiddenContinuousField z B
        (scalarUniformTime n (ends i)) u : ℝ) * Complex.I) := by
  unfold scalarUniformPastFieldTest
  congr 2
  apply congrArg Complex.ofReal
  apply Finset.sum_congr rfl
  intro i hi
  rw [scalarUniformObservationHistory, scalarHistoryTruncate_sampled]
  have hy : scalarHiddenContinuousField z B (scalarUniformTime n 0) u = z := by
    simp [scalarHiddenContinuousField, scalarUniformTime_zero, hzero]
  rw [scalarLastField_sampled (fun k => scalarHiddenContinuousField z B (scalarUniformTime n k))
    z (ends i) u hy]

lemma integral_scalarUniformPastFieldTest {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (z : ℝ) (eta : ι → ℝ) (ends : ι → ℕ) (m : ℕ) (hp : ∀ i, ends i ≤ m)
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (n : ℕ) :
    (∫ H, scalarUniformPastFieldTest z eta ends m hp H
      ∂scalarObservationHistoryLaw z (brownianMeshVariance (scalarUniformTime n)) m) =
      ∫ u, Complex.exp ((∑ i, eta i * scalarHiddenContinuousField z B
        (scalarUniformTime n (ends i)) u : ℝ) * Complex.I) ∂scalarHiddenBrownianLaw z P := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hLaw := scalarUniformObservationHistory_hasLaw hB z n m
  have h := hLaw.integral_comp
    (measurable_scalarUniformPastFieldTest z eta ends m hp).aestronglyMeasurable
  have hz : ∀ᵐ u ∂scalarHiddenBrownianLaw z P, B 0 u.2 = 0 :=
    (measurePreserving_snd (μ := scalarHiddenPriorBool z) (ν := P)).quasiMeasurePreserving.ae
      hB.eval_zero_ae_eq_zero
  have he : (fun u => scalarUniformPastFieldTest z eta ends m hp
      (scalarUniformObservationHistory z B n m u)) =ᵐ[scalarHiddenBrownianLaw z P]
      (fun u => Complex.exp ((∑ i, eta i * scalarHiddenContinuousField z B
        (scalarUniformTime n (ends i)) u : ℝ) * Complex.I)) := by
    filter_upwards [hz] with u hu
    exact scalarUniformPastFieldTest_sampled z eta ends m hp B n u hu
  exact h.symm.trans (integral_congr_ae he)

lemma scalarHistoryConditionalInnovationChar_uniform (z : ℝ) {ι Ω : Type*}
    [Fintype ι] [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (eta : ι → ℝ) (ends : ι → ℕ)
    (theta : ℝ) (n m N : ℕ) (hp : ∀ i, ends i ≤ m) (hmN : m ≤ N) :
    scalarHistoryConditionalInnovationChar z (brownianMeshVariance (scalarUniformTime n))
      (fun _ => theta) m N hmN (scalarUniformPastFieldTest z eta ends m hp) =
      ∫ u, Complex.exp (((∑ i, eta i * scalarHiddenContinuousField z B
        (scalarUniformTime n (ends i)) u) + theta *
          (scalarEulerInnovation z B (scalarUniformTime n N) n u -
            scalarEulerInnovation z B (scalarUniformTime n m) n u) : ℝ) * Complex.I)
        ∂scalarHiddenBrownianLaw z P := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hLaw := scalarUniformObservationHistory_hasLaw hB z n N
  have hmPhi := measurable_scalarUniformPastFieldTest z eta ends m hp
  have hmTr := measurable_scalarHistoryTruncate N m hmN
  have hInt := hLaw.integral_comp
    (f := fun H => scalarUniformPastFieldTest z eta ends m hp (scalarHistoryTruncate N m hmN H) *
      Complex.exp ((scalarHistoryWeightedInnovationSum z
        (brownianMeshVariance (scalarUniformTime n)) (scalarFutureCoefficient (fun _ => theta) m)
        N H : ℂ) * Complex.I))
    ((hmPhi.comp hmTr).mul (by fun_prop)).aestronglyMeasurable
  have hz : ∀ᵐ u ∂scalarHiddenBrownianLaw z P, B 0 u.2 = 0 :=
    (measurePreserving_snd (μ := scalarHiddenPriorBool z) (ν := P)).quasiMeasurePreserving.ae
      hB.eval_zero_ae_eq_zero
  apply hInt.symm.trans
  apply integral_congr_ae
  filter_upwards [hz] with u hu
  simp only [Function.comp_def]
  rw [scalarHistoryFutureInnovationSum_const z _ theta m N hmN]
  have hTr : scalarHistoryTruncate N m hmN (scalarUniformObservationHistory z B n N u) =
      scalarUniformObservationHistory z B n m u :=
    scalarHistoryTruncate_sampled _ N m hmN u
  rw [hTr, scalarUniformPastFieldTest_sampled z eta ends m hp B n u hu,
    scalarHistoryInnovationSum_uniform_eq z B n N u hu,
    scalarHistoryInnovationSum_uniform_eq z B n m u hu, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma scalarUniformTime_interval_variance (n m N : ℕ) (hmN : m ≤ N) :
    (∑ k ∈ Finset.Ico m N, (brownianMeshVariance (scalarUniformTime n) k : ℝ)) =
      (scalarUniformTime n N : ℝ) - (scalarUniformTime n m : ℝ) := by
  simp only [brownianMeshVariance_scalarUniformTime, NNReal.coe_div, NNReal.coe_one,
    NNReal.coe_add, NNReal.coe_natCast, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul,
    Nat.cast_sub hmN, scalarUniformTime_coe]
  ring

lemma scalarUniformTestedIncrement_characteristic_error (z : ℝ) {ι Ω : Type*}
    [Fintype ι] [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (eta : ι → ℝ) (ends : ι → ℕ)
    (theta : ℝ) (n m N : ℕ) (hp : ∀ i, ends i ≤ m) (hmN : m ≤ N) :
    ‖(∫ u, Complex.exp (((∑ i, eta i * scalarHiddenContinuousField z B
        (scalarUniformTime n (ends i)) u) + theta *
          (scalarEulerInnovation z B (scalarUniformTime n N) n u -
            scalarEulerInnovation z B (scalarUniformTime n m) n u) : ℝ) * Complex.I)
        ∂scalarHiddenBrownianLaw z P) -
      Complex.exp (-((theta ^ 2 * ((scalarUniformTime n N : ℝ) -
        (scalarUniformTime n m : ℝ)) / 2 : ℝ) : ℂ)) *
        (∫ u, Complex.exp ((∑ i, eta i * scalarHiddenContinuousField z B
          (scalarUniformTime n (ends i)) u : ℝ) * Complex.I) ∂scalarHiddenBrownianLaw z P)‖ ≤
      Real.exp (2 * |theta|) / ((n : ℝ) + 1) * theta ^ 2 *
        ((scalarUniformTime n N : ℝ) - (scalarUniformTime n m : ℝ)) := by
  let dt : ℕ → ℝ≥0 := brownianMeshVariance (scalarUniformTime n)
  let h : ℝ := 1 / ((n : ℝ) + 1)
  have hw (k : ℕ) : (dt k : ℝ) = h := by
    dsimp [dt, h]
    rw [brownianMeshVariance_scalarUniformTime]
    simp only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_add, NNReal.coe_natCast]
  have hh : h ≤ 1 := by
    dsimp [h]
    apply (div_le_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hPhi := measurable_scalarUniformPastFieldTest z eta ends m hp
  have hbound : ∀ H, ‖scalarUniformPastFieldTest z eta ends m hp H‖ ≤ (1 : ℝ) := by
    intro H
    exact (scalarUniformPastFieldTest_norm z eta ends m hp H).le
  have hc := scalarHistoryConditionalInnovationChar_mesh_error z dt (fun _ => theta)
    m N hmN (scalarUniformPastFieldTest z eta ends m hp) hPhi 1 zero_le_one hbound
    |theta| h (abs_nonneg _) hh (fun k hk => (hw k).le) (fun k hk => le_refl _)
  rw [scalarHistoryConditionalInnovationChar_uniform z hB eta ends theta n m N hp hmN,
    integral_scalarUniformPastFieldTest z eta ends m hp hB n] at hc
  have he : (∑ k ∈ Finset.Ico m N, theta ^ 2 * (dt k : ℝ)) =
      theta ^ 2 * ((scalarUniformTime n N : ℝ) - (scalarUniformTime n m : ℝ)) := by
    rw [← Finset.mul_sum]
    rw [scalarUniformTime_interval_variance n m N hmN]
  have hehalf : (∑ k ∈ Finset.Ico m N, theta ^ 2 * (dt k : ℝ) / 2) =
      theta ^ 2 * ((scalarUniformTime n N : ℝ) - (scalarUniformTime n m : ℝ)) / 2 := by
    rw [← Finset.sum_div, he]
  rw [hehalf] at hc
  simp only [one_mul, he] at hc
  calc
    _ ≤ Real.exp (2 * |theta|) * h *
      (theta ^ 2 * ((scalarUniformTime n N : ℝ) - (scalarUniformTime n m : ℝ))) := hc
    _ = _ := by dsimp [h]; ring

lemma aemeasurable_scalarHiddenContinuousField_conditional {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (T : ℝ≥0) :
    AEMeasurable (scalarHiddenContinuousField z B T) (scalarHiddenBrownianLaw z P) := by
  have hs : AEMeasurable (fun u : Bool × Ω => scalarHiddenSign u.1)
      (scalarHiddenBrownianLaw z P) :=
    ((measurable_of_finite scalarHiddenSign).comp measurable_fst).aemeasurable
  have hb : AEMeasurable (fun u : Bool × Ω => B T u.2)
      (scalarHiddenBrownianLaw z P) := (hB.aemeasurable T).comp_snd
  exact (aemeasurable_const.add (hs.mul_const (T : ℝ))).add hb

lemma scalarUniformPastFieldFourier_ae_tendsto {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (z : ℝ) (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (eta : ι → ℝ) (T : ι → ℝ≥0) :
    ∀ᵐ u ∂scalarHiddenBrownianLaw z P,
      Tendsto (fun n => ∑ i, eta i * scalarHiddenContinuousField z B
        (scalarUniformTime n ⌊((n : ℝ) + 1) * (T i : ℝ)⌋₊) u)
        atTop (nhds (∑ i, eta i * scalarHiddenContinuousField z B (T i) u)) := by
  have hc : ∀ᵐ u ∂scalarHiddenBrownianLaw z P, Continuous (fun t => B t u.2) :=
    (measurePreserving_snd (μ := scalarHiddenPriorBool z) (ν := P)).quasiMeasurePreserving.ae hB.cont
  filter_upwards [hc] with u hu
  have hy : Continuous (fun t : ℝ≥0 => scalarHiddenContinuousField z B t u) := by
    dsimp [scalarHiddenContinuousField]
    fun_prop
  apply tendsto_finsetSum
  intro i hi
  exact ((hy.tendsto (T i)).comp (scalarUniformTime_floor_tendsto (T i))).const_mul (eta i)

lemma scalarContinuousInnovation_tested_increment_characteristic {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (z : ℝ) (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (eta : ι → ℝ) (T : ι → ℝ≥0) (s t : ℝ≥0) (hst : s ≤ t)
    (hpast : ∀ i, T i ≤ s) (theta : ℝ) :
    (∫ u, Complex.exp (((∑ i, eta i * scalarHiddenContinuousField z B (T i) u) +
        theta * (scalarContinuousInnovation z B t u - scalarContinuousInnovation z B s u) : ℝ) *
        Complex.I) ∂scalarHiddenBrownianLaw z P) =
      Complex.exp (-((theta ^ 2 * ((t : ℝ) - (s : ℝ)) / 2 : ℝ) : ℂ)) *
        (∫ u, Complex.exp ((∑ i, eta i * scalarHiddenContinuousField z B (T i) u : ℝ) *
          Complex.I) ∂scalarHiddenBrownianLaw z P) := by
  let ends : ℕ → ι → ℕ := fun n i => ⌊((n : ℝ) + 1) * (T i : ℝ)⌋₊
  let m : ℕ → ℕ := fun n => ⌊((n : ℝ) + 1) * (s : ℝ)⌋₊
  let N : ℕ → ℕ := fun n => ⌊((n : ℝ) + 1) * (t : ℝ)⌋₊
  let past : ℕ → Bool × Ω → ℝ := fun n u =>
    ∑ i, eta i * scalarHiddenContinuousField z B (scalarUniformTime n (ends n i)) u
  let pastLimit : Bool × Ω → ℝ := fun u => ∑ i, eta i * scalarHiddenContinuousField z B (T i) u
  let F : ℕ → Bool × Ω → ℝ := fun n u => past n u + theta *
    (scalarEulerInnovation z B (scalarUniformTime n (N n)) n u -
      scalarEulerInnovation z B (scalarUniformTime n (m n)) n u)
  let f : Bool × Ω → ℝ := fun u => pastLimit u + theta *
    (scalarContinuousInnovation z B t u - scalarContinuousInnovation z B s u)
  let duration : ℕ → ℝ := fun n =>
    (scalarUniformTime n (N n) : ℝ) - (scalarUniformTime n (m n) : ℝ)
  let G : ℕ → ℂ := fun n => Complex.exp (-((theta ^ 2 * duration n / 2 : ℝ) : ℂ))
  have hPastMeas (n : ℕ) : AEMeasurable (past n) (scalarHiddenBrownianLaw z P) := by
    apply Finset.aemeasurable_fun_sum
    intro i hi
    exact (aemeasurable_scalarHiddenContinuousField_conditional P z B hB.toIsPreBrownianReal _).const_mul (eta i)
  have hFMeas (n : ℕ) : AEMeasurable (F n) (scalarHiddenBrownianLaw z P) :=
    (hPastMeas n).add (((aemeasurable_scalarEulerInnovation P z B hB.toIsPreBrownianReal _ n).sub
      (aemeasurable_scalarEulerInnovation P z B hB.toIsPreBrownianReal _ n)).const_mul theta)
  have hPastLimit := scalarUniformPastFieldFourier_ae_tendsto P z B hB eta T
  have hc : ∀ᵐ u ∂scalarHiddenBrownianLaw z P, Continuous (fun t => B t u.2) :=
    (measurePreserving_snd (μ := scalarHiddenPriorBool z) (ν := P)).quasiMeasurePreserving.ae hB.cont
  have hFLimit : ∀ᵐ u ∂scalarHiddenBrownianLaw z P,
      Tendsto (fun n => F n u) atTop (nhds (f u)) := by
    filter_upwards [hc, hPastLimit] with u hu hPast
    have hs : Tendsto (fun n => scalarEulerInnovation z B (scalarUniformTime n (m n)) n u)
        atTop (nhds (scalarContinuousInnovation z B s u)) := by
      dsimp [m]
      simp_rw [scalarUniformTime_floor_eq]
      exact scalarEulerInnovation_prefix_tendsto_path z B s u hu
    have ht : Tendsto (fun n => scalarEulerInnovation z B (scalarUniformTime n (N n)) n u)
        atTop (nhds (scalarContinuousInnovation z B t u)) := by
      dsimp [N]
      simp_rw [scalarUniformTime_floor_eq]
      exact scalarEulerInnovation_prefix_tendsto_path z B t u hu
    exact hPast.add ((ht.sub hs).const_mul theta)
  have hPastIntegral := integral_exp_imag_tendsto_of_ae_tendsto
    (scalarHiddenBrownianLaw z P) past pastLimit hPastMeas hPastLimit
  have hFIntegral := integral_exp_imag_tendsto_of_ae_tendsto
    (scalarHiddenBrownianLaw z P) F f hFMeas hFLimit
  have hduration : Tendsto duration atTop (nhds ((t : ℝ) - (s : ℝ))) := by
    have ht := NNReal.continuous_coe.continuousAt.tendsto.comp (scalarUniformTime_floor_tendsto t)
    have hs := NNReal.continuous_coe.continuousAt.tendsto.comp (scalarUniformTime_floor_tendsto s)
    exact ht.sub hs
  have hG : Tendsto G atTop
      (nhds (Complex.exp (-((theta ^ 2 * ((t : ℝ) - (s : ℝ)) / 2 : ℝ) : ℂ)))) := by
    exact Complex.continuous_exp.continuousAt.tendsto.comp
      (((hduration.const_mul (theta ^ 2)).div_const 2).ofReal.neg)
  have hError (n : ℕ) :
      ‖(∫ u, Complex.exp ((F n u : ℂ) * Complex.I) ∂scalarHiddenBrownianLaw z P) -
        G n * (∫ u, Complex.exp ((past n u : ℂ) * Complex.I) ∂scalarHiddenBrownianLaw z P)‖ ≤
      Real.exp (2 * |theta|) / ((n : ℝ) + 1) * theta ^ 2 * duration n := by
    have hmN : m n ≤ N n := Nat.floor_mono
      (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr hst) (by positivity))
    have hends : ∀ i, ends n i ≤ m n := fun i => Nat.floor_mono
      (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr (hpast i)) (by positivity))
    exact scalarUniformTestedIncrement_characteristic_error z hB.toIsPreBrownianReal
      eta (ends n) theta n (m n) (N n) hends hmN
  have hErrorLimit : Tendsto (fun n : ℕ => Real.exp (2 * |theta|) / ((n : ℝ) + 1) *
      theta ^ 2 * duration n) atTop (nhds 0) := by
    have h := ((tendsto_one_div_add_atTop_nhds_zero_nat.const_mul
      (Real.exp (2 * |theta|))).mul_const (theta ^ 2)).mul hduration
    simpa only [mul_zero, zero_mul, div_eq_mul_inv, one_mul] using h
  have hZero : Tendsto (fun n => (∫ u, Complex.exp ((F n u : ℂ) * Complex.I)
      ∂scalarHiddenBrownianLaw z P) - G n *
      (∫ u, Complex.exp ((past n u : ℂ) * Complex.I) ∂scalarHiddenBrownianLaw z P))
      atTop (nhds 0) := squeeze_zero_norm hError hErrorLimit
  have hActual := hFIntegral.sub (hG.mul hPastIntegral)
  exact sub_eq_zero.mp (tendsto_nhds_unique hActual hZero)

end SKConstants
