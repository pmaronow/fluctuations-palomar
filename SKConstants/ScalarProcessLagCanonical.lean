module
public import SKConstants.ScalarProcessLagTailMoments
public import SKConstants.ScalarProcessLagMGFLimit
public import SKConstants.ScalarProcessLogCoshLimit
public import SKConstants.ScalarProcessInnovationBrownian

public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
namespace SKConstants

def scalarContinuousLocalLagInformation {Ω : Type*} (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (u : Bool × Ω) : ℝ :=
  scalarContinuousLogCoshInformation z B T u -
    Real.tanh z * scalarContinuousInnovation z B T u

lemma scalarLagInnovationSum_uniform_eq {Ω : Type*} (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (n m : ℕ) (u : Bool × Ω) (hzero : B 0 u.2 = 0) :
    scalarLagInnovationSum z (brownianMeshVariance (scalarUniformTime n)) m
      (scalarUniformObservationHistory z B n m u) =
    scalarWeightedInnovationMeshSum Real.tanh z B n m u - Real.tanh z *
      scalarHistoryInnovationSum z (brownianMeshVariance (scalarUniformTime n)) m
        (scalarUniformObservationHistory z B n m u) := by
  have hy : scalarHiddenContinuousField z B (scalarUniformTime n 0) u = z := by
    simp [scalarHiddenContinuousField, scalarUniformTime_zero, hzero]
  induction m with
  | zero => simp [scalarLagInnovationSum, scalarWeightedInnovationMeshSum, scalarHistoryInnovationSum]
  | succ m ih =>
    change scalarLagInnovationSum z _ m (scalarUniformObservationHistory z B n m u) +
      (Real.tanh (scalarLastField z m (scalarUniformObservationHistory z B n m u)) - Real.tanh z) *
        scalarInnovation (scalarLastField z m (scalarUniformObservationHistory z B n m u))
          _ (scalarHiddenContinuousField z B (scalarUniformTime n (m+1)) u) = _
    have hl := scalarLastField_sampled
      (fun k => scalarHiddenContinuousField z B (scalarUniformTime n k)) z m u hy
    change scalarLastField z m (scalarUniformObservationHistory z B n m u) = _ at hl
    rw [ih, hl]
    unfold scalarWeightedInnovationMeshSum
    rw [Finset.sum_range_succ]
    change _ = _ - Real.tanh z * (scalarHistoryInnovationSum z _ m
      (scalarUniformObservationHistory z B n m u) +
        scalarInnovation (scalarLastField z m (scalarUniformObservationHistory z B n m u))
          _ (scalarHiddenContinuousField z B (scalarUniformTime n (m+1)) u))
    rw [hl]
    ring

lemma scalarUniformMeshVariance_sum (n m : ℕ) :
    (∑ k ∈ Finset.range m, (brownianMeshVariance (scalarUniformTime n) k : ℝ)) =
      (scalarUniformTime n m : ℝ) := by
  simp only [brownianMeshVariance_scalarUniformTime, NNReal.coe_div, NNReal.coe_one,
    NNReal.coe_add, NNReal.coe_natCast, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, scalarUniformTime_coe]
  ring

lemma scalarLagUniformTime_floor_le (n : ℕ) (T : ℝ≥0) :
    (scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ : ℝ) ≤ T := by
  rw [scalarUniformTime_coe]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr
  exact (Nat.floor_le (by positivity)).trans_eq (mul_comm _ _)

lemma scalarLagInnovationSum_uniform_local_mgf {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (T : ℝ≥0) (hT : 0 < T) (hT1 : T ≤ 1) (n : ℕ) :
    Concentration.LocalQuadraticMGF
      (scalarLagInnovationSum z (brownianMeshVariance (scalarUniformTime n))
        ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ ∘
        scalarUniformObservationHistory z B n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊)
      (scalarHiddenBrownianLaw z P) (2048*Real.exp 1*(T:ℝ)^2) (1/(32*(T:ℝ))) := by
  apply (scalarLagInnovationSum_local_mgf z _ (T:ℝ) (by exact_mod_cast hT)
    (by exact_mod_cast hT1) _ (fun k _ => by exact_mod_cast scalarUniformMeshVariance_le_one n k)
    (by rw [scalarUniformMeshVariance_sum]; exact scalarLagUniformTime_floor_le n T)).comp_hasLaw
  exact scalarUniformObservationHistory_hasLaw hB z n _

lemma aestronglyMeasurable_scalarContinuousLocalLagInformation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (T : ℝ≥0) :
    AEStronglyMeasurable (scalarContinuousLocalLagInformation z B T) (scalarHiddenBrownianLaw z P) :=
  (aestronglyMeasurable_scalarContinuousLogCoshInformation P z B hB T).sub
    ((aestronglyMeasurable_scalarContinuousInnovation P z B hB T).const_mul (Real.tanh z))

theorem scalarContinuousLocalLagInformation_local_mgf {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (T : ℝ≥0) (hT : 0 < T) (hT1 : T ≤ 1) :
    Concentration.LocalQuadraticMGF (scalarContinuousLocalLagInformation z B T)
      (scalarHiddenBrownianLaw z P) (2048*Real.exp 1*(T:ℝ)^2) (1/(32*(T:ℝ))) := by
  let m : ℕ → ℕ := fun n => ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊
  let X : ℕ → Bool × Ω → ℝ := fun n => scalarLagInnovationSum z
    (brownianMeshVariance (scalarUniformTime n)) (m n) ∘ scalarUniformObservationHistory z B n (m n)
  have hX (n : ℕ) : Concentration.LocalQuadraticMGF (X n) (scalarHiddenBrownianLaw z P)
      (2048*Real.exp 1*(T:ℝ)^2) (1/(32*(T:ℝ))) :=
    scalarLagInnovationSum_uniform_local_mgf P z B hB.toIsPreBrownianReal T hT hT1 n
  have hXm (n : ℕ) : AEStronglyMeasurable (X n) (scalarHiddenBrownianLaw z P) :=
    ((measurable_scalarPredictableInnovationSum z _ _ (measurable_scalarLagCoefficient z) _).comp_aemeasurable
      (scalarUniformObservationHistory_hasLaw hB.toIsPreBrownianReal z n (m n)).aemeasurable).aestronglyMeasurable
  have hL2 := scalarWeightedLogCoshInnovation_L2 P z B hB T
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_integral_sq hL2.1 hL2.2).exists_seq_tendsto_ae
  apply localQuadraticMGF_of_tendsto_ae (fun n => hX (ns n)) (fun n => hXm (ns n))
  have hc : ∀ᵐ u ∂scalarHiddenBrownianLaw z P, Continuous (fun t => B t u.2) :=
    (measurePreserving_snd (μ := scalarHiddenPriorBool z) (ν := P)).quasiMeasurePreserving.ae hB.cont
  have hz : ∀ᵐ u ∂scalarHiddenBrownianLaw z P, B 0 u.2 = 0 :=
    (measurePreserving_snd (μ := scalarHiddenPriorBool z) (ν := P)).quasiMeasurePreserving.ae
      hB.eval_zero_ae_eq_zero
  filter_upwards [hae, hc, hz] with u hu hcu hzu
  have hM := (scalarHistoryInnovationSum_uniform_prefix_tendsto z B T u hcu hzu).comp hns.tendsto_atTop
  have ht := hu.sub (hM.const_mul (Real.tanh z))
  simpa only [X, Function.comp_apply, scalarLagInnovationSum_uniform_eq z B _ _ u hzu,
    m, scalarContinuousLocalLagInformation] using ht

lemma scalarWeightedBrownianLagMeshSum_eq {Ω : Type*} (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (n m : ℕ) (u : Bool × Ω) :
    scalarWeightedBrownianMeshSum (fun y => Real.tanh y - Real.tanh z) z B n m u =
      scalarWeightedBrownianMeshSum Real.tanh z B n m u - Real.tanh z *
        (scalarContinuousInnovation z B (scalarUniformTime n m) u -
          scalarContinuousInnovation z B 0 u) := by
  induction m with
  | zero => simp [scalarWeightedBrownianMeshSum, scalarUniformTime_zero]
  | succ m ih =>
    unfold scalarWeightedBrownianMeshSum at *
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    ring

theorem scalarContinuousLocalLagInformation_refining_L2 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (T : ℝ≥0) :
    (∀ n, Integrable (fun u => (scalarWeightedBrownianMeshSum
        (fun y => Real.tanh y - Real.tanh z) z B n ⌊((n:ℝ)+1)*(T:ℝ)⌋₊ u -
          scalarContinuousLocalLagInformation z B T u)^2) (scalarHiddenBrownianLaw z P)) ∧
    Tendsto (fun n => ∫ u, (scalarWeightedBrownianMeshSum
        (fun y => Real.tanh y - Real.tanh z) z B n ⌊((n:ℝ)+1)*(T:ℝ)⌋₊ u -
          scalarContinuousLocalLagInformation z B T u)^2 ∂scalarHiddenBrownianLaw z P)
      atTop (𝓝 0) := by
  let μ := scalarHiddenBrownianLaw z P
  let m : ℕ → ℕ := fun n => ⌊((n:ℝ)+1)*(T:ℝ)⌋₊
  let S : ℕ → ℝ≥0 := fun n => scalarUniformTime n (m n)
  let A := fun n u => scalarWeightedBrownianMeshSum Real.tanh z B n (m n) u -
    scalarContinuousLogCoshInformation z B T u
  let E := fun n u => Real.tanh z * (scalarContinuousInnovation z B (S n) u -
    scalarContinuousInnovation z B T u)
  have hM := scalarContinuousInnovation_isBrownianReal P z B hB
  have hEint (n : ℕ) : Integrable (fun u => (E n u)^2) μ := by
    have hl := hM.hasLaw_sub (S n) T
    have hi := hl.integrable_comp (gaussianReal_integrable_pow 0 (nndist (S n : ℝ) (T : ℝ)) 2)
    simpa only [E, mul_pow, Function.comp_def, Pi.sub_apply, μ] using hi.const_mul ((Real.tanh z)^2)
  have hEeq (n : ℕ) : (∫ u, (E n u)^2 ∂μ) = (Real.tanh z)^2 * |(S n : ℝ)-(T:ℝ)| := by
    have hl := hM.hasLaw_sub (S n) T
    have he := hl.integral_comp
      (gaussianReal_integrable_pow 0 (nndist (S n : ℝ) (T : ℝ)) 2).aestronglyMeasurable
    change (∫ u, (scalarContinuousInnovation z B (S n) u -
      scalarContinuousInnovation z B T u)^2 ∂μ) = _ at he
    dsimp only [E]
    simp_rw [mul_pow]
    rw [integral_const_mul, he]
    have hg := gaussianReal_integral_shift_sq 0 0 (nndist (S n : ℝ) (T : ℝ))
    have hh : (∫ x:ℝ, x^2 ∂gaussianReal 0 (nndist (S n : ℝ) (T : ℝ))) =
        |(S n:ℝ)-(T:ℝ)| := by
      simpa [coe_nndist, Real.dist_eq] using hg
    exact congrArg (fun x:ℝ => (Real.tanh z)^2*x) hh
  have hElim : Tendsto (fun n => ∫ u, (E n u)^2 ∂μ) atTop (𝓝 0) := by
    simp_rw [hEeq]
    have hs : Tendsto (fun n => (S n:ℝ)) atTop (𝓝 (T:ℝ)) :=
      (NNReal.continuous_coe.tendsto T).comp (scalarUniformTime_floor_tendsto T)
    simpa using ((continuous_abs.tendsto 0).comp (by simpa using hs.sub_const (T:ℝ))).const_mul
      ((Real.tanh z)^2)
  have hAm (n : ℕ) : AEMeasurable (A n) μ :=
    (aemeasurable_scalarWeightedBrownianMeshSum P Real.tanh measurable_scalarTanh z B hB n (m n)).sub
      (aestronglyMeasurable_scalarContinuousLogCoshInformation P z B hB T).aemeasurable
  have hEm (n : ℕ) : AEMeasurable (E n) μ :=
    ((aestronglyMeasurable_scalarContinuousInnovation P z B hB (S n)).aemeasurable.sub
      (aestronglyMeasurable_scalarContinuousInnovation P z B hB T).aemeasurable).const_mul (Real.tanh z)
  have hA := scalarWeightedLogCoshBrownian_L2 P z B hB T
  have hEq (n : ℕ) : (fun u => scalarWeightedBrownianMeshSum
      (fun y => Real.tanh y - Real.tanh z) z B n (m n) u -
        scalarContinuousLocalLagInformation z B T u) =ᵐ[μ] (fun u => A n u - E n u) := by
    filter_upwards [scalarContinuousInnovation_zero_ae P z B hB.toIsPreBrownianReal] with u hu
    rw [scalarWeightedBrownianLagMeshSum_eq, hu]
    dsimp [scalarContinuousLocalLagInformation, A, E, S]
    ring
  constructor
  · intro n
    exact (integrable_sq_sub (hAm n) (hEm n) (hA.1 n) (hEint n)).congr
      ((hEq n).symm.mono (fun _ h => congrArg (fun x:ℝ => x^2) h))
  · have hlim := tendsto_integral_sq_sub hAm hEm hA.1 hEint hA.2 hElim
    apply hlim.congr
    intro n
    exact integral_congr_ae ((hEq n).symm.mono (fun _ h => congrArg (fun x:ℝ => x^2) h))

end SKConstants
