module
public import SKConstants.ScalarProcessRowMGFLimit
public import SKConstants.ScalarProcessRowMGFMesh
public import SKConstants.ScalarProcessPosteriorItoLimit
public import Mathlib.Analysis.InnerProductSpace.PiL2

public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology InnerProductSpace
set_option backward.isDefEq.respectTransparency false
namespace SKConstants

@[expose] def scalarContinuousPosteriorIncrement {Ω : Type*} (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (S T : ℝ≥0) (u : Bool × Ω) : ℝ :=
  Real.tanh (scalarHiddenContinuousField z B T u) -
    Real.tanh (scalarHiddenContinuousField z B S u)

lemma aemeasurable_scalarContinuousPosteriorIncrement {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (S T : ℝ≥0) :
    AEMeasurable (scalarContinuousPosteriorIncrement z B S T) (scalarHiddenBrownianLaw z P) :=
  (measurable_scalarTanh.comp_aemeasurable
    (aemeasurable_scalarHiddenContinuousField P z B hB T)).sub
      (measurable_scalarTanh.comp_aemeasurable
        (aemeasurable_scalarHiddenContinuousField P z B hB S))

lemma integrable_scalarPosteriorMesh_square_error {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (T : ℝ≥0) (n : ℕ) :
    Integrable (fun u => (scalarWeightedBrownianMeshSum scalarDefect z B n
      ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ u -
      (Real.tanh (scalarHiddenContinuousField z B T u) - Real.tanh z))^2)
      (scalarHiddenBrownianLaw z P) := by
  apply integrable_sq_sub
  · exact aemeasurable_scalarWeightedBrownianMeshSum P scalarDefect measurable_scalarDefect
      z B hB n _
  · exact (measurable_scalarTanh.comp_aemeasurable
      (aemeasurable_scalarHiddenContinuousField P z B hB.toIsPreBrownianReal T)).sub_const _
  · exact (scalarWeightedBrownianMeshSum_defect_L2_isometry P z B hB n _).1
  · apply (integrable_const (4 : ℝ)).mono'
    · exact (((measurable_scalarTanh.comp_aemeasurable
        (aemeasurable_scalarHiddenContinuousField P z B hB.toIsPreBrownianReal T)).sub_const
          (Real.tanh z)).pow_const 2).aestronglyMeasurable
    · apply ae_of_all
      intro u
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h := (norm_sub_le (Real.tanh (scalarHiddenContinuousField z B T u))
        (Real.tanh z)).trans (add_le_add (norm_tanh_le_one _) (norm_tanh_le_one _))
      rw [Real.norm_eq_abs] at h
      nlinarith [sq_abs (Real.tanh (scalarHiddenContinuousField z B T u) - Real.tanh z),
        abs_nonneg (Real.tanh (scalarHiddenContinuousField z B T u) - Real.tanh z)]

lemma scalarContinuousPosterior_linearForm_tendsto_L2 {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (t : ℕ → ℝ≥0)
    (a : ℕ → ℝ) (d : ℕ) :
    Tendsto (fun n => ∫ u,
      ((∑ i ∈ Finset.range d, a i *
        (scalarWeightedBrownianMeshSum scalarDefect z B n
            ⌊((n : ℝ) + 1) * (t (i+1) : ℝ)⌋₊ u -
          scalarWeightedBrownianMeshSum scalarDefect z B n
            ⌊((n : ℝ) + 1) * (t i : ℝ)⌋₊ u)) -
        (∑ i ∈ Finset.range d, a i *
          scalarContinuousPosteriorIncrement z B (t i) (t (i+1)) u)) ^ 2
      ∂scalarHiddenBrownianLaw z P) atTop (𝓝 0) := by
  let m : ℕ → ℕ → ℕ := fun n i => ⌊((n : ℝ) + 1) * (t i : ℝ)⌋₊
  let F : ℕ → ℕ → Bool × Ω → ℝ := fun i n u =>
    scalarWeightedBrownianMeshSum scalarDefect z B n (m n i) u -
      (Real.tanh (scalarHiddenContinuousField z B (t i) u) - Real.tanh z)
  have hFm (i n : ℕ) : AEMeasurable (F i n) (scalarHiddenBrownianLaw z P) :=
    (aemeasurable_scalarWeightedBrownianMeshSum P scalarDefect measurable_scalarDefect
      z B hB n _).sub ((measurable_scalarTanh.comp_aemeasurable
        (aemeasurable_scalarHiddenContinuousField P z B hB.toIsPreBrownianReal (t i))).sub_const _)
  have hFi (i n : ℕ) : Integrable (fun u => F i n u ^ 2) (scalarHiddenBrownianLaw z P) :=
    integrable_scalarPosteriorMesh_square_error P z B hB (t i) n
  have hFlim (i : ℕ) : Tendsto (fun n => ∫ u, F i n u ^ 2 ∂scalarHiddenBrownianLaw z P)
      atTop (𝓝 0) := scalarWeightedBrownianMeshSum_posterior_tendsto_L2 P z B hB (t i)
  let X : ℕ → Bool × Ω → ℝ := fun n u => ∑ i ∈ Finset.range d, a i *
    (scalarWeightedBrownianMeshSum scalarDefect z B n (m n (i+1)) u -
      scalarWeightedBrownianMeshSum scalarDefect z B n (m n i) u)
  let Y : Bool × Ω → ℝ := fun u => ∑ i ∈ Finset.range d,
    a i * scalarContinuousPosteriorIncrement z B (t i) (t (i+1)) u
  have herr (n : ℕ) (u : Bool × Ω) : X n u - Y u =
      ∑ i ∈ Finset.range d, a i * (F (i+1) n u - F i n u) := by
    dsimp [X, Y, F, scalarContinuousPosteriorIncrement]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hRlim (i : ℕ) : Tendsto
      (fun n => ∫ u, (a i * (F (i+1) n u - F i n u))^2 ∂scalarHiddenBrownianLaw z P)
      atTop (𝓝 0) := by
    have h := (tendsto_integral_sq_sub (hFm (i+1)) (hFm i) (hFi (i+1)) (hFi i)
      (hFlim (i+1)) (hFlim i)).const_mul (a i ^ 2)
    simpa only [mul_pow, integral_const_mul, mul_zero] using h
  change Tendsto (fun n => ∫ u, (X n u - Y u)^2 ∂scalarHiddenBrownianLaw z P) atTop (𝓝 0)
  simp_rw [herr]
  exact tendsto_integral_sq_finset_sum (Finset.range d)
    (fun i hi n => ((hFm (i+1) n).sub (hFm i n)).const_mul _)
    (fun i hi n => by
      simpa only [mul_pow] using
        (integrable_sq_sub (hFm (i+1) n) (hFm i n) (hFi (i+1) n) (hFi i n)).const_mul (a i ^ 2))
    (fun i hi => hRlim i)

lemma scalarContinuousPosterior_linearForm_hasSubgaussianMGF {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (a : ℕ → ℝ) (d : ℕ) :
    HasSubgaussianMGF
      (fun u => ∑ i ∈ Finset.range d,
        a i * scalarContinuousPosteriorIncrement z B (t i) (t (i+1)) u)
      (∑ i ∈ Finset.range d, ‖a i‖₊ ^ 2 * (t (i+1) - t i))
      (scalarHiddenBrownianLaw z P) := by
  let m : ℕ → ℕ → ℕ := fun n i => ⌊((n : ℝ) + 1) * (t i : ℝ)⌋₊
  have hm (n : ℕ) : Monotone (m n) := by
    intro i j hij
    apply Nat.floor_le_floor
    exact mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr (ht hij)) (by positivity)
  let F : ℕ → ℕ → Bool × Ω → ℝ := fun i n u =>
    scalarWeightedBrownianMeshSum scalarDefect z B n (m n i) u -
      (Real.tanh (scalarHiddenContinuousField z B (t i) u) - Real.tanh z)
  have hFm (i n : ℕ) : AEMeasurable (F i n) (scalarHiddenBrownianLaw z P) :=
    (aemeasurable_scalarWeightedBrownianMeshSum P scalarDefect measurable_scalarDefect
      z B hB n _).sub ((measurable_scalarTanh.comp_aemeasurable
        (aemeasurable_scalarHiddenContinuousField P z B hB.toIsPreBrownianReal (t i))).sub_const _)
  have hFi (i n : ℕ) : Integrable (fun u => F i n u ^ 2) (scalarHiddenBrownianLaw z P) :=
    integrable_scalarPosteriorMesh_square_error P z B hB (t i) n
  have hFlim (i : ℕ) : Tendsto (fun n => ∫ u, F i n u ^ 2 ∂scalarHiddenBrownianLaw z P)
      atTop (𝓝 0) := scalarWeightedBrownianMeshSum_posterior_tendsto_L2 P z B hB (t i)
  let X : ℕ → Bool × Ω → ℝ := fun n u => ∑ i ∈ Finset.range d, a i *
    (scalarWeightedBrownianMeshSum scalarDefect z B n (m n (i+1)) u -
      scalarWeightedBrownianMeshSum scalarDefect z B n (m n i) u)
  let Y : Bool × Ω → ℝ := fun u => ∑ i ∈ Finset.range d,
    a i * scalarContinuousPosteriorIncrement z B (t i) (t (i+1)) u
  let V : ℕ → ℝ≥0 := fun n => ∑ i ∈ Finset.range d, ‖a i‖₊ ^ 2 *
    (scalarUniformTime n (m n (i+1)) - scalarUniformTime n (m n i))
  have herr (n : ℕ) (u : Bool × Ω) : X n u - Y u =
      ∑ i ∈ Finset.range d, a i * (F (i+1) n u - F i n u) := by
    dsimp [X, Y, F, scalarContinuousPosteriorIncrement]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hRi (i n : ℕ) : Integrable (fun u => (a i * (F (i+1) n u - F i n u))^2)
      (scalarHiddenBrownianLaw z P) := by
    simpa only [mul_pow] using
      (integrable_sq_sub (hFm (i+1) n) (hFm i n) (hFi (i+1) n) (hFi i n)).const_mul (a i ^ 2)
  have hRlim (i : ℕ) : Tendsto
      (fun n => ∫ u, (a i * (F (i+1) n u - F i n u))^2 ∂scalarHiddenBrownianLaw z P)
      atTop (𝓝 0) := by
    have h := (tendsto_integral_sq_sub (hFm (i+1)) (hFm i) (hFi (i+1)) (hFi i)
      (hFlim (i+1)) (hFlim i)).const_mul (a i ^ 2)
    simpa only [mul_pow, integral_const_mul, mul_zero] using h
  change HasSubgaussianMGF Y _ _
  apply hasSubgaussianMGF_of_tendsto_integral_sq (X := X) (Y := Y) (V := V)
  · intro n
    exact scalarRowPosteriorMesh_hasSubgaussianMGF P z B hB n (m n) (hm n) a d
  · intro n
    simp_rw [herr]
    exact integrable_sq_finset_sum (Finset.range d)
      (fun i hi => ((hFm (i+1) n).sub (hFm i n)).const_mul _)
      (fun i hi => hRi i n)
  · simp_rw [herr]
    exact tendsto_integral_sq_finset_sum (Finset.range d)
      (fun i hi n => ((hFm (i+1) n).sub (hFm i n)).const_mul _)
      (fun i hi => hRi i) (fun i hi => hRlim i)
  · apply tendsto_finsetSum
    intro i hi
    exact tendsto_const_nhds.mul
      ((scalarUniformTime_floor_tendsto (t (i+1))).sub
        (scalarUniformTime_floor_tendsto (t i)))

@[expose] def scalarNormalizedPosteriorRow {Ω : Type*} (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0) {d : ℕ} (s : Fin d → ℝ≥0)
    (u : Bool × Ω) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i =>
    scalarContinuousPosteriorIncrement z B (t i) (t (i+1)) u / (s i : ℝ))

lemma aemeasurable_scalarNormalizedPosteriorRow {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (t : ℕ → ℝ≥0) {d : ℕ} (s : Fin d → ℝ≥0) :
    AEMeasurable (scalarNormalizedPosteriorRow z B t s) (scalarHiddenBrownianLaw z P) := by
  apply (WithLp.measurable_toLp 2 _).comp_aemeasurable
  exact AEMeasurable.of_eval (fun i =>
    (aemeasurable_scalarContinuousPosteriorIncrement P z B hB (t i) (t (i+1))).div_const _)

lemma scalarNormalizedPosteriorRow_linearForm_hasSubgaussianMGF {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (t : ℕ → ℝ≥0) (ht : Monotone t)
    {d : ℕ} (s : Fin d → ℝ≥0) (a : EuclideanSpace ℝ (Fin d)) :
    HasSubgaussianMGF (fun u => ⟪scalarNormalizedPosteriorRow z B t s u, a⟫_ℝ)
      (∑ i : Fin d, ‖a i / (s i : ℝ)‖₊ ^ 2 * (t (i+1) - t i))
      (scalarHiddenBrownianLaw z P) := by
  let b : ℕ → ℝ := fun k => if hk : k < d then a ⟨k,hk⟩ / (s ⟨k,hk⟩ : ℝ) else 0
  have h := scalarContinuousPosterior_linearForm_hasSubgaussianMGF P z B hB t ht b d
  have hv : (∑ k ∈ Finset.range d, ‖b k‖₊ ^ 2 * (t (k+1) - t k)) =
      ∑ i : Fin d, ‖a i / (s i : ℝ)‖₊ ^ 2 * (t (i+1) - t i) := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [b, Finset.mem_range.mp hk, dite_true]
  rw [hv] at h
  apply h.congr
  apply ae_of_all
  intro u
  change (∑ i ∈ Finset.range d, b i *
    scalarContinuousPosteriorIncrement z B (t i) (t (i+1)) u) =
      ⟪scalarNormalizedPosteriorRow z B t s u, a⟫_ℝ
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, Pi.star_apply, star_trivial, scalarNormalizedPosteriorRow,
    WithLp.ofLp_toLp]
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [b, Finset.mem_range.mp hk, dite_true]
  ring

lemma scalarNormalizedPosteriorRow_unit_hasSubgaussianMGF {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (t : ℕ → ℝ≥0) (ht : Monotone t)
    {d : ℕ} (s : Fin d → ℝ≥0) (hs : ∀ i, 0 < s i) (K : ℝ≥0)
    (hbudget : ∀ i : Fin d, t (i+1) - t i ≤ K * s i ^ 2)
    (a : EuclideanSpace ℝ (Fin d)) (ha : ‖a‖ ≤ 1) :
    HasSubgaussianMGF (fun u => ⟪scalarNormalizedPosteriorRow z B t s u, a⟫_ℝ)
      K (scalarHiddenBrownianLaw z P) := by
  have h := scalarNormalizedPosteriorRow_linearForm_hasSubgaussianMGF P z B hB t ht s a
  have hv : (∑ i : Fin d, ‖a i / (s i : ℝ)‖₊ ^ 2 * (t (i+1) - t i)) ≤ K := by
    apply NNReal.coe_le_coe.mp
    push_cast
    calc
      _ ≤ ∑ i : Fin d, (K : ℝ) * (a i)^2 := by
        apply Finset.sum_le_sum
        intro i hi
        have hsi : 0 < (s i : ℝ) := NNReal.coe_pos.mpr (hs i)
        have hi := NNReal.coe_le_coe.mpr (hbudget i)
        have hmul := mul_le_mul_of_nonneg_left hi (sq_nonneg (a i / (s i : ℝ)))
        rw [Real.norm_eq_abs, sq_abs]
        calc
          _ ≤ (a i / (s i : ℝ)) ^ 2 * ((K : ℝ) * (s i : ℝ)^2) := by simpa using hmul
          _ = _ := by field_simp
      _ = (K : ℝ) * ‖a‖^2 := by rw [← Finset.mul_sum, EuclideanSpace.real_norm_sq_eq]
      _ ≤ (K : ℝ) := by
        have hn : ‖a‖^2 ≤ 1 := by nlinarith [norm_nonneg a]
        simpa using mul_le_mul_of_nonneg_left hn K.coe_nonneg
  refine ⟨h.integrable_exp_mul, fun θ => (h.mgf_le θ).trans ?_⟩
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.mpr hv) (sq_nonneg θ)) (by norm_num)

end SKConstants
