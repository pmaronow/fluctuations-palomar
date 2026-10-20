module

public import SKBarriers2.Corner.FrozenRowsInduction
public import SKBarriers2.Corner.PathEnergyProof3

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

section WeightedTransport

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
private theorem integral_weight_bound {f w : Ω → ℝ} {C T : ℝ} {p : ℕ}
    (hi : Integrable (fun x => w x ^ p) μ) (hC : 0 ≤ C)
    (hf : ∀ x, |f x| ≤ C * w x ^ p) (hT : (∫ x, w x ^ p ∂μ) ≤ T) :
    |∫ x, f x ∂μ| ≤ C * T := by
  calc
    _ ≤ ∫ x, |f x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, C * w x ^ p ∂μ :=
      integral_mono_of_nonneg (ae_of_all _ (fun x => abs_nonneg _))
        (hi.const_mul C) (ae_of_all _ hf)
    _ = C * (∫ x, w x ^ p ∂μ) := integral_const_mul _ _
    _ ≤ C * T := mul_le_mul_of_nonneg_left hT hC

theorem covariance_weight_bound {f g w : Ω → ℝ} {C D T : ℝ} {p q : ℕ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hb₁ : ∀ x, |f x| ≤ C * w x ^ p) (hb₂ : ∀ x, |g x| ≤ D * w x ^ q)
    (hi₁ : Integrable (fun x => w x ^ p) μ)
    (hi₂ : Integrable (fun x => w x ^ q) μ)
    (hi₃ : Integrable (fun x => w x ^ (p + q)) μ)
    (hT₁ : (∫ x, w x ^ p ∂μ) ≤ T) (hT₂ : (∫ x, w x ^ q ∂μ) ≤ T)
    (hT₃ : (∫ x, w x ^ (p + q) ∂μ) ≤ T) (hT : 0 ≤ T) :
    |covariance f g μ| ≤ C * D * (T + T ^ 2) := by
  have hp : ∀ x, |f x * g x| ≤ (C * D) * w x ^ (p + q) := by
    intro x
    rw [abs_mul, pow_add]
    exact (mul_le_mul (hb₁ x) (hb₂ x) (abs_nonneg _) ((abs_nonneg _).trans (hb₁ x))).trans_eq
      (by ring)
  have H₁ := integral_weight_bound hi₁ hC hb₁ hT₁
  have H₂ := integral_weight_bound hi₂ hD hb₂ hT₂
  have H₃ := integral_weight_bound hi₃ (mul_nonneg hC hD) hp hT₃
  rw [covariance_eq_sub hf hg]
  simp only [Pi.mul_apply]
  calc
    _ ≤ |∫ x, f x * g x ∂μ| + |(∫ x, f x ∂μ) * (∫ x, g x ∂μ)| := abs_sub _ _
    _ ≤ C * D * T + (C * T) * (D * T) := by
      apply add_le_add H₃
      rw [abs_mul]
      exact mul_le_mul H₁ H₂ (abs_nonneg _) (mul_nonneg hC hT)
    _ = _ := by ring

def averageTransportKJet (μ : Measure Ω) (g a b s t : Ω → ℝ) : MomentKJet :=
  ⟨∫ x, g x ∂μ, (∫ x, a x ∂μ) + covariance g s μ,
    StepCalculus.secondAverageTransport μ g a b s t⟩

omit [IsProbabilityMeasure μ] in
theorem averageTransportKJet_rescale (g a b s t : Ω → ℝ) (ρ : ℝ) :
    MomentKJet.rescale ρ (averageTransportKJet μ g a b s t) =
      averageTransportKJet μ g (fun x => ρ * a x) (fun x => ρ ^ 2 * b x)
        (fun x => ρ * s x) (fun x => ρ ^ 2 * t x) := by
  unfold MomentKJet.rescale averageTransportKJet StepCalculus.secondAverageTransport
  simp only [integral_const_mul, covariance_const_mul_left, covariance_const_mul_right]
  have heq : (fun x => (ρ * s x) ^ 2) = fun x => ρ ^ 2 * s x ^ 2 := by funext x; ring
  rw [heq, covariance_const_mul_right]
  congr 1 <;> ring

def weightedTransportBudget (L T : ℝ) : ℝ :=
  let Z := T + T ^ 2
  1 + T + (T + L * Z) + (T + 3 * L * Z + L ^ 2 * Z + 2 * L ^ 2 * T * Z)

theorem weightedTransportBudget_ge_one {L T : ℝ} (hL : 0 ≤ L) (hT : 0 ≤ T) :
    1 ≤ weightedTransportBudget L T := by
  have hZ : 0 ≤ T + T ^ 2 := by positivity
  have h₁ : 0 ≤ T + L * (T + T ^ 2) := by positivity
  have h₂ : 0 ≤ T + 3 * L * (T + T ^ 2) + L ^ 2 * (T + T ^ 2) +
      2 * L ^ 2 * T * (T + T ^ 2) := by positivity
  dsimp only [weightedTransportBudget]
  linarith

theorem averageTransportKJet_weight_bound
    {g a b s t w : Ω → ℝ} {C L T R : ℝ} {p : ℕ}
    (hg : MemLp g 2 μ) (ha : MemLp a 2 μ) (hs : MemLp s 2 μ)
    (ht : MemLp t 2 μ) (hsq : MemLp (fun x => s x ^ 2) 2 μ)
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 1 ≤ R)
    (hi : ∀ q ≤ p + 4, Integrable (fun x => w x ^ q) μ)
    (hMom : ∀ q ≤ p + 4, (∫ x, w x ^ q ∂μ) ≤ T)
    (hgB : ∀ x, |g x| ≤ (C * R ^ p) * w x ^ p)
    (haB : ∀ x, |a x| ≤ (C * R ^ (p + 1)) * w x ^ (p + 2))
    (hbB : ∀ x, |b x| ≤ (C * R ^ (p + 2)) * w x ^ (p + 4))
    (hsB : ∀ x, |s x| ≤ (L * R) * w x ^ 2)
    (htB : ∀ x, |t x| ≤ (L * R ^ 2) * w x ^ 4) :
    MomentKJet.Bound (averageTransportKJet μ g a b s t)
      (weightedTransportBudget L T * C * R ^ (p + 2)) := by
  let Z := T + T ^ 2
  let D := weightedTransportBudget L T
  have hR₀ : 0 ≤ R := by linarith
  have hZ : 0 ≤ Z := by dsimp only [Z]; positivity
  have hD : 1 ≤ D := weightedTransportBudget_ge_one hL hT
  have h₀ : T ≤ D := by
    have H₁ : 0 ≤ T + L * Z := by positivity
    have H₂ : 0 ≤ T + 3 * L * Z + L ^ 2 * Z + 2 * L ^ 2 * T * Z := by positivity
    dsimp only [D, weightedTransportBudget]; dsimp only [Z] at H₁ H₂; linarith
  have h₁ : T + L * Z ≤ D := by
    have H₂ : 0 ≤ T + 3 * L * Z + L ^ 2 * Z + 2 * L ^ 2 * T * Z := by positivity
    dsimp only [D, weightedTransportBudget]; dsimp only [Z] at H₂ ⊢; linarith
  have h₂ : T + 3 * L * Z + L ^ 2 * Z + 2 * L ^ 2 * T * Z ≤ D := by
    have H₁ : 0 ≤ T + L * Z := by positivity
    dsimp only [D, weightedTransportBudget]; dsimp only [Z] at H₁ ⊢; linarith
  have hsqB (x : Ω) : |s x ^ 2| ≤ (L ^ 2 * R ^ 2) * w x ^ 4 := by
    rw [abs_pow]
    exact (pow_le_pow_left₀ (abs_nonneg _) (hsB x) 2).trans_eq (by ring)
  have hEg := integral_weight_bound (hi p (by omega)) (by positivity : 0 ≤ C * R ^ p)
    hgB (hMom p (by omega))
  have hEa := integral_weight_bound (hi (p + 2) (by omega)) (by positivity : 0 ≤ C * R ^ (p + 1))
    haB (hMom (p + 2) (by omega))
  have hEb := integral_weight_bound (hi (p + 4) le_rfl) (by positivity : 0 ≤ C * R ^ (p + 2))
    hbB (hMom (p + 4) le_rfl)
  have hEs := integral_weight_bound (hi 2 (by omega)) (by positivity : 0 ≤ L * R)
    hsB (hMom 2 (by omega))
  have hgs := covariance_weight_bound hg hs (by positivity) (by positivity) hgB hsB
    (hi p (by omega)) (hi 2 (by omega)) (hi (p + 2) (by omega))
    (hMom p (by omega)) (hMom 2 (by omega)) (hMom (p + 2) (by omega)) hT
  have has := covariance_weight_bound ha hs (by positivity) (by positivity) haB hsB
    (hi (p + 2) (by omega)) (hi 2 (by omega)) (hi ((p + 2) + 2) (by omega))
    (hMom (p + 2) (by omega)) (hMom 2 (by omega)) (hMom ((p + 2) + 2) (by omega)) hT
  have hgt := covariance_weight_bound hg ht (by positivity) (by positivity) hgB htB
    (hi p (by omega)) (hi 4 (by omega)) (hi (p + 4) le_rfl)
    (hMom p (by omega)) (hMom 4 (by omega)) (hMom (p + 4) le_rfl) hT
  have hgsq := covariance_weight_bound hg hsq (by positivity) (by positivity) hgB hsqB
    (hi p (by omega)) (hi 4 (by omega)) (hi (p + 4) le_rfl)
    (hMom p (by omega)) (hMom 4 (by omega)) (hMom (p + 4) le_rfl) hT
  have hlast : |2 * (∫ x, s x ∂μ) * covariance g s μ| ≤
      2 * ((L * R) * T) * ((C * R ^ p) * (L * R) * Z) := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hEs (by norm_num)) hgs
      (abs_nonneg _) (by positivity)
  refine ⟨?_, ?_, ?_⟩
  · exact hEg.trans (by
      calc
        _ = T * C * R ^ p := by ring
        _ ≤ D * C * R ^ (p + 2) := mul_le_mul
          (mul_le_mul_of_nonneg_right h₀ hC) (pow_le_pow_right₀ hR (by omega))
          (pow_nonneg hR₀ _) (by positivity))
  · have H := (abs_add_le _ _).trans (add_le_add hEa hgs)
    apply H.trans
    calc
      _ = (T + L * Z) * C * R ^ (p + 1) := by dsimp only [Z]; rw [pow_succ]; ring
      _ ≤ D * C * R ^ (p + 2) := mul_le_mul
        (mul_le_mul_of_nonneg_right h₁ hC) (pow_le_pow_right₀ hR (by omega))
        (pow_nonneg hR₀ _) (by positivity)
  · change |StepCalculus.secondAverageTransport μ g a b s t| ≤ _
    have htwo : |2 * covariance a s μ| ≤ 2 * ((C * R ^ (p + 1)) * (L * R) * Z) := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact mul_le_mul_of_nonneg_left has (by norm_num)
    have htri (u v w x y : ℝ) : |u + v + w + x - y| ≤ |u| + |v| + |w| + |x| + |y| :=
      (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add
        ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)) le_rfl)
    unfold StepCalculus.secondAverageTransport
    apply (htri _ _ _ _ _).trans
    apply (add_le_add (add_le_add (add_le_add (add_le_add hEb htwo) hgt) hgsq) hlast).trans
    calc
      _ = (T + 3 * L * Z + L ^ 2 * Z + 2 * L ^ 2 * T * Z) * C * R ^ (p + 2) := by
        dsimp only [Z]
        simp only [pow_add, pow_one]
        ring
      _ ≤ D * C * R ^ (p + 2) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right h₂ hC) (pow_nonneg hR₀ _)

end WeightedTransport

section ActualTransport

variable {P X : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

private theorem parametric_noise_memLp {H W : P × (X × ℝ) → ℝ}
    (hH : ParamRegular H) (hW : ParamExpGrowth W) (hc : Continuous W) (q : P) (x : X) :
    MemLp (fun t => W (q, (x, t))) 2
      (gaussianStepLaw 1 (fun z : (P × X) × ℝ => H (z.1.1, (z.1.2, z.2))) (q, x)) := by
  rw [memLp_two_iff_integrable_sq]
  · simpa only [pow_two] using
      (hW.mul hW).integrable_paramStepLaw hH (hc.mul hc) 1 (q, x)
  · exact (hc.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))).aestronglyMeasurable

theorem gaussian_curve_jets_memLp {H W : P × (X × ℝ) → ℝ}
    (hH : ParamRegular H) (hW : ParamSmooth W) {p : ℝ → P} {k : ℝ}
    (hp : ContDiffAt ℝ 2 p k) (x : X) :
    let μ := gaussianStepLaw 1 (fun z : (P × X) × ℝ => H (z.1.1, (z.1.2, z.2))) (p k, x)
    MemLp (fun t => W (p k, (x, t))) 2 μ ∧
      MemLp (fun t => deriv (fun q => W (p q, (x, t))) k) 2 μ ∧
      MemLp (fun t => deriv (deriv (fun q => W (p q, (x, t)))) k) 2 μ ∧
      MemLp (fun t => (deriv (fun q => W (p q, (x, t))) k) ^ 2) 2 μ := by
  let u := deriv p k
  let b := deriv (deriv p) k
  let W₁ := fun z : P × (X × ℝ) => fderiv ℝ W z (u, 0)
  let W₂ := fun z : P × (X × ℝ) =>
    fderiv ℝ (fderiv ℝ W) z (u, 0) (u, 0) + fderiv ℝ W z (b, 0)
  have hg₁ : ParamExpGrowth W₁ := hW.2.2.1.clm (ContinuousLinearMap.apply ℝ ℝ (u, 0))
  have hc₁ : Continuous W₁ :=
    (hW.1.fderiv_right (m := 1) (by norm_num)).continuous.clm_apply continuous_const
  have hgDD : ParamExpGrowth (fun z : P × (X × ℝ) =>
      fderiv ℝ (fderiv ℝ W) z (u, 0) (u, 0)) := by
    apply hW.2.2.2.of_norm_le (K := ‖(u, (0 : X × ℝ))‖ ^ 2) (sq_nonneg _)
    intro z
    exact (((fderiv ℝ (fderiv ℝ W) z) (u, 0)).le_opNorm (u, 0)).trans
      ((mul_le_mul_of_nonneg_right ((fderiv ℝ (fderiv ℝ W) z).le_opNorm (u, 0))
        (norm_nonneg _)).trans_eq (by ring))
  have hgD : ParamExpGrowth (fun z : P × (X × ℝ) => fderiv ℝ W z (b, 0)) :=
    hW.2.2.1.clm (ContinuousLinearMap.apply ℝ ℝ (b, (0 : X × ℝ)))
  have hg₂ : ParamExpGrowth W₂ := hgDD.add hgD
  have hc₂ : Continuous W₂ :=
    (((hW.1.fderiv_right (m := 1) (by norm_num) |>.fderiv_right (m := 0) (by norm_num)).continuous.clm_apply
      continuous_const).clm_apply continuous_const).add
      ((hW.1.fderiv_right (m := 1) (by norm_num)).continuous.clm_apply continuous_const)
  have he₁ (t : ℝ) : deriv (fun q => W (p q, (x, t))) k = W₁ (p k, (x, t)) :=
    ((hW.1.differentiable (by norm_num) (p k, (x, t))).hasFDerivAt.comp_hasDerivAt k
      ((hp.differentiableAt (by norm_num)).hasDerivAt.prodMk (hasDerivAt_const k (x, t)))).deriv
  have he₂ (t : ℝ) : deriv (deriv (fun q => W (p q, (x, t)))) k = W₂ (p k, (x, t)) :=
    ParamChain.second_parameter_curve hW.1 hp (x, t)
  simp_rw [he₁, he₂]
  refine ⟨parametric_noise_memLp hH hW.2.1 hW.1.continuous _ _,
    parametric_noise_memLp hH hg₁ hc₁ _ _, parametric_noise_memLp hH hg₂ hc₂ _ _, ?_⟩
  simpa only [pow_two] using parametric_noise_memLp hH (hg₁.mul hg₁) (hc₁.mul hc₁) (p k) x

theorem gaussianAverage_curve_transportKJet {H G : P × (X × ℝ) → ℝ}
    (hH : ParamRegular H) (hG : ParamSmooth G) {p : ℝ → P} {k : ℝ}
    (hp : ContDiffAt ℝ 2 p k) (x : X) :
    let U := fun z : (P × X) × ℝ => H (z.1.1, (z.1.2, z.2))
    let J := fun z : (P × X) × ℝ => G (z.1.1, (z.1.2, z.2))
    let μ := gaussianStepLaw 1 U (p k, x)
    let A := fun q => OAI.SK.Analytic.gaussianAverage 1 U J (p q, x)
    MomentKJet.mk (A k) (deriv A k) (deriv (deriv A) k) =
      averageTransportKJet μ (fun t => G (p k, (x, t)))
        (fun t => deriv (fun q => G (p q, (x, t))) k)
        (fun t => deriv (deriv (fun q => G (p q, (x, t)))) k)
        (fun t => deriv (fun q => H (p q, (x, t))) k)
        (fun t => deriv (deriv (fun q => H (p q, (x, t)))) k) := by
  dsimp only
  have hGm := gaussian_curve_jets_memLp hH hG hp x
  have hHm := gaussian_curve_jets_memLp hH hH.toSmooth hp x
  have hfirst := ParamChain.gaussianAverage_curve_first hH hG hp x
  have hsecond := ParamChain.gaussianAverage_curve_second_covariance hH hG hp x
  dsimp only at hGm hHm hfirst hsecond
  have hexp := (hH.2.1.exp_mul 1).weakLocallyDominated.integrable_section
    (Real.continuous_exp.comp (continuous_const.mul (hH.1.continuous.comp
      (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))))) (p k, x)
  let : IsProbabilityMeasure
      (gaussianStepLaw 1 (fun z : (P × X) × ℝ => H (z.1.1, (z.1.2, z.2))) (p k, x)) :=
    isProbabilityMeasure_tilted hexp
  unfold averageTransportKJet
  congr 1
  · have hprod : Integrable (fun t => G (p k, (x, t)) *
        deriv (fun q => H (p q, (x, t))) k)
        (gaussianStepLaw 1 (fun z : (P × X) × ℝ => H (z.1.1, (z.1.2, z.2))) (p k, x)) :=
      (hGm.1.integrable_mul hHm.2.1).congr (ae_of_all _ (fun _ => by simp only [Pi.mul_apply]))
    rw [hfirst, integral_add (hGm.2.1.integrable (by norm_num)) hprod,
      covariance_eq_sub hGm.1 hHm.2.1]
    simp only [Pi.mul_apply]
    ring
  · exact hsecond.2

end ActualTransport

section ScaledActualTransport

variable {P X : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem gaussianAverage_curve_scaled_weight_bound {H G : P × (X × ℝ) → ℝ}
    (hH : ParamRegular H) (hG : ParamSmooth G) {p : ℝ → P} {k : ℝ}
    (hp : ContDiffAt ℝ 2 p k) (x : X) {C L T R ρ : ℝ} {d : ℕ} (w : ℝ → ℝ)
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 1 ≤ R) :
    let U := fun z : (P × X) × ℝ => H (z.1.1, (z.1.2, z.2))
    let J := fun z : (P × X) × ℝ => G (z.1.1, (z.1.2, z.2))
    let μ := gaussianStepLaw 1 U (p k, x)
    let A := fun q => OAI.SK.Analytic.gaussianAverage 1 U J (p q, x)
    (∀ q ≤ d + 4, Integrable (fun t => w t ^ q) μ) →
    (∀ q ≤ d + 4, (∫ t, w t ^ q ∂μ) ≤ T) →
    (∀ t, |G (p k, (x, t))| ≤ (C * R ^ d) * w t ^ d) →
    (∀ t, |ρ * deriv (fun q => G (p q, (x, t))) k| ≤
      (C * R ^ (d + 1)) * w t ^ (d + 2)) →
    (∀ t, |ρ ^ 2 * deriv (deriv (fun q => G (p q, (x, t)))) k| ≤
      (C * R ^ (d + 2)) * w t ^ (d + 4)) →
    (∀ t, |ρ * deriv (fun q => H (p q, (x, t))) k| ≤ (L * R) * w t ^ 2) →
    (∀ t, |ρ ^ 2 * deriv (deriv (fun q => H (p q, (x, t)))) k| ≤
      (L * R ^ 2) * w t ^ 4) →
    MomentKJet.Bound (MomentKJet.rescale ρ ⟨A k, deriv A k, deriv (deriv A) k⟩)
      (weightedTransportBudget L T * C * R ^ (d + 2)) := by
  dsimp only
  intro hi hMom hgB haB hbB hsB htB
  have hGm := gaussian_curve_jets_memLp hH hG hp x
  have hHm := gaussian_curve_jets_memLp hH hH.toSmooth hp x
  dsimp only at hGm hHm
  have hexp := (hH.2.1.exp_mul 1).weakLocallyDominated.integrable_section
    (Real.continuous_exp.comp (continuous_const.mul (hH.1.continuous.comp
      (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))))) (p k, x)
  let : IsProbabilityMeasure
      (gaussianStepLaw 1 (fun z : (P × X) × ℝ => H (z.1.1, (z.1.2, z.2))) (p k, x)) :=
    isProbabilityMeasure_tilted hexp
  rw [gaussianAverage_curve_transportKJet hH hG hp x, averageTransportKJet_rescale]
  have hsq : MemLp (fun t => (ρ * deriv (fun q => H (p q, (x, t))) k) ^ 2) 2
      (gaussianStepLaw 1 (fun z : (P × X) × ℝ => H (z.1.1, (z.1.2, z.2))) (p k, x)) := by
    convert hHm.2.2.2.const_mul (ρ ^ 2) using 1
    funext t
    ring
  exact averageTransportKJet_weight_bound hGm.1 (hGm.2.1.const_mul ρ) (hHm.2.1.const_mul ρ)
    (hHm.2.2.1.const_mul (ρ ^ 2)) hsq hC hL hT hR hi hMom hgB haB hbB hsB htB

theorem weightedTransport_to_row_weight {J : MomentKJet} {D M K g : ℝ} {n : ℕ}
    (hD : 1 ≤ D) (hM : 0 ≤ M) (hK : 0 ≤ K) (hn : 1 ≤ n)
    (H : MomentKJet.Bound J (D * M ^ n * ((K + 1) * (1 + |g|)) ^ (3 * n + 2))) :
    MomentKJet.Bound J
      ((D * M * (2 * (K + 1) ^ 2) ^ 3 * (1 + g ^ 2) ^ 3) ^ n) := by
  have hR : 1 ≤ (K + 1) * (1 + |g|) :=
    one_le_mul_of_one_le_of_one_le (by linarith) (by linarith [abs_nonneg g])
  have hD₀ : 0 ≤ D := by linarith
  have hDpow : D ≤ D ^ n := by
    simpa only [pow_one] using pow_le_pow_right₀ hD hn
  have hsquare : ((K + 1) * (1 + |g|)) ^ 2 ≤
      (2 * (K + 1) ^ 2) * (1 + g ^ 2) := by
    have H' : (1 + |g|) ^ 2 ≤ 2 * (1 + g ^ 2) := by
      nlinarith [sq_nonneg (|g| - 1), sq_abs g]
    simpa only [mul_pow, mul_assoc, mul_left_comm (2 : ℝ) ((K + 1) ^ 2)] using
      mul_le_mul_of_nonneg_left H' (sq_nonneg (K + 1))
  apply H.mono
  calc
    _ ≤ D ^ n * M ^ n * ((K + 1) * (1 + |g|)) ^ (6 * n) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right hDpow (pow_nonneg hM _)
      · exact pow_le_pow_right₀ hR (by omega)
      · positivity
      · positivity
    _ = D ^ n * M ^ n * (((K + 1) * (1 + |g|)) ^ 2) ^ (3 * n) := by
      rw [← pow_mul]
      congr 2
      omega
    _ ≤ D ^ n * M ^ n * ((2 * (K + 1) ^ 2) * (1 + g ^ 2)) ^ (3 * n) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sq_nonneg _) hsquare _) (by positivity)
    _ = _ := by
      simp only [mul_pow, pow_mul]
      ring

end ScaledActualTransport

section FrozenNoiseMoments

theorem qPotential_noise_weight_moments {B K m : ℝ} {f : Vec3 → ℝ}
    (hf : QPotential 3 B f) (hm : m ∈ Icc (0 : ℝ) 1) (hK : 0 ≤ K)
    (v : Vec3) (hv : ‖v‖ ≤ K) (x : Vec3) (N : ℕ) :
    ∀ q ≤ N,
      Integrable (fun t : ℝ => (1 + |t|) ^ q) (StepCalculus.stepLaw m v f x) ∧
        (∫ t : ℝ, (1 + |t|) ^ q ∂StepCalculus.stepLaw m v f x) ≤
          gaussianTiltPolynomialConstant (B * K) N := by
  let g : ℝ → ℝ := fun t => m * f (x + t • v)
  have hg : Continuous g := continuous_const.mul (hf.smooth.continuous.comp
    (continuous_const.add (continuous_id.smul continuous_const)))
  have hbound (t : ℝ) : |g t - g 0| ≤ (B * K) * |t| := by
    simp only [g, zero_smul, add_zero, ← mul_sub, abs_mul, abs_of_nonneg hm.1]
    have H := (hf.lipschitzWith (by norm_num : 1 ≤ 3)).norm_sub_le (x + t • v) x
    change |f (x + t • v) - f x| ≤ B * ‖x + t • v - x‖ at H
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at H
    calc
      _ ≤ m * (B * (|t| * ‖v‖)) := mul_le_mul_of_nonneg_left H hm.1
      _ ≤ B * (|t| * ‖v‖) := mul_le_of_le_one_left (by positivity [hf.nonneg]) hm.2
      _ ≤ B * (|t| * K) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hv (abs_nonneg t)) hf.nonneg
      _ = _ := by ring
  have hN := gaussian_tilt_polynomial_bound hg (mul_nonneg hf.nonneg hK) hbound N
  intro q hq
  have hq' := gaussian_tilt_polynomial_bound hg (mul_nonneg hf.nonneg hK) hbound q
  refine ⟨hq'.1, ?_⟩
  exact (integral_mono hq'.1 hN.1 (fun t =>
    pow_le_pow_right₀ (by linarith [abs_nonneg t]) hq)).trans hN.2

theorem scalarData_frozen_normalized_noise_moments {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) (N : ℕ) :
    ∃ h₀ T : ℝ, 0 < h₀ ∧ 1 ≤ T ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ k : ℝ, |k| ≤ 1 / 2 → ∀ z : ℝ,
      ∀ ε ∈ Icc (-1 : ℝ) 2, ∀ w t,
        w :: t <:+ frozenSchedule β (cdf (D.μ : Measure ℝ) (r - h)) (1 / 2) h k →
        ∀ x : Vec3, ∀ q ≤ N,
        let Q := terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) (r - h) h z
        let P := riccatiRecursion t (Q.scale (1 - ε))
        let R := spatialRescale (Real.sqrt h) (fun _ => z)
          (epsilonFrameResidual t Q (frozenTerminal β (cdf (D.μ : Measure ℝ)) (r - h) h) ε)
        let v := (Real.sqrt h)⁻¹ • ((Real.sqrt (P.precision w.1 w.2)⁻¹) • w.2)
        Integrable (fun g : ℝ => (1 + |g|) ^ q) (StepCalculus.stepLaw w.1 v R x) ∧
          (∫ g : ℝ, (1 + |g|) ^ q ∂StepCalculus.stepLaw w.1 v R x) ≤ T := by
  rcases scalarData_frozen_suffix_lipschitz_frames D hl hu with ⟨hF, L, hhF, _, HF⟩
  rcases scalarData_frozen_scaled_frame_qPotential D hl hu 3 (by norm_num) with
    ⟨C, hR, hC, hhR, HR⟩
  let K := 6 * (|β| + 1)
  let T := 1 + gaussianTiltPolynomialConstant (C * (2 * K)) N
  have hK : 0 < K := by dsimp only [K]; positivity
  have hT : 1 ≤ T := by
    have H := gaussianTiltPolynomialConstant_pos (C * (2 * K)) N
    dsimp only [T]
    linarith
  let h₀ := min hF (min hR (l / 2))
  refine ⟨h₀, T, lt_min hhF (lt_min hhR (by positivity)), hT, ?_⟩
  intro r hr h hh hhsmall k hk z ε hε w t ht x q hq
  have hhF' : h ≤ hF := hhsmall.trans (min_le_left _ _)
  have hhR' : h ≤ hR := (hhsmall.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhl : h ≤ l / 2 := (hhsmall.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hs : 0 < r - h := by linarith [hr.1]
  let α := cdf (D.μ : Measure ℝ)
  let Q := terminalTaylorQuadratic β α (r - h) h z
  let P := riccatiRecursion t (Q.scale (1 - ε))
  let R := spatialRescale (Real.sqrt h) (fun _ => z)
    (epsilonFrameResidual t Q (frozenTerminal β α (r - h) h) ε)
  let v := (Real.sqrt h)⁻¹ • ((Real.sqrt (P.precision w.1 w.2)⁻¹) • w.2)
  have htt := (List.suffix_cons w t).trans ht
  have hf : QPotential 3 C R := HR r hr h hh hhR' k hk z ε hε t htt
  have hm := frozenSchedule_masses β (α (r - h)) (1 / 2) h k
    ⟨scalarData_cdf_pos_of_pos D hs, cdf_le_one _ _⟩ w (ht.subset List.mem_cons_self)
  have hD : 1 / 2 ≤ P.precision w.1 w.2 :=
    (HF r hr h hh hhF' k hk z ε hε (w :: t) ht).2.1 _ List.mem_cons_self
  have hDpos : 0 < P.precision w.1 w.2 := by linarith
  have hInv : (P.precision w.1 w.2)⁻¹ ≤ 2 := by
    have H := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) hD
    norm_num at H
    exact H
  have hsqrt : Real.sqrt (P.precision w.1 w.2)⁻¹ ≤ 2 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hdir := (frozenSchedule_centered_direction_scale hh.le hk (ht.subset List.mem_cons_self)).1
  have hv : ‖v‖ ≤ 2 * K := by
    dsimp only [v]
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr hh)),
      abs_of_nonneg (Real.sqrt_nonneg _)]
    calc
      _ ≤ (Real.sqrt h)⁻¹ * (2 * (K * Real.sqrt h)) := by gcongr
      _ = _ := by field_simp [(Real.sqrt_pos.mpr hh).ne']
  have H := qPotential_noise_weight_moments hf ⟨hm.1.le, hm.2⟩ (by positivity : 0 ≤ 2 * K)
    v hv x N q hq
  refine ⟨H.1, H.2.trans ?_⟩
  dsimp only [T]
  linarith

end FrozenNoiseMoments

section SpatialNoiseTransport

private theorem transport_anchor_density {r : ℕ} {B m : ℝ} {f : Vec3 → ℝ}
    (hf : QPotential (r + 1) B f) (hm : m ∈ Icc (0 : ℝ) 1)
    (v : Vec3) (hv : ‖v‖ ≤ 1) (t : ℝ) :
    QBoundedJets r (StepCalculus.anchorJetCoefficient r B * Real.exp ((B + r) * |t|))
      (fun x => Real.exp (m * (f (x + t • v) - f x))) := by
  have hB := hf.nonneg
  have H : QBoundedJets r (B * |t|) (fun x => m * (f (x + t • v) - f x)) := by
    apply ((hf.increment (t • v)).const_smul m).mono
    rw [abs_of_nonneg hm.1, norm_smul, Real.norm_eq_abs]
    apply (mul_le_of_le_one_left (by positivity) hm.2).trans
    exact mul_le_mul_of_nonneg_left
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hv (abs_nonneg t)) hB
  apply H.exp.mono
  have hpow : (1 + B * |t|) ^ r ≤ (1 + B) ^ r * Real.exp ((r : ℝ) * |t|) := by
    have hbase : 1 + B * |t| ≤ (1 + B) * Real.exp |t| := by
      have H₁ := Real.add_one_le_exp |t|
      have H₂ := Real.one_le_exp (abs_nonneg t)
      nlinarith [mul_le_mul_of_nonneg_left (show |t| ≤ Real.exp |t| by linarith) hB]
    have H₁ := pow_le_pow_left₀ (by positivity) hbase r
    simpa only [mul_pow, ← Real.exp_nat_mul] using H₁
  calc
    _ ≤ (r.factorial : ℝ) * Real.exp (B * |t|) *
        ((1 + B) ^ r * Real.exp ((r : ℝ) * |t|)) := by gcongr
    _ = _ := by
      dsimp only [StepCalculus.anchorJetCoefficient]
      rw [add_mul, Real.exp_add]
      ring

theorem wJets_noiseMean_weighted {r p q : ℕ} {B C m : ℝ} {f : Vec3 → ℝ}
    (hf : QPotential (r + 1) B f) (hC : 0 ≤ C) {g : Vec3 → ℝ → ℝ}
    (hg : ContDiff ℝ r (fun z : ℝ × Vec3 => g z.2 z.1))
    (hgj : ∀ t, WJets r (C * (1 + |t|) ^ q) p (fun x => g x t))
    (hm : m ∈ Icc (0 : ℝ) 1) (v : Vec3) (hv : ‖v‖ ≤ 1) :
    WJets r (StepCalculus.noiseAverageCoefficient r q B * C) p
      (fun x => StepCalculus.noiseMean m v f x (g x)) := by
  have hB := hf.nonneg
  let A := StepCalculus.anchorJetCoefficient r B
  have hA : 0 ≤ A := by dsimp only [A, StepCalculus.anchorJetCoefficient]; positivity
  let b : ℝ → ℝ := fun t => (2 : ℝ) ^ r * C * A * Real.exp ((B + r + q) * |t|)
  have hNum (t : ℝ) : WJets r (b t) p
      (fun x => g x t * Real.exp (m * (f (x + t • v) - f x))) := by
    have H := (hgj t).mul ((transport_anchor_density hf hm v hv t).weighted (p := 0))
    apply H.mono _ (by simp)
    have hpow : (1 + |t|) ^ q ≤ Real.exp ((q : ℝ) * |t|) := by
      rw [Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by positivity)
        (by simpa only [add_comm] using Real.add_one_le_exp |t|) q
    calc
      _ ≤ (2 : ℝ) ^ r * (C * Real.exp ((q : ℝ) * |t|)) *
          (A * Real.exp ((B + r) * |t|)) := by gcongr
      _ = b t := by
        dsimp only [b]
        rw [show (B + (r : ℝ) + q) * |t| = (q : ℝ) * |t| + (B + r) * |t| by ring,
          Real.exp_add]
        ring
  have hExp : ContDiff ℝ r (fun z : ℝ × Vec3 =>
      Real.exp (m * (f (z.2 + z.1 • v) - f z.2))) :=
    (((contDiff_const.mul ((hf.smooth.comp (contDiff_snd.add
      (contDiff_fst.smul contDiff_const))).sub (hf.smooth.comp contDiff_snd))).exp).of_le
        (by exact_mod_cast Nat.le_succ r))
  have hN := WJets.integral (gaussianReal 0 1) (hg.mul hExp) hNum
    ((integrable_exp_mul_abs_gaussian (B + r + q)).const_mul ((2 : ℝ) ^ r * C * A))
  have hP := hN.mul ((StepCalculus.qBoundedJets_inv_anchorPartition hf hm v hv).weighted (p := 0))
  have heq : (fun x => StepCalculus.noiseMean m v f x (g x)) = fun x =>
      (∫ t, g x t * Real.exp (m * (f (x + t • v) - f x)) ∂gaussianReal 0 1) *
        (StepCalculus.anchorPartition m v f x)⁻¹ := by
    funext x
    rw [StepCalculus.noiseMean_anchor, div_eq_mul_inv]
  rw [heq]
  convert hP using 1
  dsimp only [b, StepCalculus.noiseAverageCoefficient, StepCalculus.gaussianExpMoment, A]
  rw [integral_const_mul]
  ring

theorem wJets_noiseMean_weighted_boundedNoise {r p q : ℕ} {B C m K : ℝ} {f : Vec3 → ℝ}
    (hf : QPotential (r + 1) B f) (hC : 0 ≤ C) {g : Vec3 → ℝ → ℝ}
    (hg : ContDiff ℝ r (fun z : ℝ × Vec3 => g z.2 z.1))
    (hgj : ∀ t, WJets r (C * (1 + |t|) ^ q) p (fun x => g x t))
    (hm : m ∈ Icc (0 : ℝ) 1) (hK : 1 ≤ K) (v : Vec3) (hv : ‖v‖ ≤ K) :
    WJets r (StepCalculus.noiseAverageCoefficient r q (B * K ^ (r + 1)) *
      (C * K ^ (p + r))) p (fun x => StepCalculus.noiseMean m v f x (g x)) := by
  have hK₀ : 0 < K := by linarith
  have hKi : |K⁻¹| ≤ 1 := by
    rw [abs_of_pos (inv_pos.mpr hK₀)]
    exact (inv_le_one₀ hK₀).mpr hK
  have hv' : ‖K⁻¹ • v‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hK₀)]
    exact (mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr hK₀.le)).trans_eq
      (inv_mul_cancel₀ hK₀.ne')
  have hg' : ContDiff ℝ r (fun z : ℝ × Vec3 => g (K • z.2) z.1) :=
    hg.comp (contDiff_fst.prodMk (contDiff_snd.const_smul K))
  have hgj' (t : ℝ) : WJets r ((C * K ^ (p + r)) * (1 + |t|) ^ q) p
      (fun x => g (K • x) t) := by
    convert (hgj t).dilate hK using 1
    · ring
    · funext x
      simp only [spatialRescale, add_zero]
  have H := (wJets_noiseMean_weighted (hf.dilate hK) (by positivity : 0 ≤ C * K ^ (p + r))
    hg' hgj' hm (K⁻¹ • v) hv').spatialContract hKi
  have heq : spatialRescale K⁻¹ 0
      (fun x => StepCalculus.noiseMean m (K⁻¹ • v) (spatialRescale K 0 f) x
        (fun t => g (K • x) t)) = fun x => StepCalculus.noiseMean m v f x (g x) := by
    funext x
    simp only [spatialRescale, StepCalculus.noiseMean, StepCalculus.stepLaw, gaussianStepLaw,
      Function.comp_apply, vectorTranslation, add_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', add_zero]
    have hpoint (a : ℝ) : K • (K⁻¹ • x + a • (K⁻¹ • v)) = x + a • v := by
      simp only [smul_add, smul_smul, mul_left_comm K a,
        mul_inv_cancel₀ hK₀.ne', one_smul, mul_one]
    simp only [smul_smul] at hpoint
    simp only [hpoint, smul_smul, mul_inv_cancel₀ hK₀.ne', one_smul]
  rw [heq] at H
  exact H

end SpatialNoiseTransport

end SKBarriers2.Corner
