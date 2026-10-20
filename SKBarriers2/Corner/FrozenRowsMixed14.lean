module

public import SKBarriers2.Corner.FrozenRowsMixed13

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic

namespace SKBarriers2.StepCalculus
local notation "X" => (Fin 3 → ℝ)

theorem noiseMean_quadratic_decomposition {r q : ℕ} {B L m δ : ℝ} {f : X → ℝ}
    {t₀ t₁ t₂ : ℝ → X → ℝ} (hf : QPotential (r + 2) B f) (hL : 0 ≤ L)
    (ht₀ : ContDiff ℝ r (Function.uncurry t₀))
    (ht₁ : ContDiff ℝ r (Function.uncurry t₁))
    (ht₂ : ContDiff ℝ r (Function.uncurry t₂))
    (ht₀j : ∀ t, WJets r (L * (1 + |t|) ^ q) 0 (t₀ t))
    (ht₁j : ∀ t, WJets r (L * (1 + |t|) ^ q) 1 (t₁ t))
    (ht₂j : ∀ t, WJets r (L * (1 + |t|) ^ q) 2 (t₂ t))
    (v : X) (A : X →L[ℝ] X) (b : X) :
    (fun x => noiseMean m v f (A x + b)
      (fun t => t₀ t x + δ * t₁ t x + δ ^ 2 * t₂ t x)) =
      fun x => noiseMean m v f (A x + b) (fun t => t₀ t x) +
        δ * noiseMean m v f (A x + b) (fun t => t₁ t x) +
        δ ^ 2 * noiseMean m v f (A x + b) (fun t => t₂ t x) := by
  funext x
  have h₀ := integrable_noise_weightedFamily (m := m) hf hL ht₀ ht₀j v (A x + b) x
  have h₁ := (integrable_noise_weightedFamily (m := m) hf hL ht₁ ht₁j v (A x + b) x).const_mul δ
  have h₂ := (integrable_noise_weightedFamily (m := m) hf hL ht₂ ht₂j v (A x + b) x).const_mul (δ ^ 2)
  have h₀₁ : Integrable (fun t => t₀ t x + δ * t₁ t x) (stepLaw m v f (A x + b)) := by
    convert h₀.add h₁ using 1
  unfold noiseMean
  rw [integral_add h₀₁ h₂, integral_add h₀ h₁, integral_const_mul, integral_const_mul]

theorem wJets_noiseMean_small_quadratic_covariance {r n q : ℕ} {B C L m δ : ℝ}
    {f : X → ℝ} {G t₀ t₁ t₂ : ℝ → X → ℝ}
    (hf : QPotential (r + 2) B f) (hC : 0 ≤ C) (hL : 0 ≤ L) (hδ : |δ| ≤ 1)
    (hG : ContDiff ℝ r (Function.uncurry G))
    (ht₀ : ContDiff ℝ r (Function.uncurry t₀))
    (ht₁ : ContDiff ℝ r (Function.uncurry t₁))
    (ht₂ : ContDiff ℝ r (Function.uncurry t₂))
    (hGj : ∀ t, WJets r (C * (1 + |t|) ^ q) (n + 2) (G t))
    (hδGj : ∀ t, WJets r (C * (1 + |t|) ^ q) n (fun x => δ * G t x))
    (ht₀j : ∀ t, WJets r (L * (1 + |t|) ^ q) 0 (t₀ t))
    (ht₁j : ∀ t, WJets r (L * (1 + |t|) ^ q) 1 (t₁ t))
    (ht₂j : ∀ t, WJets r (L * (1 + |t|) ^ q) 2 (t₂ t))
    (hm : m ∈ Icc (0 : ℝ) 1) (v : X) (hv : ‖v‖ ≤ 1)
    (A : X →L[ℝ] X) (b : X) :
    let K := affineNoiseAverageCoefficient r q B A
    let K₂ := affineNoiseAverageCoefficient r (q + q) B A
    WJets r (3 * (2 : ℝ) ^ r * (K₂ + K ^ 2) * C * L) (n + 2)
      (fun x => noiseMean m v f (A x + b)
          (fun t => G t x * (t₀ t x + δ * t₁ t x + δ ^ 2 * t₂ t x)) -
        noiseMean m v f (A x + b) (fun t => G t x) *
          noiseMean m v f (A x + b) (fun t => t₀ t x + δ * t₁ t x + δ ^ 2 * t₂ t x)) := by
  let K := affineNoiseAverageCoefficient r q B A
  let K₂ := affineNoiseAverageCoefficient r (q + q) B A
  let T : ℝ → X → ℝ := fun t x => t₀ t x + δ * t₁ t x + δ ^ 2 * t₂ t x
  let Ac : X → ℝ := fun x => noiseMean m v f (A x + b) (fun t => G t x)
  let At : X → ℝ := fun x => noiseMean m v f (A x + b) (fun t => T t x)
  have hAc : WJets r (K * C) (n + 2) Ac :=
    wJets_noiseMean_affine_family hf hC hG hGj hm v hv A b
  have hδAc : WJets r (K * C) n (fun x => δ * Ac x) :=
    wJets_noiseMean_affine_family_scaled hf hC hG hδGj hm v hv A b
  have hAt₀ := wJets_noiseMean_affine_family hf hL ht₀ ht₀j hm v hv A b
  have hAt₁ := wJets_noiseMean_affine_family hf hL ht₁ ht₁j hm v hv A b
  have hAt₂ := wJets_noiseMean_affine_family hf hL ht₂ ht₂j hm v hv A b
  have hMean : At = fun x => noiseMean m v f (A x + b) (fun t => t₀ t x) +
      δ * noiseMean m v f (A x + b) (fun t => t₁ t x) +
      δ ^ 2 * noiseMean m v f (A x + b) (fun t => t₂ t x) :=
    noiseMean_quadratic_decomposition hf hL ht₀ ht₁ ht₂ ht₀j ht₁j ht₂j v A b
  have hNorm : WJets r (3 * (2 : ℝ) ^ r * (K * C) * (K * L)) (n + 2)
      (fun x => Ac x * At x) := by
    have H := hAc.mul_small_quadratic_score hδAc hδ hAt₀ hAt₁ hAt₂
    convert H using 1
    funext x
    rw [congrFun hMean x]
  have hT : ContDiff ℝ r (Function.uncurry T) := by
    convert! (ht₀.add (contDiff_const.mul ht₁)).add (contDiff_const.mul ht₂) using 1
  have hProdC : ContDiff ℝ r (Function.uncurry (fun t x => G t x * T t x)) := by
    convert! hG.mul hT using 1
  have hProd (t : ℝ) : WJets r
      ((3 * (2 : ℝ) ^ r * C * L) * (1 + |t|) ^ (q + q)) (n + 2)
      (fun x => G t x * T t x) := by
    convert (hGj t).mul_small_quadratic_score (hδGj t) hδ (ht₀j t) (ht₁j t) (ht₂j t) using 1
    rw [pow_add]
    ring
  have hP := wJets_noiseMean_affine_family hf
    (show 0 ≤ 3 * (2 : ℝ) ^ r * C * L by positivity) hProdC hProd hm v hv A b
  convert hP.sub hNorm using 1
  dsimp only [K, K₂]
  ring

end SKBarriers2.StepCalculus
