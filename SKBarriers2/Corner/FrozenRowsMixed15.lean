module

public import SKBarriers2.Corner.FrozenRowsMixed14

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic

namespace SKBarriers2.StepCalculus
local notation "X" => (Fin 3 → ℝ)

theorem wJets_noiseMean_linear_score_square_covariance {r n q : ℕ} {B C L m δ : ℝ}
    {f : X → ℝ} {G s₀ s₁ : ℝ → X → ℝ}
    (hf : QPotential (r + 2) B f) (hC : 0 ≤ C) (_hL : 0 ≤ L) (hδ : |δ| ≤ 1)
    (hG : ContDiff ℝ r (Function.uncurry G))
    (hs₀ : ContDiff ℝ r (Function.uncurry s₀))
    (hs₁ : ContDiff ℝ r (Function.uncurry s₁))
    (hGj : ∀ t, WJets r (C * (1 + |t|) ^ q) (n + 2) (G t))
    (hδGj : ∀ t, WJets r (C * (1 + |t|) ^ q) n (fun x => δ * G t x))
    (hs₀j : ∀ t, WJets r (L * (1 + |t|) ^ q) 0 (s₀ t))
    (hs₁j : ∀ t, WJets r (L * (1 + |t|) ^ q) 1 (s₁ t))
    (hm : m ∈ Icc (0 : ℝ) 1) (v : X) (hv : ‖v‖ ≤ 1)
    (A : X →L[ℝ] X) (b : X) :
    let K₂ := affineNoiseAverageCoefficient r (q + q) B A
    let K₄ := affineNoiseAverageCoefficient r ((q + q) + (q + q)) B A
    WJets r (6 * ((2 : ℝ) ^ r) ^ 2 * (K₄ + K₂ ^ 2) * C * L ^ 2) (n + 2)
      (fun x => noiseMean m v f (A x + b)
          (fun t => G t x * (s₀ t x + δ * s₁ t x) ^ 2) -
        noiseMean m v f (A x + b) (fun t => G t x) *
          noiseMean m v f (A x + b) (fun t => (s₀ t x + δ * s₁ t x) ^ 2)) := by
  have hGj₂ (t : ℝ) : WJets r (C * (1 + |t|) ^ (q + q)) (n + 2) (G t) :=
    (hGj t).mono (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by linarith [abs_nonneg t]) (by omega : q ≤ q + q)) hC) le_rfl
  have hδGj₂ (t : ℝ) : WJets r (C * (1 + |t|) ^ (q + q)) n
      (fun x => δ * G t x) :=
    (hδGj t).mono (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by linarith [abs_nonneg t]) (by omega : q ≤ q + q)) hC) le_rfl
  let L₂ := 2 * (2 : ℝ) ^ r * L ^ 2
  have hL₂ : 0 ≤ L₂ := by dsimp only [L₂]; positivity
  have ht₀ : ContDiff ℝ r (Function.uncurry (fun t x => s₀ t x ^ 2)) := by
    convert! hs₀.pow 2 using 1
  have ht₁ : ContDiff ℝ r (Function.uncurry (fun t x => 2 * s₀ t x * s₁ t x)) := by
    convert! (contDiff_const.mul hs₀).mul hs₁ using 1
  have ht₂ : ContDiff ℝ r (Function.uncurry (fun t x => s₁ t x ^ 2)) := by
    convert! hs₁.pow 2 using 1
  have hparts (t : ℝ) :
      WJets r (L₂ * (1 + |t|) ^ (q + q)) 0 (fun x => s₀ t x ^ 2) ∧
      WJets r (L₂ * (1 + |t|) ^ (q + q)) 1 (fun x => 2 * s₀ t x * s₁ t x) ∧
      WJets r (L₂ * (1 + |t|) ^ (q + q)) 2 (fun x => s₁ t x ^ 2) := by
    have H := (hs₀j t).linear_score_square_profile (hs₁j t)
    convert H using 1 <;> dsimp only [L₂] <;> rw [pow_add] <;> ring
  have H := wJets_noiseMean_small_quadratic_covariance hf hC hL₂ hδ hG ht₀ ht₁ ht₂
    hGj₂ hδGj₂ (fun t => (hparts t).1) (fun t => (hparts t).2.1)
      (fun t => (hparts t).2.2) hm v hv A b
  have he (t : ℝ) (x : X) : s₀ t x ^ 2 + δ * (2 * s₀ t x * s₁ t x) +
      δ ^ 2 * s₁ t x ^ 2 = (s₀ t x + δ * s₁ t x) ^ 2 := by ring
  simp_rw [he] at H
  convert H using 1
  dsimp only [L₂]
  ring

theorem wJets_noiseMean_score_times_covariance {r n q : ℕ} {B C L m δ : ℝ}
    {f : X → ℝ} {G s₀ s₁ : ℝ → X → ℝ}
    (hf : QPotential (r + 2) B f) (hC : 0 ≤ C) (hL : 0 ≤ L) (hδ : |δ| ≤ 1)
    (hG : ContDiff ℝ r (Function.uncurry G))
    (hs₀ : ContDiff ℝ r (Function.uncurry s₀))
    (hs₁ : ContDiff ℝ r (Function.uncurry s₁))
    (hGj : ∀ t, WJets r (C * (1 + |t|) ^ q) (n + 2) (G t))
    (hδGj : ∀ t, WJets r (C * (1 + |t|) ^ q) n (fun x => δ * G t x))
    (hs₀j : ∀ t, WJets r (L * (1 + |t|) ^ q) 0 (s₀ t))
    (hs₁j : ∀ t, WJets r (L * (1 + |t|) ^ q) 1 (s₁ t))
    (hm : m ∈ Icc (0 : ℝ) 1) (v : X) (hv : ‖v‖ ≤ 1)
    (A : X →L[ℝ] X) (b : X) :
    let K := affineNoiseAverageCoefficient r q B A
    let K₂ := affineNoiseAverageCoefficient r (q + q) B A
    WJets r (4 * ((2 : ℝ) ^ r) ^ 2 * K * (K₂ + K ^ 2) * C * L ^ 2) (n + 2)
      (fun x => noiseMean m v f (A x + b) (fun t => s₀ t x + δ * s₁ t x) *
        (noiseMean m v f (A x + b) (fun t => G t x * (s₀ t x + δ * s₁ t x)) -
          noiseMean m v f (A x + b) (fun t => G t x) *
            noiseMean m v f (A x + b) (fun t => s₀ t x + δ * s₁ t x))) := by
  have hCov := wJets_noiseMean_small_linear_covariance hf hC hL hδ
    (by omega : n + 1 ≤ n + 2) hG hs₀ hs₁ hGj hδGj hs₀j hs₁j hm v hv A b
  dsimp only at hCov
  have hAs₀ := wJets_noiseMean_affine_family hf hL hs₀ hs₀j hm v hv A b
  have hAs₁ := wJets_noiseMean_affine_family hf hL hs₁ hs₁j hm v hv A b
  have H := hCov.1.mul_small_linear_score_one_degree hCov.2 hAs₀ hAs₁
  have hMean := noiseMean_linear_decomposition (m := m) (δ := δ) hf hL hs₀ hs₁ hs₀j hs₁j v A b
  convert H using 1
  · ring
  · funext x
    rw [congrFun hMean x]
    ring

def affineNoiseCovariance (m : ℝ) (v : X) (f : X → ℝ) (A : X →L[ℝ] X)
    (b : X) (G H : ℝ → X → ℝ) (x : X) : ℝ :=
  noiseMean m v f (A x + b) (fun t => G t x * H t x) -
    noiseMean m v f (A x + b) (fun t => G t x) *
      noiseMean m v f (A x + b) (fun t => H t x)

def secondAffineNoiseTransport (m : ℝ) (v : X) (f : X → ℝ)
    (A : X →L[ℝ] X) (b : X) (B₂ A₁ C₀ S T : ℝ → X → ℝ) (x : X) : ℝ :=
  noiseMean m v f (A x + b) (fun t => B₂ t x) +
    2 * affineNoiseCovariance m v f A b A₁ S x +
    affineNoiseCovariance m v f A b C₀ T x +
    affineNoiseCovariance m v f A b C₀ (fun t y => S t y ^ 2) x -
    2 * (noiseMean m v f (A x + b) (fun t => S t x) *
      affineNoiseCovariance m v f A b C₀ S x)

def spatialFirstNoiseTransportBudget (r q : ℕ) (B L : ℝ) (A : X →L[ℝ] X) : ℝ :=
  let K := affineNoiseAverageCoefficient r q B A
  let K₂ := affineNoiseAverageCoefficient r (q + q) B A
  K + 2 * (2 : ℝ) ^ r * (K₂ + K ^ 2) * L

theorem wJets_centeredFirstNoiseTransport_profile {r n p q : ℕ} {B C L m δ : ℝ}
    {f : X → ℝ} {a c s₀ s₁ : ℝ → X → ℝ}
    (hf : QPotential (r + 2) B f) (hC : 0 ≤ C) (hL : 0 ≤ L) (hδ : |δ| ≤ 1)
    (hgap : n + 1 ≤ p)
    (ha : ContDiff ℝ r (Function.uncurry a))
    (hc : ContDiff ℝ r (Function.uncurry c))
    (hs₀ : ContDiff ℝ r (Function.uncurry s₀))
    (hs₁ : ContDiff ℝ r (Function.uncurry s₁))
    (haj : ∀ t, WJets r (C * (1 + |t|) ^ q) p (a t))
    (hcj : ∀ t, WJets r (C * (1 + |t|) ^ q) p (c t))
    (hδcj : ∀ t, WJets r (C * (1 + |t|) ^ q) n (fun x => δ * c t x))
    (hs₀j : ∀ t, WJets r (L * (1 + |t|) ^ q) 0 (s₀ t))
    (hs₁j : ∀ t, WJets r (L * (1 + |t|) ^ q) 1 (s₁ t))
    (hm : m ∈ Icc (0 : ℝ) 1) (v : X) (hv : ‖v‖ ≤ 1)
    (A : X →L[ℝ] X) (b : X) :
    WJets r (spatialFirstNoiseTransportBudget r q B L A * C) p
      (centeredFirstNoiseTransport m v f A b a c (fun t x => s₀ t x + δ * s₁ t x)) := by
  have hAvg := wJets_noiseMean_affine_family hf hC ha haj hm v hv A b
  have hCov := wJets_noiseMean_small_linear_covariance hf hC hL hδ hgap
    hc hs₀ hs₁ hcj hδcj hs₀j hs₁j hm v hv A b
  dsimp only at hCov
  convert hAvg.add hCov.1 using 1
  · dsimp only [spatialFirstNoiseTransportBudget]
    ring
  · funext x
    simp only [centeredFirstNoiseTransport]
    ring

def spatialSecondNoiseTransportBudget (r q : ℕ) (B L : ℝ) (A : X →L[ℝ] X) : ℝ :=
  let S : ℝ := (2 : ℝ) ^ r
  let K := affineNoiseAverageCoefficient r q B A
  let K₂ := affineNoiseAverageCoefficient r (q + q) B A
  let K₄ := affineNoiseAverageCoefficient r ((q + q) + (q + q)) B A
  K + 7 * S * (K₂ + K ^ 2) * L +
    6 * S ^ 2 * (K₄ + K₂ ^ 2) * L ^ 2 +
      8 * S ^ 2 * K * (K₂ + K ^ 2) * L ^ 2

theorem wJets_secondAffineNoiseTransport {r n q : ℕ} {B C L m δ : ℝ}
    {f : X → ℝ} {B₂ A₁ C₀ s₀ s₁ t₀ t₁ t₂ : ℝ → X → ℝ}
    (hf : QPotential (r + 2) B f) (hC : 0 ≤ C) (hL : 0 ≤ L) (hδ : |δ| ≤ 1)
    (hB₂ : ContDiff ℝ r (Function.uncurry B₂))
    (hA₁ : ContDiff ℝ r (Function.uncurry A₁))
    (hC₀ : ContDiff ℝ r (Function.uncurry C₀))
    (hs₀ : ContDiff ℝ r (Function.uncurry s₀))
    (hs₁ : ContDiff ℝ r (Function.uncurry s₁))
    (ht₀ : ContDiff ℝ r (Function.uncurry t₀))
    (ht₁ : ContDiff ℝ r (Function.uncurry t₁))
    (ht₂ : ContDiff ℝ r (Function.uncurry t₂))
    (hB₂j : ∀ t, WJets r (C * (1 + |t|) ^ q) (n + 2) (B₂ t))
    (hA₁j : ∀ t, WJets r (C * (1 + |t|) ^ q) (n + 2) (A₁ t))
    (hδA₁j : ∀ t, WJets r (C * (1 + |t|) ^ q) (n + 1) (fun x => δ * A₁ t x))
    (hC₀j : ∀ t, WJets r (C * (1 + |t|) ^ q) (n + 2) (C₀ t))
    (hδC₀j : ∀ t, WJets r (C * (1 + |t|) ^ q) n (fun x => δ * C₀ t x))
    (hs₀j : ∀ t, WJets r (L * (1 + |t|) ^ q) 0 (s₀ t))
    (hs₁j : ∀ t, WJets r (L * (1 + |t|) ^ q) 1 (s₁ t))
    (ht₀j : ∀ t, WJets r (L * (1 + |t|) ^ q) 0 (t₀ t))
    (ht₁j : ∀ t, WJets r (L * (1 + |t|) ^ q) 1 (t₁ t))
    (ht₂j : ∀ t, WJets r (L * (1 + |t|) ^ q) 2 (t₂ t))
    (hm : m ∈ Icc (0 : ℝ) 1) (v : X) (hv : ‖v‖ ≤ 1)
    (A : X →L[ℝ] X) (b : X) :
    WJets r (spatialSecondNoiseTransportBudget r q B L A * C) (n + 2)
      (secondAffineNoiseTransport m v f A b B₂ A₁ C₀
        (fun t x => s₀ t x + δ * s₁ t x)
        (fun t x => t₀ t x + δ * t₁ t x + δ ^ 2 * t₂ t x)) := by
  have hAvg := wJets_noiseMean_affine_family hf hC hB₂ hB₂j hm v hv A b
  have hCovA := wJets_noiseMean_small_linear_covariance hf hC hL hδ
    (by omega : (n + 1) + 1 ≤ n + 2) hA₁ hs₀ hs₁ hA₁j hδA₁j hs₀j hs₁j hm v hv A b
  have hCovT := wJets_noiseMean_small_quadratic_covariance hf hC hL hδ
    hC₀ ht₀ ht₁ ht₂ hC₀j hδC₀j ht₀j ht₁j ht₂j hm v hv A b
  have hCovSq := wJets_noiseMean_linear_score_square_covariance hf hC hL hδ
    hC₀ hs₀ hs₁ hC₀j hδC₀j hs₀j hs₁j hm v hv A b
  have hCross := wJets_noiseMean_score_times_covariance hf hC hL hδ
    hC₀ hs₀ hs₁ hC₀j hδC₀j hs₀j hs₁j hm v hv A b
  dsimp only at hCovA hCovT hCovSq hCross
  have H := (((hAvg.add (hCovA.1.const_smul 2)).add hCovT).add hCovSq).sub
    (hCross.const_smul 2)
  convert H using 1
  · norm_num
    dsimp only [spatialSecondNoiseTransportBudget]
    ring
  · funext x
    simp only [secondAffineNoiseTransport, affineNoiseCovariance, smul_eq_mul]

end SKBarriers2.StepCalculus
