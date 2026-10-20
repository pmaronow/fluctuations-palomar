module

public import SKBarriers2.Corner.FrozenRowsMixed7
public import SKBarriers2.Corner.FrozenRowsMixed9

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic

namespace SKBarriers2.StepCalculus
local notation "X" => (Fin 3 → ℝ)

theorem stepLaw_congr_line {m : ℝ} {v w x y : X} {f g : X → ℝ}
    (h : ∀ t : ℝ, f (x + t • v) = g (y + t • w)) :
    stepLaw m v f x = stepLaw m w g y := by
  change (gaussianReal 0 1).tilted (fun t => m * f (x + t • v)) =
    (gaussianReal 0 1).tilted (fun t => m * g (y + t • w))
  apply tilted_congr
  exact ae_of_all _ (fun t => congrArg (fun a => m * a) (h t))

theorem noiseMean_congr_line {m : ℝ} {v w x y : X} {f g : X → ℝ}
    (h : ∀ t : ℝ, f (x + t • v) = g (y + t • w)) (G : ℝ → ℝ) :
    noiseMean m v f x G = noiseMean m w g y G := by
  rw [noiseMean, stepLaw_congr_line h]
  rfl

theorem stepLaw_comp_affine (m : ℝ) (v x : X) (f : X → ℝ)
    (A : X →L[ℝ] X) (b : X) :
    stepLaw m v (fun y => f (A y + b)) x = stepLaw m (A v) f (A x + b) := by
  apply stepLaw_congr_line
  intro t
  congr 1
  simp only [map_add, map_smul]
  abel

theorem integrable_noise_weightedFamily {r p q : ℕ} {B C m : ℝ} {f : X → ℝ}
    {G : ℝ → X → ℝ} (hf : QPotential (r + 2) B f) (hC : 0 ≤ C)
    (hG : ContDiff ℝ r (Function.uncurry G))
    (hGj : ∀ t, WJets r (C * (1 + |t|) ^ q) p (G t))
    (v a x : X) : Integrable (fun t => G t x) (stepLaw m v f a) := by
  apply integrable_noise hf (by omega) m v a
  · refine ⟨C * (1 + ‖x‖) ^ p, q, by positivity, by positivity, ?_⟩
    intro t
    have hpow : (1 + |t|) ^ q ≤ Real.exp ((q : ℝ) * |t|) := by
      rw [Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by positivity)
        (by simpa only [add_comm] using Real.add_one_le_exp |t|) q
    calc
      _ ≤ C * (1 + |t|) ^ q * (1 + ‖x‖) ^ p := (hGj t).norm_le x
      _ ≤ C * Real.exp ((q : ℝ) * |t|) * (1 + ‖x‖) ^ p := by gcongr
      _ = _ := by rw [Real.norm_eq_abs]; ring
  · exact hG.continuous.comp (continuous_id.prodMk continuous_const)

theorem noiseMean_linear_decomposition {r q : ℕ} {B L m δ : ℝ} {f : X → ℝ}
    {s₀ s₁ : ℝ → X → ℝ} (hf : QPotential (r + 2) B f) (hL : 0 ≤ L)
    (hs₀ : ContDiff ℝ r (Function.uncurry s₀))
    (hs₁ : ContDiff ℝ r (Function.uncurry s₁))
    (hs₀j : ∀ t, WJets r (L * (1 + |t|) ^ q) 0 (s₀ t))
    (hs₁j : ∀ t, WJets r (L * (1 + |t|) ^ q) 1 (s₁ t))
    (v : X) (A : X →L[ℝ] X) (b : X) :
    (fun x => noiseMean m v f (A x + b) (fun t => s₀ t x + δ * s₁ t x)) =
      fun x => noiseMean m v f (A x + b) (fun t => s₀ t x) +
        δ * noiseMean m v f (A x + b) (fun t => s₁ t x) := by
  funext x
  unfold noiseMean
  rw [integral_add
    (integrable_noise_weightedFamily hf hL hs₀ hs₀j v (A x + b) x)
    ((integrable_noise_weightedFamily hf hL hs₁ hs₁j v (A x + b) x).const_mul δ),
    integral_const_mul]

theorem wJets_noiseMean_affine_family {r p q : ℕ} {B C m : ℝ} {f : X → ℝ}
    {G : ℝ → X → ℝ} (hf : QPotential (r + 2) B f) (hC : 0 ≤ C)
    (hG : ContDiff ℝ r (Function.uncurry G))
    (hGj : ∀ t, WJets r (C * (1 + |t|) ^ q) p (G t))
    (hm : m ∈ Icc (0 : ℝ) 1) (v : X) (hv : ‖v‖ ≤ 1)
    (A : X →L[ℝ] X) (b : X) :
    WJets r (affineNoiseAverageCoefficient r q B A * C) p
      (fun x => noiseMean m v f (A x + b) (fun t => G t x)) := by
  convert wJets_noiseMean_affine_weighted (hf.of_le (by omega : r + 1 ≤ r + 2))
    hC hG hGj hm v hv A b using 1
  dsimp only [affineNoiseAverageCoefficient]
  ring

theorem wJets_noiseMean_affine_family_scaled {r p q : ℕ} {B C m δ : ℝ} {f : X → ℝ}
    {G : ℝ → X → ℝ} (hf : QPotential (r + 2) B f) (hC : 0 ≤ C)
    (hG : ContDiff ℝ r (Function.uncurry G))
    (hδGj : ∀ t, WJets r (C * (1 + |t|) ^ q) p (fun x => δ * G t x))
    (hm : m ∈ Icc (0 : ℝ) 1) (v : X) (hv : ‖v‖ ≤ 1)
    (A : X →L[ℝ] X) (b : X) :
    WJets r (affineNoiseAverageCoefficient r q B A * C) p
      (fun x => δ * noiseMean m v f (A x + b) (fun t => G t x)) := by
  have hδG : ContDiff ℝ r (Function.uncurry (fun t x => δ * G t x)) := by
    convert! contDiff_const.mul hG using 1
  have H := wJets_noiseMean_affine_family hf hC hδG hδGj hm v hv A b
  simpa only [noiseMean, integral_const_mul] using H

theorem wJets_noiseMean_mul_small_linear_score {r n p q : ℕ} {B C L m δ : ℝ}
    {f : X → ℝ} {G s₀ s₁ : ℝ → X → ℝ}
    (hf : QPotential (r + 2) B f) (hC : 0 ≤ C) (hL : 0 ≤ L) (hδ : |δ| ≤ 1)
    (hgap : n + 1 ≤ p)
    (hG : ContDiff ℝ r (Function.uncurry G))
    (hs₀ : ContDiff ℝ r (Function.uncurry s₀))
    (hs₁ : ContDiff ℝ r (Function.uncurry s₁))
    (hGj : ∀ t, WJets r (C * (1 + |t|) ^ q) p (G t))
    (hδGj : ∀ t, WJets r (C * (1 + |t|) ^ q) n (fun x => δ * G t x))
    (hs₀j : ∀ t, WJets r (L * (1 + |t|) ^ q) 0 (s₀ t))
    (hs₁j : ∀ t, WJets r (L * (1 + |t|) ^ q) 1 (s₁ t))
    (hm : m ∈ Icc (0 : ℝ) 1) (v : X) (hv : ‖v‖ ≤ 1)
    (A : X →L[ℝ] X) (b : X) :
    let K := affineNoiseAverageCoefficient r (q + q) B A
    let a := fun x => noiseMean m v f (A x + b)
      (fun t => G t x * (s₀ t x + δ * s₁ t x))
    WJets r (2 * (2 : ℝ) ^ r * K * C * L) p a ∧
      WJets r (2 * (2 : ℝ) ^ r * K * C * L) (n + 1) (fun x => δ * a x) := by
  let K := affineNoiseAverageCoefficient r (q + q) B A
  let S : ℝ → X → ℝ := fun t x => s₀ t x + δ * s₁ t x
  have hS : ContDiff ℝ r (Function.uncurry S) := by
    convert! hs₀.add (contDiff_const.mul hs₁) using 1
  have hSj (t : ℝ) : WJets r (2 * L * (1 + |t|) ^ q) 1 (S t) := by
    have H₀ := (hs₀j t).mono le_rfl (by omega : 0 ≤ 1)
    have H₁ := (hs₁j t).const_smul δ
    have H₁' : WJets r (L * (1 + |t|) ^ q) 1 (fun x => δ * s₁ t x) := by
      apply H₁.mono _ le_rfl
      exact mul_le_of_le_one_left (by positivity) hδ
    convert H₀.add H₁' using 1
    ring
  have hProd (t : ℝ) : WJets r
      ((2 * (2 : ℝ) ^ r * C * L) * (1 + |t|) ^ (q + q)) p
      (fun x => G t x * S t x) := by
    convert (hGj t).mul_small_linear_score_of_gap (hδGj t) (hs₀j t) (hs₁j t) hgap using 1
    rw [pow_add]
    ring
  have hδProd (t : ℝ) : WJets r
      ((2 * (2 : ℝ) ^ r * C * L) * (1 + |t|) ^ (q + q)) (n + 1)
      (fun x => (δ * G t x) * S t x) := by
    convert (hδGj t).mul (hSj t) using 1
    rw [pow_add]
    ring
  have hProdC : ContDiff ℝ r (Function.uncurry (fun t x => G t x * S t x)) := by
    convert! hG.mul hS using 1
  have hδProdC : ContDiff ℝ r (Function.uncurry (fun t x => (δ * G t x) * S t x)) := by
    convert! (contDiff_const.mul hG).mul hS using 1
  have hP := wJets_noiseMean_affine_weighted
    (hf.of_le (by omega : r + 1 ≤ r + 2))
    (show 0 ≤ 2 * (2 : ℝ) ^ r * C * L by positivity) hProdC hProd hm v hv A b
  have hδP := wJets_noiseMean_affine_weighted
    (hf.of_le (by omega : r + 1 ≤ r + 2))
    (show 0 ≤ 2 * (2 : ℝ) ^ r * C * L by positivity) hδProdC hδProd hm v hv A b
  constructor
  · convert hP using 1
    dsimp only [K, affineNoiseAverageCoefficient]
    ring
  · have he : (fun x => noiseMean m v f (A x + b)
        (fun t => (δ * G t x) * S t x)) =
        fun x => δ * noiseMean m v f (A x + b) (fun t => G t x * S t x) := by
      funext x
      simp only [mul_assoc, noiseMean, integral_const_mul]
    rw [he] at hδP
    convert hδP using 1
    dsimp only [K, affineNoiseAverageCoefficient]
    ring

theorem wJets_noiseMean_small_linear_covariance {r n p q : ℕ} {B C L m δ : ℝ}
    {f : X → ℝ} {G s₀ s₁ : ℝ → X → ℝ}
    (hf : QPotential (r + 2) B f) (hC : 0 ≤ C) (hL : 0 ≤ L) (hδ : |δ| ≤ 1)
    (hgap : n + 1 ≤ p)
    (hG : ContDiff ℝ r (Function.uncurry G))
    (hs₀ : ContDiff ℝ r (Function.uncurry s₀))
    (hs₁ : ContDiff ℝ r (Function.uncurry s₁))
    (hGj : ∀ t, WJets r (C * (1 + |t|) ^ q) p (G t))
    (hδGj : ∀ t, WJets r (C * (1 + |t|) ^ q) n (fun x => δ * G t x))
    (hs₀j : ∀ t, WJets r (L * (1 + |t|) ^ q) 0 (s₀ t))
    (hs₁j : ∀ t, WJets r (L * (1 + |t|) ^ q) 1 (s₁ t))
    (hm : m ∈ Icc (0 : ℝ) 1) (v : X) (hv : ‖v‖ ≤ 1)
    (A : X →L[ℝ] X) (b : X) :
    let K := affineNoiseAverageCoefficient r q B A
    let K₂ := affineNoiseAverageCoefficient r (q + q) B A
    let a := fun x =>
      noiseMean m v f (A x + b) (fun t => G t x * (s₀ t x + δ * s₁ t x)) -
        noiseMean m v f (A x + b) (fun t => G t x) *
          noiseMean m v f (A x + b) (fun t => s₀ t x + δ * s₁ t x)
    WJets r (2 * (2 : ℝ) ^ r * (K₂ + K ^ 2) * C * L) p a ∧
      WJets r (2 * (2 : ℝ) ^ r * (K₂ + K ^ 2) * C * L) (n + 1) (fun x => δ * a x) := by
  let K := affineNoiseAverageCoefficient r q B A
  let K₂ := affineNoiseAverageCoefficient r (q + q) B A
  let S : ℝ → X → ℝ := fun t x => s₀ t x + δ * s₁ t x
  let Ac : X → ℝ := fun x => noiseMean m v f (A x + b) (fun t => G t x)
  let As : X → ℝ := fun x => noiseMean m v f (A x + b) (fun t => S t x)
  have hAc : WJets r (K * C) p Ac := by
    convert wJets_noiseMean_affine_weighted (hf.of_le (by omega : r + 1 ≤ r + 2))
      hC hG hGj hm v hv A b using 1
    dsimp only [K, affineNoiseAverageCoefficient]
    ring
  have hδAc : WJets r (K * C) n (fun x => δ * Ac x) := by
    have hδG : ContDiff ℝ r (Function.uncurry (fun t x => δ * G t x)) := by
      convert! contDiff_const.mul hG using 1
    have H := wJets_noiseMean_affine_weighted (hf.of_le (by omega : r + 1 ≤ r + 2))
      hC hδG hδGj hm v hv A b
    have he : (fun x => noiseMean m v f (A x + b) (fun t => δ * G t x)) =
        fun x => δ * Ac x := by
      funext x
      exact integral_const_mul _ _
    rw [he] at H
    convert H using 1
    dsimp only [K, affineNoiseAverageCoefficient]
    ring
  have hAs₀ : WJets r (K * L) 0
      (fun x => noiseMean m v f (A x + b) (fun t => s₀ t x)) := by
    convert wJets_noiseMean_affine_weighted (hf.of_le (by omega : r + 1 ≤ r + 2))
      hL hs₀ hs₀j hm v hv A b using 1
    dsimp only [K, affineNoiseAverageCoefficient]
    ring
  have hAs₁ : WJets r (K * L) 1
      (fun x => noiseMean m v f (A x + b) (fun t => s₁ t x)) := by
    convert wJets_noiseMean_affine_weighted (hf.of_le (by omega : r + 1 ≤ r + 2))
      hL hs₁ hs₁j hm v hv A b using 1
    dsimp only [K, affineNoiseAverageCoefficient]
    ring
  have hMean : As = fun x => noiseMean m v f (A x + b) (fun t => s₀ t x) +
      δ * noiseMean m v f (A x + b) (fun t => s₁ t x) :=
    noiseMean_linear_decomposition hf hL hs₀ hs₁ hs₀j hs₁j v A b
  have hAs : WJets r (2 * (K * L)) 1 As := by
    have H₀ := hAs₀.mono le_rfl (by omega : 0 ≤ 1)
    have H₁ : WJets r (K * L) 1
        (fun x => δ * noiseMean m v f (A x + b) (fun t => s₁ t x)) := by
      apply (hAs₁.const_smul δ).mono _ le_rfl
      exact mul_le_of_le_one_left hAs₁.nonneg hδ
    rw [hMean]
    convert H₀.add H₁ using 1
    ring
  have hNorm : WJets r (2 * (2 : ℝ) ^ r * (K * C) * (K * L)) p
      (fun x => Ac x * As x) := by
    have H := hAc.mul_small_linear_score_of_gap hδAc hAs₀ hAs₁ hgap
    convert H using 1
    funext x
    rw [congrFun hMean x]
  have hδNorm := hδAc.mul hAs
  have hP := wJets_noiseMean_mul_small_linear_score hf hC hL hδ hgap
    hG hs₀ hs₁ hGj hδGj hs₀j hs₁j hm v hv A b
  dsimp only at hP
  constructor
  · convert hP.1.sub hNorm using 1
    dsimp only [K, K₂]
    ring
  · convert hP.2.sub hδNorm using 1
    · dsimp only [K, K₂]
      ring
    · funext x
      dsimp only [Ac, As, S]
      ring

end SKBarriers2.StepCalculus
