module

public import SKBarriers2.Corner.FrozenRowsMixedCore

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic

namespace SKBarriers2.StepCalculus
local notation "X" => (Fin 3 → ℝ)

def affineNoiseAverageCoefficient (r q : ℕ) (B : ℝ) (A : X →L[ℝ] X) : ℝ :=
  noiseAverageCoefficient r q B * (max 1 ‖A‖ ^ r) ^ 2

def centeredFirstNoiseTransport (m : ℝ) (v : X) (f : X → ℝ)
    (A : X →L[ℝ] X) (b : X) (a c s : ℝ → X → ℝ) (x : X) : ℝ :=
  noiseMean m v f (A x + b) (fun t => a t x) +
    noiseMean m v f (A x + b) (fun t => c t x * s t x) -
    noiseMean m v f (A x + b) (fun t => c t x) *
      noiseMean m v f (A x + b) (fun t => s t x)

theorem wJets_centeredFirstNoiseTransport {r p q : ℕ} {B C H L m : ℝ}
    {f : X → ℝ} {a c s : ℝ → X → ℝ}
    (hf : QPotential (r + 1) B f) (hC : 0 ≤ C) (hH : 0 ≤ H) (hL : 0 ≤ L)
    (ha : ContDiff ℝ r (Function.uncurry a))
    (hc : ContDiff ℝ r (Function.uncurry c))
    (hs : ContDiff ℝ r (Function.uncurry s))
    (haj : ∀ t, WJets r (H * (1 + |t|) ^ q) (p + 1) (a t))
    (hcj : ∀ t, WJets r (C * (1 + |t|) ^ q) p (c t))
    (hsj : ∀ t, WJets r (L * (1 + |t|) ^ q) 1 (s t))
    (hm : m ∈ Icc (0 : ℝ) 1) (v : X) (hv : ‖v‖ ≤ 1)
    (A : X →L[ℝ] X) (b : X) :
    let K := affineNoiseAverageCoefficient r q B A
    let K₂ := affineNoiseAverageCoefficient r (q + q) B A
    WJets r (K * H + (2 : ℝ) ^ r * (K₂ + K ^ 2) * C * L) (p + 1)
      (centeredFirstNoiseTransport m v f A b a c s) := by
  let K := affineNoiseAverageCoefficient r q B A
  let K₂ := affineNoiseAverageCoefficient r (q + q) B A
  have hAa : WJets r (K * H) (p + 1)
      (fun x => noiseMean m v f (A x + b) (fun t => a t x)) := by
    convert wJets_noiseMean_affine_weighted hf hH ha haj hm v hv A b using 1
    dsimp only [K, affineNoiseAverageCoefficient]
    ring
  have hAc : WJets r (K * C) p
      (fun x => noiseMean m v f (A x + b) (fun t => c t x)) := by
    convert wJets_noiseMean_affine_weighted hf hC hc hcj hm v hv A b using 1
    dsimp only [K, affineNoiseAverageCoefficient]
    ring
  have hAs : WJets r (K * L) 1
      (fun x => noiseMean m v f (A x + b) (fun t => s t x)) := by
    convert wJets_noiseMean_affine_weighted hf hL hs hsj hm v hv A b using 1
    dsimp only [K, affineNoiseAverageCoefficient]
    ring
  have hcsj (t : ℝ) : WJets r
      (((2 : ℝ) ^ r * C * L) * (1 + |t|) ^ (q + q)) (p + 1)
      (fun x => c t x * s t x) := by
    convert (hcj t).mul (hsj t) using 1
    rw [pow_add]
    ring
  have hAcs : WJets r (K₂ * ((2 : ℝ) ^ r * C * L)) (p + 1)
      (fun x => noiseMean m v f (A x + b) (fun t => c t x * s t x)) := by
    convert wJets_noiseMean_affine_weighted (G := fun t x => c t x * s t x) hf
      (show 0 ≤ (2 : ℝ) ^ r * C * L by positivity)
      (by convert! hc.mul hs using 1) hcsj hm v hv A b using 1
    dsimp only [K₂, affineNoiseAverageCoefficient]
    ring
  convert (hAa.add hAcs).sub (hAc.mul hAs) using 1
  · dsimp only [K, K₂]
    ring
  · rfl

end SKBarriers2.StepCalculus
