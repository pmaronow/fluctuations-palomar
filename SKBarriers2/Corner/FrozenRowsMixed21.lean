module

public import SKBarriers2.Analysis.ScaledChain
public import SKBarriers2.Corner.FrozenRowsMixed15

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic
namespace SKBarriers2.StepCalculus
local notation "X" => (Fin 3 → ℝ)

theorem noiseMean_scale_inv {K : ℝ} (hK : K ≠ 0)
    (m : ℝ) (v : X) (f : X → ℝ) (A : X →L[ℝ] X) (b x : X) (G : ℝ → ℝ) :
    noiseMean m (K⁻¹ • v) (spatialRescale K 0 f) ((K⁻¹ • A) x+K⁻¹ • b) G =
      noiseMean m v f (A x+b) G := by
  apply noiseMean_congr_line
  intro t
  apply congrArg f
  change K • ((K⁻¹ • A) x+K⁻¹ • b+t • (K⁻¹ • v))+0 = A x+b+t • v
  have he : (K⁻¹ • A) x+K⁻¹ • b+t • (K⁻¹ • v) = K⁻¹ • (A x+b+t • v) := by
    simp only [smul_apply,smul_add,smul_comm t K⁻¹]
  rw [he,smul_smul,mul_inv_cancel₀ hK,one_smul,add_zero]

theorem centeredFirstNoiseTransport_profile_scale_inv {K : ℝ} (hK : K ≠ 0)
    (m : ℝ) (v : X) (f : X → ℝ) (A : X →L[ℝ] X) (b : X)
    (a c S : ℝ → X → ℝ) :
    centeredFirstNoiseTransport m (K⁻¹ • v) (spatialRescale K 0 f)
      (K⁻¹ • A) (K⁻¹ • b) a c S = centeredFirstNoiseTransport m v f A b a c S := by
  funext x
  simp only [centeredFirstNoiseTransport,noiseMean_scale_inv hK]

theorem secondAffineNoiseTransport_scale_inv {K : ℝ} (hK : K ≠ 0)
    (m : ℝ) (v : X) (f : X → ℝ) (A : X →L[ℝ] X) (b : X)
    (B₂ A₁ C₀ S T : ℝ → X → ℝ) :
    secondAffineNoiseTransport m (K⁻¹ • v) (spatialRescale K 0 f)
      (K⁻¹ • A) (K⁻¹ • b) B₂ A₁ C₀ S T =
        secondAffineNoiseTransport m v f A b B₂ A₁ C₀ S T := by
  funext x
  simp only [secondAffineNoiseTransport,affineNoiseCovariance,noiseMean_scale_inv hK]

theorem wJets_secondAffineNoiseTransport_boundedNoise {r n q : ℕ} {B C L m δ K : ℝ}
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
    (hm : m ∈ Icc (0 : ℝ) 1) (hK : 1 ≤ K) (v : X) (hv : ‖v‖ ≤ K)
    (A : X →L[ℝ] X) (b : X) :
    WJets r (spatialSecondNoiseTransportBudget r q (B*K^(r+2)) L (K⁻¹ • A) * C) (n + 2)
      (secondAffineNoiseTransport m v f A b B₂ A₁ C₀
        (fun t x => s₀ t x + δ * s₁ t x)
        (fun t x => t₀ t x + δ * t₁ t x + δ ^ 2 * t₂ t x)) := by
  have hK₀ : 0 < K := by linarith
  have hv' : ‖K⁻¹ • v‖ ≤ 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hK₀)]
    exact (mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr hK₀.le)).trans_eq
      (inv_mul_cancel₀ hK₀.ne')
  have H := wJets_secondAffineNoiseTransport (hf.dilate hK) hC hL hδ
    hB₂ hA₁ hC₀ hs₀ hs₁ ht₀ ht₁ ht₂ hB₂j hA₁j hδA₁j hC₀j hδC₀j
    hs₀j hs₁j ht₀j ht₁j ht₂j hm (K⁻¹ • v) hv' (K⁻¹ • A) (K⁻¹ • b)
  rwa [secondAffineNoiseTransport_scale_inv hK₀.ne'] at H

theorem wJets_centeredFirstNoiseTransport_profile_boundedNoise {r n p q : ℕ} {B C L m δ K : ℝ}
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
    (hm : m ∈ Icc (0 : ℝ) 1) (hK : 1 ≤ K) (v : X) (hv : ‖v‖ ≤ K)
    (A : X →L[ℝ] X) (b : X) :
    WJets r (spatialFirstNoiseTransportBudget r q (B*K^(r+2)) L (K⁻¹ • A) * C) p
      (centeredFirstNoiseTransport m v f A b a c (fun t x => s₀ t x + δ * s₁ t x)) := by
  have hK₀ : 0 < K := by linarith
  have hv' : ‖K⁻¹ • v‖ ≤ 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hK₀)]
    exact (mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr hK₀.le)).trans_eq
      (inv_mul_cancel₀ hK₀.ne')
  have H := wJets_centeredFirstNoiseTransport_profile (hf.dilate hK) hC hL hδ hgap
    ha hc hs₀ hs₁ haj hcj hδcj hs₀j hs₁j hm (K⁻¹ • v) hv' (K⁻¹ • A) (K⁻¹ • b)
  rwa [centeredFirstNoiseTransport_profile_scale_inv hK₀.ne'] at H

theorem wJets_noiseMean_affine_family_boundedNoise {r p q : ℕ} {B C m K : ℝ} {f : X → ℝ}
    {G : ℝ → X → ℝ} (hf : QPotential (r + 2) B f) (hC : 0 ≤ C)
    (hG : ContDiff ℝ r (Function.uncurry G))
    (hGj : ∀ t, WJets r (C * (1 + |t|) ^ q) p (G t))
    (hm : m ∈ Icc (0 : ℝ) 1) (hK : 1 ≤ K) (v : X) (hv : ‖v‖ ≤ K)
    (A : X →L[ℝ] X) (b : X) :
    WJets r (affineNoiseAverageCoefficient r q (B*K^(r+2)) (K⁻¹ • A) * C) p
      (fun x => noiseMean m v f (A x + b) (fun t => G t x)) := by
  have hK₀ : 0 < K := by linarith
  have hv' : ‖K⁻¹ • v‖ ≤ 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hK₀)]
    exact (mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr hK₀.le)).trans_eq
      (inv_mul_cancel₀ hK₀.ne')
  have H := wJets_noiseMean_affine_family (hf.dilate hK) hC hG hGj hm
    (K⁻¹ • v) hv' (K⁻¹ • A) (K⁻¹ • b)
  simpa only [noiseMean_scale_inv hK₀.ne'] using H

end SKBarriers2.StepCalculus
