module

public import SKBarriers2.Corner.FrozenRowsMixed21
public import SKBarriers2.Corner.FrozenRowsMixed20
public import SKBarriers2.Corner.FrozenRowsMixed2

@[expose] public section

noncomputable section
open scoped Topology
open Set OAI.SK.Analytic SKOptimized.Overshoot
namespace SKBarriers2.Corner
open StepCalculus

def affineNoiseKJet (m : ℝ) (v : Vec3) (f : Vec3 → ℝ)
    (A : Vec3 →L[ℝ] Vec3) (b : Vec3)
    (G a c B₂ A₁ S T : ℝ → Vec3 → ℝ) (x : Vec3) : MomentKJet :=
  ⟨noiseMean m v f (A x+b) (fun t => G t x),
    centeredFirstNoiseTransport m v f A b a c S x,
    secondAffineNoiseTransport m v f A b B₂ A₁ c S T x⟩

theorem spatialBound_affineNoiseKJet {r p q : ℕ} {B C L m δ K D : ℝ}
    {f : Vec3 → ℝ} {G a c B₂ A₁ s₀ s₁ t₀ t₁ t₂ : ℝ → Vec3 → ℝ}
    (hp : 2 ≤ p) (hf : QPotential (r+2) B f)
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hδ : |δ| ≤ 1)
    (hG : ContDiff ℝ r (Function.uncurry G))
    (ha : ContDiff ℝ r (Function.uncurry a))
    (hc : ContDiff ℝ r (Function.uncurry c))
    (hB₂ : ContDiff ℝ r (Function.uncurry B₂))
    (hA₁ : ContDiff ℝ r (Function.uncurry A₁))
    (hs₀ : ContDiff ℝ r (Function.uncurry s₀))
    (hs₁ : ContDiff ℝ r (Function.uncurry s₁))
    (ht₀ : ContDiff ℝ r (Function.uncurry t₀))
    (ht₁ : ContDiff ℝ r (Function.uncurry t₁))
    (ht₂ : ContDiff ℝ r (Function.uncurry t₂))
    (hGj : ∀ t, WJets r (C*(1+|t|)^q) p (G t))
    (haj : ∀ t, WJets r (C*(1+|t|)^q) p (a t))
    (hcj : ∀ t, WJets r (C*(1+|t|)^q) p (c t))
    (hδcj : ∀ t, WJets r (C*(1+|t|)^q) (p-2) (fun x => δ*c t x))
    (hB₂j : ∀ t, WJets r (C*(1+|t|)^q) p (B₂ t))
    (hA₁j : ∀ t, WJets r (C*(1+|t|)^q) p (A₁ t))
    (hδA₁j : ∀ t, WJets r (C*(1+|t|)^q) (p-1) (fun x => δ*A₁ t x))
    (hs₀j : ∀ t, WJets r (L*(1+|t|)^q) 0 (s₀ t))
    (hs₁j : ∀ t, WJets r (L*(1+|t|)^q) 1 (s₁ t))
    (ht₀j : ∀ t, WJets r (L*(1+|t|)^q) 0 (t₀ t))
    (ht₁j : ∀ t, WJets r (L*(1+|t|)^q) 1 (t₁ t))
    (ht₂j : ∀ t, WJets r (L*(1+|t|)^q) 2 (t₂ t))
    (hm : m ∈ Icc (0 : ℝ) 1) (hK : 1 ≤ K) (v : Vec3) (hv : ‖v‖ ≤ K)
    (A : Vec3 →L[ℝ] Vec3) (b : Vec3)
    (hD : affineNoiseAverageCoefficient r q (B*K^(r+2)) (K⁻¹ • A) ≤ D ∧
      spatialFirstNoiseTransportBudget r q (B*K^(r+2)) L (K⁻¹ • A) ≤ D ∧
      spatialSecondNoiseTransportBudget r q (B*K^(r+2)) L (K⁻¹ • A) ≤ D) :
    MomentKJet.SpatialBound r (D*C) p
      (affineNoiseKJet m v f A b G a c B₂ A₁
        (fun t x => s₀ t x+δ*s₁ t x)
        (fun t x => t₀ t x+δ*t₁ t x+δ^2*t₂ t x)) := by
  have hp₂ : (p-2)+2 = p := by omega
  have hp₁ : (p-2)+1 = p-1 := by omega
  have Hvalue := wJets_noiseMean_affine_family_boundedNoise hf hC hG hGj hm hK v hv A b
  have Hfirst := wJets_centeredFirstNoiseTransport_profile_boundedNoise hf hC hL hδ
    (show (p-2)+1 ≤ p by omega) ha hc hs₀ hs₁ haj hcj hδcj hs₀j hs₁j hm hK v hv A b
  have Hsecond := wJets_secondAffineNoiseTransport_boundedNoise hf hC hL hδ
    hB₂ hA₁ hc hs₀ hs₁ ht₀ ht₁ ht₂
    (by simpa only [hp₂] using hB₂j) (by simpa only [hp₂] using hA₁j)
    (by simpa only [hp₁] using hδA₁j) (by simpa only [hp₂] using hcj) hδcj
    hs₀j hs₁j ht₀j ht₁j ht₂j hm hK v hv A b
  refine ⟨Hvalue.mono (mul_le_mul_of_nonneg_right hD.1 hC) le_rfl,
    Hfirst.mono (mul_le_mul_of_nonneg_right hD.2.1 hC) le_rfl,?_⟩
  simpa only [hp₂,affineNoiseKJet] using Hsecond.mono (mul_le_mul_of_nonneg_right hD.2.2 hC) le_rfl

theorem spatialNoiseTransportBudget_uniform_boundedGeometry
    (d q : ℕ) (B L K : ℝ) (hK : 1 ≤ K) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ r ≤ d, ∀ A : Vec3 →L[ℝ] Vec3, ‖A‖ ≤ K →
      affineNoiseAverageCoefficient r q (B*K^(r+2)) (K⁻¹ • A) ≤ D ∧
      spatialFirstNoiseTransportBudget r q (B*K^(r+2)) L (K⁻¹ • A) ≤ D ∧
      spatialSecondNoiseTransportBudget r q (B*K^(r+2)) L (K⁻¹ • A) ≤ D := by
  obtain ⟨D,hD,HD⟩ := spatialNoiseTransportBudget_uniform_order_family d q
    (fun r => B*K^(r+2)) (fun _ => L) 1
  refine ⟨D,hD,?_⟩
  intro r hr A hA
  apply HD r hr (K⁻¹ • A)
  have hK₀ : 0 < K := lt_of_lt_of_le zero_lt_one hK
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hK₀)]
  exact (mul_le_mul_of_nonneg_left hA (inv_nonneg.mpr hK₀.le)).trans_eq
    (inv_mul_cancel₀ hK₀.ne')

end SKBarriers2.Corner
