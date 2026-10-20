module

public import SKBarriers2.Corner.FrozenRowsNoise2
public import SKBarriers2.Corner.FrozenRowsAssembly

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

def noiseParameterJet (f : ℝ × ℝ → ℝ) (k g : ℝ) : MomentKJet :=
  ⟨f (k, g), deriv (fun t => f (t, g)) k,
    deriv (deriv (fun t => f (t, g))) k⟩

private def firstNoisePartial (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ f p (1, 0)

private def secondNoisePartial (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ (firstNoisePartial f) p (1, 0)

private theorem noise_partial_hasDerivAt {f : ℝ × ℝ → ℝ}
    {n : WithTop ℕ∞} {V : Set ℝ} (hV : IsOpen V)
    (hf : ContDiffOn ℝ n f (V ×ˢ univ)) (hn : n ≠ 0)
    {k : ℝ} (hk : k ∈ V) (g : ℝ) :
    HasDerivAt (fun t => f (t, g)) (firstNoisePartial f (k, g)) k := by
  have hU : IsOpen (V ×ˢ (univ : Set ℝ)) := hV.prod isOpen_univ
  have H := (hf.contDiffAt (x := (k, g)) (hU.mem_nhds ⟨hk, mem_univ g⟩)).differentiableAt hn
  exact H.hasFDerivAt.comp_hasDerivAt k
    ((hasDerivAt_id k).prodMk (hasDerivAt_const k g))

theorem noiseParameterJet_regular {f : ℝ × ℝ → ℝ} {V : Set ℝ}
    (hV : IsOpen V) (hf : ContDiffOn ℝ 2 f (V ×ˢ univ)) {k : ℝ} (hk : k ∈ V) :
    (Continuous (fun g => (noiseParameterJet f k g).value) ∧
      Continuous (fun g => (noiseParameterJet f k g).first) ∧
      Continuous (fun g => (noiseParameterJet f k g).second)) ∧
      ∀ g, MomentKJet.Differentiates (fun t => noiseParameterJet f t g) k := by
  have hU : IsOpen (V ×ˢ (univ : Set ℝ)) := hV.prod isOpen_univ
  have h₁ : ContDiffOn ℝ 1 (firstNoisePartial f) (V ×ˢ univ) :=
    (hf.fderiv_of_isOpen hU (by norm_num)).clm_apply contDiffOn_const
  have h₂ : ContDiffOn ℝ 0 (secondNoisePartial f) (V ×ˢ univ) :=
    (h₁.fderiv_of_isOpen hU (by norm_num)).clm_apply contDiffOn_const
  have hfirst (t : ℝ) (ht : t ∈ V) (g : ℝ) :
      deriv (fun u => f (u, g)) t = firstNoisePartial f (t, g) :=
    (noise_partial_hasDerivAt hV hf (by norm_num) ht g).deriv
  have hsecond (g : ℝ) :
      deriv (deriv (fun u => f (u, g))) k = secondNoisePartial f (k, g) := by
    have he : deriv (fun u => f (u, g)) =ᶠ[𝓝 k]
        fun u => firstNoisePartial f (u, g) := by
      filter_upwards [hV.mem_nhds hk] with t ht
      exact hfirst t ht g
    rw [he.deriv_eq]
    exact (noise_partial_hasDerivAt hV h₁ (by norm_num) hk g).deriv
  have hc₀ : Continuous (fun g : ℝ => f (k, g)) :=
    hf.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
      (fun g => ⟨hk, mem_univ g⟩)
  have hc₁ : Continuous (fun g : ℝ => firstNoisePartial f (k, g)) :=
    h₁.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
      (fun g => ⟨hk, mem_univ g⟩)
  have hc₂ : Continuous (fun g : ℝ => secondNoisePartial f (k, g)) :=
    h₂.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
      (fun g => ⟨hk, mem_univ g⟩)
  refine ⟨⟨hc₀, ?_, ?_⟩, ?_⟩
  · simpa only [noiseParameterJet, hfirst k hk] using hc₁
  · simpa only [noiseParameterJet, hsecond] using hc₂
  · intro g
    have hreg : ContDiffAt ℝ 2 (fun t => f (t, g)) k :=
      (hf.contDiffAt (x := (k, g)) (hU.mem_nhds ⟨hk, mem_univ g⟩)).comp k
        (contDiffAt_id.prodMk contDiffAt_const)
    exact ⟨(hreg.differentiableAt (by norm_num)).hasDerivAt,
      ((hreg.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt⟩

theorem frozenRowsNoiseRegularity_of_joint {β : ℝ} (D : ScalarData β)
    (I : Set ℝ)
    (H : ∃ h₀ : ℝ, 0 < h₀ ∧
      ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z : ℝ, ∀ ε ∈ Icc (0 : ℝ) 1,
        ∀ j : ℕ, j < 11 → ∀ i : Fin 4,
          ContDiffOn ℝ 2
            (fun p : ℝ × ℝ => frozenRowsNoise β (cdf (D.μ : Measure ℝ))
              (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h z ε j i p.1 p.2)
            (frozenRowsKDomain ×ˢ univ)) :
    FrozenRowsNoiseRegularity D I := by
  obtain ⟨h₀, hh₀, H⟩ := H
  refine ⟨h₀, hh₀, ?_⟩
  intro r hr h hh hsmall z ε hε j hj
  have hreg := H r hr h hh hsmall z ε hε j hj
  have hV : IsOpen frozenRowsKDomain := isOpen_Ioo
  constructor
  · intro k hk i
    exact (noiseParameterJet_regular hV (hreg i) hk).1
  · intro g k hk i
    exact (noiseParameterJet_regular hV (hreg i) hk).2 g

end SKBarriers2.Corner
