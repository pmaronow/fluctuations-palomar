module

public import SKBarriers2.Corner.PathEnergyGenerator2

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic

namespace SKBarriers2.StepCalculus

local notation "E" => (Fin 3 → ℝ)

theorem generatorProductJet_hasDerivAt
    {m m₁ m₂ : ℝ → ℝ} {A A₁ A₂ B B₁ B₂ : ℝ → E → ℝ} {k : ℝ}
    (hm : HasDerivAt m (m₁ k) k)
    (hA : ∀ x, HasDerivAt (fun t => A t x) (A₁ k x) k)
    (hB : ∀ x, HasDerivAt (fun t => B t x) (B₁ k x) k) (x : E) :
    HasDerivAt (fun t => generatorProductJet (m t) (m₁ t) (m₂ t)
        ![A t,A₁ t,A₂ t] ![B t,B₁ t,B₂ t] 0 x)
      (generatorProductJet (m k) (m₁ k) (m₂ k)
        ![A k,A₁ k,A₂ k] ![B k,B₁ k,B₂ k] 1 x) k := by
  convert ((hm.mul (hA x)).mul (hB x)) using 1
  · funext t
    norm_num [generatorProductJet,Pi.mul_apply]
  · norm_num [generatorProductJet,Pi.mul_apply]
    ring

theorem generatorProductJet_first_hasDerivAt
    {m m₁ m₂ : ℝ → ℝ} {A A₁ A₂ B B₁ B₂ : ℝ → E → ℝ} {k : ℝ}
    (hm : HasDerivAt m (m₁ k) k)
    (hA : ∀ x, HasDerivAt (fun t => A t x) (A₁ k x) k)
    (hB : ∀ x, HasDerivAt (fun t => B t x) (B₁ k x) k)
    (hm₁ : HasDerivAt m₁ (m₂ k) k)
    (hA₁ : ∀ x, HasDerivAt (fun t => A₁ t x) (A₂ k x) k)
    (hB₁ : ∀ x, HasDerivAt (fun t => B₁ t x) (B₂ k x) k) (x : E) :
    HasDerivAt (fun t => generatorProductJet (m t) (m₁ t) (m₂ t)
        ![A t,A₁ t,A₂ t] ![B t,B₁ t,B₂ t] 1 x)
      (generatorProductJet (m k) (m₁ k) (m₂ k)
        ![A k,A₁ k,A₂ k] ![B k,B₁ k,B₂ k] 2 x) k := by
  convert ((((hm₁.mul (hA x)).mul (hB x)).add
    ((hm.mul (hA₁ x)).mul (hB x))).add ((hm.mul (hA x)).mul (hB₁ x))) using 1
  · funext t
    norm_num [generatorProductJet,Pi.mul_apply,Pi.add_apply]
  · norm_num [generatorProductJet,Pi.mul_apply]
    ring

theorem generatorProductJet_eq_iteratedDeriv_of_hasDerivAt
    {m m₁ m₂ : ℝ → ℝ} {A A₁ A₂ B B₁ B₂ : ℝ → E → ℝ} {k : ℝ}
    (hm : ∀ᶠ t in 𝓝 k, HasDerivAt m (m₁ t) t)
    (hA : ∀ᶠ t in 𝓝 k, ∀ x, HasDerivAt (fun q => A q x) (A₁ t x) t)
    (hB : ∀ᶠ t in 𝓝 k, ∀ x, HasDerivAt (fun q => B q x) (B₁ t x) t)
    (hm₁ : HasDerivAt m₁ (m₂ k) k)
    (hA₁ : ∀ x, HasDerivAt (fun q => A₁ q x) (A₂ k x) k)
    (hB₁ : ∀ x, HasDerivAt (fun q => B₁ q x) (B₂ k x) k)
    (c : Fin 3) (x : E) :
    generatorProductJet (m k) (m₁ k) (m₂ k)
      ![A k,A₁ k,A₂ k] ![B k,B₁ k,B₂ k] c x =
      iteratedDeriv c.val (fun t => m t*A t x*B t x) k := by
  let P := fun t => m t*A t x*B t x
  let P₁ := fun t => m₁ t*A t x*B t x+m t*A₁ t x*B t x+m t*A t x*B₁ t x
  have hfirst : ∀ᶠ t in 𝓝 k, HasDerivAt P (P₁ t) t := by
    filter_upwards [hm,hA,hB] with t hmt hAt hBt
    convert ((hmt.mul (hAt x)).mul (hBt x)) using 1
    dsimp only [P₁,Pi.mul_apply]
    ring
  have hderiv : deriv P =ᶠ[𝓝 k] P₁ := by
    filter_upwards [hfirst] with t ht
    exact ht.deriv
  have hsecond : HasDerivAt P₁
      (generatorProductJet (m k) (m₁ k) (m₂ k)
        ![A k,A₁ k,A₂ k] ![B k,B₁ k,B₂ k] 2 x) k := by
    have hmk := hm.self_of_nhds
    have hAk := hA.self_of_nhds x
    have hBk := hB.self_of_nhds x
    convert ((((hm₁.mul hAk).mul hBk).add
      ((hmk.mul (hA₁ x)).mul hBk)).add ((hmk.mul hAk).mul (hB₁ x))) using 1
    norm_num [generatorProductJet]
    ring
  fin_cases c
  · norm_num [generatorProductJet]
  · simpa [generatorProductJet,iteratedDeriv_one,P,P₁] using hfirst.self_of_nhds.deriv.symm
  · have H := hsecond.deriv.symm
    rw [← hderiv.deriv_eq] at H
    simpa [iteratedDeriv_succ,iteratedDeriv_zero,P] using H

end SKBarriers2.StepCalculus
