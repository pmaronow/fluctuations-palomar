module

public import SKBarriers2.Corner.PathEnergyGeneratorSum2
public import SKBarriers2.Corner.PathEnergyGenerator9
public import SKBarriers2.Corner.PathEnergyRecursions3

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic
namespace SKBarriers2.StepCalculus
local notation "E" => (Fin 3 → ℝ)

theorem hasDerivAt_generatorDirectionalJet_zero {F F₁ F₂ : ℝ → E → ℝ}
    {v v₁ v₂ : ℝ → E} {A k : ℝ}
    (hF : ∀ᶠ t in 𝓝 k, ∀ x, DifferentiableAt ℝ (F t) x)
    (hd : ∀ᶠ t in 𝓝 k, ∀ x, HasDerivAt (fun q => F q x) (F₁ t x) t)
    (hF₁ : ∀ᶠ t in 𝓝 k, QBoundedJets 2 A (F₁ t))
    (hv : HasDerivAt v (v₁ k) k) (x : E) :
    HasDerivAt
      (fun t => generatorDirectionalJet (F t) (F₁ t) (F₂ t) (v t) (v₁ t) (v₂ t) 0 x)
      (generatorDirectionalJet (F k) (F₁ k) (F₂ k) (v k) (v₁ k) (v₂ k) 1 x) k := by
  simpa only [generatorDirectionalJet,Matrix.cons_val_zero,Matrix.cons_val_one] using
    hasDerivAt_moving_spatial_of_uniform_jets hF hd hF₁ hv x

theorem hasDerivAt_generatorDirectionalJet_one {F F₁ F₂ : ℝ → E → ℝ}
    {v v₁ v₂ : ℝ → E} {A H k : ℝ}
    (hF : ∀ᶠ t in 𝓝 k, ∀ x, DifferentiableAt ℝ (F t) x)
    (hd₀ : ∀ᶠ t in 𝓝 k, ∀ x, HasDerivAt (fun q => F q x) (F₁ t x) t)
    (hd₁ : ∀ᶠ t in 𝓝 k, ∀ x, HasDerivAt (fun q => F₁ q x) (F₂ t x) t)
    (hF₁ : ∀ᶠ t in 𝓝 k, QBoundedJets 2 A (F₁ t))
    (hF₂ : ∀ᶠ t in 𝓝 k, QBoundedJets 2 H (F₂ t))
    (hv : HasDerivAt v (v₁ k) k) (hv₁ : HasDerivAt v₁ (v₂ k) k) (x : E) :
    HasDerivAt
      (fun t => generatorDirectionalJet (F t) (F₁ t) (F₂ t) (v t) (v₁ t) (v₂ t) 1 x)
      (generatorDirectionalJet (F k) (F₁ k) (F₂ k) (v k) (v₁ k) (v₂ k) 2 x) k := by
  have hF₁diff : ∀ᶠ t in 𝓝 k, ∀ y, DifferentiableAt ℝ (F₁ t) y := by
    filter_upwards [hF₁] with t ht y
    exact ht.smooth.differentiable (by norm_num) y
  have HA := hasDerivAt_moving_spatial_of_uniform_jets hF₁diff hd₁ hF₂ hv x
  have HB := hasDerivAt_moving_spatial_of_uniform_jets hF hd₀ hF₁ hv₁ x
  change HasDerivAt
    (fun t => fderiv ℝ (F₁ t) x (v t) + fderiv ℝ (F t) x (v₁ t))
    (fderiv ℝ (F₂ k) x (v k) + 2 * fderiv ℝ (F₁ k) x (v₁ k) +
      fderiv ℝ (F k) x (v₂ k)) k
  convert HA.add HB using 1
  ring

theorem iteratedDeriv_eq_of_twoJet {J : Fin 3 → ℝ → ℝ} {k : ℝ}
    (h₀ : ∀ᶠ t in 𝓝 k, HasDerivAt (J 0) (J 1 t) t)
    (h₁ : HasDerivAt (J 1) (J 2 k) k) (c : Fin 3) :
    iteratedDeriv c.val (J 0) k = J c k := by
  have he : deriv (J 0) =ᶠ[𝓝 k] J 1 := by
    filter_upwards [h₀] with t ht
    exact ht.deriv
  fin_cases c
  · simp
  · simpa [iteratedDeriv_one] using h₀.self_of_nhds.deriv
  · simpa [iteratedDeriv_succ,iteratedDeriv_zero,he.deriv_eq] using h₁.deriv

theorem fullGeneratorJet_eq_iteratedDeriv_of_hasDerivAt
    {m m₁ m₂ : ℝ → ℝ} {F F₁ F₂ g a q : ℝ → E → ℝ}
    {v v₁ v₂ : ℝ → E} {k : ℝ}
    (hm : ∀ᶠ t in 𝓝 k, HasDerivAt m (m₁ t) t)
    (hm₁ : HasDerivAt m₁ (m₂ k) k)
    (hA : ∀ᶠ t in 𝓝 k, ∀ x, HasDerivAt
      (fun z => generatorDirectionalJet (F z) (F₁ z) (F₂ z) (v z) (v₁ z) (v₂ z) 0 x)
      (generatorDirectionalJet (F t) (F₁ t) (F₂ t) (v t) (v₁ t) (v₂ t) 1 x) t)
    (hA₁ : ∀ x, HasDerivAt
      (fun z => generatorDirectionalJet (F z) (F₁ z) (F₂ z) (v z) (v₁ z) (v₂ z) 1 x)
      (generatorDirectionalJet (F k) (F₁ k) (F₂ k) (v k) (v₁ k) (v₂ k) 2 x) k)
    (hB : ∀ᶠ t in 𝓝 k, ∀ x, HasDerivAt
      (fun z => generatorDirectionalJet (g z) (a z) (q z) (v z) (v₁ z) (v₂ z) 0 x)
      (generatorDirectionalJet (g t) (a t) (q t) (v t) (v₁ t) (v₂ t) 1 x) t)
    (hB₁ : ∀ x, HasDerivAt
      (fun z => generatorDirectionalJet (g z) (a z) (q z) (v z) (v₁ z) (v₂ z) 1 x)
      (generatorDirectionalJet (g k) (a k) (q k) (v k) (v₁ k) (v₂ k) 2 x) k)
    (hC : ∀ᶠ t in 𝓝 k, ∀ x, HasDerivAt
      (fun z => generatorHessianJet (g z) (a z) (q z) (v z) (v₁ z) (v₂ z) 0 x)
      (generatorHessianJet (g t) (a t) (q t) (v t) (v₁ t) (v₂ t) 1 x) t)
    (hC₁ : ∀ x, HasDerivAt
      (fun z => generatorHessianJet (g z) (a z) (q z) (v z) (v₁ z) (v₂ z) 1 x)
      (generatorHessianJet (g k) (a k) (q k) (v k) (v₁ k) (v₂ k) 2 x) k)
    (c : Fin 3) (x : E) :
    fullGeneratorJet (m k) (m₁ k) (m₂ k) (F k) (F₁ k) (F₂ k)
      (g k) (a k) (q k) (v k) (v₁ k) (v₂ k) c x =
    iteratedDeriv c.val (fun t => fullGeneratorJet (m t) (m₁ t) (m₂ t)
      (F t) (F₁ t) (F₂ t) (g t) (a t) (q t) (v t) (v₁ t) (v₂ t) 0 x) k := by
  let A := fun t i x => generatorDirectionalJet (F t) (F₁ t) (F₂ t) (v t) (v₁ t) (v₂ t) i x
  let B := fun t i x => generatorDirectionalJet (g t) (a t) (q t) (v t) (v₁ t) (v₂ t) i x
  have hAe (t : ℝ) : ![A t 0,A t 1,A t 2] = A t := by
    funext i
    fin_cases i <;> rfl
  have hBe (t : ℝ) : ![B t 0,B t 1,B t 2] = B t := by
    funext i
    fin_cases i <;> rfl
  have hzero : ∀ᶠ t in 𝓝 k, HasDerivAt
      (fun z => fullGeneratorJet (m z) (m₁ z) (m₂ z) (F z) (F₁ z) (F₂ z)
        (g z) (a z) (q z) (v z) (v₁ z) (v₂ z) 0 x)
      (fullGeneratorJet (m t) (m₁ t) (m₂ t) (F t) (F₁ t) (F₂ t)
        (g t) (a t) (q t) (v t) (v₁ t) (v₂ t) 1 x) t := by
    filter_upwards [hm,hA,hB,hC] with t hmt hAt hBt hCt
    have HP := generatorProductJet_hasDerivAt
      (A := fun t => A t 0) (A₁ := fun t => A t 1) (A₂ := fun t => A t 2)
      (B := fun t => B t 0) (B₁ := fun t => B t 1) (B₂ := fun t => B t 2)
      (m₂ := m₂) hmt hAt hBt x
    simp only [hAe,hBe] at HP
    exact HP.add (hCt x)
  have HP := generatorProductJet_first_hasDerivAt
    (A := fun t => A t 0) (A₁ := fun t => A t 1) (A₂ := fun t => A t 2)
    (B := fun t => B t 0) (B₁ := fun t => B t 1) (B₂ := fun t => B t 2)
    hm.self_of_nhds hA.self_of_nhds hB.self_of_nhds hm₁ hA₁ hB₁ x
  simp only [hAe,hBe] at HP
  exact (iteratedDeriv_eq_of_twoJet
    (J := fun i t => fullGeneratorJet (m t) (m₁ t) (m₂ t) (F t) (F₁ t) (F₂ t)
      (g t) (a t) (q t) (v t) (v₁ t) (v₂ t) i x)
    hzero (HP.add (hC₁ x)) c).symm

end SKBarriers2.StepCalculus
