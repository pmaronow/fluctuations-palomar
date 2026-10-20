module

public import SKBarriers2.Corner.PathEnergyGeneratorSum4

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic
namespace SKBarriers2.StepCalculus
local notation "E" => (Fin 3 → ℝ)

theorem curveFullGeneratorJet_twoJet {f g : ℝ → E → ℝ}
    {A H C D k : ℝ} (p : ℝ → ℝ × E) (hp : ContDiffAt ℝ 2 p k)
    (hfs : ∀ᶠ t in 𝓝 k, ContDiff ℝ 2 (f t))
    (hgs : ∀ᶠ t in 𝓝 k, ContDiff ℝ 2 (g t))
    (hfp : ∀ᶠ t in 𝓝 k, ∀ x, ContDiffAt ℝ 2 (fun z => f z x) t)
    (hgp : ∀ᶠ t in 𝓝 k, ∀ x, ContDiffAt ℝ 2 (fun z => g z x) t)
    (hf₁ : ∀ᶠ t in 𝓝 k, QBoundedJets 3 A (fun x => deriv (fun z => f z x) t))
    (hf₂ : ∀ᶠ t in 𝓝 k, QBoundedJets 3 H
      (fun x => deriv (deriv (fun z => f z x)) t))
    (hg₁ : ∀ᶠ t in 𝓝 k, QBoundedJets 3 C (fun x => deriv (fun z => g z x) t))
    (hg₂ : ∀ᶠ t in 𝓝 k, QBoundedJets 3 D
      (fun x => deriv (deriv (fun z => g z x)) t)) :
    let f₁ := fun t x => deriv (fun z => f z x) t
    let f₂ := fun t x => deriv (deriv (fun z => f z x)) t
    let g₁ := fun t x => deriv (fun z => g z x) t
    let g₂ := fun t x => deriv (deriv (fun z => g z x)) t
    (∀ᶠ t in 𝓝 k, ∀ x,
      HasDerivAt (fun z => curveFullGeneratorJet f f₁ f₂ g g₁ g₂ p 0 z x)
        (curveFullGeneratorJet f f₁ f₂ g g₁ g₂ p 1 t x) t) ∧
    (∀ x, HasDerivAt (fun z => curveFullGeneratorJet f f₁ f₂ g g₁ g₂ p 1 z x)
      (curveFullGeneratorJet f f₁ f₂ g g₁ g₂ p 2 k x) k) := by
  dsimp only
  let f₁ := fun t x => deriv (fun z => f z x) t
  let f₂ := fun t x => deriv (deriv (fun z => f z x)) t
  let g₁ := fun t x => deriv (fun z => g z x) t
  let g₂ := fun t x => deriv (deriv (fun z => g z x)) t
  let m := fun t => (p t).1
  let m₁ := deriv m
  let m₂ := deriv (deriv m)
  let v := fun t => (p t).2
  let v₁ := deriv v
  let v₂ := deriv (deriv v)
  have hm : ∀ᶠ t in 𝓝 k, HasDerivAt m (m₁ t) t := by
    filter_upwards [hp.eventually (by norm_num)] with t ht
    exact (ht.fst.differentiableAt (by norm_num)).hasDerivAt
  have hm₁ : HasDerivAt m₁ (m₂ k) k :=
    ((hp.fst.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
  have hv : ∀ᶠ t in 𝓝 k, HasDerivAt v (v₁ t) t := by
    filter_upwards [hp.eventually (by norm_num)] with t ht
    exact (ht.snd.differentiableAt (by norm_num)).hasDerivAt
  have hv₁ : HasDerivAt v₁ (v₂ k) k :=
    ((hp.snd.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
  have hfd₀ : ∀ᶠ t in 𝓝 k, ∀ x, HasDerivAt (fun z => f z x) (f₁ t x) t := by
    filter_upwards [hfp] with t ht x
    exact ((ht x).differentiableAt (by norm_num)).hasDerivAt
  have hfd₁ : ∀ᶠ t in 𝓝 k, ∀ x, HasDerivAt (fun z => f₁ z x) (f₂ t x) t := by
    filter_upwards [hfp] with t ht x
    exact (((ht x).derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
  have hgd₀ : ∀ᶠ t in 𝓝 k, ∀ x, HasDerivAt (fun z => g z x) (g₁ t x) t := by
    filter_upwards [hgp] with t ht x
    exact ((ht x).differentiableAt (by norm_num)).hasDerivAt
  have hgd₁ : ∀ᶠ t in 𝓝 k, ∀ x, HasDerivAt (fun z => g₁ z x) (g₂ t x) t := by
    filter_upwards [hgp] with t ht x
    exact (((ht x).derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
  have hfdiff : ∀ᶠ t in 𝓝 k, ∀ x, DifferentiableAt ℝ (f t) x := by
    filter_upwards [hfs] with t ht x
    exact ht.differentiable (by norm_num) x
  have hgdiff : ∀ᶠ t in 𝓝 k, ∀ x, DifferentiableAt ℝ (g t) x := by
    filter_upwards [hgs] with t ht x
    exact ht.differentiable (by norm_num) x
  have hf₁' := hf₁.mono (fun t ht => ht.of_le (by norm_num : 2 ≤ 3))
  have hf₂' := hf₂.mono (fun t ht => ht.of_le (by norm_num : 2 ≤ 3))
  have hg₁' := hg₁.mono (fun t ht => ht.of_le (by norm_num : 2 ≤ 3))
  have hg₂' := hg₂.mono (fun t ht => ht.of_le (by norm_num : 2 ≤ 3))
  let U := fun t i x => generatorDirectionalJet (f t) (f₁ t) (f₂ t) (v t) (v₁ t) (v₂ t) i x
  let V := fun t i x => generatorDirectionalJet (g t) (g₁ t) (g₂ t) (v t) (v₁ t) (v₂ t) i x
  have hU (t : ℝ) : ![U t 0,U t 1,U t 2] = U t := by
    funext i
    fin_cases i <;> rfl
  have hV (t : ℝ) : ![V t 0,V t 1,V t 2] = V t := by
    funext i
    fin_cases i <;> rfl
  have hU₀ : ∀ᶠ t in 𝓝 k, ∀ x, HasDerivAt (fun z => U z 0 x) (U t 1 x) t := by
    filter_upwards [eventually_eventually_nhds.mpr hfdiff,
      eventually_eventually_nhds.mpr hfd₀,eventually_eventually_nhds.mpr hf₁',hv]
      with t hft hdt h₁t hvt x
    exact hasDerivAt_generatorDirectionalJet_zero hft hdt h₁t hvt x
  have hV₀ : ∀ᶠ t in 𝓝 k, ∀ x, HasDerivAt (fun z => V z 0 x) (V t 1 x) t := by
    filter_upwards [eventually_eventually_nhds.mpr hgdiff,
      eventually_eventually_nhds.mpr hgd₀,eventually_eventually_nhds.mpr hg₁',hv]
      with t hgt hdt h₁t hvt x
    exact hasDerivAt_generatorDirectionalJet_zero hgt hdt h₁t hvt x
  have hU₁ (x : E) : HasDerivAt (fun z => U z 1 x) (U k 2 x) k :=
    hasDerivAt_generatorDirectionalJet_one hfdiff hfd₀ hfd₁ hf₁' hf₂' hv.self_of_nhds hv₁ x
  have hV₁ (x : E) : HasDerivAt (fun z => V z 1 x) (V k 2 x) k :=
    hasDerivAt_generatorDirectionalJet_one hgdiff hgd₀ hgd₁ hg₁' hg₂' hv.self_of_nhds hv₁ x
  have hW₀ : ∀ᶠ t in 𝓝 k, ∀ x, HasDerivAt
      (fun z => generatorHessianJet (g z) (g₁ z) (g₂ z) (v z) (v₁ z) (v₂ z) 0 x)
      (generatorHessianJet (g t) (g₁ t) (g₂ t) (v t) (v₁ t) (v₂ t) 1 x) t := by
    filter_upwards [eventually_eventually_nhds.mpr hgs,
      eventually_eventually_nhds.mpr hgd₀,eventually_eventually_nhds.mpr hg₁,hv]
      with t hgt hdt h₁t hvt x
    exact hasDerivAt_generatorHessianJet_zero hgt hdt h₁t hvt x
  have hW₁ (x : E) := hasDerivAt_generatorHessianJet_one hgs hgd₀ hgd₁
    hg₁ hg₂ hv.self_of_nhds hv₁ x
  refine ⟨?_,?_⟩
  · filter_upwards [hm,hU₀,hV₀,hW₀] with t hmt hUt hVt hWt x
    have HP := generatorProductJet_hasDerivAt
      (A := fun t => U t 0) (A₁ := fun t => U t 1) (A₂ := fun t => U t 2)
      (B := fun t => V t 0) (B₁ := fun t => V t 1) (B₂ := fun t => V t 2)
      (m₂ := m₂) hmt hUt hVt x
    simp only [hU,hV] at HP
    exact HP.add (hWt x)
  · intro x
    have HP := generatorProductJet_first_hasDerivAt
      (A := fun t => U t 0) (A₁ := fun t => U t 1) (A₂ := fun t => U t 2)
      (B := fun t => V t 0) (B₁ := fun t => V t 1) (B₂ := fun t => V t 2)
      hm.self_of_nhds hU₀.self_of_nhds hV₀.self_of_nhds hm₁ hU₁ hV₁ x
    simp only [hU,hV] at HP
    exact HP.add (hW₁ x)

end SKBarriers2.StepCalculus
