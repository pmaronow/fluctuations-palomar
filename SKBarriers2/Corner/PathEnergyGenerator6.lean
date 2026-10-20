module

public import SKBarriers2.Corner.PathEnergyGenerator5
public import SKBarriers2.Corner.PathEnergyGeneratorSum

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic

namespace SKBarriers2.StepCalculus

local notation "E" => (Fin 3 → ℝ)

private theorem generator_directionalJet_two {g : E → ℝ}
    (hg : ContDiff ℝ 2 g) (v x : E) :
    directionalJet v 2 g x = fderiv ℝ (fderiv ℝ g) x v v := by
  have hd := ((hg.fderiv_right (m := 1) (by norm_num)).differentiable
    (by norm_num) x).hasFDerivAt
  have H := hd.clm_apply (hasFDerivAt_const v x)
  have H' := congrArg (fun D : E →L[ℝ] ℝ => D v) H.fderiv
  change directionalJet v 2 g x =
    fderiv ℝ g x 0+fderiv ℝ (fderiv ℝ g) x v v at H'
  simpa only [map_zero,zero_add] using H'

theorem pathGenerator_eq_fullGeneratorJet_zero {g : E → ℝ}
    (hg : ContDiff ℝ 2 g) (m dm ddm : ℝ) (f f₁ f₂ a q : E → ℝ)
    (v w b x : E) :
    pathGenerator m v f g x = fullGeneratorJet m dm ddm f f₁ f₂ g a q v w b 0 x := by
  simp only [pathGenerator,generator_directionalJet_two hg,fullGeneratorJet,
    generatorHessianJet,generatorProductJet,generatorDirectionalJet,Matrix.cons_val_zero]

theorem firstMovingAverageQuadratic_sub_test_eq_fullGeneratorJet
    {a : E → ℝ} (ha : ContDiff ℝ 2 a) (m dm ddm : ℝ)
    (f f₁ f₂ g q : E → ℝ) (v w b x : E) :
    firstMovingAverageQuadratic m dm v w f f₁ g a x-a x =
      fullGeneratorJet m dm ddm f f₁ f₂ g a q v w b 1 x := by
  simp only [firstMovingAverageQuadratic,pathGenerator,
    generator_directionalJet_two ha,mixedDirectionSource,fullGeneratorJet,
    generatorHessianJet,generatorProductJet,generatorDirectionalJet]
  norm_num
  ring

theorem secondMovingAverageQuadratic_sub_test_eq_fullGeneratorJet
    {q : E → ℝ} (hq : ContDiff ℝ 2 q) (m dm ddm : ℝ)
    (f f₁ f₂ g a : E → ℝ) (v w b x : E) :
    secondMovingAverageQuadratic m dm ddm v w b f f₁ f₂ g a q x-q x =
      fullGeneratorJet m dm ddm f f₁ f₂ g a q v w b 2 x := by
  simp only [secondMovingAverageQuadratic,pathGenerator,
    generator_directionalJet_two hq,mixedDirectionSource,fullGeneratorJet,
    generatorHessianJet,generatorProductJet,generatorDirectionalJet]
  norm_num
  ring

theorem abs_secondMovingAverageSource_sub_generator_cubic {B A H C d m dm ddm : ℝ}
    {f f₁ f₂ g a q : E → ℝ}
    (hf : QPotential 4 B f) (hf₁ : QBoundedJets 3 A f₁) (hf₂ : QBoundedJets 2 H f₂)
    (hg : QBoundedJets 4 C g) (ha : QBoundedJets 4 C a) (hq : QBoundedJets 4 C q)
    (hm : m ∈ Icc (0:ℝ) 1) (hdm : |dm| ≤ 1) (hddm : |ddm| ≤ 1)
    (hd : 0 ≤ d) (hd1 : d ≤ 1) (v w b x : E)
    (hv : ‖v‖ ≤ d) (hw : ‖w‖ ≤ d) (hb : ‖b‖ ≤ d) :
    |secondMovingAverageSource m dm ddm v w b f f₁ f₂ g a q x-q x-
      fullGeneratorJet m dm ddm f f₁ f₂ g a q v w b 2 x| ≤
      C*secondWeakCubicCoefficient B A H*d^3 := by
  have he := secondMovingAverageQuadratic_sub_test_eq_fullGeneratorJet
    (hq.smooth.of_le (by norm_num)) m dm ddm f f₁ f₂ g a v w b x
  have hs := abs_secondMovingAverageSource_sub_quadratic_cubic
    hf hf₁ hf₂ hg ha hq hm hdm hddm hd hd1 v w b x hv hw hb
  rw [← he]
  convert hs using 1
  congr 1
  ring

theorem eventually_secondMovingAverageSource_energy_le {B A H C₀ h eps L : ℝ}
    (hB : 0 ≤ B) (hA : 0 ≤ A) (hH : 0 ≤ H) (hC₀ : 0 ≤ C₀)
    (hh : 0 ≤ h) (heps : 0 < eps) :
    ∀ᶠ N : ℕ in atTop, ∀ (f f₁ f₂ g a q : E → ℝ) (m dm ddm : ℝ)
      (v w b x : E) (e : ℝ),
      QPotential 4 B f → QBoundedJets 3 A f₁ → QBoundedJets 2 H f₂ →
      QBoundedJets 4 (C₀*h/(N:ℝ)) g → QBoundedJets 4 (C₀*h/(N:ℝ)) a →
      QBoundedJets 4 (C₀*h/(N:ℝ)) q →
      m ∈ Icc (0:ℝ) 1 → |dm| ≤ 1 → |ddm| ≤ 1 →
      ‖v‖^2+‖w‖^2+‖b‖^2 ≤ e → e ≤ L*h/(N:ℝ) →
      |secondMovingAverageSource m dm ddm v w b f f₁ f₂ g a q x-q x-
        fullGeneratorJet m dm ddm f f₁ f₂ g a q v w b 2 x| ≤ (eps/(N:ℝ))*e := by
  filter_upwards [eventually_mesh_cubic_energy_le
    (L := L) (secondWeakCubicCoefficient_nonneg hB hA hH) hC₀ hh heps] with N hN
  intro f f₁ f₂ g a q m dm ddm v w b x e hf hf₁ hf₂ hg ha hq hm hdm hddm he hmesh
  have he0 : 0 ≤ e := by
    nlinarith only [he,sq_nonneg ‖v‖,sq_nonneg ‖w‖,sq_nonneg ‖b‖]
  have hv : ‖v‖ ≤ Real.sqrt e := Real.le_sqrt_of_sq_le
    (by nlinarith only [he,sq_nonneg ‖w‖,sq_nonneg ‖b‖])
  have hw : ‖w‖ ≤ Real.sqrt e := Real.le_sqrt_of_sq_le
    (by nlinarith only [he,sq_nonneg ‖v‖,sq_nonneg ‖b‖])
  have hb : ‖b‖ ≤ Real.sqrt e := Real.le_sqrt_of_sq_le
    (by nlinarith only [he,sq_nonneg ‖v‖,sq_nonneg ‖w‖])
  exact (abs_secondMovingAverageSource_sub_generator_cubic hf hf₁ hf₂ hg ha hq
    hm hdm hddm (Real.sqrt_nonneg e) (hN e he0 hmesh).1 v w b x hv hw hb).trans
      (hN e he0 hmesh).2

end SKBarriers2.StepCalculus
