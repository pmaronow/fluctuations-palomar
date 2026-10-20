module

public import SKBarriers2.Corner.PathEnergyGeneratorSum

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic

namespace SKBarriers2.StepCalculus

local notation "E" => (Fin 3 → ℝ)

theorem fullGeneratorJet_sub_eq_generatorProductJet
    {F F₁ F₂ G G₁ G₂ : E → ℝ}
    (hF : Differentiable ℝ F) (hF₁ : Differentiable ℝ F₁)
    (hF₂ : Differentiable ℝ F₂) (hG : Differentiable ℝ G)
    (hG₁ : Differentiable ℝ G₁) (hG₂ : Differentiable ℝ G₂)
    (m dm ddm : ℝ) (g a q : E → ℝ) (v w b : E) (c : Fin 3) (x : E) :
    fullGeneratorJet m dm ddm F F₁ F₂ g a q v w b c x-
      fullGeneratorJet m dm ddm G G₁ G₂ g a q v w b c x =
      generatorProductJet m dm ddm
        (generatorDirectionalJet (fun y => F y-G y) (fun y => F₁ y-G₁ y)
          (fun y => F₂ y-G₂ y) v w b)
        (generatorDirectionalJet g a q v w b) c x := by
  have he (P Q : E → ℝ) (hP : Differentiable ℝ P) (hQ : Differentiable ℝ Q)
      (z : E) : fderiv ℝ (fun y => P y-Q y) x z = fderiv ℝ P x z-fderiv ℝ Q x z := by
    rw [fderiv_fun_sub (hP x) (hQ x)]
    rfl
  fin_cases c <;>
    norm_num [fullGeneratorJet,generatorProductJet,generatorDirectionalJet,
      he F G hF hG,he F₁ G₁ hF₁ hG₁,he F₂ G₂ hF₂ hG₂] <;> ring

theorem qBoundedJets_fullGeneratorJet_sub {H C e m dm ddm : ℝ}
    {F F₁ F₂ G G₁ G₂ g a q : E → ℝ}
    (hF : Differentiable ℝ F) (hF₁ : Differentiable ℝ F₁)
    (hF₂ : Differentiable ℝ F₂) (hG : Differentiable ℝ G)
    (hG₁ : Differentiable ℝ G₁) (hG₂ : Differentiable ℝ G₂)
    (hD : QBoundedJets 5 H (fun y => F y-G y))
    (hD₁ : QBoundedJets 3 H (fun y => F₁ y-G₁ y))
    (hD₂ : QBoundedJets 1 H (fun y => F₂ y-G₂ y))
    (hg : QBoundedJets 5 C g) (ha : QBoundedJets 3 C a) (hq : QBoundedJets 1 C q)
    (hm : |m| ≤ 1) (hdm : |dm| ≤ 1) (hddm : |ddm| ≤ 1)
    (v w b : E) (he : ‖v‖^2+‖w‖^2+‖b‖^2 ≤ e) :
    let D := fun c x => fullGeneratorJet m dm ddm F F₁ F₂ g a q v w b c x-
      fullGeneratorJet m dm ddm G G₁ G₂ g a q v w b c x
    QBoundedJets 4 (256*H*C*e) (D 0) ∧
      QBoundedJets 2 (256*H*C*e) (D 1) ∧
      QBoundedJets 0 (256*H*C*e) (D 2) := by
  have heq : (fun c x => fullGeneratorJet m dm ddm F F₁ F₂ g a q v w b c x-
      fullGeneratorJet m dm ddm G G₁ G₂ g a q v w b c x) =
      generatorProductJet m dm ddm
        (generatorDirectionalJet (fun y => F y-G y) (fun y => F₁ y-G₁ y)
          (fun y => F₂ y-G₂ y) v w b)
        (generatorDirectionalJet g a q v w b) := by
    funext c x
    exact fullGeneratorJet_sub_eq_generatorProductJet hF hF₁ hF₂ hG hG₁ hG₂
      m dm ddm g a q v w b c x
  dsimp only
  rw [congrFun heq 0,congrFun heq 1,congrFun heq 2]
  exact qBoundedJets_generatorComparisonJet hD hD₁ hD₂ hg ha hq hm hdm hddm v w b he

end SKBarriers2.StepCalculus
