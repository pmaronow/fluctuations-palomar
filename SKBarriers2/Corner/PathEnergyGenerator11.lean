module

public import SKBarriers2.Corner.PathEnergyGenerator10
public import SKBarriers2.Corner.PathEnergyGenerator7

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic

namespace SKBarriers2.StepCalculus

local notation "E" => (Fin 3 → ℝ)

theorem eventually_weakGeneratorDefect_sources {B A H C₀ h eps L : ℝ}
    (hB : 0 ≤ B) (hA : 0 ≤ A) (hH : 0 ≤ H)
    (hC₀ : 0 < C₀) (hh : 0 < h) (heps : 0 < eps) :
    ∀ᶠ N : ℕ in atTop, ∀ (f f₁ f₂ g a q : E → ℝ) (m dm ddm : ℝ)
      (v w b : E) (e : ℝ),
      QPotential 8 B f → QBoundedJets 4 A f₁ → QBoundedJets 2 H f₂ →
      QBoundedJets 8 (C₀*h/(N:ℝ)) g → QBoundedJets 5 (C₀*h/(N:ℝ)) a →
      QBoundedJets 4 (C₀*h/(N:ℝ)) q →
      m ∈ Icc (0:ℝ) 1 → |dm| ≤ 1 → |ddm| ≤ 1 →
      ‖v‖^2+‖w‖^2+‖b‖^2 ≤ e → e ≤ L*h/(N:ℝ) →
      QBoundedJets 4 ((eps/(N:ℝ))*e) (tiltedGeneratorDefect m v f g) ∧
        QBoundedJets 2 ((eps/(N:ℝ))*e) (fun x =>
          firstTiltedAverageSource m v f f₁ g a dm w x-a x-
            fullGeneratorJet m dm ddm f f₁ f₂ g a q v w b 1 x) ∧
        ∀ x, |secondMovingAverageSource m dm ddm v w b f f₁ f₂ g a q x-q x-
          fullGeneratorJet m dm ddm f f₁ f₂ g a q v w b 2 x| ≤ (eps/(N:ℝ))*e := by
  filter_upwards [eventually_tiltedGeneratorDefect_energy_le (L := L) hB hC₀ hh heps,
    eventually_firstMovingAverageSource_energy_le (L := L) hB hA hC₀ hh heps,
    eventually_secondMovingAverageSource_energy_le (L := L) hB hA hH hC₀.le hh.le heps]
    with N hval hfirst hsecond
  intro f f₁ f₂ g a q m dm ddm v w b e hf hf₁ hf₂ hg ha hq hm hdm hddm he hmesh
  have he0 : 0 ≤ e := by
    nlinarith only [he,sq_nonneg ‖v‖,sq_nonneg ‖w‖,sq_nonneg ‖b‖]
  have hv : ‖v‖^2 ≤ e := by nlinarith only [he,sq_nonneg ‖w‖,sq_nonneg ‖b‖]
  have hvw : ‖v‖^2+‖w‖^2 ≤ e := by nlinarith only [he,sq_nonneg ‖b‖]
  refine ⟨hval f g hf hg m hm v e he0 hv hmesh,?_,?_⟩
  · exact hfirst f f₁ f₂ g a q m dm ddm v w b e (hf.of_le (by norm_num : 6 ≤ 8))
      hf₁ (hg.of_le (by norm_num : 5 ≤ 8)) ha hm hdm hvw hmesh
  · intro x
    exact hsecond f f₁ f₂ g a q m dm ddm v w b x e (hf.of_le (by norm_num : 4 ≤ 8))
      (hf₁.of_le (by norm_num : 3 ≤ 4)) hf₂ (hg.of_le (by norm_num : 4 ≤ 8))
      (ha.of_le (by norm_num : 4 ≤ 5)) hq hm hdm hddm he hmesh

end SKBarriers2.StepCalculus
