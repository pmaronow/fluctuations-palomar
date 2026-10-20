module

public import SKBarriers2.Corner.PathEnergyGeneratorSum5

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic
namespace SKBarriers2.StepCalculus
local notation "E" => (Fin 3 → ℝ)

theorem actualGeneratorCurveSum_spatialJets {f g : ℝ → E → ℝ}
    {B A H C k : ℝ} (ps : List (ℝ → ℝ × E))
    (hreg : ∀ p ∈ ps, ContDiffAt ℝ 2 p k)
    (hfs : ∀ᶠ t in 𝓝 k, ContDiff ℝ 2 (f t))
    (hgs : ∀ᶠ t in 𝓝 k, ContDiff ℝ 2 (g t))
    (hfp : ∀ᶠ t in 𝓝 k, ∀ x, ContDiffAt ℝ 2 (fun z => f z x) t)
    (hgp : ∀ᶠ t in 𝓝 k, ∀ x, ContDiffAt ℝ 2 (fun z => g z x) t)
    (hf₁n : ∀ᶠ t in 𝓝 k, QBoundedJets 3 A (fun x => deriv (fun z => f z x) t))
    (hf₂n : ∀ᶠ t in 𝓝 k, QBoundedJets 3 H
      (fun x => deriv (deriv (fun z => f z x)) t))
    (hg₁n : ∀ᶠ t in 𝓝 k, QBoundedJets 3 C (fun x => deriv (fun z => g z x) t))
    (hg₂n : ∀ᶠ t in 𝓝 k, QBoundedJets 3 C
      (fun x => deriv (deriv (fun z => g z x)) t))
    (hf : QPotential 7 B (f k))
    (hf₁ : QBoundedJets 5 A (fun x => deriv (fun z => f z x) k))
    (hf₂ : QBoundedJets 3 H (fun x => deriv (deriv (fun z => f z x)) k))
    (hg : QBoundedJets 8 C (g k))
    (hg₁ : QBoundedJets 6 C (fun x => deriv (fun z => g z x) k))
    (hg₂ : QBoundedJets 4 C (fun x => deriv (deriv (fun z => g z x)) k))
    (hm : ∀ p ∈ ps, |(p k).1| ≤ 1 ∧ |deriv (fun t => (p t).1) k| ≤ 1 ∧
      |deriv (deriv (fun t => (p t).1)) k| ≤ 1) :
    let K := (1024 * (B + A + H) + 5) * C *
      (ps.map (fun p => ‖(p k).2‖ ^ 2 + ‖deriv (fun t => (p t).2) k‖ ^ 2 +
        ‖deriv (deriv (fun t => (p t).2)) k‖ ^ 2)).sum
    let J := fun t x => pathGeneratorSum (f t) (g t) (ps.map (fun p => p t)) x
    QBoundedJets 6 K (J k) ∧
      QBoundedJets 4 K (fun x => deriv (fun t => J t x) k) ∧
      QBoundedJets 2 K (fun x => deriv (deriv (fun t => J t x)) k) := by
  let f₁ := fun t x => deriv (fun z => f z x) t
  let f₂ := fun t x => deriv (deriv (fun z => f z x)) t
  let g₁ := fun t x => deriv (fun z => g z x) t
  let g₂ := fun t x => deriv (deriv (fun z => g z x)) t
  have hjet (p) (hp : p ∈ ps) := curveFullGeneratorJet_twoJet p (hreg p hp)
    hfs hgs hfp hgp hf₁n hf₂n hg₁n hg₂n
  have hid (c : Fin 3) :
      fullGeneratorCurveSumJet (f k) (f₁ k) (f₂ k) (g k) (g₁ k) (g₂ k) k ps c =
      fun x => iteratedDeriv c.val
        (fun t => pathGeneratorSum (f t) (g t) (ps.map (fun p => p t)) x) k := by
    funext x
    exact fullGeneratorCurveSumJet_eq_iteratedDeriv ps hgs
      (fun p hp => (hjet p hp).1) (fun p hp => (hjet p hp).2) c x
  have Hjets := qBoundedJets_fullGeneratorCurveSumJet hf hf₁ hf₂ hg hg₁ hg₂ k ps hm
  dsimp only at Hjets ⊢
  rw [hid 0,hid 1,hid 2] at Hjets
  simpa [iteratedDeriv_succ,iteratedDeriv_zero] using Hjets

end SKBarriers2.StepCalculus
