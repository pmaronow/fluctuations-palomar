module

public import SKConstants.Completion.LBase.CurvatureIntegral

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants.Completion.LBase
open SKConstantsOAI.ZeroTemperatureSK
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedLipschitzDrift.solution
variable {Ω : Type*} [MeasurableSpace Ω]

def actualCurvatureIntervalSum (W : BrownianSystem Ω) (β : ℝ)
    (S T : ℝ≥0) (l : ℕ) (w : Ω) : ℝ :=
  actualCurvatureLeftSum W β (brownianDyadicGrid T) 1 l w -
    actualCurvatureLeftSum W β (brownianDyadicGrid S) 1 l w

theorem actual_curvature_interval_meanSquare_tendsto
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (S T : ℝ≥0) :
    Tendsto (fun l => ∫ w, (actualCurvatureIntervalSum W β S T l w -
      actualParisiMagnetizationIncrement W β S T w)^2 ∂W.law) atTop (𝓝 0) := by
  let X := fun l w => actualCurvatureLeftSum W β (brownianDyadicGrid T) 1 l w -
    actualParisiMagnetizationObservable W β T w
  let Y := fun l w => actualCurvatureLeftSum W β (brownianDyadicGrid S) 1 l w -
    actualParisiMagnetizationObservable W β S w
  have hX (l : ℕ) : MemLp (X l) 2 W.law :=
    (memLp_actualCurvatureLeftSum W β (brownianDyadicGrid T) 1 l).sub (memLp_actualMagnetization W β T)
  have hY (l : ℕ) : MemLp (Y l) 2 W.law :=
    (memLp_actualCurvatureLeftSum W β (brownianDyadicGrid S) 1 l).sub (memLp_actualMagnetization W β S)
  have h := tendsto_integral_sq_sub
    (fun l => (hX l).aestronglyMeasurable.aemeasurable)
    (fun l => (hY l).aestronglyMeasurable.aemeasurable)
    (fun l => (hX l).integrable_sq) (fun l => (hY l).integrable_sq)
    (actual_curvature_dyadic_meanSquare_tendsto W β hβ T)
    (actual_curvature_dyadic_meanSquare_tendsto W β hβ S)
  convert h using 1
  funext l
  apply integral_congr_ae
  apply ae_of_all
  intro w
  dsimp only [actualCurvatureIntervalSum, actualParisiMagnetizationIncrement, X, Y]
  congr 1
  ring

theorem actual_curvature_interval_integral_exists
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (S T : ℝ≥0) :
    ∃ I : Ω → ℝ, MemLp I 2 W.law ∧
      Tendsto (fun l => ∫ w, (actualCurvatureIntervalSum W β S T l w - I w)^2 ∂W.law)
        atTop (𝓝 0) ∧ I =ᵐ[W.law] actualParisiMagnetizationIncrement W β S T := by
  obtain ⟨IT, hIT, _, heT⟩ := actual_curvature_integral_exists W β hβ T
  obtain ⟨IS, hIS, _, heS⟩ := actual_curvature_integral_exists W β hβ S
  let I := fun w => IT w - IS w
  have hI : MemLp I 2 W.law := hIT.sub hIS
  have he : I =ᵐ[W.law] actualParisiMagnetizationIncrement W β S T := by
    filter_upwards [heT, heS] with w hwT hwS
    exact congrArg₂ (fun x y : ℝ => x - y) hwT hwS
  refine ⟨I, hI, ?_, he⟩
  apply (actual_curvature_interval_meanSquare_tendsto W β hβ S T).congr'
  apply Filter.Eventually.of_forall
  intro l
  exact integral_congr_ae (he.symm.mono (fun w hw => congrArg
    (fun x : ℝ => (actualCurvatureIntervalSum W β S T l w - x)^2) hw))

end SKConstants.Completion.LBase
