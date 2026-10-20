module

public import SKBarriers2.Corner.FrozenRowsPotential6
public import SKBarriers2.Corner.FrozenRowsPotential13

@[expose] public section

noncomputable section
open scoped Topology ContDiff
open Set Filter OAI.SK.Analytic

namespace SKBarriers2.Corner
open StepCalculus

theorem fixedMassChain_moving_endpoint_jets_identity {n : ℕ} (m : Fin n → ℝ)
    {v : ℝ → Fin n → (Fin 3 → ℝ)} {x : ℝ → Fin 3 → ℝ} {k B : ℝ}
    {f : (Fin 3 → ℝ) → ℝ} (hf : QPotential 2 B f)
    (hv : ContDiffAt ℝ 2 v k) (hx : ContDiffAt ℝ 2 x k) (hm : ∀ i, 0 < m i) :
    let F := fun t y => vectorIncrementChain (List.ofFn (fun i => (m i,v t i))) f y
    let G := fun y => deriv (fun t => F t y) k
    let H := fun y => deriv (deriv (fun t => F t y)) k
    deriv (fun t => F t (x t)) k = G (x k) + fderiv ℝ (F k) (x k) (deriv x k) ∧
      deriv (deriv (fun t => F t (x t))) k = H (x k) +
        2 * fderiv ℝ G (x k) (deriv x k) +
        fderiv ℝ (fderiv ℝ (F k)) (x k) (deriv x k) (deriv x k) +
        fderiv ℝ (F k) (x k) (deriv (deriv x) k) := by
  let P := FixedMassParameters n
  let cs := fixedMassCoordinateSteps m
  let p := fixedMassParameterCurve v (fun _ => (0 : Fin 3 → ℝ))
  let F : P × (Fin 3 → ℝ) → ℝ := ParamChain.exponentialChain cs (fun z => f z.2)
  have hF : ParamRegular F := ParamChain.regular_exponentialChain cs
    (ParamChain.regular_fixedTerminal hf le_rfl P)
  have hp : ContDiffAt ℝ 2 p k := (fixedMassParameterCurve_jets hv contDiffAt_const).1
  have hpath (t : ℝ) : ParamChain.exponentialSteps cs (p t) =
      List.ofFn (fun i => (m i,v t i)) := fixedMassCoordinateSteps_apply m v _ hm t
  have H := parametric_moving_endpoint_jets hF hp hx
  simpa only [F, ParamChain.exponentialChain, hpath] using H

end SKBarriers2.Corner
