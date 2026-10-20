module

public import SKBarriers2.Corner.FrozenRowsMixed16

@[expose] public section

noncomputable section
open scoped Topology ContDiff
open Set Filter OAI.SK.Analytic
namespace SKBarriers2.Corner
variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_const_mul_real (c : ℝ) (f : E → ℝ) (x : E) :
    fderiv ℝ (fun y => c*f y) x = c • fderiv ℝ f x :=
  congrFun (fderiv_const_smul_field c) x

theorem paramSmooth_moving_endpoint_scaled_jets {F : P × (Fin 3 → ℝ) → ℝ}
    (hF : ParamSmooth F) {p : ℝ → P} {x : ℝ → Fin 3 → ℝ} {k : ℝ}
    (hp : ContDiffAt ℝ 2 p k) (hx : ContDiffAt ℝ 2 x k) (σ : ℝ) :
    let f := fun y => F (p k,y)
    let a := fun y => σ*deriv (fun t => F (p t,y)) k
    let b := fun y => σ^2*deriv (deriv (fun t => F (p t,y))) k
    σ*deriv (fun t => F (p t,x t)) k = a (x k)+fderiv ℝ f (x k) (σ • deriv x k) ∧
      σ^2*deriv (deriv (fun t => F (p t,x t))) k =
        b (x k)+2*fderiv ℝ a (x k) (σ • deriv x k)+
          fderiv ℝ (fderiv ℝ f) (x k) (σ • deriv x k) (σ • deriv x k)+
            fderiv ℝ f (x k) (σ^2 • deriv (deriv x) k) := by
  have H := paramSmooth_moving_endpoint_jets hF hp hx
  dsimp only at H ⊢
  constructor
  · rw [H.1,map_smul,smul_eq_mul]
    ring
  · rw [H.2,fderiv_const_mul_real]
    simp only [map_smul,smul_apply,smul_eq_mul]
    ring

end SKBarriers2.Corner
