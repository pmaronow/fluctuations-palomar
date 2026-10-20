module

public import SKBarriers2.Corner.FrozenRowsMixed23
public import SKBarriers2.Corner.FrozenRowsMovingTestProfiles2

@[expose] public section

noncomputable section
open scoped Topology
open Set Filter OAI.SK.Analytic
namespace SKBarriers2.Corner
local notation "E" => (Fin 3 → ℝ)
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem actualMovingTest_sources_eq {F : P × E → ℝ} (hF : ParamSmooth F)
    {p : ℝ → P} {X : ℝ → ℝ → E → E} {k σ δ : ℝ}
    (hp : ContDiffAt ℝ 2 p k)
    (hX : ∀ t y, ContDiffAt ℝ 2 (fun κ => X κ t y) k)
    (A : E →L[ℝ] E) (d v : E) (V₀ W₀ : ℝ → E) (V₁ W₁ : E → E)
    (hY : ∀ t y, X k t y = A y+d+t • v)
    (hV : ∀ t y, σ • deriv (fun κ => X κ t y) k = V₀ t+δ • V₁ y)
    (hW : ∀ t y, σ^2 • deriv (deriv (fun κ => X κ t y)) k = W₀ t+δ • W₁ y) :
    let f := fun y => F (p k,y)
    let a := fun y => σ*deriv (fun κ => F (p κ,y)) k
    let b := fun y => σ^2*deriv (deriv (fun κ => F (p κ,y))) k
    (fun t y => F (p k,X k t y)-F (p k,X k 0 y)) = affineMovingCenteredValue f A d v ∧
    (fun t y => σ*deriv (fun κ => F (p κ,X κ t y)-F (p κ,X κ 0 y)) k) =
      affineMovingCenteredFirst f a A d v δ V₀ V₁ ∧
    (fun t y => σ^2*deriv (deriv (fun κ => F (p κ,X κ t y))) k) =
      affineMovingRawSecond f a b A d v δ V₀ W₀ V₁ W₁ ∧
    (fun t y => σ*deriv (fun κ => F (p κ,X κ t y)) k) =
      affineMovingRawFirst f a A d v δ V₀ V₁ := by
  dsimp only
  have hraw (t : ℝ) (y : E) := paramSmooth_moving_endpoint_scaled_jets hF hp (hX t y) σ
  dsimp only at hraw
  have hfirst (t : ℝ) (y : E) : σ*deriv (fun κ => F (p κ,X κ t y)) k =
      affineMovingRawFirst (fun y => F (p k,y))
        (fun y => σ*deriv (fun κ => F (p κ,y)) k) A d v δ V₀ V₁ t y := by
    have H := (hraw t y).1
    rw [hY t y,hV t y] at H
    exact H
  have hsecond (t : ℝ) (y : E) : σ^2*deriv (deriv (fun κ => F (p κ,X κ t y))) k =
      affineMovingRawSecond (fun y => F (p k,y))
        (fun y => σ*deriv (fun κ => F (p κ,y)) k)
        (fun y => σ^2*deriv (deriv (fun κ => F (p κ,y))) k) A d v δ V₀ W₀ V₁ W₁ t y := by
    have H := (hraw t y).2
    rw [hY t y,hV t y,hW t y] at H
    exact H
  refine ⟨?_,?_,funext (fun t => funext (fun y => hsecond t y)),
    funext (fun t => funext (fun y => hfirst t y))⟩
  · funext t y
    rw [hY t y,hY 0 y]
    simp only [affineMovingCenteredValue,zero_smul,add_zero]
  · funext t y
    have hc (z : ℝ) : ContDiffAt ℝ 2 (fun κ => F (p κ,X κ z y)) k :=
      hF.1.contDiffAt.comp k (hp.prodMk (hX z y))
    rw [deriv_fun_sub ((hc t).differentiableAt (by norm_num))
      ((hc 0).differentiableAt (by norm_num)),mul_sub,hfirst t y,hfirst 0 y]
    rfl

theorem actualMovingTestProfiles_of_affine {F : P × E → ℝ} (hF : ParamSmooth F)
    {p : ℝ → P} {X : ℝ → ℝ → E → E} {k σ δ t C : ℝ} {r n : ℕ}
    (hp : ContDiffAt ℝ 2 p k)
    (hX : ∀ t y, ContDiffAt ℝ 2 (fun κ => X κ t y) k)
    (A : E →L[ℝ] E) (d v : E) (V₀ W₀ : ℝ → E) (V₁ W₁ : E → E)
    (hY : ∀ t y, X k t y = A y+d+t • v)
    (hV : ∀ t y, σ • deriv (fun κ => X κ t y) k = V₀ t+δ • V₁ y)
    (hW : ∀ t y, σ^2 • deriv (deriv (fun κ => X κ t y)) k = W₀ t+δ • W₁ y)
    (H : MovingTestProfiles r C n δ
      (affineMovingCenteredValue (fun y => F (p k,y)) A d v t)
      (affineMovingCenteredFirst (fun y => F (p k,y))
        (fun y => σ*deriv (fun κ => F (p κ,y)) k) A d v δ V₀ V₁ t)
      (affineMovingRawSecond (fun y => F (p k,y))
        (fun y => σ*deriv (fun κ => F (p κ,y)) k)
        (fun y => σ^2*deriv (deriv (fun κ => F (p κ,y))) k) A d v δ V₀ W₀ V₁ W₁ t)) :
    MovingTestProfiles r C n δ
      (fun y => F (p k,X k t y)-F (p k,X k 0 y))
      (fun y => σ*deriv (fun κ => F (p κ,X κ t y)-F (p κ,X κ 0 y)) k)
      (fun y => σ^2*deriv (deriv (fun κ => F (p κ,X κ t y))) k) := by
  have hi := actualMovingTest_sources_eq hF hp hX A d v V₀ W₀ V₁ W₁ hY hV hW
  dsimp only at hi
  rw [congrFun hi.1 t,congrFun hi.2.1 t,congrFun hi.2.2.1 t]
  exact H

theorem actualMovingRawFirst_of_affine {F : P × E → ℝ} (hF : ParamSmooth F)
    {p : ℝ → P} {X : ℝ → ℝ → E → E} {k σ δ t C : ℝ} {r n : ℕ}
    (hp : ContDiffAt ℝ 2 p k)
    (hX : ∀ t y, ContDiffAt ℝ 2 (fun κ => X κ t y) k)
    (A : E →L[ℝ] E) (d v : E) (V₀ W₀ : ℝ → E) (V₁ W₁ : E → E)
    (hY : ∀ t y, X k t y = A y+d+t • v)
    (hV : ∀ t y, σ • deriv (fun κ => X κ t y) k = V₀ t+δ • V₁ y)
    (hW : ∀ t y, σ^2 • deriv (deriv (fun κ => X κ t y)) k = W₀ t+δ • W₁ y)
    (H : WJets r C n (affineMovingRawFirst (fun y => F (p k,y))
      (fun y => σ*deriv (fun κ => F (p κ,y)) k) A d v δ V₀ V₁ t)) :
    WJets r C n (fun y => σ*deriv (fun κ => F (p κ,X κ t y)) k) := by
  have hi := actualMovingTest_sources_eq hF hp hX A d v V₀ W₀ V₁ W₁ hY hV hW
  dsimp only at hi
  rw [congrFun hi.2.2.2 t]
  exact H

theorem actualMovingTestProfiles_contDiff_of_affine {F : P × E → ℝ} (hF : ParamSmooth F)
    {p : ℝ → P} {X : ℝ → ℝ → E → E} {k σ δ : ℝ} {r : ℕ}
    (hp : ContDiffAt ℝ 2 p k)
    (hX : ∀ t y, ContDiffAt ℝ 2 (fun κ => X κ t y) k)
    (A : E →L[ℝ] E) (d v : E) (V₀ W₀ : ℝ → E) (V₁ W₁ : E → E)
    (hY : ∀ t y, X k t y = A y+d+t • v)
    (hV : ∀ t y, σ • deriv (fun κ => X κ t y) k = V₀ t+δ • V₁ y)
    (hW : ∀ t y, σ^2 • deriv (deriv (fun κ => X κ t y)) k = W₀ t+δ • W₁ y)
    (H :
      ContDiff ℝ r (Function.uncurry (affineMovingCenteredValue (fun y => F (p k,y)) A d v)) ∧
      ContDiff ℝ r (Function.uncurry (affineMovingCenteredFirst (fun y => F (p k,y))
        (fun y => σ*deriv (fun κ => F (p κ,y)) k) A d v δ V₀ V₁)) ∧
      ContDiff ℝ r (Function.uncurry (affineMovingRawSecond (fun y => F (p k,y))
        (fun y => σ*deriv (fun κ => F (p κ,y)) k)
        (fun y => σ^2*deriv (deriv (fun κ => F (p κ,y))) k) A d v δ V₀ W₀ V₁ W₁)) ∧
      ContDiff ℝ r (Function.uncurry (affineMovingRawFirst (fun y => F (p k,y))
        (fun y => σ*deriv (fun κ => F (p κ,y)) k) A d v δ V₀ V₁))) :
    ContDiff ℝ r (Function.uncurry (fun t y => F (p k,X k t y)-F (p k,X k 0 y))) ∧
    ContDiff ℝ r (Function.uncurry (fun t y =>
      σ*deriv (fun κ => F (p κ,X κ t y)-F (p κ,X κ 0 y)) k)) ∧
    ContDiff ℝ r (Function.uncurry (fun t y =>
      σ^2*deriv (deriv (fun κ => F (p κ,X κ t y))) k)) ∧
    ContDiff ℝ r (Function.uncurry (fun t y =>
      σ*deriv (fun κ => F (p κ,X κ t y)) k)) := by
  have hi := actualMovingTest_sources_eq hF hp hX A d v V₀ W₀ V₁ W₁ hY hV hW
  dsimp only at hi
  rw [hi.1,hi.2.1,hi.2.2.1,hi.2.2.2]
  exact H

end SKBarriers2.Corner
