module

public import SKBarriers2.Corner.FrozenRowsMixed30
public import SKBarriers2.Corner.FrozenRowsActualMovingTestProfiles

@[expose] public section

noncomputable section
open scoped Topology ContDiff
open Set OAI.SK.Analytic
namespace SKBarriers2.Corner
local notation "E" => (Fin 3 → ℝ)
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem MovingNoiseTestPacket.actual_of_affine {F : P × E → ℝ} (hF : ParamSmooth F)
    {p : ℝ → P} {X : ℝ → ℝ → E → E} {k σ δ C : ℝ} {r n q : ℕ}
    (hp : ContDiffAt ℝ 2 p k)
    (hX : ∀ t y, ContDiffAt ℝ 2 (fun κ => X κ t y) k)
    (A : E →L[ℝ] E) (d v : E) (V₀ W₀ : ℝ → E) (U V : E → E)
    (hY : ∀ t y, X k t y = A y+d+t • v)
    (hV : ∀ t y, σ • deriv (fun κ => X κ t y) k = V₀ t+δ • U y)
    (hW : ∀ t y, σ^2 • deriv (deriv (fun κ => X κ t y)) k = W₀ t+δ • V y)
    (H : MovingNoiseTestPacket r C n q δ
      (fun t y => F (p k,A y+d+t • v))
      (affineMovingRawFirst (fun y => F (p k,y))
        (fun y => σ*deriv (fun κ => F (p κ,y)) k) A d v δ V₀ U)
      (affineMovingCenteredValue (fun y => F (p k,y)) A d v)
      (affineMovingCenteredFirst (fun y => F (p k,y))
        (fun y => σ*deriv (fun κ => F (p κ,y)) k) A d v δ V₀ U)
      (affineMovingRawSecond (fun y => F (p k,y))
        (fun y => σ*deriv (fun κ => F (p κ,y)) k)
        (fun y => σ^2*deriv (deriv (fun κ => F (p κ,y))) k) A d v δ V₀ W₀ U V)) :
    MovingNoiseTestPacket r C n q δ
      (fun t y => F (p k,X k t y))
      (fun t y => σ*deriv (fun κ => F (p κ,X κ t y)) k)
      (fun t y => F (p k,X k t y)-F (p k,X k 0 y))
      (fun t y => σ*deriv (fun κ => F (p κ,X κ t y)) k-
        σ*deriv (fun κ => F (p κ,X κ 0 y)) k)
      (fun t y => σ^2*deriv (deriv (fun κ => F (p κ,X κ t y))) k) := by
  have hi := actualMovingTest_sources_eq hF hp hX A d v V₀ W₀ U V hY hV hW
  dsimp only at hi
  have hvalue : (fun t y => F (p k,X k t y)) = fun t y => F (p k,A y+d+t • v) := by
    funext t y
    rw [hY]
  have hfirst : (fun t y => σ*deriv (fun κ => F (p κ,X κ t y)) k) =
      affineMovingRawFirst (fun y => F (p k,y))
        (fun y => σ*deriv (fun κ => F (p κ,y)) k) A d v δ V₀ U := hi.2.2.2
  have hcenter : (fun t y => σ*deriv (fun κ => F (p κ,X κ t y)) k-
      σ*deriv (fun κ => F (p κ,X κ 0 y)) k) =
      affineMovingCenteredFirst (fun y => F (p k,y))
        (fun y => σ*deriv (fun κ => F (p κ,y)) k) A d v δ V₀ U := by
    funext t y
    rw [congrFun (congrFun hfirst t) y,congrFun (congrFun hfirst 0) y]
    rfl
  rw [hvalue,hfirst,hi.1,hcenter,hi.2.2.1]
  exact H

end SKBarriers2.Corner
