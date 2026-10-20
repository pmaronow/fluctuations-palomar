module

public import SKBarriers2.Corner.FrozenRowsMixed28
public import SKBarriers2.Corner.FrozenRowsMixed32

@[expose] public section

noncomputable section
open scoped Topology ContDiff
open Set OAI.SK.Analytic SKOptimized.Overshoot
namespace SKBarriers2.Corner

theorem FrozenRowsNaturalRealization.movingBellTestPacket
    {β a s h z ε k g C K : ℝ} {α : ℝ → ℝ} {r n : ℕ}
    (H : FrozenRowsNaturalRealization β α a s h z ε)
    (parent q : Fin 12) (i : Fin 3) (hn : 2 ≤ n) (hK : 1 ≤ K)
    (V₀ W₀ : ℝ → Vec3) (U V : Vec3 →L[ℝ] Vec3)
    (hp : ContDiffAt ℝ 2 (frozenRowsMovingParameterCurve β α a s h z ε parent q g) k)
    (hδ : |(Real.sqrt h)^3/(1+|g|)| ≤ 1)
    (hA : ‖frozenRowsCompletedMeanLinear β α a s h z ε q.val k‖ ≤ K)
    (hd : ‖frozenRowsCompletedMeanShift β α a s h z ε q.val k+
      g • frozenRowsCompletedMeanLinear β α a s h z ε q.val k (frozenUnitDirection β k parent)‖ ≤ K*(1+|g|))
    (hv : ‖frozenRowsCompletedHeadDirection β α a s h z ε q.val k‖ ≤ K)
    (hU : ‖U‖ ≤ K) (hV : ‖V‖ ≤ K)
    (hV₀ : ContDiff ℝ r V₀) (hW₀ : ContDiff ℝ r W₀)
    (hVW : ∀ t, ‖V₀ t‖ ≤ K*(1+|t|) ∧ ‖W₀ t‖ ≤ K*(1+|t|))
    (hX : ∀ t y, ContDiffAt ℝ 2
      (fun κ => frozenRowsMovingTestEndpoint β α a s h z ε parent q g κ t y) k)
    (hfirst : ∀ t y, (Real.sqrt h/(1+|g|)) • deriv
      (fun κ => frozenRowsMovingTestEndpoint β α a s h z ε parent q g κ t y) k =
        V₀ t+((Real.sqrt h)^3/(1+|g|)) • U y)
    (hsecond : ∀ t y, (Real.sqrt h/(1+|g|))^2 • deriv (deriv
      (fun κ => frozenRowsMovingTestEndpoint β α a s h z ε parent q g κ t y)) k =
        W₀ t+((Real.sqrt h)^3/(1+|g|)) • V y)
    (HI : IntrinsicTestProfiles r C n ((Real.sqrt h)^3/(1+|g|))
      (fun y => frozenRowsNaturalBellTest β α s h z ε q i
        (frozenRowsMovingParameterCurve β α a s h z ε parent q g k,y))
      (fun y => (Real.sqrt h/(1+|g|))*deriv (fun κ => frozenRowsNaturalBellTest β α s h z ε q i
        (frozenRowsMovingParameterCurve β α a s h z ε parent q g κ,y)) k)
      (fun y => (Real.sqrt h/(1+|g|))^2*deriv (deriv (fun κ => frozenRowsNaturalBellTest β α s h z ε q i
        (frozenRowsMovingParameterCurve β α a s h z ε parent q g κ,y))) k)) :
    let c := frozenRowsNaturalHead h z q
    let G := frozenRowsNaturalBellTest β α s h z ε q i
    let p := frozenRowsMovingParameterCurve β α a s h z ε parent q g
    let σ := Real.sqrt h/(1+|g|)
    MovingNoiseTestPacket r (C*movingTestProfileUniformCoefficient r n K*(1+|g|)^n) n (n+2)
      ((Real.sqrt h)^3/(1+|g|))
      (fun t y => affineCoordinateObservable c G (p k,(y,t)))
      (fun t y => σ*deriv (fun κ => affineCoordinateObservable c G (p κ,(y,t))) k)
      (fun t y => affineCoordinateObservable c G (p k,(y,t))-affineCoordinateObservable c G (p k,(y,0)))
      (fun t y => σ*deriv (fun κ => affineCoordinateObservable c G (p κ,(y,t))) k-
        σ*deriv (fun κ => affineCoordinateObservable c G (p κ,(y,0))) k)
      (fun t y => σ^2*deriv (deriv (fun κ => affineCoordinateObservable c G (p κ,(y,t)))) k) := by
  let A := frozenRowsCompletedMeanLinear β α a s h z ε q.val k
  let d := frozenRowsCompletedMeanShift β α a s h z ε q.val k+
    g • A (frozenUnitDirection β k parent)
  let v := frozenRowsCompletedHeadDirection β α a s h z ε q.val k
  let X := frozenRowsMovingTestEndpoint β α a s h z ε parent q g
  let G := frozenRowsNaturalBellTest β α s h z ε q i
  let p := frozenRowsMovingParameterCurve β α a s h z ε parent q g
  have hW : 1 ≤ 1+|g| := by linarith [abs_nonneg g]
  have Haffine := movingNoiseTestPacket_affine HI hn hδ hK hW A d v V₀ W₀ U V
    hA hd hv hU hV hV₀ hW₀ hVW
  have hY (t : ℝ) (y : Vec3) : X k t y = A y+d+t • v := by
    dsimp only [X,frozenRowsMovingTestEndpoint,A,d,v]
    abel
  have Hactual := MovingNoiseTestPacket.actual_of_affine (H.bell_smooth q i) hp hX
    A d v V₀ W₀ U V hY hfirst hsecond Haffine
  have hobs (κ t : ℝ) (y : Vec3) :
      affineCoordinateObservable (frozenRowsNaturalHead h z q) G (p κ,(y,t)) = G (p κ,X κ t y) := by
    unfold affineCoordinateObservable
    rw [frozenRowsMovingParameterCurve_endpoint β α a s h z ε H.mass_pos H.scale_pos parent q g κ t y]
  dsimp only [G,p,X] at hobs
  dsimp only
  simpa only [hobs] using Hactual

end SKBarriers2.Corner
