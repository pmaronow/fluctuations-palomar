module

public import ComparisonSignedCavityActualResourceRestReadout
public import ComparisonSignedCavityActualFrozenResourceMoments
public import ComparisonSignedCavityActualTwoFreshRecursionSource

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {as : List PositiveMass} {i star U k : ℕ}

theorem native_actual_centered_fresh_resource_readout
    (q : ℕ→RestCoordinate n→ℝ) (b h K C : ℕ→ℝ)
    (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T)
    (ho : MassOrdered 0 as)
    (σ : (nativeFreshAtSlot T 0 P.live.test.target star).tree.Assignment) :
    let qfull:=cutFullVariance n q U 1 1 b h K
    let g:=nativeFreshAtSlot T 0 P.live.test.target star
    let Pc:=nativeOriginalCenteredRestTest n q U b h K T
      (nativeActualResourceRestValue P 0 qfull 0 C)
    Pc (g.restRestrict (g.tree.cavityAssignment σ).1)=
      (P.retarget 0).value (fullWeight n) (fullFeature n) 0 qfull
        (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C 0 σ+
      (P.retarget 0).freeze.value (fullWeight n) (fullFeature n) 0 qfull
        (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C 0 σ := by
  let g:=nativeFreshAtSlot T 0 P.live.test.target star
  dsimp only
  rw [←g.restRestrict_actual,P.retarget_value,
    (P.retarget 0).freeze_value (fullWeight_pos n) (fullFeature n) ho,
    P.retarget_disorder_marginal (fullWeight_pos n) (fullFeature n) ho]
  simpa only [sub_eq_add_neg] using congrFun
    (native_actual_resource_original_centered_readout P 0
      (cutFullVariance n q U 1 1 b h K) 0 C q U b h K)
    ((nativeFreshAtSlot T 0 P.live.test.target star).restrict σ)

theorem native_actual_centered_fresh_pair_moment_eq_two_resources
    (q : ℕ→RestCoordinate n→ℝ) (b h K C : ℕ→ℝ)
    (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T)
    (ho : MassOrdered 0 as) :
    let qfull:=cutFullVariance n q U 1 1 b h K
    let g:=nativeFreshAtSlot T 0 P.live.test.target star
    let R:=fun σ τ : Spin n×Bool=>deletedOverlap n (joinSpin σ) (joinSpin τ)
    let D:=fun σ : g.tree.Assignment=>R (T.atSlot (g.restrict σ) P.live.test.target)
      (g.spin σ)-C star
    nativeActualOriginalFreshPairMoment n q U b h K C T
      (nativeOriginalCenteredRestTest n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C))
      P.live.test.target star=
      g.tree.disorderExpect (fullWeight n) (fullFeature n) 0 qfull
        (fun σ=>(P.retarget 0).value (fullWeight n) (fullFeature n) 0 qfull R C 0 σ*D σ) 0+
      g.tree.disorderExpect (fullWeight n) (fullFeature n) 0 qfull
        (fun σ=>(P.retarget 0).freeze.value (fullWeight n) (fullFeature n) 0 qfull R C 0 σ*D σ) 0 := by
  dsimp only
  unfold nativeActualOriginalFreshPairMoment
  dsimp only
  simp_rw [native_actual_centered_fresh_resource_readout q b h K C T P ho,add_mul]
  simp only [ClockTree.disorderExpect,mul_add,Finset.sum_add_distrib]

theorem normalized_actual_centered_fresh_pair_moment_abs_le
    (q : ℕ→RestCoordinate n→ℝ) (b h K C : ℕ→ℝ)
    (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T)
    {seed : List NativeResourceMark}
    (hP : NativeActualResourceGenerated i star U seed k T P)
    (ho : MassOrdered 0 as) (hi : i ≤ star) (hstar : star < as.length)
    (A x W eps B : ℝ) (hA : 0 < A) (hx : 0 < x) (hW : 0 < W)
    (heps : 0 < eps) (hB : 0 ≤ B)
    (hm : let qfull:=cutFullVariance n q U 1 1 b h K;
      (P.retarget 0).PairMomentBudget (fullWeight n) (fullFeature n) 0 qfull
        (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C 0 A x W eps)
    (hmf : let qfull:=cutFullVariance n q U 1 1 b h K;
      (P.retarget 0).freeze.PairMomentBudget (fullWeight n) (fullFeature n) 0 qfull
        (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C 0 A x W eps)
    (hD : let g:=nativeFreshAtSlot T 0 P.live.test.target star;
      g.tree.disorderExpect (fullWeight n) (fullFeature n) 0
        (cutFullVariance n q U 1 1 b h K)
        (fun σ=>(deletedOverlap n (joinSpin (T.atSlot (g.restrict σ) P.live.test.target))
          (joinSpin (g.spin σ))-C star)^2) 0 ≤ B^2) :
    let qfull:=cutFullVariance n q U 1 1 b h K
    |(W⁻¹)^k*nativeActualOriginalFreshPairMoment n q U b h K C T
      (nativeOriginalCenteredRestTest n q U b h K T
        (nativeActualResourceRestValue P 0 qfull 0 C)) P.live.test.target star| ≤
      2*|P.coefficient| *A^(seed.length+k)*nativeResourceScale x W eps seed*eps^k*B := by
  dsimp only at hm hmf hD ⊢
  let qfull:=cutFullVariance n q U 1 1 b h K
  let R:=fun σ τ : Spin n×Bool=>deletedOverlap n (joinSpin σ) (joinSpin τ)
  let g:=nativeFreshAtSlot T 0 P.live.test.target star
  let D:=fun σ : g.tree.Assignment=>R (T.atSlot (g.restrict σ) P.live.test.target) (g.spin σ)-C star
  have H1:=hP.retarget.normalized_frozen_transported_terminal_pairing_abs_le
    (P.retarget 0) rfl rfl (fullWeight_pos n) (fullFeature n) ho
    0 qfull 0 0 qfull R C 0 A x W eps hA hx hW heps hi hstar hm hm.1 D B hB hD
  have H2:=hP.retarget.freeze.normalized_frozen_transported_terminal_pairing_abs_le
    (P.retarget 0).freeze rfl rfl (fullWeight_pos n) (fullFeature n) ho
    0 qfull 0 0 qfull R C 0 A x W eps hA hx hW heps hi hstar hmf hmf.1 D B hB hD
  rw [native_actual_centered_fresh_pair_moment_eq_two_resources q b h K C T P ho,mul_add]
  dsimp only
  rw [g.tree.disorderExpect_const_mul (fullWeight_pos n) (fullFeature n) ho] at H1 H2
  have Hcoef1 : (P.retarget 0).coefficient=P.coefficient:=rfl
  have Hcoef2 : (P.retarget 0).freeze.coefficient= -P.coefficient:=rfl
  rw [Hcoef1] at H1
  rw [Hcoef2,abs_neg] at H2
  have H:=(abs_add_le _ _).trans (add_le_add H1 H2)
  convert H using 1
  ring

end OAI.SKFluctuations.Cavity
