module

public import ComparisonSignedCavityScalarRadiusSavedRow
public import ComparisonActualHighOnlyAnalyticBasics
public import ComparisonActualHighOnlyResourcePhysicalFactories
public import ComparisonActualHighOnlyPullbackFourInterfaces
public import ComparisonActualHighOnlySourceProjectionAlong
public import ComparisonActualHighOnlyGaCurrentPrerequisites
public import ComparisonActualHighOnlyScalarRadiusRowAllocation

@[expose] public section

noncomputable section
set_option linter.unusedVariables false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
set_option maxHeartbeats 20000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity ClockTree

theorem eventually_actual_minimum_scalar_radius_saved_row_decay_high_only
    {eta : ℝ} (heta : 0 < eta) (A : ℝ) (hA : 0 ≤ A)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 < m) (hcu : 0 ≤ cu) (hC0 : 0 < C0) :
    ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀us : List PositiveMass,(∀u∈us,u.val ≤ 1) →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        ∀(i star U : ℕ) (T : ClockTree (Spin n×Bool) as)
          (seed : List NativeResourceMark) (depth : ℕ) (P : NativeResourceTerm i star T),
          NativeActualResourceGenerated i star U seed depth T P → i ≤ star →
        ∀W V s : ℝ,M.xs ≤ W → M.xs ≤ V → V ≤ 1 → M.z ≤ V →
          M.R (partitionPoint 0 as star) ≤ V/2 → M.xs ≤ s →
          A*((n:ℝ)^(-eta))^2*
          ((T.markedAttach 0).map (fun p=>|p.coeff| *
            M.R (partitionPoint 0 as (p.tree.splitIndex (p.embed P.live.test.target) p.mark))*
            nativeTargetOffDiagonalProfile T P.live.test.target
              (fun j=>if V ≤ M.R (partitionPoint 0 as j) then
                nativeSavedIncomingScale M.xs W s (M.R (partitionPoint 0 as j)) else 0) p)).sum  ≤
            (n:ℝ)^(-eta)*(W*M.xs^2) := by
  let C:=2*(2*cu+1)
  have hC : 0 ≤ C:=by dsimp only [C];positivity
  let L:=2/Real.log 2+2
  have hL : 0 ≤ L:=by dsimp only [L];positivity [Real.log_pos (by norm_num : (1:ℝ) < 2)]
  have HC:=eventually_actual_minimum_radius_dyadic_cover_high_only
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm hC0
  have HD:=eventually_native_saved_row_polynomial_decay heta (A*(C*L))
    (mul_nonneg hA (mul_nonneg hC hL))
  filter_upwards [HC,HD] with n hc hd
  intro M us hus
  filter_upwards [actual_minimum_scalar_radius_row_on_every_final_net_high_only M hcu us hus] with k hk
  dsimp only at hk ⊢
  intro i star U T seed depth P hP hi W V s hxW hxV hV1 hzV hstar hxsS
  let as:=finiteCutMasses us k
  let target:=P.live.test.target
  let radius:=fun p : MarkedPlacement T=>M.R (partitionPoint 0 as (p.tree.splitIndex (p.embed target) p.mark))
  let weight:=fun p : MarkedPlacement T=>if p.embed target=p.mark then 0 else |p.coeff| *radius p
  have hW : 0 < W:=M.hxs.trans_le hxW
  have hV : 0 < V:=M.hxs.trans_le hxV
  have hs : 0 < s:=M.hxs.trans_le hxsS
  have hr (p : MarkedPlacement T) : 0 ≤ radius p:=
    (M.R_bounds _).1
  have H:=native_finite_saved_incoming_row_le (T.markedAttach 0) weight radius
    (x:=M.xs) (W:=W) (s:=s) (V:=V) (C:=C)
    (by intro p hp;dsimp only [weight];split_ifs <;> first | exact le_refl 0 | exact mul_nonneg (abs_nonneg _) (hr p))
    (by intro p hp;exact (M.R_bounds _).2)
    M.hxs.le hW hs hV hxW hxsS (by
      intro j hj
      have hvj : V ≤ V*(2:ℝ)^j:=by nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n:=j)]
      have HB:=hk i star U T seed depth P hP hi (V*(2:ℝ)^j)
        (hxV.trans hvj) (hzV.trans hvj) (by linarith)
      convert HB using 1
      apply congrArg List.sum
      apply List.map_congr_left
      intro p hp
      dsimp only [weight,radius,nativeTargetOffDiagonalProfile,nativeRadiusRowBand,target,as,C]
      split_ifs <;> ring)
  have Heq : (T.markedAttach 0).map (fun p=>weight p*(if V ≤ radius p then
      nativeSavedIncomingScale M.xs W s (radius p) else 0))=
      (T.markedAttach 0).map (fun p=>|p.coeff| *radius p*
        nativeTargetOffDiagonalProfile T target (fun j=>if V ≤ M.R (partitionPoint 0 as j) then
          nativeSavedIncomingScale M.xs W s (M.R (partitionPoint 0 as j)) else 0) p) := by
    apply List.map_congr_left
    intro p hp
    dsimp only [weight,radius,nativeTargetOffDiagonalProfile]
    split_ifs <;> ring
  rw [Heq] at H
  have Hlog:=H.trans (by
    have HH:=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hc M V hxV hV1).1 hC) (show 0 ≤ W*M.xs^2 by positivity)
    convert HH using 1)
  have HA:=mul_le_mul_of_nonneg_left Hlog (show 0 ≤ A*((n:ℝ)^(-eta))^2 by positivity)
  apply HA.trans
  convert mul_le_mul_of_nonneg_right hd (show 0 ≤ W*M.xs^2 by positivity) using 1
  ring

end OAI.SKFluctuations.LaplaceWindowFormalization
