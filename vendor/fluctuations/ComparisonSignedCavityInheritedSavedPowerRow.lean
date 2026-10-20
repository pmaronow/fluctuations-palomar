module

public import ComparisonSignedCavityActualSavedPowerRow
public import ComparisonSignedCavityInheritedSavedIncomingRow
public import ComparisonSignedCavityCalibratedStarSubtreeProjection

@[expose] public section

noncomputable section
set_option maxHeartbeats 14000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity ClockTree

theorem eventually_actual_minimum_inherited_saved_power_row_bound
    (Bclock Temp Cf : ℝ) (hT : 0 ≤ Temp) (hCf : 0 ≤ Cf) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cg : ℝ,0 < Cg ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        ∀(i star U : ℕ) (T : ClockTree (Spin n×Bool) as)
          (seed : List NativeResourceMark) (depth : ℕ) (P : NativeResourceTerm i star T),
          NativeActualResourceGenerated i star U seed depth T P → i ≤ star → 0 < U →
        ∀W V : ℝ,M.xs ≤ W → M.xs ≤ V → V ≤ 1 → M.z ≤ V →
          M.R (partitionPoint 0 as star) ≤ V/2 →
          ((T.markedAttach 0).map (fun p=>|p.coeff| *
            |fullScalarCutGamma p.tree U (nativeContinuumMixedClock n M.bf M.hf as)
              (p.embed P.live.test.target) p.mark| *
            nativeTargetOffDiagonalProfile T P.live.test.target
              (fun j=>if V ≤ M.R (partitionPoint 0 as j) then
                nativeSavedIncomingScale M.xs W W
                  (M.R (partitionPoint 0 as j)) else 0) p)).sum ≤
            Cg*Real.log ((n+1:ℕ):ℝ)*(W*M.xs^2) := by
  obtain ⟨Cg,hCg,HG⟩:=eventually_actual_minimum_inherited_gamma_radius_row_bound
    (D:=D) Bclock Temp Cf hT hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  have HC:=eventually_actual_minimum_radius_dyadic_cover
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm hC0
  refine ⟨Cg*(2/Real.log 2+2),by positivity [Real.log_pos (by norm_num : (1:ℝ) < 2)],?_⟩
  filter_upwards [HG,HC] with n hn hc
  intro M hsource hxs L us hus hret hmesh
  filter_upwards [hn M hsource hxs L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro i star U T seed depth P hP hi hU W V hxW hxV hV1 hzV hstar
  let as:=finiteCutMasses us k
  let s:=P.live.test.target
  let radius:=fun p : MarkedPlacement T=>M.R (partitionPoint 0 as (p.tree.splitIndex (p.embed s) p.mark))
  let weight:=fun p : MarkedPlacement T=>if p.embed s=p.mark then 0 else
    |p.coeff| * |fullScalarCutGamma p.tree U (nativeContinuumMixedClock n M.bf M.hf as) (p.embed s) p.mark|
  have hW : 0 < W:=M.hxs.trans_le hxW
  have hV : 0 < V:=M.hxs.trans_le hxV
  have H:=native_finite_saved_incoming_row_le (T.markedAttach 0) weight radius
    (x:=M.xs) (W:=W) (s:=W) (V:=V) (C:=Cg)
    (by intro p hp;dsimp only [weight];split_ifs <;> positivity)
    (by intro p hp;exact (comparisonSweepQuantile_bounds M.context.hc M.context.hk M.context.hkc
      M.context.hm M.context.hM M.alpha _).2)
    M.hxs.le hW hW hV hxW hxW (by
      intro j hj
      have hvj : V ≤ V*(2:ℝ)^j := by nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n:=j)]
      have HB:=hk i star U T seed depth P hP hi hU (V*(2:ℝ)^j)
        (hxV.trans hvj) (hzV.trans hvj) (by linarith)
      convert HB using 1
      apply congrArg List.sum
      apply List.map_congr_left
      intro p hp
      dsimp only [weight,radius,nativeTargetOffDiagonalProfile,nativeRadiusRowBand,s,as]
      split_ifs <;> ring)
  have Heq : (T.markedAttach 0).map (fun p=>weight p*(if V ≤ radius p then
      nativeSavedIncomingScale M.xs W W (radius p) else 0))=
      (T.markedAttach 0).map (fun p=>|p.coeff| *
        |fullScalarCutGamma p.tree U (nativeContinuumMixedClock n M.bf M.hf as) (p.embed s) p.mark| *
        nativeTargetOffDiagonalProfile T s (fun j=>if V ≤ M.R (partitionPoint 0 as j) then
          nativeSavedIncomingScale M.xs W W (M.R (partitionPoint 0 as j)) else 0) p) := by
    apply List.map_congr_left
    intro p hp
    dsimp only [weight,radius,nativeTargetOffDiagonalProfile]
    split_ifs <;> ring
  rw [Heq] at H
  exact H.trans (by
    have HH:=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hc M V hxV hV1).1 hCg.le) (show 0 ≤ W*M.xs^2 by positivity)
    convert HH using 1
    ring)

end OAI.SKFluctuations.LaplaceWindowFormalization
