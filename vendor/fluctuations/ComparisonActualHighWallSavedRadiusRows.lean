module

public import ComparisonActualHighWallGammaRadiusRow
public import ComparisonActualHighWallBufferEndpointGeometry
public import ComparisonSignedCavityIncomingDyadicRowScale
public import ComparisonSignedCavitySavedRowPolynomialDecay

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity ClockTree
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000
attribute [local instance] Classical.propDecidable

theorem eventually_actual_high_wall_saved_polarized_radius_row_bound
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cg : ℝ,0<Cg ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀us : List PositiveMass,(∀u∈us,u.val≤1) →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(i star U : ℕ) (T : ClockTree (Spin n×Bool) as)
          (seed : List NativeResourceMark) (depth : ℕ) (P : NativeResourceTerm i star T),
          NativeActualResourceGenerated i star U seed depth T P → i ≤ star → 0<U →
        ∀W V : ℝ,M.xs ≤ W → M.xs ≤ V → V ≤ 1 → M.z ≤ V →
          M.data.wallRadius M.alpha (partitionPoint 0 as star) ≤ V/2 →
        ∀s : ℝ,s=M.xs+partitionPoint 0 as i ∨ s=W →
        ((T.markedAttach 0).map (fun p=>|p.coeff| *
          |fullScalarCutGamma p.tree U (nativeContinuumMixedClock n M.bf M.hf as)
            (p.embed P.live.test.target) p.mark| *
          nativeTargetOffDiagonalProfile T P.live.test.target
            (fun j=>if V ≤ M.data.wallRadius M.alpha (partitionPoint 0 as j) then
              nativeSavedIncomingScale M.xs W s (M.data.wallRadius M.alpha (partitionPoint 0 as j))
              else 0) p)).sum ≤ Cg*Real.log ((n+1:ℕ):ℝ)*(W*M.xs^2) := by
  obtain ⟨Cg,hCg,HG⟩:=eventually_actual_high_wall_gamma_radius_row_bound
    (D:=D) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  have HC:=ActualHighWallOverlapMinimum.eventually_actual_high_wall_scale_polynomial_lower
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm hC0
  have Hlog : ∀ᶠn : ℕ in atTop,1 ≤ Real.log ((n+1:ℕ):ℝ):=
    (tendsto_add_atTop_nat 1).eventually
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1))
  refine ⟨Cg*(2/Real.log 2+2),by positivity [Real.log_pos (by norm_num : (1:ℝ)<2)],?_⟩
  filter_upwards [HG,HC,Hlog,eventually_gt_atTop (0:ℕ)] with n hn hc hlog hn0
  intro M hwork us hus
  filter_upwards [hn M hwork us hus] with jGrid hj
  dsimp only at hj ⊢
  intro i star U T seed depth P hP hi hU W V hxW hxV hV1 hzV hstar s hs
  let as:=finiteCutMasses us jGrid
  let target:=P.live.test.target
  let radius:=fun p : MarkedPlacement T=>M.data.wallRadius M.alpha
    (partitionPoint 0 as (p.tree.splitIndex (p.embed target) p.mark))
  let weight:=fun p : MarkedPlacement T=>if p.embed target=p.mark then 0 else
    |p.coeff| *|fullScalarCutGamma p.tree U (nativeContinuumMixedClock n M.bf M.hf as) (p.embed target) p.mark|
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hW : 0<W:=M.hxs.trans_le hxW
  have hV : 0<V:=M.hxs.trans_le hxV
  have hs0 : 0<s:=by rcases hs with rfl|rfl;exact add_pos_of_pos_of_nonneg M.hxs (partitionPoint_mem as ho i).1;exact hW
  have hxs : M.xs ≤ s:=by rcases hs with rfl|rfl;exact le_add_of_nonneg_right (partitionPoint_mem as ho i).1;exact hxW
  have H:=native_finite_saved_incoming_row_le (T.markedAttach 0) weight radius
    (x:=M.xs) (W:=W) (s:=s) (V:=V) (C:=Cg)
    (by intro p hp;dsimp only [weight];split_ifs <;> positivity)
    (fun p _=>(M.data.wallRadius_bounds M.alpha _).2)
    M.hxs.le hW hs0 hV hxW hxs (by
      intro j hj'
      have hvj : V ≤ V*(2:ℝ)^j:=by nlinarith [one_le_pow₀ (by norm_num : (1:ℝ)≤2) (n:=j)]
      have HB:=hj i star U T seed depth P hP hi hU (V*(2:ℝ)^j)
        (hxV.trans hvj) (hzV.trans hvj) (by linarith only [hstar,hvj])
      convert HB using 1
      apply congrArg List.sum
      apply List.map_congr_left
      intro p hp
      dsimp only [weight,radius,nativeTargetOffDiagonalProfile,nativeRadiusRowBand,target,as]
      split_ifs <;> ring)
  have Heq : (T.markedAttach 0).map (fun p=>weight p*(if V ≤ radius p then
      nativeSavedIncomingScale M.xs W s (radius p) else 0))=
      (T.markedAttach 0).map (fun p=>|p.coeff| *
        |fullScalarCutGamma p.tree U (nativeContinuumMixedClock n M.bf M.hf as) (p.embed target) p.mark| *
        nativeTargetOffDiagonalProfile T target (fun j=>if V ≤ M.data.wallRadius M.alpha (partitionPoint 0 as j) then
          nativeSavedIncomingScale M.xs W s (M.data.wallRadius M.alpha (partitionPoint 0 as j)) else 0) p):=by
    apply List.map_congr_left
    intro p hp
    dsimp only [weight,radius,nativeTargetOffDiagonalProfile]
    split_ifs <;> ring
  rw [Heq] at H
  have Hcard:=native_radius_dyadic_card_le (by exact_mod_cast (show 1<n+1 by omega))
    hlog hV hV1 ((hc M).trans hxV)
  have HH:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left Hcard hCg.le)
    (show 0≤W*M.xs^2 by positivity)
  exact H.trans (HH.trans_eq (by ring))

end OAI.SKFluctuations.LaplaceWindowFormalization
