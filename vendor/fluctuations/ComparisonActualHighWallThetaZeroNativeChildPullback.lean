module

public import ComparisonActualHighWallThetaZeroFirstHighOnlyChild
public import ComparisonNativeClockRegularity

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 14000000
set_option linter.unusedVariables false

namespace ActualThetaZeroOverlapMinimum
variable {n:ℕ} {m delta cl cu Az C0 Ct D Bclock:ℝ}
variable (M:ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)

theorem changed_clocks_mass_cut_branches
    (l r:ℝ) (hl:0≤l) (_hlr:l≤r) (hr:r≤1)
    (Hside:r<M.data.s ∨ M.data.s≤l) :
    let P:=M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld
    ∃Kb Kh:ℝ≥0,
      LipschitzOnWith Kb (fun u=>P.b u-P.coefficient M.alpha u) (Icc l r) ∧
      LipschitzOnWith Kh (fun u=>P.h u+P.coefficient M.alpha u*P.R M.alpha u) (Icc l r) := by
  dsimp only
  let P:=M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld
  rcases Hside with Hleft|Hright
  · refine ⟨0,0,?_,?_⟩
    · apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      have hxS:x<M.data.s:=hx.2.trans_lt Hleft
      have hyS:y<M.data.s:=hy.2.trans_lt Hleft
      rw [M.data.theta_zero_changed_low_matrix M.lam M.hlam M.hld M.alpha hxS,
        M.data.theta_zero_changed_low_matrix M.lam M.hlam M.hld M.alpha hyS]
      simp
    · apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      have hxS:x<M.data.s:=hx.2.trans_lt Hleft
      have hyS:y<M.data.s:=hy.2.trans_lt Hleft
      have hzero(u:ℝ)(hu:u<M.data.s):P.h u+P.coefficient M.alpha u*P.R M.alpha u=0:=by
        change (0:ℝ)+omittedStrengthCoefficient M.data.d M.data.s
          (M.data.wallRadius M.alpha) M.lam u*(M.data.wallRadius M.alpha u)=0
        simp only [omittedStrengthCoefficient,ite_eq_right (not_le.mpr hu),zero_mul,add_zero]
      rw [hzero x hxS,hzero y hyS]
      simp
  · let g:=laplaceComparisonStrength M.data.d M.lam
    obtain ⟨Kb,Hb⟩:=(laplaceComparisonStrength_contDiff M.data.d M.lam).contDiffOn.exists_lipschitzOnWith
      (by norm_num) (convex_Icc M.data.rmin 1) isCompact_Icc
    obtain ⟨Kh,Hh⟩:=((laplaceComparisonStrength_contDiff M.data.d M.lam).mul contDiff_id).contDiffOn.exists_lipschitzOnWith
      (by norm_num) (convex_Icc M.data.rmin 1) isCompact_Icc
    let Kr:ℝ≥0:=⟨1/(M.data.k 1),div_nonneg zero_le_one M.data.hc.le⟩
    have HR:LipschitzOnWith Kr (M.data.wallRadius M.alpha) (Icc l r):=
      (M.data.wallRadius_lipschitz M.alpha).lipschitzOnWith
    have Hmap:MapsTo (M.data.wallRadius M.alpha) (Icc l r) (Icc M.data.rmin 1):=
      fun u _=>M.data.wallRadius_bounds M.alpha u
    have HB:=Hb.comp HR Hmap
    have HH:=Hh.comp HR Hmap
    refine ⟨Kb*Kr,Kh*Kr,?_,?_⟩
    · apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      have hxS:M.data.s≤x:=Hright.trans hx.1
      have hyS:M.data.s≤y:=Hright.trans hy.1
      have hval(u:ℝ)(hu:M.data.s≤u):P.b u-P.coefficient M.alpha u=
          M.data.T-g (M.data.wallRadius M.alpha u):=by
        change wallBareMatrix M.data.T M.data.epsilon 0 M.data.s u-
          omittedStrengthCoefficient M.data.d M.data.s
            (M.data.wallRadius M.alpha) M.lam u=_
        simp only [wallBareMatrix,not_lt.mpr hu,ite_false,
          omittedStrengthCoefficient,ite_eq_left hu,g]
      rw [hval x hxS,hval y hyS]
      simpa only [Function.comp_def,Real.dist_eq,
        show M.data.T-g (M.data.wallRadius M.alpha x)-
          (M.data.T-g (M.data.wallRadius M.alpha y))=
          -(g (M.data.wallRadius M.alpha x)-g (M.data.wallRadius M.alpha y)) by ring,
        abs_neg] using HB.dist_le_mul x hx y hy
    · apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      have hxS:M.data.s≤x:=Hright.trans hx.1
      have hyS:M.data.s≤y:=Hright.trans hy.1
      have hval(u:ℝ)(hu:M.data.s≤u):P.h u+P.coefficient M.alpha u*P.R M.alpha u=
          g (M.data.wallRadius M.alpha u)*M.data.wallRadius M.alpha u:=by
        change (0:ℝ)+omittedStrengthCoefficient M.data.d M.data.s
          (M.data.wallRadius M.alpha) M.lam u*M.data.wallRadius M.alpha u=_
        simp only [omittedStrengthCoefficient,ite_eq_left hu,zero_add,g]
      rw [hval x hxS,hval y hyS]
      exact HH.dist_le_mul x hx y hy

theorem changed_pullback_on_native_child_profile
    {N:ℕ} {deltaChild:ℝ} (child:NativeChildBarrierParameters N deltaChild)
    (beta:child.Profile) :
    let P:=M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld
    NativePullbackClockRegularity beta.val.val
      (fun u=>P.b u-P.coefficient M.alpha u)
      (fun u=>P.h u+P.coefficient M.alpha u*P.R M.alpha u) 0 1 := by
  dsimp only
  let P:=M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld
  let cut:=child.R beta M.data.s
  have Hcut:cut∈Icc (0:ℝ) 1:=comparisonSweepQuantile_bounds
    child.hc child.hk child.hkc child.hm child.hM beta M.data.s
  have Hspec:beta.val.val cut=M.data.s:=comparisonSweepQuantile_spec
    child.hc child.hk child.hkc child.hm child.hM beta ⟨M.data.hs.1.le,M.data.hs1⟩
  have Hbeta:=inverseIntegralConstraints_lipschitz child.hm child.hM beta.property
  refine Or.inr ⟨cut,?_⟩
  intro l r hl hlr hr hside
  have Hl:l∈Icc (0:ℝ) 1:=⟨hl,hlr.trans hr⟩
  have Hr:r∈Icc (0:ℝ) 1:=⟨hl.trans hlr,hr⟩
  have Hside:beta.val.val r<M.data.s ∨ M.data.s≤beta.val.val l:=by
    rcases hside with Hleft|Hright
    · have H:=inverseConstraint_strictMonoOn child.hc child.hk child.hkc beta.property Hr Hcut Hleft
      exact Or.inl (by simpa only [Hspec] using H)
    · exact Or.inr (by simpa only [Hspec] using beta.val.property.2 Hright)
  obtain ⟨Kb,Kh,Hb,Hh⟩:=M.changed_clocks_mass_cut_branches
    (beta.val.val l) (beta.val.val r) (beta.val.property.1 l).1
    (beta.val.property.2 hlr) (beta.val.property.1 r).2 Hside
  have Hmap:MapsTo beta.val.val (Icc l r) (Icc (beta.val.val l) (beta.val.val r)):=by
    intro x hx
    exact ⟨beta.val.property.2 hx.1,beta.val.property.2 hx.2⟩
  have Ha:=Hbeta.mono (Icc_subset_Icc hl hr)
  exact ⟨Kb*⟨child.M 1,child.hM⟩,Kh*⟨child.M 1,child.hM⟩,
    Hb.comp Ha Hmap,Hh.comp Ha Hmap⟩

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
