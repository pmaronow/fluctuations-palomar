module

public import ComparisonActualHighOnlyWeakComparableClocks
public import ComparisonNativeActualGeneralBareHistoryRegularity

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 18000000
set_option linter.unusedVariables false

theorem NativePullbackClockRegularity.congr_on_pullback
    {alpha b h b' h' : ℝ→ℝ} {a z : ℝ}
    (H : NativePullbackClockRegularity alpha b h a z)
    (Hb : ∀r∈Icc a z,b' (alpha r)=b (alpha r))
    (Hh : ∀r∈Icc a z,h' (alpha r)=h (alpha r)) :
    NativePullbackClockRegularity alpha b' h' a z := by
  have congrLip {f f' : ℝ→ℝ} {S : Set ℝ} {K : ℝ≥0}
      (Hf : LipschitzOnWith K f S) (He : ∀r∈S,f' r=f r) : LipschitzOnWith K f' S := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [He x hx,He y hy]
    exact Hf.dist_le_mul x hx y hy
  rcases H with ⟨Kb,Kh,Hb0,Hh0⟩|⟨s,Hs⟩
  · exact Or.inl ⟨Kb,Kh,congrLip Hb0 Hb,congrLip Hh0 Hh⟩
  · refine Or.inr ⟨s,?_⟩
    intro l r hal hlr hrz hside
    obtain ⟨Kb,Kh,Hb0,Hh0⟩:=Hs l r hal hlr hrz hside
    exact ⟨Kb,Kh,congrLip Hb0 (fun x hx=>Hb x (Icc_subset_Icc hal hrz hx)),
      congrLip Hh0 (fun x hx=>Hh x (Icc_subset_Icc hal hrz hx))⟩

namespace ActualHighOnlyOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock c0 : ℝ} {N : ℕ→ℕ}

theorem full_radius_additions_lipschitz {n : ℕ}
    (P : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    (∃Kb : ℝ≥0,LipschitzWith Kb (fun u=>laplaceComparisonStrength P.data.d P.lam (P.R u))) ∧
      ∃Kh : ℝ≥0,LipschitzWith Kh (fun u=>laplaceComparisonStrength P.data.d P.lam (P.R u)*P.R u) := by
  let g:=laplaceComparisonStrength P.data.d P.lam
  have HG:=laplaceComparisonStrength_contDiff P.data.d P.lam
  obtain ⟨Kb,HB⟩:=HG.contDiffOn.exists_lipschitzOnWith (by norm_num) (convex_Icc (0:ℝ) 1) isCompact_Icc
  obtain ⟨Kh,HH⟩:=(HG.mul contDiff_id).contDiffOn.exists_lipschitzOnWith
    (by norm_num) (convex_Icc (0:ℝ) 1) isCompact_Icc
  let Kr : ℝ≥0:=⟨1/P.data.floor,div_nonneg zero_le_one P.data.hc.le⟩
  have HR : LipschitzWith Kr P.R:=omittedSweepQuantile_lipschitz zero_le_one
    ⟨P.data.hs.1,P.data.hs1⟩ P.data.hc P.data.hk P.data.hkc P.data.hm P.data.hM P.alpha
  have hR u : P.R u∈Icc (0:ℝ) 1:=omittedSweepQuantile_bounds zero_le_one
    ⟨P.data.hs.1,P.data.hs1⟩ P.data.hc P.data.hk P.data.hkc P.data.hm P.data.hM P.alpha u
  constructor
  · refine ⟨Kb*Kr,LipschitzWith.of_dist_le_mul (fun x y=>?_ )⟩
    have H:=(HB.dist_le_mul (P.R x) (hR x) (P.R y) (hR y)).trans
      (mul_le_mul_of_nonneg_left (HR.dist_le_mul x y) Kb.coe_nonneg)
    simpa only [NNReal.coe_mul,mul_assoc] using H
  · refine ⟨Kh*Kr,LipschitzWith.of_dist_le_mul (fun x y=>?_ )⟩
    have H:=(HH.dist_le_mul (P.R x) (hR x) (P.R y) (hR y)).trans
      (mul_le_mul_of_nonneg_left (HR.dist_le_mul x y) Kh.coe_nonneg)
    simpa only [Pi.mul_apply,id_eq,NNReal.coe_mul,mul_assoc] using H

theorem coefficient_on_same_origin_inverse {n : ℕ}
    (P Q : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : Q.data.s=P.data.s) {r : ℝ} (hr : r∈Icc (0:ℝ) 1) :
    P.coefficient (Q.alpha.val.val r)=
      laplaceComparisonStrength P.data.d P.lam (P.R (Q.alpha.val.val r)) := by
  have H:=Q.alpha.val.property.2 hr.1
  rw [Q.alpha.property.1,hs] at H
  simp only [coefficient,ActualHighOnlyComparisonData.coefficient,omittedStrengthCoefficient,ite_eq_left H]

 theorem ActualWeakHighOnlyHistoryChain.pullback_all_same_origins
    {root M : (n:ℕ)→ActualHighOnlyOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock}
    (H : ActualWeakHighOnlyHistoryChain c0 root M)
    (Hroot : ∀ᶠn in atTop,∀Q : ActualHighOnlyOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock,
      Q.data.s=(root n).data.s → NativePullbackClockRegularity Q.alpha.val.val (root n).b (root n).h 0 1) :
    ∀ᶠn in atTop,∀Q : ActualHighOnlyOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock,
      Q.data.s=(root n).data.s → NativePullbackClockRegularity Q.alpha.val.val (M n).b (M n).h 0 1 := by
  induction H with
  | root=>exact Hroot
  | @child P M history x hx hxunit htarget hcap hweak hd hE hs hb hh ih=>
    filter_upwards [ih,history.same_omission,hb,hh] with n hn hns hnb hnh Q hQ
    have Hs : Q.data.s=(P n).data.s:=hQ.trans hns.symm
    obtain ⟨⟨Kb,HB⟩,Kh,HH⟩:=(P n).full_radius_additions_lipschitz
    have Hp:=(hn Q hQ).perturb_by_lipschitz
      (inverseIntegralConstraints_lipschitz Q.data.hm Q.data.hM Q.alpha.property) HB HH
    apply Hp.congr_on_pullback
    · intro r hr
      rw [hnb,(P n).coefficient_on_same_origin_inverse Q Hs hr]
    · intro r hr
      rw [hnh,(P n).coefficient_on_same_origin_inverse Q Hs hr]

 theorem ActualWeakHighOnlyHistoryChain.pullback
    {root M : (n:ℕ)→ActualHighOnlyOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock}
    (H : ActualWeakHighOnlyHistoryChain c0 root M)
    (Hroot : ∀ᶠn in atTop,∀Q : ActualHighOnlyOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock,
      Q.data.s=(root n).data.s → NativePullbackClockRegularity Q.alpha.val.val (root n).b (root n).h 0 1) :
    ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1 := by
  filter_upwards [H.pullback_all_same_origins Hroot,H.same_omission] with n hn hns
  exact hn (M n) hns

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
