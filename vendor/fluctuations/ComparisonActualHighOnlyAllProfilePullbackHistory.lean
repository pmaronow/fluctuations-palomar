module

public import ComparisonActualHighOnlyWeakHistoryRegularity
public import ComparisonActualHighWallThetaZeroHighOnlyChildPullback

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 18000000

namespace ActualHighOnlyOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock c0 : ℝ} {dim : ℕ→ℕ}

theorem coefficient_on_same_origin_profile {n : ℕ}
    (P : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (a : ActualHighOnlyComparisonData (n+1) delta) (alpha : a.Profile)
    (hs : a.s=P.data.s) {r : ℝ} (hr : r∈Icc (0:ℝ) 1) :
    P.coefficient (alpha.val.val r)=
      laplaceComparisonStrength P.data.d P.lam
        (P.R (alpha.val.val r)) := by
  have H := alpha.val.property.2 hr.1
  rw [alpha.property.1,hs] at H
  simp only [coefficient,ActualHighOnlyComparisonData.coefficient,
    omittedStrengthCoefficient,ite_eq_left H]

theorem ActualWeakHighOnlyHistoryChain.pullback_all_profiles_same_origin
    {root M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock}
    (H : ActualWeakHighOnlyHistoryChain c0 root M)
    (Hroot : ∀ᶠn in atTop,
      ∀a : ActualHighOnlyComparisonData (dim n+1) delta,
      ∀alpha : a.Profile, a.s=(root n).data.s →
        NativePullbackClockRegularity alpha.val.val
          (root n).b (root n).h 0 1) :
    ∀ᶠn in atTop,
      ∀a : ActualHighOnlyComparisonData (dim n+1) delta,
      ∀alpha : a.Profile, a.s=(root n).data.s →
        NativePullbackClockRegularity alpha.val.val
          (M n).b (M n).h 0 1 := by
  induction H with
  | root => exact Hroot
  | @child P M history x hx hxunit htarget hcap hweak hd hE hs hb hh ih =>
    filter_upwards [ih,history.same_omission,hb,hh]
      with n hn hns hnb hnh a alpha ha
    have hsame : a.s=(P n).data.s := ha.trans hns.symm
    obtain ⟨⟨Kb,HB⟩,Kh,HH⟩ := (P n).full_radius_additions_lipschitz
    have Hp := (hn a alpha ha).perturb_by_lipschitz
      (inverseIntegralConstraints_lipschitz a.hm a.hM alpha.property)
      HB HH
    apply Hp.congr_on_pullback
    · intro r hr
      rw [hnb,(P n).coefficient_on_same_origin_profile a alpha hsame hr]
    · intro r hr
      rw [hnh,(P n).coefficient_on_same_origin_profile a alpha hsame hr]

theorem ActualWeakHighOnlyHistoryChain.child_pullback_all_profiles
    {root M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock}
    (H : ActualWeakHighOnlyHistoryChain c0 root M)
    (Hroot : ∀ᶠn in atTop,
      ∀a : ActualHighOnlyComparisonData (dim n+1) delta,
      ∀alpha : a.Profile, a.s=(root n).data.s →
        NativePullbackClockRegularity alpha.val.val
          (root n).b (root n).h 0 1) :
    ∀ᶠn in atTop,
      ∀child : ActualHighOnlyComparisonData (dim n+1) delta,
        child.s=(M n).data.s →
        child.b=(fun u=>(M n).b u-(M n).coefficient u) →
        child.h=(fun u=>(M n).h u+(M n).coefficient u*(M n).R u) →
        ∀alpha : child.Profile,
          NativePullbackClockRegularity alpha.val.val child.b child.h 0 1 := by
  filter_upwards [H.pullback_all_profiles_same_origin Hroot,H.same_omission]
    with n hn hsame child hmass hbare hfield alpha
  have hroot : child.s=(root n).data.s := hmass.trans hsame
  obtain ⟨⟨Kb,HB⟩,Kh,HH⟩ := (M n).full_radius_additions_lipschitz
  have Hp := (hn child alpha hroot).perturb_by_lipschitz
    (inverseIntegralConstraints_lipschitz child.hm child.hM alpha.property)
    HB HH
  apply Hp.congr_on_pullback
  · intro r hr
    rw [hbare]
    dsimp only
    rw [(M n).coefficient_on_same_origin_profile child alpha hmass hr]
  · intro r hr
    rw [hfield]
    dsimp only
    rw [(M n).coefficient_on_same_origin_profile child alpha hmass hr]

end ActualHighOnlyOverlapMinimum

namespace ActualThetaZeroOverlapMinimum

theorem high_only_root_all_profile_pullback
    {m delta cl cu Az C0 Ct D Bclock : ℝ} {dim : ℕ→ℕ}
    (P : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock)
    (root : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock)
    (hsame : ∀ᶠn in atTop,(root n).data.s=(P n).data.s)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=(P n).changedBare u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=(P n).changedField u) :
    ∀ᶠn in atTop,
      ∀a : ActualHighOnlyComparisonData (dim n+1) delta,
      ∀alpha : a.Profile, a.s=(root n).data.s →
        NativePullbackClockRegularity alpha.val.val
          (root n).b (root n).h 0 1 := by
  filter_upwards [hsame,hb,hh] with n hns hnb hnh a alpha ha
  have HB : (root n).b=(P n).changedBare := funext hnb
  have HH : (root n).h=(P n).changedField := funext hnh
  rw [HB,HH]
  exact (P n).changed_pullback_on_high_only_profile a alpha
    (ha.trans hns)

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
