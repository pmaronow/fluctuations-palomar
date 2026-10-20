module

public import ComparisonNativeActualWeakSelectedHistoryClocks
public import ComparisonNativeActualWeakStrengthLimit

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 7000000
namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock c0 : ℝ} {N : ℕ→ℕ}

theorem ActualWeakSelectedHistoryChain.uniform_clock_perturbation
    {root M : (n:ℕ)→NativeOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock}
    (Hhistory : ActualWeakSelectedHistoryChain c0 root M) :
    ∃eta : ℕ→ℝ,(∀n,0 ≤ eta n) ∧ Tendsto eta atTop (𝓝 0) ∧
      ∀ᶠn in atTop,∀u∈Icc (0:ℝ) 1,
        |(M n).b u-(root n).b u| ≤ eta n ∧
        |(M n).h u-(root n).h u| ≤ eta n := by
  induction Hhistory with
  | root =>
    refine ⟨fun _=>0,fun _=>le_rfl,tendsto_const_nhds,?_⟩
    exact Filter.Eventually.of_forall (fun n u _=>by simp)
  | @child P M history x hx hxunit htarget hcap hweak hd hE hb hh ih =>
    obtain ⟨eta,heta,hetalim,Hparent⟩:=ih
    have Hlam:=comparison_parameter_tendsto_zero_of_weak_bounded_call P x hx hxunit hweak
    refine ⟨fun n=>eta n+(P n).lam,fun n=>add_nonneg (heta n) (P n).hlam.le,?_,?_⟩
    · simpa only [zero_add] using hetalim.add Hlam
    · filter_upwards [Hparent,hb,hh] with n hn hnb hnh
      intro u hu
      have Hr:=comparisonSweepQuantile_bounds (P n).context.hc (P n).context.hk
        (P n).context.hkc (P n).context.hm (P n).context.hM (P n).alpha u
      have Hg0 : 0 ≤ laplaceComparisonStrength (P n).context.d (P n).lam ((P n).R u):=
        (laplaceComparisonStrength_pos _ (P n).hlam _).le
      have Hg:=laplaceComparisonStrength_le (P n).context.d (P n).hlam.le ((P n).R u)
      have Hfield : laplaceComparisonStrength (P n).context.d (P n).lam ((P n).R u)*(P n).R u ≤ (P n).lam := by
        exact (mul_le_mul_of_nonneg_left Hr.2 Hg0).trans (by simpa only [mul_one] using Hg)
      have Hp:=hn u hu
      constructor
      · rw [hnb u]
        have Heq : (P n).b u-laplaceComparisonStrength (P n).context.d (P n).lam ((P n).R u)-(root n).b u=
            ((P n).b u-(root n).b u)-laplaceComparisonStrength (P n).context.d (P n).lam ((P n).R u) := by ring
        rw [Heq]
        have H:=abs_sub ((P n).b u-(root n).b u)
          (laplaceComparisonStrength (P n).context.d (P n).lam ((P n).R u))
        rw [abs_of_nonneg Hg0] at H
        linarith only [H,Hp.1,Hg]
      · rw [hnh u]
        have Heq : (P n).h u+laplaceComparisonStrength (P n).context.d (P n).lam ((P n).R u)*(P n).R u-(root n).h u=
            ((P n).h u-(root n).h u)+laplaceComparisonStrength (P n).context.d (P n).lam ((P n).R u)*(P n).R u := by ring
        rw [Heq]
        have H:=abs_add_le ((P n).h u-(root n).h u)
          (laplaceComparisonStrength (P n).context.d (P n).lam ((P n).R u)*(P n).R u)
        rw [abs_of_nonneg (mul_nonneg Hg0 Hr.1)] at H
        linarith only [H,Hp.2,Hfield]

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
