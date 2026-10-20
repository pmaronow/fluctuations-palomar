module

public import SKProof.OriginalQNativeRootHistory
public import ComparisonNativeActualComparableBandCompleteProfile

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity NativeOverlapMinimum
open scoped Topology NNReal

namespace NativeOverlapMinimum

theorem OriginalQNativeRootHistory.successful_child_comparable_context_original_q
    {m delta cl cu Az C0 Ct D Bclock T c0 C : ℝ} {dim : ℕ → ℕ}
    (hm : 0 < m) (hdelta : 0 < delta)
    (hcl : 0 < cl) (hcu : 0 < cu)
    (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hC : 0 ≤ C) (hAzC : Az ≤ 4*C/cl)
    (hmargin : delta/4 < 3*m-99*delta)
    (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (hdim : Tendsto dim atTop atTop)
    {M : (n : ℕ) → NativeOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock}
    (G : OriginalQNativeRootHistory M T c0)
    (Q : (n : ℕ) → NativeOverlapMinimum (dim n+1)
      m delta (cl/4) (4*cu) (4*C/cl) C0
        (max Ct 1) (max D 1) (max Bclock T))
    (x : ℕ → ℝ) (hxs : ∀n, (M n).xs ≤ x n)
    (hxlim : Tendsto x atTop (𝓝 0))
    (htarget : ∀ᶠn in atTop,
      comparisonConditionalScale (M n).context.N delta
        (M n).context.E (M n).lam ≤ x n)
    (hweak : Tendsto (fun n => laplaceComparisonStrength
      (M n).context.d (M n).lam (x n)/(x n)^2)
      atTop (𝓝 0))
    (hd : ∀ᶠn in atTop, (Q n).context.d = actualChildRadius c0 (x n))
    (hE : ∀ᶠn in atTop, (Q n).context.E = actualChildErrorBudget
      (dim n+1) delta c0 (M n).context.d (M n).lam (x n))
    (hb : ∀ᶠn in atTop, ∀u, (Q n).b u = (M n).b u-
      laplaceComparisonStrength (M n).context.d (M n).lam ((M n).R u))
    (hh : ∀ᶠn in atTop, ∀u, (Q n).h u = (M n).h u+
      laplaceComparisonStrength (M n).context.d (M n).lam ((M n).R u)*
        (M n).R u)
    (hQxs : ∀n, (Q n).xs = x n) :
    Nonempty (NativeActualComparableBandContext Q T) := by
  have hclW : cl/4 ≤ cl := by linarith
  have hcuW : cu ≤ 4*cu := by linarith
  let GW := G.weaken_constants_original_q hclW hcuW hAzC
    (le_max_left Ct 1) (le_max_left D 1)
    (le_max_left Bclock T)
  have hx n : 0 < x n := (M n).hxs.trans_le (hxs n)
  have hcap : ∀ᶠn in atTop,
      (M n).z ≤ (4*C/cl)*x n := by
    filter_upwards [] with n
    exact (M n).hzxs.trans
      ((mul_le_mul_of_nonneg_left (hxs n) hAz).trans
        (mul_le_mul_of_nonneg_right hAzC (hx n).le))
  have hQlim : Tendsto (fun n => (Q n).xs) atTop (𝓝 0) := by
    simpa only [hQxs] using hxlim
  let GQ := GW.append_child_original_q Q x hx
    (hxlim.eventually (eventually_le_nhds zero_lt_one))
    htarget hcap hweak hd hE hb hh
  exact GQ.history.exists_theta_zero_comparable_context_original_q
    hm hdelta (by positivity : 0 < cl/4)
    (by positivity : 0 ≤ 4*C/cl) hC0 hc0 hc01 G.hT
    hmargin hcapmargin hgapmargin dim hdim GQ.wall GQ.root Q
    GQ.hTemp GQ.hunit GQ.htarget GQ.hweak GQ.hsCut
    GQ.hcut GQ.hb GQ.hh hQlim

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
