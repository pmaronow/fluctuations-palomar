module

public import ComparisonNativeActualWallRawHistory

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity
open scoped Topology NNReal
set_option maxHeartbeats 14000000
set_option linter.unusedVariables false
namespace NativeOverlapMinimum
def ActualWeakSelectedHistoryChain.concrete_wall_raw_history
    {m cl cu Az C0 Ct D Bclock c0 T : ℝ}
    (hm : 0 < m) (hmsmall : m ≤ (1:ℝ)/120) (hcl : 0 < cl) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hc0 : 0 < c0) (hc01 : c0 ≤ 1) (hTpos : 0 < T)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (P : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m (m/10000) cl cu Az C0 Ct D Bclock)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m (m/10000) cl cu Az C0 Ct D Bclock)
    (H : ActualWeakSelectedHistoryChain c0 root M)
    (hT : ∀ᶠn in atTop,(P n).data.T=T)
    (hE : ∀ᶠn in atTop,(P n).data.E=wallHighError m (dim n+1))
    (hd : ∀ᶠn in atTop,(P n).data.d=wallHighD m (dim n+1))
    (hs : ∀ᶠn in atTop,(P n).data.s=wallHighMass m (dim n+1))
    (x : ℕ→ℝ) (hx : ∀n,0 < x n) (hxunit : ∀ᶠn in atTop,x n ≤ 1)
    (htarget : ∀ᶠn in atTop,comparisonConditionalScale (P n).data.N (m/10000)
      (P n).data.E ((P n).data.d^2) ≤ x n)
    (hcap : ∀ᶠn in atTop,(P n).z ≤ Az*x n)
    (hweak : Tendsto (fun n=>(P n).data.g (x n)/(x n)^2) atTop (𝓝 0))
    (hfirstd : ∀ᶠn in atTop,(root n).context.d=actualChildRadius c0 (x n))
    (hfirstE : ∀ᶠn in atTop,(root n).context.E=actualChildErrorBudget (dim n+1) (m/10000)
      c0 (P n).data.d ((P n).data.d^2) (x n))
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=(P n).data.b (P n).alpha u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=(P n).data.h (P n).alpha u)
    :
    ActualNativeWallHistory M T c0 := by
  have hdelta : 0 < m/10000:=by positivity
  have Hcut : ∀ᶠn in atTop,actualChildCutoff (dim n+1) (m/10000) c0 (P n).data.d
      ((P n).data.d^2) (x n) ≤ comparisonLowerScale (root n).context.N
        (root n).context.E (root n).context.d := by
    filter_upwards [hfirstd,hfirstE] with n hnd hnE
    simp only [comparisonLowerScale,NativeOverlapContext.N,hnd,hnE,actualChildCutoff]
    exact le_rfl
  have Hratio : Tendsto (fun n=>(P n).data.s/
      comparisonLowerScale (P n).data.N (P n).data.E (P n).data.d) atTop (𝓝 0) := by
    apply ((concrete_wall_omission_ratio_tendsto_zero hm).comp
      ((tendsto_add_atTop_nat 1).comp hdim)).congr'
    filter_upwards [hE,hd,hs] with n hnE hnd hns
    simp only [Function.comp_apply,hnE,hnd,hns,ActualHighWallData.N]
  have Hs:=actual_wall_omission_ratio_inherits_child_cutoff hm hdelta hC0 hc0 (by linarith)
    dim hdim P x hx htarget hweak Hratio
  have Hinherit:=actual_wall_child_cutoff_inheritance hm hdelta hC0 hc0 (by linarith)
    dim hdim P x hx htarget hweak
  have Hfieldscale : ∀ᶠn in atTop,(P n).data.d^2 ≤ comparisonLowerScale
      (root n).context.N (root n).context.E (root n).context.d := by
    filter_upwards [hE,hd,Hinherit,Hcut] with n hnE hnd hnIn hnCut
    have Hnum:=concrete_wall_square_strength_le_lower_scale hmsmall (by omega : 0<dim n+1)
    rw [←hnd,←hnE] at Hnum
    exact Hnum.trans (hnIn.trans hnCut)
  exact ⟨P,root,H,x,hx,hxunit,htarget,hcap,hweak,Hs,Hcut,hb,hh,Hfieldscale,hT,hTpos⟩
theorem ActualNativeWallHistory.concrete_wall_limits
    {m delta cl cu Az C0 Ct D Bclock c0 T : ℝ} {dim : ℕ→ℕ}
    {M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    (G : ActualNativeWallHistory M T c0) (hmmax : m < 1/300)
    (hdim : Tendsto dim atTop atTop)
    (hd : ∀ᶠn in atTop,(G.wall n).data.d=wallHighD m (dim n+1))
    (hs : ∀ᶠn in atTop,(G.wall n).data.s=wallHighMass m (dim n+1)) :
    Tendsto (fun n=>(G.wall n).data.s) atTop (𝓝 0) ∧
      Tendsto (fun n=>(G.wall n).data.d) atTop (𝓝 0) := by
  have HN : Tendsto (fun n=>((dim n+1:ℕ):ℝ)) atTop atTop:=
    tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim)
  constructor
  · have H:=(tendsto_rpow_neg_atTop (show 0 < (1:ℝ)/6-5*m by linarith)).comp HN
    apply H.congr'
    filter_upwards [hs] with n hn
    simp only [wallHighMass,Function.comp_apply] at *
    rw [hn]
    congr 1
    ring
  · have H:=(tendsto_rpow_neg_atTop (show 0 < (1:ℝ)/6-15*m by linarith)).comp HN
    apply H.congr'
    filter_upwards [hd] with n hn
    simp only [wallHighD,Function.comp_apply] at *
    rw [hn]
    congr 1
    ring

theorem ActualNativeWallHistory.root_matrix_lower_of_small_epsilon
    {m delta cl cu Az C0 Ct D Bclock c0 T : ℝ} {dim : ℕ→ℕ}
    {M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    (G : ActualNativeWallHistory M T c0)
    (heps : ∀ᶠn in atTop,(G.wall n).data.epsilon ≤ T/4)
    (hd : ∀ᶠn in atTop,(G.wall n).data.d^2 ≤ 3*T/8) :
    ∀ᶠn in atTop,5*T/8 ≤ (G.root n).b 0 := by
  filter_upwards [G.hb,G.hTemp,heps,hd] with n hnb hnT hnE hnD
  have HE : (G.wall n).data.epsilon ≤ (G.wall n).data.T/4 := by simpa only [hnT] using hnE
  have HD : (G.wall n).data.d^2 ≤ 3*(G.wall n).data.T/8 := by simpa only [hnT] using hnD
  have H:=(G.wall n).data.changed_global_matrix_lower_of_small_epsilon (G.wall n).alpha HE HD 0 (by norm_num)
  rw [hnb]
  simpa only [hnT] using H

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
