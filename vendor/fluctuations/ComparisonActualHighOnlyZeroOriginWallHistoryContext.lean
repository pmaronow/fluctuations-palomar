module

public import ComparisonActualHighWallZeroOriginChildPullback

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity
open scoped Topology NNReal
set_option maxHeartbeats 14000000
set_option linter.unusedVariables false

namespace ActualHighOnlyOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock c0 T : ℝ}

theorem ActualWeakHighOnlyHistoryChain.exists_zero_origin_wall_comparable_context
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hc0 : 0 < c0) (hc01 : c0 ≤ 1) (hTpos : 0 < T)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1 : ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (P : (n : ℕ) → ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (root M : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (H : ActualWeakHighOnlyHistoryChain c0 root M)
    (hT : ∀ᶠ n in atTop,(P n).data.T = T)
    (hzero : ∀ᶠ n in atTop,(root n).data.s = 0)
    (x : ℕ → ℝ) (hx : ∀ n,0 < x n) (hxunit : ∀ᶠ n in atTop,x n ≤ 1)
    (htarget : ∀ᶠ n in atTop,comparisonConditionalScale (P n).data.N delta
      (P n).data.E ((P n).data.d^2) ≤ x n)
    (hcap : ∀ᶠ n in atTop,(P n).z ≤ Az*x n)
    (hweak : Tendsto (fun n => (P n).data.g (x n)/(x n)^2) atTop (𝓝 0))
    (hs : Tendsto (fun n => (P n).data.s/
      actualChildCutoff (dim n+1) delta c0 (P n).data.d ((P n).data.d^2) (x n)) atTop (𝓝 0))
    (hcut : ∀ᶠ n in atTop,actualChildCutoff (dim n+1) delta c0 (P n).data.d
      ((P n).data.d^2) (x n) ≤ comparisonLowerScale (root n).context.N
        (root n).context.E (root n).context.d)
    (hb : ∀ᶠ n in atTop,∀ u,(root n).b u = (P n).data.b (P n).alpha u)
    (hh : ∀ᶠ n in atTop,∀ u,(root n).h u = (P n).data.h (P n).alpha u)
    (hfieldscale : ∀ᶠ n in atTop,(P n).data.d^2 ≤ comparisonLowerScale
      (root n).context.N (root n).context.E (root n).context.d)
    (hxs : Tendsto (fun n => (M n).xs) atTop (𝓝 0)) :
    Nonempty (HighOnlyActualComparableBandContext M T) := by
  have Hroot : ∀ᶠ n in atTop,(∀ u ∈ Icc (0 : ℝ) 1,(root n).h u+(root n).b u ≤ T) ∧
      (root n).h 0 = 0 := by
    filter_upwards [hT,hb,hh] with n hnT hnb hnh
    constructor
    · intro u hu
      rw [hnb,hnh,←((P n).data.clock_coe (P n).alpha hu).1,
        ←((P n).data.clock_coe (P n).alpha hu).2,←hnT]
      exact (P n).data.total_clock_le (P n).alpha u hu
    · rw [hnh,←((P n).data.clock_coe (P n).alpha (by norm_num)).2,
        (P n).data.root_field_zero (P n).alpha]
      rfl
  have Hfield : ∃ C : ℝ,0 ≤ C ∧ ∀ᶠ n in atTop,∀ u ∈ Icc (0 : ℝ) 1,(root n).h u ≤
      C*(comparisonLowerScale (root n).context.N (root n).context.E (root n).context.d+u) := by
    refine ⟨1,zero_le_one,?_⟩
    filter_upwards [hh,hfieldscale] with n hnh hn u hu
    rw [hnh,←((P n).data.clock_coe (P n).alpha hu).2,one_mul]
    exact ((P n).data.field_le_strength (P n).alpha hu).trans (by linarith [hu.1])
  have Hbare : ∀ᶠ n in atTop,∀ Q : ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock,
      Q.data.s = (root n).data.s → NativePullbackClockRegularity Q.alpha.val.val
        (root n).b (root n).h 0 1 := by
    filter_upwards [hzero,hb,hh] with n hns hnb hnh Q hQ
    have HB : (root n).b = (P n).data.b (P n).alpha := funext hnb
    have HH : (root n).h = (P n).data.h (P n).alpha := funext hnh
    rw [HB,HH]
    exact (P n).data.changed_pullback_on_zero_origin_high_only (P n).alpha Q (hQ.trans hns)
  have Htotal := H.total_root Hroot
  obtain ⟨Cf,hCf,Hsource⟩ := H.bare_field_budget hm hdelta hcl hAz hC0 hc0
    hmargin hcapmargin hdim Hfield
  have Hphysical : ∀ᶠ n in atTop,∀ u ∈ Icc (0 : ℝ) 1,((M n).bf u : ℝ) ≤ T ∧
      ((M n).hf u : ℝ) ≤ (Cf+D^2*(Az+1/cl))*((M n).xs+u) := by
    filter_upwards [Htotal,Hsource] with n hn hnS
    exact (M n).small_source_clocks_of_bare_field hcl hAz hCf hn.1 hnS
  have Hinherit := H.cutoff_inherits_root hm hdelta hAz hC0 hc0 hmargin hcapmargin hdim
  have Homit : Tendsto (fun n => (M n).data.s/comparisonLowerScale
      (M n).context.N (M n).context.E (M n).context.d) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [H.same_omission,hzero] with n hnS hnroot
    simp only [hnS,hnroot,zero_div]
  have Hpositive := actual_wall_first_child_comparable_bare_clocks hdelta hcl hAz hC0 hc0 hc01
    hgapmargin dim hdim P hT x hx hxunit htarget hcap hweak hs
  have Hseed := SequentialComparableBareClocks.toHighOnly Hpositive root hcut hb hh
  exact ⟨⟨hTpos,hxs,Homit,H.pullback Hbare,Htotal,Cf+D^2*(Az+1/cl),
    by positivity,Hphysical,H.comparable_clocks hm hdelta hcl hAz hC0 hc0 hc01
      hmargin hcapmargin hgapmargin hdim Hseed⟩⟩

 theorem ActualWeakHighOnlyHistoryChain.exists_concrete_zero_origin_wall_comparable_context
    {m cl cu Az C0 Ct D Bclock c0 T : ℝ}
    (hm : 0 < m) (hmsmall : m ≤ (1:ℝ)/120) (hcl : 0 < cl) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hc0 : 0 < c0) (hc01 : c0 ≤ 1) (hTpos : 0 < T)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (P : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m (m/10000) cl cu Az C0 Ct D Bclock)
    (root M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m (m/10000) cl cu Az C0 Ct D Bclock)
    (H : ActualWeakHighOnlyHistoryChain c0 root M)
    (hT : ∀ᶠn in atTop,(P n).data.T=T)
    (hE : ∀ᶠn in atTop,(P n).data.E=wallHighError m (dim n+1))
    (hd : ∀ᶠn in atTop,(P n).data.d=wallHighD m (dim n+1))
    (hs : ∀ᶠn in atTop,(P n).data.s=wallHighMass m (dim n+1))
    (hzero : ∀ᶠn in atTop,(root n).data.s=0)
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
    (hxs : Tendsto (fun n=>(M n).xs) atTop (𝓝 0)) :
    Nonempty (HighOnlyActualComparableBandContext M T) := by
  have hdelta : 0 < m/10000:=by positivity
  have Hcut : ∀ᶠn in atTop,actualChildCutoff (dim n+1) (m/10000) c0 (P n).data.d
      ((P n).data.d^2) (x n) ≤ comparisonLowerScale (root n).context.N
        (root n).context.E (root n).context.d := by
    filter_upwards [hfirstd,hfirstE] with n hnd hnE
    simp only [comparisonLowerScale,ActualHighOnlyComparisonData.N,hnd,hnE,actualChildCutoff]
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
    have Hnum:=NativeOverlapMinimum.concrete_wall_square_strength_le_lower_scale hmsmall (by omega : 0<dim n+1)
    rw [←hnd,←hnE] at Hnum
    exact Hnum.trans (hnIn.trans hnCut)
  exact H.exists_zero_origin_wall_comparable_context hm hdelta hcl hAz hC0 hc0 hc01 hTpos
    (by linarith) (by linarith) (by linarith) dim hdim P root M hT hzero x hx hxunit htarget hcap
    hweak Hs Hcut hb hh Hfieldscale hxs

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
