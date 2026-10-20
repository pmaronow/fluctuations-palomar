module

public import ComparisonActualHighWallComparableBandClocks
public import ComparisonActualHighWallBarePullback
public import ComparisonActualHighWallSourceClockBudget
public import ComparisonNativeActualGeneralBareHistoryCavityContext
public import ComparisonNativeActualComparableBandContext

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity NativeOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 12000000
set_option linter.unusedVariables false
namespace NativeOverlapMinimum

 theorem ActualWeakSelectedHistoryChain.exists_wall_comparable_context
    {m delta cl cu Az C0 Ct D Bclock c0 T : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hc0 : 0 < c0) (hc01 : c0 ≤ 1) (hTpos : 0 < T)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (P : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (H : ActualWeakSelectedHistoryChain c0 root M)
    (hT : ∀ᶠn in atTop,(P n).data.T=T)
    (x : ℕ→ℝ) (hx : ∀n,0 < x n) (hxunit : ∀ᶠn in atTop,x n ≤ 1)
    (htarget : ∀ᶠn in atTop,comparisonConditionalScale (P n).data.N delta
      (P n).data.E ((P n).data.d^2) ≤ x n)
    (hcap : ∀ᶠn in atTop,(P n).z ≤ Az*x n)
    (hweak : Tendsto (fun n=>(P n).data.g (x n)/(x n)^2) atTop (𝓝 0))
    (hs : Tendsto (fun n=>(P n).data.s/
      actualChildCutoff (dim n+1) delta c0 (P n).data.d ((P n).data.d^2) (x n)) atTop (𝓝 0))
    (hcut : ∀ᶠn in atTop,actualChildCutoff (dim n+1) delta c0 (P n).data.d
      ((P n).data.d^2) (x n) ≤ comparisonLowerScale (root n).context.N
        (root n).context.E (root n).context.d)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=(P n).data.b (P n).alpha u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=(P n).data.h (P n).alpha u)
    (hfieldscale : ∀ᶠn in atTop,(P n).data.d^2 ≤ comparisonLowerScale
      (root n).context.N (root n).context.E (root n).context.d)
    (hxs : Tendsto (fun n=>(M n).xs) atTop (𝓝 0)) :
    Nonempty (NativeActualComparableBandContext M T) := by
  have Hroot : ∀ᶠn in atTop,(∀u∈Icc (0:ℝ) 1,(root n).h u+(root n).b u ≤ T) ∧
      (root n).h 0=0 := by
    filter_upwards [hT,hb,hh] with n hnT hnb hnh
    constructor
    · intro u hu
      rw [hnb,hnh,←((P n).data.clock_coe (P n).alpha hu).1,
        ←((P n).data.clock_coe (P n).alpha hu).2,←hnT]
      exact (P n).data.total_clock_le (P n).alpha u hu
    · rw [hnh,←((P n).data.clock_coe (P n).alpha (by norm_num)).2,
        (P n).data.root_field_zero (P n).alpha]
      rfl
  have Hfield : ∀ᶠn in atTop,∀u∈Icc (0:ℝ) 1,(root n).h u ≤
      (1:ℝ)*(comparisonLowerScale (root n).context.N (root n).context.E (root n).context.d+u) := by
    filter_upwards [hh,hfieldscale] with n hnh hn u hu
    rw [hnh,←((P n).data.clock_coe (P n).alpha hu).2,one_mul]
    exact ((P n).data.field_le_strength (P n).alpha hu).trans (by linarith [hu.1])
  have Hbare : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val
      (root n).b (root n).h 0 1 := by
    filter_upwards [hb,hh] with n hnb hnh
    have Hb : (fun r=>(root n).b ((M n).alpha.val.val r))=
        (fun r=>((P n).data.bf (P n).alpha ((M n).alpha.val.val r):ℝ)) := by
      funext r
      rw [hnb,((P n).data.clock_coe (P n).alpha ((M n).alpha.val.property.1 r)).1]
    have Hh : (fun r=>(root n).h ((M n).alpha.val.val r))=
        (fun r=>((P n).data.hf (P n).alpha ((M n).alpha.val.val r):ℝ)) := by
      funext r
      rw [hnh,((P n).data.clock_coe (P n).alpha ((M n).alpha.val.property.1 r)).2]
    unfold NativePullbackClockRegularity
    rw [Hb,Hh]
    exact (P n).data.changed_pullback_clock_regularity (P n).alpha (M n)
  obtain ⟨G⟩:=H.exists_general_bare_cavity_clock_context hm hdelta hcl hAz hC0 hc0
    hTpos (by norm_num : (0:ℝ)≤1) hmargin hcapmargin hdim Hroot Hfield Hbare hxs
  have Hpositive:=actual_wall_first_child_comparable_bare_clocks hdelta hcl hAz hC0 hc0 hc01
    hgapmargin dim hdim P hT x hx hxunit htarget hcap hweak hs
  have Hseed:=Hpositive.toNative root hcut hb hh
  exact ⟨⟨G,H.comparable_clocks hm hdelta hcl hAz hC0 hc0 hc01 hmargin hcapmargin
    hgapmargin hdim Hseed⟩⟩

 theorem concrete_wall_square_strength_le_lower_scale
    {m : ℝ} (hm : m ≤ (1:ℝ)/120) {n : ℕ} (hn : 0 < n) :
    (wallHighD m n)^2 ≤ comparisonLowerScale (n:ℝ) (wallHighError m n) (wallHighD m n) := by
  rw [wallHighLowerScale_eq m hn]
  unfold wallHighD
  rw [←Real.rpow_two,←Real.rpow_mul (by positivity : 0≤(n:ℝ))]
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn : (1:ℝ)≤(n:ℝ))
  norm_num
  linarith

 theorem ActualWeakSelectedHistoryChain.exists_concrete_wall_comparable_context
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
    (hxs : Tendsto (fun n=>(M n).xs) atTop (𝓝 0)) :
    Nonempty (NativeActualComparableBandContext M T) := by
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
  exact H.exists_wall_comparable_context hm hdelta hcl hAz hC0 hc0 hc01 hTpos
    (by linarith) (by linarith) (by linarith) dim hdim P root M hT x hx hxunit htarget hcap
    hweak Hs Hcut hb hh Hfieldscale hxs

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
