module

public import ComparisonSignedCavityActualTargetMeanCorrectionRate
public import ComparisonNativeActualSelectedBadHistorySourceClocks

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem actual_selected_bad_history_target_mean_correction_vanishing_along
    (Bclock Temp Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0) (hmargin : delta/4 < 3*m-99*delta)
    (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n : ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hepsilon : 0 ≤ epsilon)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock Temp epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : NativeOverlapMinimum.ActualSelectedBadHistoryChain c0 root M)
    (x : ℕ → ℝ) (hxs : ∀n,(M n).xs ≤ x n) (hxlim : Tendsto x atTop (𝓝 0)) :
    ∃eta : ℕ → ℝ,(∀n,0 ≤ eta n) ∧ Tendsto eta atTop (𝓝 0) ∧
      ∀ᶠn in atTop,∀us : List PositiveMass,(∀u∈us,u.val ≤ 1) →∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀i U : ℕ,i<U → U ≤ as.length → partitionPoint 0 as i ≤ Ccut*x n →
          |nativeActualTargetOriginalMeanCorrection (M n) as i U| ≤ eta n*(x n)^3 := by
  obtain ⟨Cf,hCf,Hsource⟩ := NativeOverlapMinimum.actual_selected_bad_history_small_source_clocks
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim root M epsilon shell hepsilon hTemp hb hh Hhistory
  have Htotal:=NativeOverlapMinimum.actual_selected_bad_history_total_clock_and_root
    dim root M epsilon shell hepsilon hb hh Hhistory
  obtain ⟨C,hC,Hrate⟩:=eventually_actual_inherited_target_mean_correction_rate
    (D:=D) Bclock Temp Cf Ccut hTemp hCf hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨fun n=>C*((dim n+1:ℕ):ℝ)^(-(1:ℝ)/6),fun n=>by positivity,?_,?_⟩
  · have H:=((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/6)).comp
      ((tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).comp hdim)).const_mul C
    simpa only [Function.comp_def,mul_zero,neg_div] using H
  · have HX:=hxlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
    filter_upwards [hdim.eventually Hrate,Hsource,Htotal,HX] with n hn hs ht hx
    intro us hus
    filter_upwards [hn (M n) hs ht.1 ht.2 ((hxs n).trans hx) us hus] with jGrid hj
    dsimp only at hj ⊢
    intro i U hi hU hmass
    exact hj i U hi hU (x n) (hxs n) hmass

end OAI.SKFluctuations.Cavity
