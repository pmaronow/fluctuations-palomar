module

public import ComparisonSignedCavityActualFourCollectiveIteration
public import ComparisonSignedCavityActualFourFrozenLevelAlong
public import ComparisonSignedCavityActualSharpSourceCutReadout
public import ComparisonNativeActualHistoryScalarEndpointLimits
public import ComparisonNativeActualSelectedBadHistorySourceClocks

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

def nativeActualFourFrozenChildResidualEnvelope
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star U : ℕ} (hs : star<U) (hU : U ≤ as.length)
    (W : ℝ) (depth : ℕ) (xs : List (NativeActualResourceState (Spin n×Bool) as i star)) : ℝ :=
  ((List.range depth).map (fun d=>|nativeActualFourFrozenChildSum M hs hU W
    (nativeActualMinimumFourCenteredForest M hs hU W d xs)|)).sum

def ActualInitialFrozenChildEnvelopeOnGivenCutsAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (Cmass : ℝ) (err : ℕ→ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us → ∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      let star:=retainedMassPrefixIndex (w n).star.val as
      let U:=retainedMassPrefixIndex (high n).val as
      ∃hs : star<U,∃hU : U ≤ as.length,
      ∀(i : ℕ) (hi : i ≤ star) (x : ℝ),(M n).xs ≤ x → x ≤ W n →
        partitionPoint 0 as i ≤ Cmass*x →
        nativeActualFourFrozenChildResidualEnvelope (M n) hs hU (W n) depth
          [nativeActualInitialState as i star 0 (hi.trans (hs.le.trans hU))] ≤
            err n*(x*(M n).xs^2)

theorem actual_initial_frozen_child_envelope_of_levels_along
    {m delta cl cu Az C0 Ct D Bclock Cmass c cK A : ℝ}
    (depth : ℕ)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W radius : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) c cK A)
    (Hlevels : ∀d : ℕ,d<depth → ActualOriginalFourFrozenChildLevelSavingAlong d Cmass M W w) :
    ActualInitialFrozenChildEnvelopeOnGivenCutsAlong depth Cmass
      (fun n=>(depth:ℝ)*((dim n+1:ℕ):ℝ)^(-(1:ℝ)/6)) M W w high outer := by
  have HN:=Filter.eventually_all.mpr (fun d : Fin depth=>Hlevels d.val d.isLt)
  filter_upwards [HN,Hcuts] with n hn hcuts
  intro L us hus hret hmesh hstar hhigh houter
  have Hgrid:=Filter.eventually_all.mpr (fun d : Fin depth=>hn d L us hus hstar hret hmesh)
  filter_upwards [Hgrid] with jGrid hj
  dsimp only at hj ⊢
  obtain ⟨hs,HUV,HV,_,_,_,_,_,_,_,_,_,_⟩:=
    hcuts.finite_net_readout us hus hstar hhigh houter jGrid
  have hU:=HUV.le.trans HV
  refine ⟨hs,hU,?_⟩
  intro i hi x hxsx hxW hmass
  unfold nativeActualFourFrozenChildResidualEnvelope
  apply (List.sum_le_sum (fun d hd=>hj ⟨d,List.mem_range.mp hd⟩ _ i hi hs hU x hxsx hxW hmass)).trans_eq
  simp only [List.map_const',List.length_range,List.sum_replicate,nsmul_eq_mul]
  ring

theorem actual_history_initial_frozen_child_envelope_of_pair_budgets_along
    {m delta cl cu Az C0 Ct D Bclock Temp gamma c0 Cmass c cK A : ℝ}
    (depth : ℕ) (hm : 0 < m) (hC0 : 0 < C0) (hTemp : 0 ≤ Temp)
    (hgamma : 0 < gamma) (hcK : 0 < cK) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hepsilon : 0 ≤ epsilon)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock Temp epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (W radius : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n)
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) c cK A)
    (Hpair : ∀d : ℕ,d<depth → ∃B : ℝ,1 ≤ B ∧
      ActualSquareResourcePairBudgetOnEveryFinalNetAlong (d+2) B gamma Cmass M W w) :
    ∃err : ℕ→ℝ,(∀n,0 ≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧
      ActualInitialFrozenChildEnvelopeOnGivenCutsAlong depth Cmass err M W w high outer := by
  have Htotal:=actual_selected_bad_history_total_clock_and_root dim root M epsilon shell hepsilon hb hh Hhistory
  have HK:=Hcuts.mono (fun _ hn=>hn.clock_star)
  have Hlevels (d : ℕ) (hd : d<depth) : ActualOriginalFourFrozenChildLevelSavingAlong d Cmass M W w:=by
    obtain ⟨B,hB,HP⟩:=Hpair d hd
    exact actual_inherited_four_frozen_child_level_saving_of_pair_budget_along
      hm hC0 hTemp hgamma hcK d hB Cmass dim hdim M W hxs
      (Htotal.mono (fun _ hn=>hn.1)) (Htotal.mono (fun _ hn=>hn.2)) w HK HP
  let err n:=(depth:ℝ)*((dim n+1:ℕ):ℝ)^(-(1:ℝ)/6)
  have Hlim : Tendsto err atTop (𝓝 0):=by
    have H:=(tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/6)).comp
      (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
    simpa only [err,Function.comp_def,mul_zero,neg_div] using H.const_mul (depth:ℝ)
  exact ⟨err,(fun n=>by dsimp only [err];positivity),Hlim,
    actual_initial_frozen_child_envelope_of_levels_along depth M W radius w high outer Hcuts Hlevels⟩

theorem actual_selected_bad_history_initial_frozen_child_envelope_on_given_cuts_along
    {m delta cl cu Az C0 Ct D Bclock Temp gamma c0 Cmass c cK A : ℝ}
    (depth : ℕ) (hCm : 0 ≤ Cmass) (hcK : 0 < cK)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0) (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgamma : 0 < gamma) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hepsilon : 0 ≤ epsilon) (hTemp : 0 ≤ Temp)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock Temp epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (W radius : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) c cK A)
    (Hsquare : ∀p : ℕ,ActualOriginalSquareStarMomentOnEveryFinalNetAlong p gamma M W w) :
    ∃err : ℕ→ℝ,(∀n,0 ≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧
      ActualInitialFrozenChildEnvelopeOnGivenCutsAlong depth Cmass err M W w high outer := by
  obtain ⟨Cf,hCf,Hsource⟩:=actual_selected_bad_history_small_source_clocks
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim
    root M epsilon shell hepsilon hTemp hb hh Hhistory
  have hxs n : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  apply actual_history_initial_frozen_child_envelope_of_pair_budgets_along depth hm hC0 hTemp
    hgamma hcK hdim root M epsilon shell hepsilon hb hh Hhistory W radius hxs w high outer Hcuts
  intro d _hd
  exact actual_inherited_square_resource_pair_budget_of_actual_pair_producers_along (d+2) (by omega)
    hm hdelta hroom hcl hcu hAz hC0 hCt hTemp hCf Cmass hCm
    dim hdim M W hxs hWlim Hsource w (Hsquare (d+2-1))

end OAI.SKFluctuations.Cavity
