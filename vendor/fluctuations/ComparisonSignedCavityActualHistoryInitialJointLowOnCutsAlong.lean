module

public import ComparisonSignedCavityActualInitialJointLowRestorationAlong
public import ComparisonSignedCavityActualConstantSourceCategoryReduction
public import ComparisonNativeActualSelectedBadHistorySourceClocks
public import ComparisonSignedCavityActualSharpSourceCutReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 22000000
set_option backward.isDefEq.respectTransparency false

theorem actual_inherited_initial_joint_LOW_restoration_category_rate_along
    (depth : ℕ) (Bclock Temp Cf Cmass Ccut cK : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 < Ccut) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D Tstar Lwin Cwindow : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cwindow (w n)) :
    ∃err : ℕ→ℝ,(∀n,0 ≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧ ∀ᶠn in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        ∀(i U : ℕ) (hi : i ≤ star) (hs : star<U) (hU : U ≤ as.length),
        partitionPoint 0 as U ≤ min (Ccut*W n) 1 →
        partitionPoint 0 as star ≤ Cmass*W n →
        cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as star →
        ∀x : ℝ,(M n).xs ≤ x → x ≤ W n → partitionPoint 0 as i ≤ Cmass*x → ∀seedMass : ℝ,
        let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) as i star seedMass (hi.trans (hs.le.trans hU))
        let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
        let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
        |nativeActualFourOtherCategorySum (M n) U (W n)
          (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth [st])
          .jointLowRestoration|/(chi*K star) ≤
            err n*x*(M n).xs^2 := by
  obtain ⟨err,herr,hlim,H⟩:=actual_inherited_initial_joint_LOW_restoration_forest_rate_along
    depth Bclock Temp Cf Cmass Ccut cK hTemp hCf hCmass hCcut hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M W hcanonical hWlim Hsource w hw
  refine ⟨err,herr,hlim,?_⟩
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [H,Hsource,HW] with n hn hsource hW1
  have hxW : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hW : 0 < W n:=(M n).hxs.trans_le hxW
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar] with jGrid hj
  dsimp only at hj ⊢
  intro i U hi hs hU hcut hmassstar hstarK x hxsx hxWscale hmi seedMass
  have HR:=actual_joint_LOW_restoration_category_signed_sum_abs_le_error_sum (M n) hCf hsource
    (hxW.trans hW1) (finiteCutMasses_ordered us hus jGrid) hs hU hW hcK hstarK
    (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth
      [nativeActualInitialState (S:=Spin (dim n)×Bool) (finiteCutMasses us jGrid) i
        (retainedMassPrefixIndex (w n).star.val (finiteCutMasses us jGrid)) seedMass
        (hi.trans (hs.le.trans hU))])
  exact HR.trans (hj i U hi hs hU hcut hmassstar hstarK x hxsx hxWscale hmi seedMass)

def ActualInitialJointLowRestorationOnGivenCutsAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} {dim : ℕ→ℕ}
    (depth : ℕ) (A : ℝ) (err : ℕ→ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us → ∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      let star:=retainedMassPrefixIndex (w n).star.val as
      let U:=retainedMassPrefixIndex (high n).val as
      ∀(i : ℕ) (hi : i ≤ star) (hs : star<U) (hU : U ≤ as.length),
      ∀x : ℝ,(M n).xs ≤ x → x ≤ W n → partitionPoint 0 as i ≤ A*x → ∀seedMass : ℝ,
      let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) as i star seedMass (hi.trans (hs.le.trans hU))
      let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
      let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
      |nativeActualFourOtherCategorySum (M n) U (W n)
        (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth [st])
        .jointLowRestoration|/(chi*K star) ≤ err n*x*(M n).xs^2

theorem actual_inherited_initial_joint_LOW_restoration_on_given_cuts_along
    {m delta cl cu Az C0 Ct D Bclock Temp Cf Tstar Lwin Cwindow cFirst cK A : ℝ}
    (depth : ℕ) (hA : 0 < A) (hcK : 0 < cK)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W radius : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cwindow (w n))
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) cFirst cK A) :
    ∃err : ℕ→ℝ,(∀n,0 ≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧
      ActualInitialJointLowRestorationOnGivenCutsAlong depth A err M W w high outer := by
  obtain ⟨err,herr,hlim,H⟩:=actual_inherited_initial_joint_LOW_restoration_category_rate_along
    depth Bclock Temp Cf A A cK hTemp hCf hA.le hA hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M W hcanonical hWlim Hsource w hw
  refine ⟨err,herr,hlim,?_⟩
  filter_upwards [H,Hcuts] with n hn hcuts
  intro L us hus hret hmesh hstar hhigh houter
  filter_upwards [hn L us hus hret hmesh hstar] with jGrid hj
  dsimp only at hj ⊢
  intro i hi hs hU x hxsx hxW hmi seedMass
  have Hread:=hcuts.finite_net_readout us hus hstar hhigh houter jGrid
  obtain ⟨_,_,_,_,hstarMass,_,_,_,_,_,_,hstarK,_⟩:=Hread
  have huMass:=nativeRetainedCut_partitionPoint (finiteCutMasses us jGrid)
    (finiteCutMasses_ordered us hus jGrid) (high n) (finiteCutMasses_nodes us jGrid hhigh)
  have hcut : partitionPoint 0 (finiteCutMasses us jGrid)
      (retainedMassPrefixIndex (high n).val (finiteCutMasses us jGrid)) ≤ min (A*W n) 1 := by
    rw [huMass]
    exact le_min (hcuts.high_lt.le.trans hcuts.outer_scale)
      (hcuts.high_lt.le.trans hcuts.outer_le_one)
  exact hj i _ hi hs hU hcut hstarMass hstarK x hxsx hxW hmi seedMass

theorem actual_selected_bad_history_initial_joint_LOW_restoration_on_given_cuts_along
    {m delta cl cu Az C0 Ct D Bclock Temp Tstar Lwin Cwindow c0 cFirst cK A : ℝ}
    (depth : ℕ) (hA : 0 < A) (hcK : 0 < cK)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0) (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hepsilon : 0 ≤ epsilon) (hTemp : 0 ≤ Temp)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock Temp epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (W radius : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cwindow (w n))
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) cFirst cK A) :
    ∃err : ℕ→ℝ,(∀n,0 ≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧
      ActualInitialJointLowRestorationOnGivenCutsAlong depth A err M W w high outer := by
  obtain ⟨Cf,hCf,Hsource⟩:=actual_selected_bad_history_small_source_clocks
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim root M
    epsilon shell hepsilon hTemp hb hh Hhistory
  exact actual_inherited_initial_joint_LOW_restoration_on_given_cuts_along
    depth hA hcK hm hdelta hroom hcl hcu hAz hC0 hCt hTemp hCf dim hdim M W radius
    hcanonical hWlim Hsource w high outer hw Hcuts

end OAI.SKFluctuations.Cavity
