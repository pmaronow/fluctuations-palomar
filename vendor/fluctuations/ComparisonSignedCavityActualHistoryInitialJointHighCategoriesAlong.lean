module

public import ComparisonSignedCavityActualInitialJointHighRestorationCategoryAlong
public import ComparisonNativeActualSelectedBadHistorySourceClocks

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 26000000
set_option backward.isDefEq.respectTransparency false

theorem actual_selected_bad_history_initial_joint_HIGH_categories_rate_along
    (depth : ℕ) (Bclock Temp Cmass Ccut cK : ℝ)
    (hTemp : 0 ≤ Temp) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D Cs c c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c)
    (hc0 : 0 < c0) (hmargin : delta/4 < 3*m-99*delta)
    (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (epsilon shell : ℝ) (hepsilon : 0 ≤ epsilon)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock Temp epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (x : ℕ→ℝ) (hxsx : ∀ᶠn in atTop,(M n).xs ≤ x n) (hxW : ∀ᶠn in atTop,x n ≤ W n)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2 ≤ Cs*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (w : ℕ→ActualSlowWindowChoice) :
    ∃Cf : ℝ,0 ≤ Cf ∧ (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf) ∧
      ∀kind : NativeJointHighRestorationKind,∃err : ℕ→ℝ,(∀n,0 ≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧ ∀ᶠn in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        ∀(i U : ℕ) (hi : i ≤ star) (hs : star<U) (hU : U ≤ as.length),
        2*c*W n ≤ partitionPoint 0 as U → partitionPoint 0 as U ≤ Ccut*W n →
        partitionPoint 0 as i ≤ Cmass*x n →
        partitionPoint 0 as star ≤ Cmass*W n →
        cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as star →
        ∀seedMass : ℝ,
        let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) as i star seedMass (hi.trans (hs.le.trans hU))
        let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
        let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
        |nativeActualFourOtherCategorySum (M n) U (W n)
          (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth [st]) kind.category|/
          (chi*K star) ≤ err n*(x n*(M n).xs^2) := by
  obtain ⟨Cf,hCf,Hsource⟩:=actual_selected_bad_history_small_source_clocks
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim root M
    epsilon shell hepsilon hTemp hb hh Hhistory
  obtain ⟨ps,Hps⟩:=Hhistory.literal_readout epsilon shell hb hh
  have Hshell : ∀ᶠn in atTop,∃(Tbase eps sh : ℝ) (ts : List ComparisonHistoryTerm),
      (∀u,(M n).b u=historyMatrixClock Tbase eps sh ts u) ∧
      (∀u,(M n).h u=historyFieldClock ts u):=by
    filter_upwards [Hps] with n hn
    exact ⟨Temp,epsilon,shell,((ps.map (fun P=>P n)).map (fun P=>P.toHistoryTerm)),hn.2.1,hn.2.2⟩
  refine ⟨Cf,hCf,Hsource,?_⟩
  intro kind
  obtain ⟨raw,Hraw,H⟩:=actual_inherited_initial_joint_HIGH_restoration_category_rate_along
    kind depth Bclock Temp Cf Cmass Ccut cK hTemp hCf hCmass hCcut hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
    dim hdim M W hcanonical hWlim Hsource x hxsx hxW hsmall Hshell w
  refine ⟨fun n=>|raw n|,fun n=>abs_nonneg _,?_,?_⟩
  · simpa only [abs_zero] using Hraw.abs
  · filter_upwards [H,hxsx] with n hn hnx
    intro L us hus hret hmesh hstar
    filter_upwards [hn L us hus hret hmesh hstar] with jGrid hj
    dsimp only at hj ⊢
    intro i U hi hs hU hcutlo hcut hmi hmassstar hstarK seedMass
    apply (hj i U hi hs hU hcutlo hcut hmi hmassstar hstarK seedMass).trans
    exact mul_le_mul_of_nonneg_right (le_abs_self (raw n))
      (mul_nonneg ((M n).hxs.le.trans hnx) (sq_nonneg _))

end OAI.SKFluctuations.Cavity
