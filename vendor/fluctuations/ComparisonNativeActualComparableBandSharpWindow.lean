module

public import ComparisonNativeActualComparableBandContext
public import ComparisonSignedCavityActualPositiveBandSharpWindowSequence
public import ComparisonSignedCavityActualPositiveBandSharpWindowSequenceLateHalf
public import ComparisonSignedCavityScalarInheritedContinuumRemainder

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity NativeStarBuffer NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 14000000
set_option linter.unusedVariables false

 theorem exists_actual_comparable_context_sharp_window_sequence
    {m delta cl cu Az C0 Ct D Bclock T L Ctest : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCtest : 0 ≤ Ctest) (hL : 0 < L)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ctest*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    ∃Cs : ℝ,0 < Cs ∧ ∃w : ℕ→ActualSlowWindowChoice,
      ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cs (w n) := by
  have hxs n : (M n).xs ≤ W n := by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have hay : ∀ᶠn in atTop,comparisonLowerScale (M n).context.N (M n).context.E (M n).context.d ≤ W n :=
    Eventually.of_forall (fun n=>(M n).hscale.trans (hxs n))
  exact exists_actual_regular_positive_band_sharp_window_sequence hm hdelta hroom hcl hcu hAz hC0 hCt
    hCtest G.hT hL dim hdim M W hcanonical hWlim hcompare G.pullback (G.comparable W hWlim hay)

 theorem exists_actual_comparable_context_sharp_window_sequence_later_half
    {m delta cl cu Az C0 Ct D Bclock T L Ctest : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCtest : 0 ≤ Ctest) (hL : 0 < L)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ctest*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    ∃Cs : ℝ,0 < Cs ∧ ∃w : ℕ→ActualSlowWindowChoice,
      (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cs (w n)) ∧
      ∀ᶠn in atTop,(calibratedBandStart cu Az+2*L)*W n < (w n).star.val := by
  have hxs n : (M n).xs ≤ W n := by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have hay : ∀ᶠn in atTop,comparisonLowerScale (M n).context.N (M n).context.E (M n).context.d ≤ W n :=
    Eventually.of_forall (fun n=>(M n).hscale.trans (hxs n))
  exact exists_actual_regular_positive_band_sharp_window_sequence_later_half hm hdelta hroom hcl hcu hAz hC0 hCt
    hCtest G.hT hL dim hdim M W hcanonical hWlim hcompare G.pullback (G.comparable W hWlim hay)

 theorem eventually_actual_cavity_context_original_continuum_scalar_remainder
    {m delta cl cu Az C0 Ct D Bclock Temp : ℝ}
    (A : ℝ) (hA : 0 ≤ A)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualCavityClockContext M Temp)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0)) :
    ∃R : ℝ,0 < R ∧ ∀ᶠn in atTop,
      ∀(before after : List PositiveMass) (a : PositiveMass),
        MassOrdered 0 (before++a::after) →
      ∀j V : ℕ,j < before.length+1 → before.length+1 ≤ V →
        V ≤ (before++a::after).length →
        a.val < partitionPoint 0 (before++a::after) V →
        partitionPoint 0 (before++a::after) V ≤ A*(W n) →
      ∀(tree : ClockTree (Spin (dim n)×Bool) (before++a::after))
        (start : ℝ) (_hoa : MassOrdered start (before++a::after)) (s : tree.Slot),
      let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf (before++a::after)
      let chi:=((tree.markedAttach start).map (fun p=>p.coeff*
        fullScalarCutGamma p.tree (before.length+1) K (p.embed s) p.mark)).sum
      |nativeOriginalScalarPairMean (before++a::after) K j-chi^2*K j| ≤
        nativeScalarLowRemainderConstant A R R*(W n)^3 := by
  obtain ⟨R,hR,HR⟩:=eventually_actual_minimum_inherited_original_continuum_scalar_remainder
    Bclock Temp G.Cf A G.hT.le G.hCf hA hm hdelta hroom hcl hcu hAz hC0 hCt
  have Hsmall : ∀ᶠn in atTop,R*W n ≤ 1 :=
    ((hWlim.const_mul R).eventually (eventually_le_nhds (by simp : R*(0:ℝ)<1)))
  refine ⟨R,hR,?_⟩
  filter_upwards [hdim.eventually HR,G.source,G.total_root,Hsmall] with n hn hnSource hnRoot hnSmall
  intro before after a ho j V hj hUV hV hbuffer hsize tree start hoa s
  exact hn (M n) hnSource hnRoot.2 before after a ho (W n)
    ((M n).hxs.trans_le (hxs n)).le (hxs n) hnSmall j V hj hUV hV hbuffer hsize tree start hoa s

end OAI.SKFluctuations.LaplaceWindowFormalization
