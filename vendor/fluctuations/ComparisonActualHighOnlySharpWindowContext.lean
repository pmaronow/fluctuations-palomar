module

public import ComparisonActualHighOnlySharpWindowProducer

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter Hierarchy NativeOverlapMinimum ActualHighOnlyOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 12000000

theorem exists_actual_comparable_context_sharp_window_sequence_later_half_high_only
    {m delta cl cu Az C0 Ct D Bclock T L Ctest : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCtest : 0 ≤ Ctest) (hL : 0 < L)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : HighOnlyActualComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ctest*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    ∃Cs : ℝ,0 < Cs ∧ ∃w : ℕ→ActualSlowWindowChoice,
      (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow_high_only (M n) (W n) T L Cs (w n)) ∧
      ∀ᶠn in atTop,(calibratedBandStart cu Az+2*L)*W n < (w n).star.val := by
  exact exists_actual_high_only_sharp_window_sequence_later_half hm hdelta hroom
    hcl hcu hAz hC0 hCt hCtest G.hT hL dim hdim M G W hcanonical hWlim hcompare

theorem exists_actual_comparable_context_sharp_window_sequence_high_only
    {m delta cl cu Az C0 Ct D Bclock T L Ctest : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCtest : 0 ≤ Ctest) (hL : 0 < L)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : HighOnlyActualComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ctest*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    ∃Cs : ℝ,0 < Cs ∧ ∃w : ℕ→ActualSlowWindowChoice,
      ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow_high_only (M n) (W n) T L Cs (w n) := by
  obtain ⟨Cs,hCs,w,hw,_⟩:=exists_actual_comparable_context_sharp_window_sequence_later_half_high_only
    hm hdelta hroom hcl hcu hAz hC0 hCt hCtest hL dim hdim M G W hcanonical hWlim hcompare
  exact ⟨Cs,hCs,w,hw⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
