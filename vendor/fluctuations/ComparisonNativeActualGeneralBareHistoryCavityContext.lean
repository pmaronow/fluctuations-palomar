module

public import ComparisonNativeActualGeneralBareHistorySource
public import ComparisonNativeActualGeneralBareHistoryRegularity
public import ComparisonNativeActualCavityClockContext

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity
open scoped Topology NNReal
namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock c0 T Cbase : ℝ} {dim : ℕ→ℕ}

theorem ActualWeakSelectedHistoryChain.exists_general_bare_cavity_clock_context
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hc0 : 0 < c0) (hT : 0 < T) (hCbase : 0 ≤ Cbase)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hdim : Tendsto dim atTop atTop)
    {root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    (H : ActualWeakSelectedHistoryChain c0 root M)
    (Hroot : ∀ᶠn in atTop,(∀u∈Icc (0:ℝ) 1,(root n).h u+(root n).b u ≤ T) ∧
      (root n).h 0=0)
    (Hfield : ∀ᶠn in atTop,∀u∈Icc (0:ℝ) 1,
      (root n).h u ≤ Cbase*(comparisonLowerScale (root n).context.N
        (root n).context.E (root n).context.d+u))
    (Hbare : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val
      (root n).b (root n).h 0 1)
    (hxs : Tendsto (fun n=>(M n).xs) atTop (𝓝 0)) :
    Nonempty (NativeActualCavityClockContext M T) := by
  obtain ⟨Cf,hCf,Hsource⟩:=actual_weak_general_bare_history_small_source_clocks
    hm hdelta hcl hAz hC0 hc0 hT.le hCbase hmargin hcapmargin hdim root M H Hroot Hfield
  exact ⟨⟨hT,hxs,H.pullback_general_bare Hbare,H.total_root_general_bare Hroot,Cf,hCf,Hsource⟩⟩

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
