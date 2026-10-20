module

public import ComparisonNativeActualGeneralHistoryContext

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity
open scoped Topology NNReal
namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ} {dim : ℕ→ℕ}

structure NativeActualCavityClockContext
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (T : ℝ) where
  hT : 0 < T
  xs_zero : Tendsto (fun n=>(M n).xs) atTop (𝓝 0)
  pullback : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1
  total_root : ∀ᶠn in atTop,(∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T) ∧ (M n).h 0=0
  Cf : ℝ
  hCf : 0 ≤ Cf
  source : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf

namespace NativeActualCavityClockContext
variable {M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}

def comp (G : NativeActualCavityClockContext M T) (phi : ℕ→ℕ) (hphi : Tendsto phi atTop atTop) :
    NativeActualCavityClockContext (fun n=>M (phi n)) T where
  hT:=G.hT
  xs_zero:=G.xs_zero.comp hphi
  pullback:=hphi.eventually G.pullback
  total_root:=hphi.eventually G.total_root
  Cf:=G.Cf
  hCf:=G.hCf
  source:=hphi.eventually G.source

end NativeActualCavityClockContext

theorem ActualNativeProfileHistory.exists_cavity_clock_context
    {M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    (G : ActualNativeProfileHistory M T c0)
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hdim : Tendsto dim atTop atTop) :
    Nonempty (NativeActualCavityClockContext M T) := by
  obtain ⟨Cf,hCf,Hsource⟩:=G.small_source hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin hdim
  exact ⟨⟨G.hT,G.xs_zero,G.pullback,G.total_root,Cf,hCf,Hsource⟩⟩

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
