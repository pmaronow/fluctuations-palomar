module

public import ComparisonNativeActualSelectedBadHistoryReadout
public import ComparisonNativeActualHistoryCutoffSourceClocks
public import ComparisonSignedCavityInheritedCanonicalSourceMoments

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity
set_option maxHeartbeats 10000000
namespace NativeOverlapMinimum

theorem actual_selected_bad_history_small_source_clocks
    {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hepsilon : 0 ≤ epsilon) (hT : 0 ≤ T)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock T epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M) :
    ∃Cf : ℝ,0 ≤ Cf ∧ ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf := by
  obtain ⟨ps,Hps⟩:=Hhistory.literal_readout epsilon shell hb hh
  let Cf:=(Az*max 1 (D^2/c0))*(ps.length:ℝ)+T/cl+bareSourceClockConstant cl Az D
  have hCf : 0 ≤ Cf := by
    have H:=bare_source_clock_constant_nonneg (D:=D) hcl hAz
    dsimp only [Cf]
    positivity
  have HC:=eventually_actual_shell_history_cutoff_source_clock_bounds
    (cu:=cu) (Ct:=Ct) (D:=D) (Bclock:=Bclock)
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin ps.length hT
  refine ⟨Cf,hCf,?_⟩
  filter_upwards [Hps,hdim.eventually HC] with n hn hc
  intro u hu
  have H:=hc (M n) (ps.map (fun P=>P n)) hn.1 (by simp)
    epsilon shell hepsilon hn.2.1 hn.2.2 u hu
  exact ⟨H.2.1,H.2.2.2⟩

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
