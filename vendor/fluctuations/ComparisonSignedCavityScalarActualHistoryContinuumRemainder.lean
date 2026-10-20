module

public import ComparisonSignedCavityScalarInheritedContinuumRemainder
public import ComparisonNativeActualHistoryCutoffSourceClocks

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity
set_option maxHeartbeats 12000000

theorem eventually_actual_cutoff_chain_original_continuum_scalar_remainder
    (depth : ℕ) (Bclock Temp A c0 : ℝ) (hT : 0 ≤ Temp) (hA : 0 ≤ A) (hc0 : 0 < c0)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m) :
    ∃R : ℝ,0 < R ∧ ∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (ps : List (NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)),
        NativeOverlapMinimum.ActualHistoryCutoffChain c0 ps M → ps.length ≤ depth →
      ∀epsilon shell : ℝ,0 ≤ epsilon →
        (∀u,M.b u=historyMatrixClock Temp epsilon shell (ps.map (fun P=>P.toHistoryTerm)) u) →
        (∀u,M.h u=historyFieldClock (ps.map (fun P=>P.toHistoryTerm)) u) →
      ∀(before after : List PositiveMass) (a : PositiveMass),
        MassOrdered 0 (before++a::after) →
      ∀W : ℝ,0 ≤ W → M.xs ≤ W → R*W ≤ 1 →
      ∀j V : ℕ,j < before.length+1 → before.length+1 ≤ V →
        V ≤ (before++a::after).length →
        a.val < partitionPoint 0 (before++a::after) V →
        partitionPoint 0 (before++a::after) V ≤ A*W →
      ∀(tree : ClockTree (Spin n×Bool) (before++a::after))
        (start : ℝ) (_hoa : MassOrdered start (before++a::after)) (s : tree.Slot),
      let K:=nativeContinuumMixedClock n M.bf M.hf (before++a::after)
      let chi:=((tree.markedAttach start).map (fun p=>p.coeff*
        fullScalarCutGamma p.tree (before.length+1) K (p.embed s) p.mark)).sum
      |nativeOriginalScalarPairMean (before++a::after) K j-chi^2*K j| ≤
        nativeScalarLowRemainderConstant A R R*W^3 := by
  let Cf:=(Az*max 1 (D^2/c0))*(depth:ℝ)+Temp/cl+
    NativeOverlapMinimum.bareSourceClockConstant cl Az D
  have hCf : 0 ≤ Cf:=by
    have H:=NativeOverlapMinimum.bare_source_clock_constant_nonneg (D:=D) hcl hAz
    dsimp only [Cf]
    positivity
  obtain ⟨R,hR,HR⟩:=eventually_actual_minimum_inherited_original_continuum_scalar_remainder
    Bclock Temp Cf A hT hCf hA hm hdelta hroom hcl hcu hAz hC0 hCt
  have HC:=NativeOverlapMinimum.eventually_actual_shell_history_cutoff_source_clock_bounds
    (cu:=cu) (Ct:=Ct) (D:=D) (Bclock:=Bclock)
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin depth hT
  refine ⟨R,hR,?_⟩
  filter_upwards [HR,HC] with n hn hc
  intro M ps hchain hdepth epsilon shell hepsilon hb hh
  have HS : NativeActualSmallSourceClocks M Temp Cf:=by
    intro u hu
    have H:=hc M ps hchain hdepth epsilon shell hepsilon hb hh u hu
    exact ⟨H.2.1,H.2.2.2⟩
  have hroot : M.h 0=0:=(M.actual_shell_history_total_root ps hepsilon hb hh).2
  exact hn M HS hroot

end OAI.SKFluctuations.LaplaceWindowFormalization
