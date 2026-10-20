module

public import ComparisonSignedCavityScalarActualHistoryContinuumRemainder
public import ComparisonNativeActualSelectedBadHistoryReadout

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity
set_option maxHeartbeats 16000000

theorem eventually_actual_selected_bad_history_original_continuum_scalar_remainder
    (Bclock Temp A c0 : ℝ) (hT : 0 ≤ Temp) (hA : 0 ≤ A) (hc0 : 0 < c0)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hepsilon : 0 ≤ epsilon)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock Temp epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : NativeOverlapMinimum.ActualSelectedBadHistoryChain c0 root M)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0)) :
    ∃R : ℝ,0 < R ∧ ∀ᶠn : ℕ in atTop,
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
  obtain ⟨ps,Hps⟩:=Hhistory.literal_readout epsilon shell hb hh
  obtain ⟨R,hR,HR⟩:=eventually_actual_cutoff_chain_original_continuum_scalar_remainder
    ps.length Bclock Temp A c0 hT hA hc0 hm hdelta hroom hcl hcu hAz hC0 hCt hmargin hcapmargin
  have Hsmall : ∀ᶠn : ℕ in atTop,R*W n ≤ 1:=by
    have H : Tendsto (fun n=>R*W n) atTop (𝓝 0):=by
      simpa only [mul_zero] using hWlim.const_mul R
    exact H.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  refine ⟨R,hR,?_⟩
  filter_upwards [Hps,hdim.eventually HR,Hsmall] with n hnps hn hsmall
  have H:=hn (M n) (ps.map (fun P=>P n)) hnps.1 (by simp)
    epsilon shell hepsilon hnps.2.1 hnps.2.2
  intro before after a ho j V hj hUV hV hbuffer hsize tree start hoa s
  exact H before after a ho (W n) ((M n).hxs.trans_le (hxs n)).le (hxs n) hsmall
    j V hj hUV hV hbuffer hsize tree start hoa s

end OAI.SKFluctuations.LaplaceWindowFormalization
