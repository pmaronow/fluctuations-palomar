module

public import ComparisonSignedCavityActualConstantPendingCategoryEnvelope

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000
variable {dim : ℕ→ℕ}

def ActualConstantSourcePendingCategoryEnvelopeAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (Temp cK C : ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us → ∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      let star:=retainedMassPrefixIndex (w n).star.val as
      let U:=retainedMassPrefixIndex (high n).val as
      ∃hs : star < U,∃hU : U ≤ as.length,
      nativeActualConstantSourceRemainingCategoryEnvelope (M n) hs hU (W n) Temp cK depth ≤
        C*((dim n+1:ℕ):ℝ)^(-(1:ℝ)/6)*(M n).xs^2+
          nativeActualConstantSourcePendingCategoryEnvelope (M n) hs hU (W n) Temp cK depth

theorem actual_constant_pending_category_envelope_along_of_deleted_rates
    {m delta cl cu Az C0 Ct D Bclock Temp cK cFirst cKcut A : ℝ}
    (depth : ℕ) (hcK : 0 < cK)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W radius : ℕ→ℝ) (hW : ∀n,0 < W n)
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) cFirst cKcut A)
    (Hrates : ∀d : ℕ,∃C : ℝ,0 < C ∧ ActualConstantSourceDeletedSiteOnGivenCutsAlong d C M W w high outer) :
    ∃C : ℝ,0 < C ∧ ActualConstantSourcePendingCategoryEnvelopeAlong depth Temp cK C M W w high outer := by
  choose C hC HC using Hrates
  let J:=((List.range depth).map C).sum
  have hJ : 0 ≤ J:=List.sum_nonneg (by
    intro z hz;obtain ⟨j,_,rfl⟩:=List.mem_map.mp hz;exact (hC j).le)
  let Aout:=J/(Real.exp (-4*Temp)*cK)+1
  have hAout : 0 < Aout:=by dsimp only [Aout];positivity
  have HG:=Filter.eventually_all.mpr (fun j : Fin depth=>HC j.val)
  refine ⟨Aout,hAout,?_⟩
  filter_upwards [HG,Hcuts] with n hn hcuts
  intro L us hus hret hmesh hstar hhigh houter
  have Hnet:=Filter.eventually_all.mpr (fun j : Fin depth=>hn j L us hus hret hmesh hstar hhigh houter)
  filter_upwards [Hnet] with jGrid hj
  dsimp only at hj ⊢
  obtain ⟨Hs,HUV,HV,_,_,_,_,_,_,_,_,_,_⟩:=
    hcuts.finite_net_readout us hus hstar hhigh houter jGrid
  have hU:=HUV.le.trans HV
  refine ⟨Hs,hU,?_⟩
  have Hr j (hjd : j < depth) := hj ⟨j,hjd⟩
  have H:=actual_constant_source_remaining_envelope_deleted_site_paid (M n) Hs hU (W n) Temp cK depth
    (hW n) hcK C (by intro j hjd;obtain ⟨_,_,Hj⟩:=Hr j hjd;exact Hj)
  have Hcoef : J/(Real.exp (-4*Temp)*cK) ≤ Aout:=by dsimp only [Aout];linarith
  have Hrate:=mul_le_mul_of_nonneg_right Hcoef
    (show 0 ≤ ((dim n+1:ℕ):ℝ)^(-(1:ℝ)/6)*(M n).xs^2 by positivity)
  apply H.trans
  have H':=add_le_add_left Hrate
    (nativeActualConstantSourcePendingCategoryEnvelope (M n) Hs hU (W n) Temp cK depth)
  calc
    _=J/(Real.exp (-4*Temp)*cK)*(((dim n+1:ℕ):ℝ)^(-(1:ℝ)/6)*(M n).xs^2)+
        nativeActualConstantSourcePendingCategoryEnvelope (M n) Hs hU (W n) Temp cK depth:=by
      dsimp only [J];ring
    _≤Aout*(((dim n+1:ℕ):ℝ)^(-(1:ℝ)/6)*(M n).xs^2)+
        nativeActualConstantSourcePendingCategoryEnvelope (M n) Hs hU (W n) Temp cK depth:=H'
    _=_:=by ring

theorem actual_selected_bad_history_constant_pending_category_envelope_along
    {m delta cl cu Az C0 Ct D Bclock Temp c0 cFirst cKcut cK A : ℝ}
    (depth : ℕ) (Cmass : ℝ) (hCm : 0 ≤ Cmass) (hA : A ≤ Cmass)
    (hcKcut : 0 < cKcut) (hcK : 0 < cK)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0) (hmargin : delta/4 < 3*m-99*delta)
    (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hepsilon : 0 ≤ epsilon) (hTemp : 0 ≤ Temp)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock Temp epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (W radius : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) cFirst cKcut A) :
    ∃C : ℝ,0 < C ∧ ActualConstantSourcePendingCategoryEnvelopeAlong depth Temp cK C M W w high outer := by
  apply actual_constant_pending_category_envelope_along_of_deleted_rates depth hcK M W radius
    (by intro n;rw [hcanonical];exact (M n).canonical_direct_test_band_pos) w high outer Hcuts
  intro d
  exact actual_selected_bad_history_constant_deleted_site_on_given_cuts_along
    d Cmass hCm hA hcKcut hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hmargin hcapmargin
    hdim root M epsilon shell hepsilon hTemp hb hh Hhistory W radius hcanonical hWlim w high outer Hcuts

end OAI.SKFluctuations.Cavity
