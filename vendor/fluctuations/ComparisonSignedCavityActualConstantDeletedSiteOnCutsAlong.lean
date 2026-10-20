module

public import ComparisonSignedCavityActualConstantDeletedSiteFamily
public import ComparisonSignedCavityActualConstantSourceClosedRatesAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000
variable {dim : ℕ→ℕ}

def ActualConstantSourceDeletedSiteOnGivenCutsAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (C : ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us → ∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      let star:=retainedMassPrefixIndex (w n).star.val as
      let U:=retainedMassPrefixIndex (high n).val as
      ∃hs : star < U,∃hU : U ≤ as.length,
      |nativeActualFourOtherCategorySum (M n) U (W n)
        (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth
          (nativeActualConstantSourceChildren (M n) as star U hs hU)) .deletedSite| ≤
        C*((dim n+1:ℕ):ℝ)^(-(1:ℝ)/6)*(W n*(M n).xs^2)

theorem actual_selected_bad_history_constant_deleted_site_on_given_cuts_along
    {m delta cl cu Az C0 Ct D Bclock Temp c0 cFirst cK A : ℝ}
    (depth : ℕ) (Cmass : ℝ) (hCm : 0 ≤ Cmass) (hA : A ≤ Cmass) (hcK : 0 < cK)
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
      (high n) (outer n) (radius n) cFirst cK A) :
    ∃C : ℝ,0 < C ∧ ActualConstantSourceDeletedSiteOnGivenCutsAlong depth C M W w high outer := by
  obtain ⟨C,hC,HR⟩:=actual_selected_bad_history_deleted_site_forest_rate_along
    0 1 3 depth Cmass cK hCm hcK hm hdelta hroom hcl hcu hAz hC0 hCt
    hc0 hmargin hcapmargin dim hdim root M epsilon shell hepsilon hTemp hb hh Hhistory
    W hcanonical hWlim
  have Htotal:=actual_selected_bad_history_total_clock_and_root dim root M epsilon shell hepsilon hb hh Hhistory
  refine ⟨6*C,by positivity,?_⟩
  filter_upwards [HR,Htotal,Hcuts] with n hn ht hcuts
  intro L us hus hret hmesh hstar hhigh houter
  filter_upwards [hn L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  obtain ⟨Hs,HUV,HV,_,Hmass,_,_,_,_,_,_,HK,_⟩:=
    hcuts.finite_net_readout us hus hstar hhigh houter jGrid
  have hU:=HUV.le.trans HV
  refine ⟨Hs,hU,?_⟩
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let U:=retainedMassPrefixIndex (high n).val as
  let rate:=((dim n+1:ℕ):ℝ)^(-(1:ℝ)/6)*(W n*(M n).xs^2)
  have hW : 0 < W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_pos
  have hrate : 0 ≤ rate:=by dsimp only [rate];positivity
  have Hmass':=Hmass.trans (mul_le_mul_of_nonneg_right hA hW.le)
  have Hrow Q (hQ : Q∈nativeActualConstantSourceChildren (M n) as star U Hs hU) :
      |nativeActualFourOtherCategorySum (M n) U (W n)
        (nativeActualMinimumFourCenteredForest (M n) Hs hU (W n) depth [Q]) .deletedSite| ≤
        |Q.term.coefficient| *(C*rate):=by
    have Hvalid:=nativeActualConstantSourceChildren_valid (M n) Hs hU Q hQ
    have Hgen:=nativeActualConstantSourceChildren_generation (M n) Hs hU Q hQ
    have Hleaf:=nativeActualConstantSourceChildren_leaves (M n) Hs hU Q hQ
    have H:=hj U 0 star [] Q (by simp) Hgen Hleaf Hvalid (Nat.zero_le star) Hs hU
      (M n).xs le_rfl (by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale)
      (by simp only [partitionPoint,partitionValues_zero,id_eq];exact mul_nonneg hCm (M n).hxs.le)
      Hmass' HK
    simp only [nativeResourceScale,List.map_nil,List.prod_nil,mul_one] at H
    exact H.trans_eq (by dsimp only [rate];ring)
  have H:=actual_constant_deleted_site_category_family_abs_le (M n) ht.1
    (finiteCutMasses_ordered us hus jGrid) Hs hU (W n) (C*rate) depth
    (mul_nonneg hC.le hrate) Hrow
  exact H.trans_eq (by dsimp only [rate];ring)

end OAI.SKFluctuations.Cavity
