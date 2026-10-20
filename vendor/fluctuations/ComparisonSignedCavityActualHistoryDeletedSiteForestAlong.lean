module

public import ComparisonSignedCavityInheritedDeletedSiteForestRate
public import ComparisonNativeActualSelectedBadHistorySourceClocks

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000

theorem actual_selected_bad_history_deleted_site_forest_rate_along
    (seedBound k₀ r₀ depth : ℕ) (Cmass cK : ℝ) (hCm : 0 ≤ Cmass) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D Bclock Temp c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0) (hmargin : delta/4 < 3*m-99*delta)
    (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hepsilon : 0 ≤ epsilon) (hTemp : 0 ≤ Temp)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock Temp epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0)) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(U i star : ℕ) (seed : List NativeResourceMark)
          (st : NativeActualResourceState (Spin (dim n)×Bool) as i star),
          seed.length ≤ seedBound → st.generation=k₀ → st.tree.leaves ≤ r₀ →
          NativeActualResourceGenerated i star U seed st.generation st.tree st.term → i ≤ star →
        ∀(hs : star < U) (hU : U ≤ as.length),
        ∀x : ℝ,(M n).xs ≤ x → x ≤ W n →
          partitionPoint 0 as i ≤ Cmass*x → partitionPoint 0 as star ≤ Cmass*W n →
          cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as star →
          |nativeActualFourOtherCategorySum (M n) U (W n)
            (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth [st]) .deletedSite| ≤
            C*|st.term.coefficient| *((dim n+1:ℕ):ℝ)^(-(1:ℝ)/6)*(W n*(M n).xs^2)*
              nativeResourceScale x (W n) 1 seed := by
  obtain ⟨Cf,hCf,Hsource⟩:=actual_selected_bad_history_small_source_clocks
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim root M
    epsilon shell hepsilon hTemp hb hh Hhistory
  obtain ⟨C,hC,HR⟩:=eventually_actual_minimum_inherited_deleted_site_forest_rate
    (D:=D) seedBound k₀ r₀ depth Bclock Temp Cf Cmass cK hTemp hCf hCm hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1))
  refine ⟨C,hC,?_⟩
  filter_upwards [hdim.eventually HR,Hsource,HW] with n hn hs hw
  have hxs1 : (M n).xs ≤ 1:=by
    have H : (M n).xs ≤ W n:=by rw [hcanonical];exact le_max_left _ _
    exact H.trans hw
  intro L us hus hret hmesh
  filter_upwards [hn (M n) hs hxs1 L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro U i star seed st hseed hgen hleaf hP hi hs hU x hx hxW hmi hms HK
  exact hj U i star seed st hseed hgen hleaf hP hi hs hU x (W n) hx hxW hmi hms HK

end OAI.SKFluctuations.Cavity
