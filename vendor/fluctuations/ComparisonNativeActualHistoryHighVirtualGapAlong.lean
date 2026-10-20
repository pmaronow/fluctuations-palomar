module

public import ComparisonNativeActualHistoryHighGradientUniformAlong
public import ComparisonNativeActualVirtualGapExistenceAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy NativeOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 20000000

theorem actual_selected_bad_history_high_virtual_gap_data_along
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    {a b B : ℝ} (ha : 0 ≤ a) (hab : a < b) (hbB : b < B)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hepsilon : 0 ≤ epsilon) (hshell : 0 < shell) (hTemp : 0 < T-epsilon)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock T epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/
      (M n).xs^2) atTop atTop)
    (g : ℝ→ℝ)
    (hG : ∀Q > 0,TendstoUniformlyOn (fun n=>comparisonRescaledScalarResponse
      (scalarCovarianceResponse (hTemp.trans_le (sub_le_self T hepsilon))
        ((M n).inheritedScalarMassProfile (hTemp.trans_le (sub_le_self T hepsilon)) (htotal n)))
      (T-epsilon) (M n).xs) g atTop (Icc (0:ℝ) Q))
    (hg : ∀Q > 0,ContinuousOn g (Icc (0:ℝ) Q))
    (V : ℝ→ℝ) (hV : Monotone V) (hnegative : ∀t<0,V t=0)
    (hCDF : ∀s,Tendsto (fun n=>(M n).alpha.val.val ((M n).xs*s)/(M n).xs) atTop (𝓝 (V s)))
    (hasupport : a∈comparisonIncrementSupport V) (hbsupport : b∈comparisonIncrementSupport V)
    (hgap : ∀r∈Ioo a b,r∉comparisonIncrementSupport V) :
    Nonempty (ComparisonVirtualGapData g a b) := by
  have hmass : 0 < V ((a+b)/2) := comparison_increment_support_positive_cdf_after
    hV hnegative hasupport (by linarith)
  let c := V ((a+b)/2)/2
  let C := V ((a+b)/2)+1
  have hc : 0 < c := half_pos hmass
  have hC : 0 < C := by dsimp only [C];linarith
  have hB : 0 < B := (ha.trans_lt hab).trans hbB
  have hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>(M n).hxs.le) _ hWlim
    intro n
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  obtain ⟨KG,hKG,Hgradient⟩ := eventually_actual_history_high_gradient_uniform_above_mass_along
    c B hc hB hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01
    hmargin hcapmargin hgapmargin dim hdim root M epsilon shell hepsilon hshell hTemp hb hh
    Hhistory W hcanonical hWlim hcompare htotal hlarge g hG hg
  let f := fun t=>-2*(T-epsilon)*g t
  have hf : IntegrableOn f (Icc a b) :=
    (((hg b (ha.trans_lt hab)).mono (fun t ht=>⟨ha.trans ht.1,ht.2⟩)).integrableOn_Icc).const_mul _
  have Hlocal : ∀s∈Ioo a b,∀t∈Ioo a b,s ≤ t →
      Tendsto (fun n=>∫r in Icc s t,|(M n).actualVirtualScaledGradient r-f r|) atTop (𝓝 0) := by
    intro s hs t ht hst
    rcases hst.eq_or_lt with rfl|hst
    · simp
    have Hmass := actual_compact_gap_mass_band_along dim M V hV hCDF hab hgap hmass hs ht
    exact (actual_selected_bad_history_high_radius_gradient_L1_along
      c C s t hc hC (ha.trans hs.1.le) hst hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01
      hmargin hcapmargin hgapmargin dim hdim root M epsilon shell hepsilon hshell hTemp hb hh
      Hhistory W hcanonical hWlim hcompare htotal Hmass hlarge g hG hg).2
  obtain ⟨K,hK,j,hj,hjbound,⟨P⟩⟩ := actual_virtual_gap_primitive_of_gradient_limit_along
    hdelta hcu.le hAz hC0 (by linarith) dim hdim M hx V hV hCDF ha hab hbB
    hasupport hbsupport hgap hmass f hf ⟨KG,hKG.le,Hgradient⟩ Hlocal
  refine ⟨P.toGap (Or.inl ?_)⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have hjpos : 0 < j t :=
    (div_pos zero_lt_one (sq_pos_of_pos (zero_lt_one.trans_le hK))).trans_le
      (hjbound t ⟨ht.1.le,ht.2.le⟩).1
  dsimp only [f]
  constructor
  · intro hgt
    exact mul_neg_of_pos_of_neg hjpos (mul_neg_of_neg_of_pos (by linarith) hgt)
  · intro hgt
    exact mul_pos hjpos (mul_pos_of_neg_of_neg (by linarith) hgt)

end OAI.SKFluctuations.LaplaceWindowFormalization
