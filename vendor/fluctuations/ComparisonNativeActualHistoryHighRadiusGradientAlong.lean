module

public import ComparisonNativeActualHistoryHighRadiusIdentificationAlong
public import ComparisonNativeActualScaledRadiusIntegrability
public import ComparisonNativeActualHistoryRadiusScalarIntervalAlong
public import ComparisonNativeActualHighFlatRadiusGradient

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy NativeOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 20000000

theorem actual_selected_bad_history_high_radius_gradient_L1_along
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (c C a b : ℝ) (hc : 0 < c) (hC : 0 < C) (ha : 0 ≤ a) (hab : a < b)
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
    (hmass : ∀ᶠn in atTop,∀t∈Icc a b,
      c*(M n).xs ≤ (M n).alpha.val.val ((M n).xs*t) ∧
        (M n).alpha.val.val ((M n).xs*t) ≤ C*(M n).xs)
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/
      (M n).xs^2) atTop atTop)
    (g : ℝ→ℝ)
    (hG : ∀Q > 0,TendstoUniformlyOn (fun n=>comparisonRescaledScalarResponse
      (scalarCovarianceResponse (hTemp.trans_le (sub_le_self T hepsilon))
        ((M n).inheritedScalarMassProfile (hTemp.trans_le (sub_le_self T hepsilon)) (htotal n)))
      (T-epsilon) (M n).xs) g atTop (Icc (0:ℝ) Q))
    (hg : ∀Q > 0,ContinuousOn g (Icc (0:ℝ) Q)) :
    (∀ᶠn in atTop,IntegrableOn (M n).actualVirtualScaledGradient (Icc a b)) ∧
    Tendsto (fun n=>∫t in Icc a b,
      |(M n).actualVirtualScaledGradient t-(-2*(T-epsilon)*g t)|) atTop (𝓝 0) := by
  let Gamma := fun n=>scalarCovarianceResponse (hTemp.trans_le (sub_le_self T hepsilon))
    ((M n).inheritedScalarMassProfile (hTemp.trans_le (sub_le_self T hepsilon)) (htotal n))
  let S := fun n t=>orderedPathS (dim n+1) (M n).bf (M n).hf
    ((M n).alpha.val.val ((M n).xs*t))
  let K := fun n t=>actualMixedClock (dim n+1) (M n).bf (M n).hf
    ((M n).alpha.val.val ((M n).xs*t))
  let P := fun n t=>comparisonRescaledScalarResponse (Gamma n) (T-epsilon) (M n).xs
    (K n t/((T-epsilon)*(M n).xs))
  let rho := fun n t=>(S n t-Gamma n (K n t))/(M n).xs^3
  let zeta := fun n t=>
    (((M n).b ((M n).alpha.val.val ((M n).xs*t))-(T-epsilon))*S n t+
      (M n).h ((M n).alpha.val.val ((M n).xs*t)))/(M n).xs^3
  obtain ⟨_Hspin,_Hclock,HP,Hz⟩ := actual_selected_bad_history_high_radius_uniform_identification_along
    c C a b hc hC ha hab hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01
    hmargin hcapmargin hgapmargin dim hdim root M epsilon shell hepsilon hshell hTemp hb hh
    Hhistory W hcanonical hWlim hcompare htotal hmass hlarge g hG hg
  have Hr := actual_selected_bad_history_compact_radius_cavity_L1_along
    c C a b hc hC ha hab hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01
    hmargin hcapmargin hgapmargin dim hdim root M epsilon shell hepsilon hshell hTemp hb hh
    Hhistory W hcanonical hWlim hcompare htotal hmass
  have Hi n := (M n).actual_scaled_radius_scalar_integrability
    (hTemp.trans_le (sub_le_self T hepsilon)) hTemp
    ((M n).inheritedScalarMassProfile (hTemp.trans_le (sub_le_self T hepsilon)) (htotal n)) a b
  have hPi n : IntegrableOn (P n) (Icc a b) := (Hi n).2.2.2.1
  have hri n : IntegrableOn (rho n) (Icc a b) := (Hi n).2.2.1
  have hzi n : IntegrableOn (zeta n) (Icc a b) := (Hi n).2.2.2.2
  have hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>(M n).hxs.le) _ hWlim
    intro n
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have Hclosure := eventually_actual_high_flat_radius_gradient_closure
    dim M hx hlarge a b ha hab Gamma (T-epsilon) hTemp
  have Heq : ∀ᶠn in atTop,∀t∈Icc a b,(M n).actualVirtualScaledGradient t=
      -2*(T-epsilon)*(P n t+rho n t)-2*zeta n t := by
    filter_upwards [Hclosure] with n hn t ht
    simpa only [P,rho,zeta,S,K,mul_div_assoc] using (hn t ht).2
  have Hfi : ∀ᶠn in atTop,IntegrableOn (M n).actualVirtualScaledGradient (Icc a b) := by
    filter_upwards [Heq] with n hn
    apply (((hPi n).add (hri n)).const_mul (-2*(T-epsilon))).sub ((hzi n).const_mul 2) |>.congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (hn t ht).symm
  refine ⟨Hfi,?_⟩
  have hgi : IntegrableOn g (Icc a b) :=
    ((hg b (ha.trans_lt hab)).mono (fun t ht=>⟨ha.trans ht.1,ht.2⟩)).integrableOn_Icc
  exact comparison_scalar_density_eventual_L1_tendsto (fun n=>(M n).actualVirtualScaledGradient)
    P rho zeta g (T-epsilon) a b Hfi hPi hri hzi hgi Heq HP Hr Hz

end OAI.SKFluctuations.LaplaceWindowFormalization
