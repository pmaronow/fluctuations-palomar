module

public import ComparisonNativeActualHistoryBoundedScalarRadiusSpinAlong
public import ComparisonNativeActualBoundedGradientL1Along

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar Cavity NativeOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 22000000

def ActualBoundedRadiusGradientLimit
    {m delta cl cu Az C0 Ct D Bclock : ℝ} {dim : ℕ→ℕ}
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (L A : ℝ) (s : NonnegativeMassProfile) : Prop :=
  ∀c C a b : ℝ,0 < c → 0 < a → a ≤ b →
    (∀ᶠn in atTop,∀t∈Icc a b,
      c*(M n).xs ≤ (M n).alpha.val.val ((M n).xs*t) ∧
      (M n).alpha.val.val ((M n).xs*t) ≤ C*(M n).xs) →
    (∀ᶠn in atTop,IntegrableOn (M n).actualVirtualScaledGradient (Icc a b)) ∧
    Tendsto (fun n=>∫t in Icc a b,|(M n).actualVirtualScaledGradient t-
      comparisonScaledStationarity (L*laplaceComparisonShape (A*t))
        (laplaceComparisonSlope (A*t)) t (s.mass t)|) atTop (𝓝 0)

theorem exists_actual_selected_bad_history_bounded_radius_gradient_limit_along
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (K : ℝ) (hK : 0 ≤ K)
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
    (hwork : ∀ᶠn in atTop,laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/
      (M n).xs^2 ≤ K)
 :
    ∃phi : ℕ→ℕ,StrictMono phi ∧
      ∃htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M (phi n)).h u+(M (phi n)).b u ≤ T,
      Nonempty (ActualInheritedLocalScalarLimitData
        (hTemp.trans_le (sub_le_self T hepsilon)) (T-epsilon)
        (fun n=>M (phi n)) htotal) ∧
      ∃(L A B : ℝ) (s : NonnegativeMassProfile),
      L∈Icc (1/Ccal^2) (K+1) ∧ A∈Icc (0:ℝ) Ccal ∧ 0 < B ∧
      (∀t : ℝ,Tendsto (fun n=>laplaceComparisonStrength (M (phi n)).context.d
        (M (phi n)).lam ((M (phi n)).xs*t)/(M (phi n)).xs^2)
        atTop (𝓝 (L*laplaceComparisonShape (A*t)))) ∧
      (∀t : ℝ,Tendsto (fun n=>comparisonLogSlope
        (laplaceComparisonStrength (M (phi n)).context.d (M (phi n)).lam)
        ((M (phi n)).xs*t)) atTop (𝓝 (laplaceComparisonSlope (A*t)))) ∧
      (∀t : ℝ,0 < L*laplaceComparisonShape (A*t) ∧ laplaceComparisonSlope (A*t)∈Ico (0:ℝ) 1) ∧
      (∀t : ℝ,0 ≤ t → s.mass t ≤ B*(1+cu*(t+Az))) ∧
      (∀t : ℝ,Tendsto (fun n=>orderedPathS (dim (phi n)+1)
        (M (phi n)).bf (M (phi n)).hf
          ((M (phi n)).alpha.val.val ((M (phi n)).xs*t))/(M (phi n)).xs)
        atTop (𝓝 (s.mass t))) ∧
      ActualBoundedRadiusGradientLimit (fun n=>M (phi n)) L A s := by
  obtain ⟨phi,hphi,htotal,hd,L,A,B,s,hL,hA,hB,HL,HA,Hpositive,Hbound,Hs⟩ :=
    exists_actual_selected_bad_history_bounded_scalar_strength_radius_spin_limit_along K hK
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim root M epsilon shell hepsilon hshell hTemp hb hh Hhistory W hcanonical hWlim
      hcompare hwork
  refine ⟨phi,hphi,htotal,hd,L,A,B,s,hL,hA,hB,HL,HA,Hpositive,Hbound,Hs,?_⟩
  have hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>(M n).hxs.le) _ hWlim
    intro n
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  intro c C a b hc ha hab hmass
  have hxphi:=hx.comp hphi.tendsto_atTop
  refine ⟨?_,?_⟩
  · have H : Tendsto (fun n=>(M (phi n)).xs*b) atTop (𝓝 0) := by
      simpa only [zero_mul,Function.comp_apply] using hxphi.mul_const b
    filter_upwards [H.eventually (eventually_le_nhds zero_lt_one)] with n hn
    exact (M (phi n)).actual_scaled_gradient_integrable ha hn
  · exact actual_selected_bad_history_bounded_radius_gradient_L1_along Bclock
      hm hdelta (by linarith) hcl hcu hAz hC0 hCt hc ha hab hK
      (fun n=>dim (phi n)) (hdim.comp hphi.tendsto_atTop)
      (fun n=>root (phi n)) (fun n=>M (phi n)) hxphi
      epsilon shell hshell (hphi.tendsto_atTop.eventually hb) (hphi.tendsto_atTop.eventually hh)
      (Hhistory.comp phi hphi.tendsto_atTop) (hphi.tendsto_atTop.eventually hwork) hmass s
      (fun t _=>HL t) (fun t _=>HA t) (fun t _=>Hs t)

end OAI.SKFluctuations.LaplaceWindowFormalization
