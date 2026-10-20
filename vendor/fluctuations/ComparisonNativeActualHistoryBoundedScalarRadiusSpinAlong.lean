module

public import ComparisonNativeActualHistoryBoundedScalarStrengthSpinAlong
public import ComparisonNativeActualRadiusSpinProfileCompactness

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar Cavity NativeOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 22000000

theorem exists_actual_selected_bad_history_bounded_scalar_strength_radius_spin_limit_along
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
      ∀t : ℝ,Tendsto (fun n=>orderedPathS (dim (phi n)+1)
        (M (phi n)).bf (M (phi n)).hf
          ((M (phi n)).alpha.val.val ((M (phi n)).xs*t))/(M (phi n)).xs)
        atTop (𝓝 (s.mass t)) := by
  obtain ⟨theta,htheta,htotal,⟨d⟩,L,A,_B,_smass,hL,hA,_hB,HL,HA,Hpositive,_Hbound,_Hs⟩ :=
    exists_actual_selected_bad_history_bounded_scalar_strength_spin_limit_along K hK
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim root M epsilon shell hepsilon hshell hTemp hb hh Hhistory W hcanonical hWlim
      hcompare hwork
  have hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>(M n).hxs.le) _ hWlim
    intro n
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  obtain ⟨s,B,psi,hB,hpsi,Hsbound,Hs⟩ := exists_actual_rescaled_radius_spin_profile_limit
    hm hdelta hroom hcl hcu hAz hC0 hCt (fun n=>dim (theta n))
    (hdim.comp htheta.tendsto_atTop) (fun n=>M (theta n)) (hx.comp htheta.tendsto_atTop)
  refine ⟨theta ∘ psi,htheta.comp hpsi,fun n=>htotal (psi n),⟨d.comp psi hpsi⟩,
    L,A,B,s,hL,hA,hB,?_,?_,Hpositive,Hsbound,Hs⟩
  · intro t
    exact (HL t).comp hpsi.tendsto_atTop
  · intro t
    exact (HA t).comp hpsi.tendsto_atTop

end OAI.SKFluctuations.LaplaceWindowFormalization
