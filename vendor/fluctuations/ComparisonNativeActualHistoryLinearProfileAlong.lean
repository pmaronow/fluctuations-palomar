module

public import ComparisonNativeActualHistoryBoundedLinearProfileAlong
public import ComparisonNativeActualHistoryHighLinearProfileAlong
public import ComparisonNonnegativeSequenceDichotomy

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar Cavity NativeOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 22000000

theorem exists_actual_selected_bad_history_linear_profile_along
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
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
 :
    ∃phi : ℕ→ℕ,StrictMono phi ∧
      ∃htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M (phi n)).h u+(M (phi n)).b u ≤ T,
        ∃d : ActualInheritedLocalScalarLimitData
          (hTemp.trans_le (sub_le_self T hepsilon)) (T-epsilon)
          (fun n=>M (phi n)) htotal,
          let kappa := ((T-epsilon)/T)*scalarInitialDensityConstant
            (hTemp.trans_le (sub_le_self T hepsilon)) d.beta
          (∀t>0,d.U.mass t=kappa*t) ∧ (∀t>0,d.V.mass t=kappa*t) ∧
            cl ≤ kappa ∧ kappa ≤ cu := by
  let strength := fun n=>laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/(M n).xs^2
  have hstrength : ∀n,0 ≤ strength n := fun n=>
    div_nonneg (laplaceComparisonStrength_nonneg (M n).context.d (M n).xs (M n).hlam.le)
      (sq_nonneg _)
  rcases nonnegative_sequence_bounded_or_divergent_subsequence strength hstrength with Hbound | Hlarge
  · obtain ⟨theta,htheta,K,hK,Hwork⟩ := Hbound
    obtain ⟨psi,hpsi,htotal,Hlimit⟩ :=
      exists_actual_selected_bad_history_bounded_linear_profile_along K hK
        hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
        (fun n=>dim (theta n)) (hdim.comp htheta.tendsto_atTop)
        (fun n=>root (theta n)) (fun n=>M (theta n)) epsilon shell hepsilon hshell hTemp
        (htheta.tendsto_atTop.eventually hb) (htheta.tendsto_atTop.eventually hh)
        (Hhistory.comp theta htheta.tendsto_atTop) (fun n=>W (theta n))
        (fun n=>hcanonical (theta n)) (hWlim.comp htheta.tendsto_atTop)
        (fun n=>hcompare (theta n)) (Eventually.of_forall Hwork)
    exact ⟨theta ∘ psi,htheta.comp hpsi,htotal,Hlimit⟩
  · obtain ⟨theta,htheta,Hwork⟩ := Hlarge
    obtain ⟨psi,hpsi,htotal,Hlimit⟩ :=
      exists_actual_selected_bad_history_high_linear_profile_along
        hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
        (fun n=>dim (theta n)) (hdim.comp htheta.tendsto_atTop)
        (fun n=>root (theta n)) (fun n=>M (theta n)) epsilon shell hepsilon hshell hTemp
        (htheta.tendsto_atTop.eventually hb) (htheta.tendsto_atTop.eventually hh)
        (Hhistory.comp theta htheta.tendsto_atTop) (fun n=>W (theta n))
        (fun n=>hcanonical (theta n)) (hWlim.comp htheta.tendsto_atTop)
        (fun n=>hcompare (theta n)) Hwork
    exact ⟨theta ∘ psi,htheta.comp hpsi,htotal,Hlimit⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
