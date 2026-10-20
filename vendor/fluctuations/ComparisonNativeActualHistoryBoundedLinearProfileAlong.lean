module

public import ComparisonNativeActualHistoryBoundedVirtualGapFactoryAlong
public import ComparisonNativeActualLocalScalarLimitGlobalRigidity

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar Cavity NativeOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 22000000

theorem exists_actual_selected_bad_history_bounded_linear_profile_along
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
      (M n).xs^2 ≤ K) :
    ∃phi : ℕ→ℕ,StrictMono phi ∧
      ∃htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M (phi n)).h u+(M (phi n)).b u ≤ T,
        ∃d : ActualInheritedLocalScalarLimitData
          (hTemp.trans_le (sub_le_self T hepsilon)) (T-epsilon)
          (fun n=>M (phi n)) htotal,
          let kappa := ((T-epsilon)/T)*scalarInitialDensityConstant
            (hTemp.trans_le (sub_le_self T hepsilon)) d.beta
          (∀t>0,d.U.mass t=kappa*t) ∧ (∀t>0,d.V.mass t=kappa*t) ∧
            cl ≤ kappa ∧ kappa ≤ cu := by
  obtain ⟨phi,hphi,htotal,d,Hvirtual⟩ :=
    exists_actual_selected_bad_history_bounded_joint_scalar_limit_with_virtual_gaps_along K hK
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim root M epsilon shell hepsilon hshell hTemp hb hh Hhistory W hcanonical hWlim
      hcompare hwork
  have Hcan : Tendsto (fun n=>(M (phi n)).canonicalDirectTestBandScale) atTop (𝓝 0) := by
    have H := hWlim.comp hphi.tendsto_atTop
    simpa only [Function.comp_def,hcanonical] using H
  have Hlinear := d.global_profile_rigidity_of_actual_history
    hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hc01 hmargin hcapmargin hgapmargin
    (hdim.comp hphi.tendsto_atTop) (fun n=>root (phi n)) Hcan shell hepsilon hshell hTemp
    (hphi.tendsto_atTop.eventually hb) (hphi.tendsto_atTop.eventually hh)
    (Hhistory.comp phi hphi.tendsto_atTop) Hvirtual
  refine ⟨phi,hphi,htotal,d,Hlinear.1,Hlinear.2,?_⟩
  have hx : Tendsto (fun n=>(M (phi n)).xs) atTop (𝓝 0) :=
    squeeze_zero (fun n=>(M (phi n)).hxs.le)
      (fun n=>(M (phi n)).canonical_direct_test_band_ge_scale) Hcan
  let t := max Az 1
  have ht : 0 < t := zero_lt_one.trans_le (le_max_right _ _)
  have Hgrowth := d.radius_outer_growth hAz hx t (le_max_left _ _)
  rw [Hlinear.2 t ht] at Hgrowth
  exact ⟨le_of_mul_le_mul_right Hgrowth.1 ht,le_of_mul_le_mul_right Hgrowth.2 ht⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
