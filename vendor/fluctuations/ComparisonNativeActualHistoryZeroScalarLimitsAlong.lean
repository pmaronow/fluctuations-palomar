module

public import ComparisonNativeActualHistoryLinearProfileAlong
public import ComparisonNativeActualLocalScalarLimitZeroPrimitives

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar Cavity NativeOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 16000000

theorem exists_actual_selected_bad_history_linear_profile_with_zero_scalar_limits_along
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1 : ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n : ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hepsilon : 0 ≤ epsilon) (hshell : 0 < shell) (hTemp : 0 < T-epsilon)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock T epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    ∃phi : ℕ → ℕ,StrictMono phi ∧
      ∃htotal : ∀n,∀u∈Icc (0 : ℝ) 1,(M (phi n)).h u+(M (phi n)).b u ≤ T,
        ∃d : ActualInheritedLocalScalarLimitData
          (hTemp.trans_le (sub_le_self T hepsilon)) (T-epsilon)
          (fun n => M (phi n)) htotal,
          let hT := hTemp.trans_le (sub_le_self T hepsilon)
          let kappa := ((T-epsilon)/T)*scalarInitialDensityConstant hT d.beta
          (∀t > 0,d.U.mass t=kappa*t) ∧ (∀t > 0,d.V.mass t=kappa*t) ∧
            cl ≤ kappa ∧ kappa ≤ cu ∧ d.sigma=0 ∧
            (∀t ≥ 0,comparisonLocalScalarLimitSlope hT (T-epsilon) d.beta d.U d.sigma t=0) ∧
            (∀t ≥ 0,comparisonLocalScalarLimitResponse hT (T-epsilon) d.beta d.U d.sigma t=0) ∧
            ∀R : ℝ,0 < R →
              TendstoUniformlyOn (fun n => comparisonLocalScalarSlope hT (T-epsilon)
                ((M (phi n)).inheritedScalarMassProfile hT (htotal n)) (M (phi n)).xs)
                (fun _ => 0) atTop (Icc (0 : ℝ) R) ∧
              TendstoUniformlyOn (fun n => comparisonRescaledScalarResponse
                (scalarCovarianceResponse hT ((M (phi n)).inheritedScalarMassProfile hT (htotal n)))
                (T-epsilon) (M (phi n)).xs) (fun _ => 0) atTop (Icc (0 : ℝ) R) := by
  obtain ⟨phi,hphi,htotal,d,Hlinear⟩ := exists_actual_selected_bad_history_linear_profile_along
    hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
    dim hdim root M epsilon shell hepsilon hshell hTemp hb hh Hhistory W hcanonical hWlim hcompare
  have Hzero := d.scalar_primitives_zero_of_linear_profiles Hlinear.1 Hlinear.2.1
  exact ⟨phi,hphi,htotal,d,Hlinear.1,Hlinear.2.1,Hlinear.2.2.1,Hlinear.2.2.2,
    Hzero.1,Hzero.2.1,Hzero.2.2,
    d.compact_scalar_zero_limits_of_linear_profiles Hlinear.1 Hlinear.2.1⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
