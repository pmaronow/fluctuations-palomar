module

public import ComparisonNativeActualHistoryHighJointScalarFactoryAlong
public import ComparisonNativeActualHistoryHighVirtualGapAlong
public import ComparisonNativeActualLocalScalarLimitRadiusReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar Cavity NativeOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 22000000

theorem exists_actual_selected_bad_history_high_joint_scalar_limit_with_virtual_gaps_along
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
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/
      (M n).xs^2) atTop atTop) :
    ∃phi : ℕ→ℕ,StrictMono phi ∧
      ∃htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M (phi n)).h u+(M (phi n)).b u ≤ T,
        ∃d : ActualInheritedLocalScalarLimitData
          (hTemp.trans_le (sub_le_self T hepsilon)) (T-epsilon)
          (fun n=>M (phi n)) htotal,
          ∀a b : ℝ,0 ≤ a → a < b →
            a∈comparisonIncrementSupport d.V.mass → b∈comparisonIncrementSupport d.V.mass →
            (∀r∈Ioo a b,r∉comparisonIncrementSupport d.V.mass) →
            Nonempty (ComparisonVirtualGapData
              (comparisonLocalScalarLimitResponse (hTemp.trans_le (sub_le_self T hepsilon))
                (T-epsilon) d.beta d.U d.sigma) a b) := by
  obtain ⟨phi,hphi,htotal,⟨d⟩⟩ := exists_actual_selected_bad_history_high_joint_scalar_limit_along
    hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
    dim hdim root M epsilon shell hepsilon hshell hTemp hb hh Hhistory W hcanonical hWlim
    hcompare hlarge
  refine ⟨phi,hphi,htotal,d,?_⟩
  intro a b ha hab hasupport hbsupport hgap
  let hT : 0<T := hTemp.trans_le (sub_le_self T hepsilon)
  let g := comparisonLocalScalarLimitResponse hT (T-epsilon) d.beta d.U d.sigma
  have hg : ∀R : ℝ,0<R → ContinuousOn g (Icc (0:ℝ) R) := by
    intro R hR
    have Hi : IntegrableOn
        (comparisonLocalScalarLimitSlope hT (T-epsilon) d.beta d.U d.sigma) (uIcc (0:ℝ) R) := by
      simpa only [uIcc_of_le hR.le] using (d.limits R hR).1.integrableOn_Icc
    change ContinuousOn (fun r=>∫s in 0..r,
      comparisonLocalScalarLimitSlope hT (T-epsilon) d.beta d.U d.sigma s) (Icc (0:ℝ) R)
    simpa only [uIcc_of_le hR.le] using intervalIntegral.continuousOn_primitive_interval Hi
  exact actual_selected_bad_history_high_virtual_gap_data_along (B:=b+1)
    ha hab (by linarith) hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01
    hmargin hcapmargin hgapmargin
    (fun n=>dim (phi n)) (hdim.comp hphi.tendsto_atTop)
    (fun n=>root (phi n)) (fun n=>M (phi n)) epsilon shell hepsilon hshell hTemp
    (hphi.tendsto_atTop.eventually hb) (hphi.tendsto_atTop.eventually hh)
    (Hhistory.comp phi hphi.tendsto_atTop) (fun n=>W (phi n)) (fun n=>hcanonical (phi n))
    (hWlim.comp hphi.tendsto_atTop) (fun n=>hcompare (phi n)) htotal
    (hlarge.comp hphi.tendsto_atTop) g (fun R hR=>(d.limits R hR).2.2) hg
    d.V.mass d.V.monotone d.radius_negative_axis_zero d.radius_inverse_cdf_limit
    hasupport hbsupport hgap

end OAI.SKFluctuations.LaplaceWindowFormalization
