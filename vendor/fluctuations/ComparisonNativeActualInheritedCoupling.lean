module

public import ComparisonNativeActualInheritedCalibration

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 6000000
namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock T : ℝ}

theorem inherited_scalar_radius_integral_le_of_eq4 {n : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ T)
    {v x Cb Ch Cs : ℝ} (hv : v∈Icc (0:ℝ) 1) (hCb : 0 ≤ Cb)
    (hb : ∀u∈Icc (0:ℝ) v,|M.b u-T| ≤ Cb*x^2)
    (hh : ∀u∈Icc (0:ℝ) v,|M.h u| ≤ Ch*x^3)
    (hs : ∀u∈Icc (0:ℝ) v,orderedPathS (n+1) M.bf M.hf u ≤ Cs*x) :
    (∫u in 0..v,|actualScalarClockQuantile T (n+1) M.bf M.hf u-M.R u|) ≤
      (∫u in 0..v,|orderedPathS (n+1) M.bf M.hf u-M.R u|)+((Cb*Cs+Ch)/T)*x^3*v := by
  have hsub : uIcc (0:ℝ) v ⊆ uIcc (0:ℝ) 1 := by
    rw [uIcc_of_le hv.1,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl hv.2
  have hqi : IntervalIntegrable (actualScalarClockQuantile T (n+1) M.bf M.hf) volume 0 v :=
    (show MonotoneOn (actualScalarClockQuantile T (n+1) M.bf M.hf) (uIcc (0:ℝ) 1) by
      simpa only [uIcc_of_le zero_le_one] using
        actualScalarClockQuantile_monotone hT (n+1) (by omega) M.bf M.hf
          M.inherited_bf_monotone M.inherited_hf_monotone).intervalIntegrable.mono_set hsub
  have hsi : IntervalIntegrable (orderedPathS (n+1) M.bf M.hf) volume 0 v :=
    (show MonotoneOn (orderedPathS (n+1) M.bf M.hf) (uIcc (0:ℝ) 1) by
      simpa only [uIcc_of_le zero_le_one] using M.mass_mean_monotone).intervalIntegrable.mono_set hsub
  have hri : IntervalIntegrable M.R volume 0 v :=
    (comparisonSweepQuantile_continuous M.context.hc M.context.hk M.context.hkc
      M.context.hm M.context.hM M.alpha).intervalIntegrable 0 v
  have H:=intervalIntegral.integral_mono_on hv.1 (hqi.sub hri).abs
    ((hsi.sub hri).abs.add intervalIntegrable_const) (fun u hu=>
      M.inherited_scalar_quantile_radius_abs_le_of_eq4 hT htotal ⟨hu.1,hu.2.trans hv.2⟩
        hCb (hb u hu) (hh u hu) (hs u hu))
  rw [intervalIntegral.integral_add (hsi.sub hri).abs intervalIntegrable_const,
    intervalIntegral.integral_const,sub_zero,smul_eq_mul] at H
  exact H.trans_eq (by ring)

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
