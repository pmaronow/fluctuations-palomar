module

public import ComparisonNativeActualHistoryRadiusStripConcentrationAlong
public import ComparisonNativeActualRadiusScalarRescaling
public import ComparisonStationarityDensityScaling

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology
set_option maxHeartbeats 6000000
namespace NativeOverlapMinimum

theorem actual_selected_bad_history_compact_radius_thermal_L1_along
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D T c0 c C a b : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc : 0 < c) (ha : 0 ≤ a) (hab : a ≤ b)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hxs : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (epsilon shell : ℝ) (hshell : 0 < shell)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock T epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (hmass : ∀ᶠn in atTop,∀t∈Icc a b,
      c*(M n).xs ≤ (M n).alpha.val.val ((M n).xs*t) ∧
        (M n).alpha.val.val ((M n).xs*t) ≤ C*(M n).xs) :
    Tendsto (fun n=>∫t in Icc a b,
      (M n).cavityRadiusPointDefect ((M n).xs*t)/(M n).xs^2) atTop (𝓝 0) := by
  let Cbig := max C b
  have Hlim := actual_selected_bad_history_radius_strip_thermal_tendsto_zero_along
    (C:=Cbig) Bclock hm hdelta hmargin hcl hcu hAz hC0 hCt hc
    dim hdim root M hxs epsilon shell hshell hb hh Hhistory
  have hsmall : ∀ᶠn in atTop,(M n).xs*b ≤ 1 := by
    have H : Tendsto (fun n=>(M n).xs*b) atTop (𝓝 0) := by
      simpa only [zero_mul] using hxs.mul_const b
    exact H.eventually (eventually_le_nhds zero_lt_one)
  have he n := comparison_radius_rescaling_integral
    (M n).cavityRadiusPointDefect hab (M n).hxs
  apply squeeze_zero' _ _ Hlim
  · filter_upwards [hsmall] with n hn
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact div_nonneg ((M n).cavityRadiusPointDefect_nonneg
      ⟨mul_nonneg (M n).hxs.le (ha.trans ht.1),
        (mul_le_mul_of_nonneg_left ht.2 (M n).hxs.le).trans hn⟩) (sq_nonneg _)
  · filter_upwards [hsmall,hmass] with n hn hmn
    rw [he n]
    apply div_le_div_of_nonneg_right _ (pow_nonneg (M n).hxs.le 3)
    have hsub : Icc ((M n).xs*a) ((M n).xs*b) ⊆
        (M n).actualRadiusTargetStrip c Cbig := by
      intro r hr
      have ht : r/(M n).xs∈Icc a b :=
        ⟨(le_div_iff₀ (M n).hxs).mpr (by simpa only [mul_comm] using hr.1),
          (div_le_iff₀ (M n).hxs).mpr (by simpa only [mul_comm] using hr.2)⟩
      have H := hmn (r/(M n).xs) ht
      rw [mul_div_cancel₀ r (M n).hxs.ne'] at H
      refine ⟨⟨(mul_nonneg (M n).hxs.le ha).trans hr.1,
        le_min ?_ (hr.2.trans hn)⟩,H.1,?_⟩
      · exact hr.2.trans (by simpa only [Cbig,mul_comm] using
          mul_le_mul_of_nonneg_left (le_max_right C b) (M n).hxs.le)
      · exact H.2.trans (mul_le_mul_of_nonneg_right (le_max_left C b) (M n).hxs.le)
    have hi := (M n).cavity_radius_point_defect_unit_integrable.mono_set
      (show (M n).actualRadiusTargetStrip c Cbig ⊆ Icc (0:ℝ) 1 from
        fun r hr=>⟨hr.1.1,hr.1.2.trans (min_le_right _ _)⟩)
    apply setIntegral_mono_set hi _ (Eventually.of_forall hsub)
    filter_upwards [ae_restrict_mem ((M n).actual_radius_target_strip_measurable c Cbig)] with r hr
    exact (M n).cavityRadiusPointDefect_nonneg ⟨hr.1.1,hr.1.2.trans (min_le_right _ _)⟩

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
