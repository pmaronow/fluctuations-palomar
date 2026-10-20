module

public import ComparisonNativeActualInitialMassMismatchLimit

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy
set_option maxHeartbeats 7000000
attribute [local instance] Measure.Subtype.measureSpace

theorem comparison_original_retained_integral_eq_interval
    {v : ℝ} (hv : v∈Icc (0:ℝ) 1) (f : ℝ→ℝ) :
    (∫w : ParisiFinite.OrderPoint in {w | (w:ℝ) ≤ v},f (w:ℝ)
      ∂(uniformOrderMass : Measure ParisiFinite.OrderPoint))=∫u in 0..v,f u := by
  rw [←integral_indicator (measurableSet_le measurable_subtype_coe measurable_const)]
  have he : (fun w : ParisiFinite.OrderPoint=>
      {w : ParisiFinite.OrderPoint | (w:ℝ) ≤ v}.indicator (fun w=>f (w:ℝ)) w)=
      fun w : ParisiFinite.OrderPoint=>(Icc (0:ℝ) v).indicator f (w:ℝ) := by
    funext w
    by_cases hw : (w:ℝ) ≤ v <;> simp only [indicator_apply,mem_ofPred_eq,mem_Icc,
      w.property.1,true_and,hw]
  rw [he]
  change (∫w : unitInterval,(Icc (0:ℝ) v).indicator f (w:ℝ)∂volume)=_
  rw [unitInterval.measurePreserving_coe.integral_comp unitInterval.measurableEmbedding_coe,
    integral_indicator measurableSet_Icc,Measure.restrict_restrict measurableSet_Icc]
  have hsub : Icc (0:ℝ) v ⊆ Icc (0:ℝ) 1 := Icc_subset_Icc le_rfl hv.2
  rw [inter_eq_left.mpr hsub,integral_Icc_eq_integral_Ioc,
    ←intervalIntegral.integral_of_le hv.1]

namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem original_retained_mismatch_integrable {n : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (v : ℝ) :
    Integrable (fun w : ParisiFinite.OrderPoint=>orderedPathS (n+1) M.bf M.hf w-M.R w)
      ((uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict {w | (w:ℝ) ≤ v}) ∧
    Integrable (fun w : ParisiFinite.OrderPoint=>(orderedPathS (n+1) M.bf M.hf w-M.R w)^2)
      ((uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict {w | (w:ℝ) ≤ v}) := by
  have hi : IntervalIntegrable (fun u=>orderedPathS (n+1) M.bf M.hf u-M.R u) volume 0 1 :=
    (show MonotoneOn (orderedPathS (n+1) M.bf M.hf) (uIcc (0:ℝ) 1) by
      simpa only [uIcc_of_le zero_le_one] using M.mass_mean_monotone).intervalIntegrable.sub
      ((comparisonSweepQuantile_continuous M.context.hc M.context.hk M.context.hkc
        M.context.hm M.context.hM M.alpha).intervalIntegrable 0 1)
  have hi1:=unitInterval.measurePreserving_coe.integrable_comp_of_integrable
    ((intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hi)
  have hi2:=unitInterval.measurePreserving_coe.integrable_comp_of_integrable
    ((intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp
      M.mass_squared_mismatch_intervalIntegrable)
  exact ⟨hi1.integrableOn,hi2.integrableOn⟩

theorem actual_original_retained_squared_mismatch_ratio_tendsto_zero
    {T H : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (M : (n : ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W v : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (hb : ∀n u,(M n).b u=T) (hh : ∀n u,(M n).h u=H)
    (C : ℝ) (hC : 0 < C) (hv : ∀n,v n∈Icc (0:ℝ) 1)
    (hvc : ∀n,v n ≤ C*W n) :
    Tendsto (fun n=>(∫w : ParisiFinite.OrderPoint in {w | (w:ℝ) ≤ v n},
      (orderedPathS (n+1) (M n).bf (M n).hf w-(M n).R w)^2
        ∂(uniformOrderMass : Measure ParisiFinite.OrderPoint))/(W n)^3) atTop (𝓝 0) := by
  have Hfull:=actual_minimum_initial_mass_squared_mismatch_ratio_tendsto_zero
    hm hdelta hroom hcl hcu hAz hC0 hCt M W hxs hWlim hb hh C hC
  have HW:=(hWlim.const_mul C).eventually
    (eventually_le_nhds (show C*(0:ℝ) < 1 by simp))
  apply squeeze_zero' _ _ Hfull
  · filter_upwards [] with n
    have hw:=(M n).hxs.trans_le (hxs n)
    exact div_nonneg (integral_nonneg (fun _=>sq_nonneg _)) (pow_pos hw 3).le
  · filter_upwards [HW] with n hnW
    have hw:=(M n).hxs.trans_le (hxs n)
    rw [comparison_original_retained_integral_eq_interval (hv n)
      (fun u=>(orderedPathS (n+1) (M n).bf (M n).hf u-(M n).R u)^2)]
    apply div_le_div_of_nonneg_right _ (pow_pos hw 3).le
    have hi:=((M n).mass_squared_mismatch_intervalIntegrable).mono_set (by
      rw [uIcc_of_le (by positivity : 0 ≤ C*W n),uIcc_of_le zero_le_one]
      exact Icc_subset_Icc le_rfl hnW)
    exact intervalIntegral.integral_mono_interval le_rfl (hv n).1 (hvc n)
      (ae_of_all _ (fun _=>sq_nonneg _)) hi

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
