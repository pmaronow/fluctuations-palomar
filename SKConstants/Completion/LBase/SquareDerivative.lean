module

public import SKConstants.Completion.LBase.FullProfiles

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants.Completion.LBase
open SKConstantsOAI.ZeroTemperatureSK
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
variable {Ω : Type*} [MeasurableSpace Ω]

def actualSquareProfileRate (W : BrownianSystem Ω) (β t : ℝ) : ℝ :=
  if t < (parisiEquilibriumPhysicalEndpoint β : ℝ) then 0 else
    4 * actualParisiFullSusceptibilitySquareExpected W β t -
      6 * actualParisiContinuationThirdMoment W β (t - (parisiEquilibriumPhysicalEndpoint β : ℝ))

theorem actual_square_profile_hasDerivWithinAt_right
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (actualParisiFullSusceptibilitySquareExpected W β)
      (actualSquareProfileRate W β t) (Ioi t) t := by
  let E : ℝ := parisiEquilibriumPhysicalEndpoint β
  by_cases hpre : t < E
  · have hc : HasDerivWithinAt (fun _ : ℝ => (1 : ℝ) / β^2) 0 (Ioi t) t :=
      hasDerivWithinAt_const _ _ _
    have he : (fun _ : ℝ => (1 : ℝ) / β^2) =ᶠ[𝓝[>] t]
        actualParisiFullSusceptibilitySquareExpected W β := by
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hpre)] with x hx hxE
      have hx0 : 0 ≤ x := ht.trans (show t < x from hx).le
      have hh := actualParisiFullSusceptibilitySquareExpected_pre W β hβ x.toNNReal
        (by apply NNReal.coe_le_coe.mp; simpa only [Real.coe_toNNReal x hx0] using hxE.le)
      simpa only [Real.coe_toNNReal x hx0] using hh.symm
    have hrt := actualParisiFullSusceptibilitySquareExpected_pre W β hβ t.toNNReal
      (by apply NNReal.coe_le_coe.mp; simpa only [Real.coe_toNNReal t ht] using hpre.le)
    rw [Real.coe_toNNReal t ht] at hrt
    rw [actualSquareProfileRate, ite_eq_left hpre]
    exact hc.congr_of_eventuallyEq he.symm hrt
  · have hpost : E ≤ t := le_of_not_gt hpre
    have hv : 0 ≤ t - E := sub_nonneg.mpr hpost
    have H := actualParisiContinuationR_hasDerivWithinAt_right W β hβ (t - E) hv
    have hc : HasDerivWithinAt (fun x : ℝ => actualParisiContinuationR W β (x - E))
        (4 * actualParisiContinuationR W β (t - E) - 6 * actualParisiContinuationThirdMoment W β (t - E))
        (Ioi t) t := by
      convert H.comp t (((hasDerivAt_id t).sub_const E).hasDerivWithinAt)
        (fun x (hx : x ∈ Ioi t) => sub_lt_sub_right (show t < x from hx) E) using 1 <;>
        simp only [mul_one, Function.comp_def, id_eq]
    have he : (fun x : ℝ => actualParisiContinuationR W β (x - E)) =ᶠ[𝓝[>] t]
        actualParisiFullSusceptibilitySquareExpected W β := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact (LQ.actual_square_profile_eq W β hβ x (ht.trans (show t < x from hx).le)).symm
    have HH := hc.congr_of_eventuallyEq he.symm (LQ.actual_square_profile_eq W β hβ t ht)
    rw [actualSquareProfileRate, ite_eq_right hpre, LQ.actual_square_profile_eq W β hβ t ht]
    exact HH

theorem actual_square_profile_derivative_bound
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (t : ℝ) (ht : 0 ≤ t) :
    |actualSquareProfileRate W β t| ≤ 2 * actualParisiFullSusceptibilitySquareExpected W β t := by
  unfold actualSquareProfileRate
  split_ifs with hpre
  · rw [abs_zero]
    exact mul_nonneg (by norm_num) (actualParisiFullSusceptibilitySquareExpected_bounds W β t).1
  · have hv : 0 ≤ t - (parisiEquilibriumPhysicalEndpoint β : ℝ) := sub_nonneg.mpr (le_of_not_gt hpre)
    rw [LQ.actual_square_profile_eq W β hβ t ht]
    have hupper := actualParisiContinuationThirdMoment_le_R W β hβ _ hv
    have hlower := actualParisiContinuationThirdMoment_ge_three_quarters W β hβ _ hv
    exact abs_le.mpr ⟨by linarith, by linarith⟩

end SKConstants.Completion.LBase
