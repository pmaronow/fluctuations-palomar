module
public import SKConstants.ParisiPicardReflection

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK

namespace BoundedLipschitzDrift

theorem solution_sub_le_of_primitive_error
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (a b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (ℱ : Filtration ℝ≥0 mΩ) (B : ℝ≥0 → Ω → ℝ) (hB : IsProgressive ℱ B)
    (T : ℝ≥0) (E : ℝ) (hE : 0 ≤ E)
    (he : ∀ (Y : ℝ≥0 → Ω → ℝ), IsProgressive ℱ Y → ∀ t ≤ T, ∀ w,
      |timePrimitive (a.action B Y) t w-timePrimitive (b.action B Y) t w| ≤ E)
    (t : ℝ≥0) (ht : t ≤ T) (w : Ω) :
    |a.solution B t w-b.solution B t w| ≤ 2*E*Real.exp (b.rate*t) := by
  have hiter : ∀ n, ∀ s ≤ T, ∀ w,
      |a.correctionIter B n s w-b.correctionIter B n s w| ≤
        2*E*Real.exp (b.rate*s) := by
    intro n
    induction n with
    | zero => intro s hs w; simp only [SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift.correctionIter, sub_self,abs_zero]; positivity
    | succ n ih =>
      intro s hs w
      have hp := he (a.correctionIter B n) (a.correctionIter_progressive ℱ hB n) s hs w
      have hq := b.timePrimitive_action_sub_estimate ℱ hB
        (a.correctionIter_progressive ℱ hB n) (b.correctionIter_progressive ℱ hB n)
        (show 0 ≤ 2*E by positivity) s w (fun r hr => ih r (hr.trans hs) w)
      have hexp : 1 ≤ Real.exp (b.rate*s) := Real.one_le_exp (mul_nonneg b.rate_pos.le s.coe_nonneg)
      calc
        _ ≤ |timePrimitive (a.action B (a.correctionIter B n)) s w-
               timePrimitive (b.action B (a.correctionIter B n)) s w|+
             |timePrimitive (b.action B (a.correctionIter B n)) s w-
               timePrimitive (b.action B (b.correctionIter B n)) s w| := abs_sub_le _ _ _
        _ ≤ E+(2*E)/2*Real.exp (b.rate*s) := add_le_add hp hq
        _ ≤ 2*E*Real.exp (b.rate*s) := by nlinarith
  have H := le_of_tendsto
    ((a.correctionIter_tendsto ℱ hB t w).sub (b.correctionIter_tendsto ℱ hB t w)).abs
    (Eventually.of_forall (fun n => hiter n t ht w))
  simpa only [SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift.solution,add_sub_add_left_eq_sub] using H

theorem primitive_error_of_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (a b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (ℱ : Filtration ℝ≥0 mΩ) (B Y : ℝ≥0 → Ω → ℝ)
    (hB : IsProgressive ℱ B) (hY : IsProgressive ℱ Y)
    (T : ℝ≥0) (e : ℝ → ℝ) (hei : IntervalIntegrable e volume 0 T)
    (he : ∀ r ∈ Icc (0:ℝ) T, ∀ x, |a.f r x-b.f r x| ≤ e r)
    (t : ℝ≥0) (ht : t ≤ T) (w : Ω) :
    |timePrimitive (a.action B Y) t w-timePrimitive (b.action B Y) t w| ≤
      ∫ r in (0:ℝ)..(t:ℝ), e r := by
  have hiA := progressive_bounded_integrable ℱ (a.action_progressive ℱ hB hY) (a.action_bound B Y) w 0 t
  have hiB := progressive_bounded_integrable ℱ (b.action_progressive ℱ hB hY) (b.action_bound B Y) w 0 t
  rw [timePrimitive,timePrimitive,←intervalIntegral.integral_sub hiA hiB]
  rw [←Real.norm_eq_abs]
  apply intervalIntegral.norm_integral_le_of_norm_le t.coe_nonneg _
    (hei.mono_set (by intro r hr; simp only [uIcc_of_le T.coe_nonneg,uIcc_of_le t.coe_nonneg] at hr ⊢; exact ⟨hr.1,hr.2.trans ht⟩))
  filter_upwards [] with r hr
  have hr0 : 0 ≤ r := hr.1.le
  simp only [SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift.action,Real.norm_eq_abs,Real.coe_toNNReal _ hr0]
  exact he r ⟨hr0,hr.2.trans ht⟩ _

end BoundedLipschitzDrift
end SKConstants
