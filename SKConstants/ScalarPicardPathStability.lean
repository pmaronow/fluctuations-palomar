module

public import SKConstants.ScalarForwardPicardPaths
public import SKConstants.ScalarWeightedPathStability
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK
namespace BoundedLipschitzDrift

theorem timePrimitive_sub_le_of_total_driver_error
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (ℱ : Filtration ℝ≥0 mΩ) (B C Y Z : ℝ≥0 → Ω → ℝ)
    (hB : IsProgressive ℱ B) (hC : IsProgressive ℱ C)
    (hY : IsProgressive ℱ Y) (hZ : IsProgressive ℱ Z)
    (A : ℝ) (hA : 0≤A) (t : ℝ≥0) (w : Ω)
    (he : ∀ s≤t, |(B s w+Y s w)-(C s w+Z s w)| ≤ A*Real.exp (b.rate*s)) :
    |timePrimitive (b.action B Y) t w-timePrimitive (b.action C Z) t w| ≤
      A/2*Real.exp (b.rate*t) := by
  have hiB := progressive_bounded_integrable ℱ (b.action_progressive ℱ hB hY)
    (b.action_bound B Y) w 0 t
  have hiC := progressive_bounded_integrable ℱ (b.action_progressive ℱ hC hZ)
    (b.action_bound C Z) w 0 t
  rw [timePrimitive,timePrimitive,←intervalIntegral.integral_sub hiB hiC]
  apply le_trans _ (b.integral_exp_contraction hA t)
  rw [←Real.norm_eq_abs]
  apply intervalIntegral.norm_integral_le_of_norm_le t.coe_nonneg _
    ((continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))).intervalIntegrable _ _)
  filter_upwards [] with s hs
  have hst : Real.toNNReal s≤t := Real.toNNReal_le_iff_le_coe.mpr hs.2
  have hh := he _ hst
  have hl := (b.lipschitz (Real.toNNReal s)).dist_le_mul
    (B (Real.toNNReal s) w+Y (Real.toNNReal s) w)
    (C (Real.toNNReal s) w+Z (Real.toNNReal s) w)
  simp only [Real.dist_eq] at hl
  simp only [Real.coe_toNNReal _ hs.1.le] at hh
  change |b.action B Y (Real.toNNReal s) w-b.action C Z (Real.toNNReal s) w|≤_
  exact hl.trans (by simpa only [mul_assoc,Pi.mul_apply,Function.comp_apply,id_eq] using
    mul_le_mul_of_nonneg_left hh b.lip.coe_nonneg)

theorem solution_sub_le_of_driver_error
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (ℱ : Filtration ℝ≥0 mΩ) (B C : ℝ≥0 → Ω → ℝ)
    (hB : IsProgressive ℱ B) (hC : IsProgressive ℱ C)
    (T : ℝ≥0) (E : ℝ) (hE : 0≤E) (w : Ω)
    (he : ∀ s≤T, |B s w-C s w|≤E)
    (t : ℝ≥0) (ht : t≤T) :
    |b.solution B t w-b.solution C t w|≤2*E*Real.exp (b.rate*t) := by
  have hiter : ∀ k, ∀ s≤T,
      |b.correctionIter B k s w-b.correctionIter C k s w|≤E*Real.exp (b.rate*s) := by
    intro k
    induction k with
    | zero => intro s hs; simp only [SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift.correctionIter,
        sub_self,abs_zero]; positivity
    | succ k ih =>
      intro s hs
      have h := timePrimitive_sub_le_of_total_driver_error b ℱ B C
        (b.correctionIter B k) (b.correctionIter C k) hB hC
        (b.correctionIter_progressive ℱ hB k) (b.correctionIter_progressive ℱ hC k)
        (2*E) (by positivity) s w (fun r hr => by
          have hh := abs_add_le (B r w-C r w)
            (b.correctionIter B k r w-b.correctionIter C k r w)
          have he' := he r (hr.trans hs)
          have hi := ih r (hr.trans hs)
          have hx : 1≤Real.exp (b.rate*r) :=
            Real.one_le_exp (mul_nonneg b.rate_pos.le r.coe_nonneg)
          have heq : (B r w+b.correctionIter B k r w)-(C r w+b.correctionIter C k r w) =
              (B r w-C r w)+(b.correctionIter B k r w-b.correctionIter C k r w) := by ring
          rw [heq]
          nlinarith)
      simpa only [SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift.correctionIter,
        show (2*E)/2=E by ring] using h
  have hh := le_of_tendsto
    ((b.correctionIter_tendsto ℱ hB t w).sub (b.correctionIter_tendsto ℱ hC t w)).abs
    (Eventually.of_forall (fun k => hiter k t ht))
  have he' := he t ht
  have hx : 1≤Real.exp (b.rate*t) :=
    Real.one_le_exp (mul_nonneg b.rate_pos.le t.coe_nonneg)
  have hb := abs_add_le (B t w-C t w) (b.correction B t w-b.correction C t w)
  have heq : b.solution B t w-b.solution C t w =
      (B t w-C t w)+(b.correction B t w-b.correction C t w) := by
    unfold SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift.solution
    ring
  rw [heq]
  nlinarith

end BoundedLipschitzDrift

theorem scalarForwardPicardPath_difference_le
    (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift) (T : ℝ≥0)
    (p q : ℝ × ScalarContinuousPath T) (t : Icc (0 : ℝ) (T : ℝ)) :
    |scalarForwardPicardPath b T p t-scalarForwardPicardPath b T q t|≤
      2*(|p.1-q.1|+‖p.2-q.2‖)*Real.exp (b.rate*(t : ℝ)) := by
  let B : ℝ≥0 → Unit → ℝ := fun s _ => scalarContinuousSeedDriver T s p
  let C : ℝ≥0 → Unit → ℝ := fun s _ => scalarContinuousSeedDriver T s q
  let ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Unit) :=
    Filtration.const ℝ≥0 _ le_rfl
  have hB : IsProgressive ℱ B := by
    intro s
    exact ((continuous_scalarContinuousSeedDriver T).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_const)).measurable
  have hC : IsProgressive ℱ C := by
    intro s
    exact ((continuous_scalarContinuousSeedDriver T).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_const)).measurable
  have hE : 0≤|p.1-q.1|+‖p.2-q.2‖ := by positivity
  have he : ∀ s≤T, |B s ()-C s ()|≤|p.1-q.1|+‖p.2-q.2‖ := by
    intro s hs
    let v := projIcc 0 (T : ℝ) T.coe_nonneg (s : ℝ)
    have hv : |p.2 v-q.2 v|≤‖p.2-q.2‖ := (p.2-q.2).norm_coe_le_norm v
    have ha := abs_add_le (p.1-q.1) (p.2 v-q.2 v)
    have heq : B s ()-C s () = (p.1-q.1)+(p.2 v-q.2 v) := by
      dsimp [B,C,scalarContinuousSeedDriver,IccExtend,v]
      ring
    rw [heq]
    linarith
  have h := BoundedLipschitzDrift.solution_sub_le_of_driver_error b ℱ B C hB hC T
    (|p.1-q.1|+‖p.2-q.2‖) hE () he (NNReal.mk (t : ℝ) t.property.1) t.property.2
  have hBp : b.solution B (NNReal.mk (t : ℝ) t.property.1) () = scalarForwardPicardPath b T p t :=
    solution_congr_prefix b B (scalarContinuousSeedDriver T) () p T (fun s hs => rfl)
      (NNReal.mk (t : ℝ) t.property.1) t.property.2
  have hCq : b.solution C (NNReal.mk (t : ℝ) t.property.1) () = scalarForwardPicardPath b T q t :=
    solution_congr_prefix b C (scalarContinuousSeedDriver T) () q T (fun s hs => rfl)
      (NNReal.mk (t : ℝ) t.property.1) t.property.2
  rw [hBp,hCq] at h
  change |scalarForwardPicardPath b T p t-scalarForwardPicardPath b T q t|≤
    2*(|p.1-q.1|+‖p.2-q.2‖)*Real.exp (b.rate*(t : ℝ)) at h
  exact h

theorem scalarForwardPicardPath_norm_difference_le
    (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift) (T : ℝ≥0)
    (p q : ℝ × ScalarContinuousPath T) :
    ‖scalarForwardPicardPath b T p-scalarForwardPicardPath b T q‖≤
      2*(|p.1-q.1|+‖p.2-q.2‖)*Real.exp (b.rate*T) := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  have h := scalarForwardPicardPath_difference_le b T p q t
  have hx : Real.exp (b.rate*(t : ℝ))≤Real.exp (b.rate*T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left t.property.2 b.rate_pos.le)
  exact h.trans (mul_le_mul_of_nonneg_left hx (by positivity))

theorem scalarTwoDriverPicardPath_norm_difference_le
    (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g) (T : ℝ≥0)
    (z w : ℝ) (B C D E : ScalarContinuousPath T) :
    ‖scalarTwoDriverPicardPath b f g hf hg T (z,(B,D))-
        scalarTwoDriverPicardPath b f g hf hg T (w,(C,E))‖≤
      2*(|z-w|+scalarStieltjesPathBound f T*‖B-C‖+
        scalarStieltjesPathBound g T*‖D-E‖)*Real.exp (b.rate*T) := by
  have h := scalarForwardPicardPath_norm_difference_le b T
    (z,scalarTwoDriverWeightedPath f g hf hg T (B,D))
    (w,scalarTwoDriverWeightedPath f g hf hg T (C,E))
  have hw := scalarTwoDriverWeightedPath_norm_difference_le f g hf hg T B C D E
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  linarith

end SKConstants
