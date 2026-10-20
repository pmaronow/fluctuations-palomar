module
public import SKConstants.ParisiPicardStability
public import SKConstants.ScalarForwardPicardPaths

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants.BoundedLipschitzDrift
open SKConstantsOAI.ZeroTemperatureSK

def translated (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift) (a x₀ : ℝ) :
    SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift where
  f t x := b.f (a+t) (x₀+x)
  bound := b.bound
  lip := b.lip
  measurable := b.measurable.comp
    ((measurable_const.add measurable_fst).prodMk
      (measurable_const.add measurable_snd))
  bounded t x := b.bounded _ _
  lipschitz t := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Real.dist_eq,add_sub_add_left_eq_sub] using
      (b.lipschitz (a+t)).dist_le_mul (x₀+x) (x₀+y)

theorem solution_translated_add_seed
    {Ω : Type*} [MeasurableSpace Ω]
    (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift) (a x₀ : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (w : Ω) :
    x₀+(translated b a x₀).solution B t w =
      (translated b a 0).solution (fun s u => x₀+B s u) t w := by
  have he : ∀ n s u, (translated b a x₀).correctionIter B n s u =
      (translated b a 0).correctionIter (fun s u => x₀+B s u) n s u := by
    intro n
    induction n with
    | zero => intro s u; rfl
    | succ n ih =>
      intro s u
      simp only [SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift.correctionIter,timePrimitive,
        SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift.action]
      apply intervalIntegral.integral_congr
      intro r hr
      dsimp only
      rw [ih]
      simp only [translated,zero_add]
      congr 1
      ring
  have hlim : (translated b a x₀).correction B t w =
      (translated b a 0).correction (fun s u => x₀+B s u) t w := by
    unfold SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift.correction
    congr 1
    exact funext (fun n => he n t w)
  simp only [SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift.solution,hlim]
  ring

theorem solution_congr_nonneg_drift
    {Ω : Type*} [MeasurableSpace Ω]
    (b c : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (h : ∀ r ≥ 0, ∀ x, b.f r x = c.f r x)
    (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (w : Ω) : b.solution B t w = c.solution B t w := by
  have hi : ∀ n s u, b.correctionIter B n s u = c.correctionIter B n s u := by
    intro n
    induction n with
    | zero => intro s u; rfl
    | succ n ih =>
      intro s u
      simp only [SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift.correctionIter,timePrimitive,
        SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift.action]
      apply intervalIntegral.integral_congr
      intro r hr
      dsimp only
      rw [ih,h _ (Real.toNNReal r).coe_nonneg]
  unfold SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift.solution
    SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift.correction
  congr 2
  exact funext (fun n => hi n t w)

theorem solution_eq_of_integral_equation
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (ℱ : Filtration ℝ≥0 mΩ) (B Y : ℝ≥0 → Ω → ℝ)
    (hB : IsProgressive ℱ B) (hY : IsProgressive ℱ Y)
    (T : ℝ≥0)
    (he : ∀ t ≤ T, ∀ w, Y t w = B t w+
      ∫ s in (0:ℝ)..(t:ℝ), b.f (Real.toNNReal s) (Y (Real.toNNReal s) w))
    (t : ℝ≥0) (ht : t ≤ T) (w : Ω) :
    b.solution B t w = Y t w := by
  let C : ℝ≥0 → Ω → ℝ := Y-B
  have hC : IsProgressive ℱ C := hY.sub hB
  have hfixed (s : ℝ≥0) (hs : s ≤ T) (w : Ω) :
      C s w = timePrimitive (b.action B C) s w := by
    change Y s w-B s w =
      ∫ r in (0:ℝ)..(s:ℝ), b.f (Real.toNNReal r)
        (B (Real.toNNReal r) w+(Y (Real.toNNReal r) w-B (Real.toNNReal r) w))
    have hh (r : ℝ) : B (Real.toNNReal r) w+
        (Y (Real.toNNReal r) w-B (Real.toNNReal r) w) = Y (Real.toNNReal r) w := by ring
    simp_rw [hh]
    rw [he s hs w]
    ring
  have hbound (s : ℝ≥0) (hs : s ≤ T) (w : Ω) : |C s w| ≤ b.bound*s := by
    rw [hfixed s hs]
    exact timePrimitive_bound ℱ (b.action_progressive ℱ hB hC) (b.action_bound B C) s w
  have hiter : ∀ n, ∀ s ≤ T, ∀ w,
      |b.correctionIter B n s w-C s w| ≤
        (b.bound:ℝ)*(T:ℝ)*(1/2:ℝ)^n*Real.exp (b.rate*s) := by
    intro n
    induction n with
    | zero =>
      intro s hs w
      simp only [SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift.correctionIter,
        zero_sub,abs_neg,pow_zero,mul_one]
      have hexp : 1 ≤ Real.exp (b.rate*s) :=
        Real.one_le_exp (mul_nonneg b.rate_pos.le s.coe_nonneg)
      calc
        |C s w| ≤ (b.bound:ℝ)*(s:ℝ) := hbound s hs w
        _ ≤ (b.bound:ℝ)*(T:ℝ) := mul_le_mul_of_nonneg_left hs b.bound.coe_nonneg
        _ ≤ (b.bound:ℝ)*(T:ℝ)*Real.exp (b.rate*s) := by
          nlinarith [mul_nonneg b.bound.coe_nonneg T.coe_nonneg]
    | succ n ih =>
      intro s hs w
      rw [SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift.correctionIter,hfixed s hs]
      have H := b.timePrimitive_action_sub_estimate ℱ hB
        (b.correctionIter_progressive ℱ hB n) hC
        (show 0 ≤ (b.bound:ℝ)*(T:ℝ)*(1/2:ℝ)^n by positivity)
        s w (fun r hr => ih r (hr.trans hs) w)
      convert H using 1 <;> rw [pow_succ] <;> ring
  have hgeo : Tendsto (fun n : ℕ => (b.bound:ℝ)*(T:ℝ)*(1/2:ℝ)^n*
      Real.exp (b.rate*t)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)).const_mul
        ((b.bound:ℝ)*(T:ℝ)) |>.mul_const (Real.exp (b.rate*t))
  have H : |b.correction B t w-C t w| ≤ 0 :=
    le_of_tendsto_of_tendsto
      ((b.correctionIter_tendsto ℱ hB t w).sub tendsto_const_nhds).abs hgeo
      (Eventually.of_forall (fun n => hiter n t ht w))
  have HC : b.correction B t w = C t w := sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm H (abs_nonneg _)))
  simp only [SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift.solution,HC,C,Pi.sub_apply,
    add_sub_cancel]

theorem solution_restart
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (ℱ : Filtration ℝ≥0 mΩ) (B : ℝ≥0 → Ω → ℝ) (hB : IsProgressive ℱ B)
    (w : Ω) (hBc : Continuous (fun s => B s w)) (a t : ℝ≥0) :
    b.solution B (a+t) w = b.solution B a w+
      (translated b a (b.solution B a w)).solution
        (fun s (_ : Unit) => B (a+s) w-B a w) t () := by
  let C : ℝ≥0 → Unit → ℝ := fun s _ => B (a+s) w-B a w
  let Y : ℝ≥0 → Unit → ℝ := fun s _ => b.solution B (a+s) w-b.solution B a w
  let ℱ₀ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Unit) :=
    Filtration.const ℝ≥0 _ le_rfl
  have hYc : Continuous (fun s => b.solution B s w) := b.solution_continuous ℱ hB hBc
  have hC : IsProgressive ℱ₀ C := by
    intro u
    exact (((hBc.comp (continuous_const.add
      (continuous_subtype_val.comp continuous_fst))).sub continuous_const)).measurable
  have hY : IsProgressive ℱ₀ Y := by
    intro u
    exact (((hYc.comp (continuous_const.add
      (continuous_subtype_val.comp continuous_fst))).sub continuous_const)).measurable
  have hi (p q : ℝ) : IntervalIntegrable
      (fun r => b.f (Real.toNNReal r) (b.solution B (Real.toNNReal r) w)) volume p q := by
    apply (intervalIntegrable_const (c := (b.bound:ℝ))).mono_fun
    · exact (b.measurable.comp
        ((measurable_subtype_coe.comp measurable_real_toNNReal).prodMk
          (hYc.measurable.comp measurable_real_toNNReal))).aestronglyMeasurable
    · exact Eventually.of_forall (fun r => by simpa only [Real.norm_eq_abs,abs_of_nonneg b.bound.coe_nonneg] using b.bounded _ _)
  have he (s : ℝ≥0) (hs : s ≤ t) (u : Unit) :
      Y s u = C s u+
        ∫ r in (0:ℝ)..(s:ℝ), (translated b a (b.solution B a w)).f
          (Real.toNNReal r) (Y (Real.toNNReal r) u) := by
    have hshift :
        (∫ r in (0:ℝ)..(s:ℝ), (translated b a (b.solution B a w)).f
          (Real.toNNReal r) (Y (Real.toNNReal r) u)) =
        ∫ r in (a:ℝ)..((a+s):ℝ), b.f (Real.toNNReal r)
          (b.solution B (Real.toNNReal r) w) := by
      have H := intervalIntegral.integral_comp_add_left
        (fun r => b.f (Real.toNNReal r) (b.solution B (Real.toNNReal r) w))
        (a:ℝ) (a := (0:ℝ)) (b := (s:ℝ))
      simp only [add_zero,NNReal.coe_add] at H
      rw [←H]
      apply intervalIntegral.integral_congr
      intro r hr
      have hr0 : 0 ≤ r := by simpa only [min_eq_left s.coe_nonneg] using hr.1
      have har : 0 ≤ (a:ℝ)+r := add_nonneg a.coe_nonneg hr0
      have heNN : a+Real.toNNReal r = Real.toNNReal ((a:ℝ)+r) := by
        apply NNReal.coe_injective
        simp only [NNReal.coe_add,Real.coe_toNNReal _ hr0,Real.coe_toNNReal _ har]
      simp only [translated,Y,Real.coe_toNNReal _ hr0,heNN,Real.coe_toNNReal _ har]
      congr 1
      ring
    rw [hshift]
    dsimp only [Y,C]
    rw [b.solution_eq ℱ hB (a+s) w,b.solution_eq ℱ hB a w]
    have H := intervalIntegral.integral_add_adjacent_intervals (hi 0 a) (hi a (a+s))
    simp only [NNReal.coe_add]
    linarith
  have H := solution_eq_of_integral_equation (translated b a (b.solution B a w))
    ℱ₀ C Y hC hY t he t le_rfl ()
  change _ = b.solution B (a+t) w-b.solution B a w at H
  rw [H]
  ring

end SKConstants.BoundedLipschitzDrift
