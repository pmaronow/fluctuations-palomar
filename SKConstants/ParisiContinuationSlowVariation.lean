module
public import SKConstants.ParisiScalarProfileBounds
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK ParisiFullSupport
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type*} [MeasurableSpace Ω]
local instance ParisiContinuationSlowVariation_localInstance1 (W : BrownianSystem Ω) : IsProbabilityMeasure W.law := W.isProbability

theorem actualParisiContinuationThirdMoment_le_R (W : BrownianSystem Ω) (β : ℝ) (hβ : 1<β)
    (v : ℝ) (hv : 0≤v) :
    actualParisiContinuationThirdMoment W β v≤actualParisiContinuationR W β v := by
  rw [actualParisiContinuationR_eq_full_process_moment W β hβ v hv]
  let X := actualParisiFullScalarProcess W β (parisiEquilibriumPhysicalEndpoint β+v.toNNReal)
  have HM : Measurable (fun w => scalarDefect (X w)) :=
    measurable_scalarDefect.comp ((actualParisiFullScalarDrift β).solution_measurable W _)
  have HI (n : ℕ) : Integrable (fun w => (scalarDefect (X w))^n) W.law := by
    apply Integrable.of_bound (HM.pow_const n).aestronglyMeasurable 1
    apply ae_of_all
    intro w
    have H := pow_le_pow_left₀ (abs_nonneg _) (by simpa only [Real.norm_eq_abs] using norm_scalarDefect_le_one (X w)) n
    simpa only [Real.norm_eq_abs,abs_pow,one_pow] using H
  exact integral_mono (HI 3) (HI 2) (fun w => by
    have H0 := scalarDefect_pos (X w)
    have H1 := scalarDefect_le_one (X w)
    nlinarith [sq_nonneg (scalarDefect (X w)),mul_nonneg (sq_nonneg (scalarDefect (X w))) (sub_nonneg.mpr H1)])

theorem actualParisiContinuationR_drop_le (W : BrownianSystem Ω) (β : ℝ) (hβ : 1<β)
    (S T : ℝ) (hS : 0≤S) (hST : S≤T) :
    actualParisiContinuationR W β S-actualParisiContinuationR W β T≤
      2*actualParisiContinuationR W β S*(T-S) := by
  let B := fun v => -actualParisiContinuationR W β S+2*actualParisiContinuationR W β S*(v-S)
  have HD (v : ℝ) (hv : v∈Ico S T) :
      HasDerivWithinAt (fun u => -actualParisiContinuationR W β u)
        (-(4*actualParisiContinuationR W β v-6*actualParisiContinuationThirdMoment W β v)) (Ici v) v :=
    (actualParisiContinuationR_hasDerivWithinAt_right W β hβ v (hS.trans hv.1)).neg.Ici_of_Ioi
  have HB (v : ℝ) (_hv : v∈Ico S T) :
      HasDerivWithinAt B (2*actualParisiContinuationR W β S) (Ici v) v := by
    simpa only [B,mul_one,id_eq] using ((hasDerivWithinAt_id v (Ici v)).sub_const S).const_mul
      (2*actualParisiContinuationR W β S) |>.const_add (-actualParisiContinuationR W β S)
  have H := image_le_of_deriv_right_le_deriv_boundary
    (continuous_actualParisiContinuationR W β).neg.continuousOn HD
    (B:=B) (B':=fun _ => 2*actualParisiContinuationR W β S)
    (by simp only [B,sub_self,mul_zero,add_zero];exact le_rfl)
    ((continuous_const.add (continuous_const.mul (continuous_id.sub continuous_const))).continuousOn) HB (by
      intro v hv
      have HC := actualParisiContinuationThirdMoment_le_R W β hβ v (hS.trans hv.1)
      have HR := actualParisiContinuationR_antitone W β hβ hv.1
      linarith)
  have HT := H ⟨hST,le_rfl⟩
  dsimp only [B] at HT
  change -actualParisiContinuationR W β T≤
    -actualParisiContinuationR W β S+2*actualParisiContinuationR W β S*(T-S) at HT
  linarith

lemma actualParisiContinuationR_nonpos_eq_zero (W : BrownianSystem Ω) (β v : ℝ) (hv : v≤0) :
    actualParisiContinuationR W β v=actualParisiContinuationR W β 0 := by
  rw [←actualParisiContinuationR_clamp W β v,Real.toNNReal_eq_zero.mpr hv,NNReal.coe_zero]

theorem actualParisiContinuationR_drop_le_all (W : BrownianSystem Ω) (β : ℝ) (hβ : 1<β)
    (S T : ℝ) (hST : S≤T) :
    actualParisiContinuationR W β S-actualParisiContinuationR W β T≤
      2*actualParisiContinuationR W β S*(T-S) := by
  by_cases hT : T≤0
  · rw [actualParisiContinuationR_nonpos_eq_zero W β T hT,
      actualParisiContinuationR_nonpos_eq_zero W β S (hST.trans hT)]
    rw [sub_self]
    exact mul_nonneg (mul_nonneg (by norm_num) (actualParisiContinuationR_pos W β 0).le)
      (sub_nonneg.mpr hST)
  have hT0 : 0≤T := (lt_of_not_ge hT).le
  by_cases hS : 0≤S
  · exact actualParisiContinuationR_drop_le W β hβ S T hS hST
  have hS0 : S≤0 := (lt_of_not_ge hS).le
  rw [actualParisiContinuationR_nonpos_eq_zero W β S hS0]
  have H := actualParisiContinuationR_drop_le W β hβ 0 T le_rfl hT0
  simp only [sub_zero] at H
  exact H.trans (mul_le_mul_of_nonneg_left (by linarith : T≤T-S)
    (mul_nonneg (by norm_num) (actualParisiContinuationR_pos W β 0).le))

theorem actualParisiQueryRho_sq_drop_le (W : BrownianSystem Ω) (β : ℝ) (hβ : 1<β)
    (S T : ℝ) (hST : S≤T) :
    0≤(actualParisiQueryRho W β S)^2-(actualParisiQueryRho W β T)^2 ∧
      (actualParisiQueryRho W β S)^2-(actualParisiQueryRho W β T)^2≤
        2*β^2*actualParisiContinuationR W β (S-(parisiEquilibriumPhysicalEndpoint β:ℝ))*(T-S) := by
  have H := actualParisiContinuationR_drop_le_all W β hβ
    (S-(parisiEquilibriumPhysicalEndpoint β:ℝ)) (T-(parisiEquilibriumPhysicalEndpoint β:ℝ))
    (sub_le_sub_right hST _)
  have HC := mul_le_mul_of_nonneg_left H (sq_nonneg β)
  have HM := actualParisiContinuationR_antitone W β hβ (sub_le_sub_right hST (parisiEquilibriumPhysicalEndpoint β:ℝ))
  simp only [actualParisiQueryRho,actualParisiPostRho_sq]
  constructor
  · exact sub_nonneg.mpr (mul_le_mul_of_nonneg_left HM (sq_nonneg β))
  · nlinarith [HC]

end SKConstants
