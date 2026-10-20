module

public import SKConstants.ScalarProcessParisiRDerivative
public import SKConstants.ParisiPostMomentRatio
public import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω]
local instance ScalarProcessParisiRho_localInstance1 (W : BrownianSystem Ω) : IsProbabilityMeasure W.law := W.isProbability

theorem actualParisiContinuationThirdMoment_ge_three_quarters
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (v : ℝ) (hv : 0 ≤ v) :
    (3/4 : ℝ)*actualParisiContinuationR W β v ≤ actualParisiContinuationThirdMoment W β v := by
  let V := parisiEquilibriumPhysicalEndpoint β
  have hs : β^2*parisiEquilibriumSupportEndpoint β ≤ (V : ℝ)+v := by
    rw [show (V : ℝ)=β^2*parisiEquilibriumSupportEndpoint β from parisiEquilibriumPhysicalEndpoint_coe β hβ]
    linarith
  have H := actualParisiFullProcess_post_third_moment_ge W β hβ ((V : ℝ)+v) hs
  have he : ((V : ℝ)+v).toNNReal=V+v.toNNReal := by
    apply NNReal.eq
    rw [Real.coe_toNNReal _ (by positivity),NNReal.coe_add,Real.coe_toNNReal v hv]
  rw [he] at H
  rw [actualParisiContinuationR_eq_full_process_moment W β hβ v hv]
  exact H

theorem actualParisiContinuationR_antitoneOn
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) :
    AntitoneOn (actualParisiContinuationR W β) (Ici (0 : ℝ)) := by
  intro a ha b hb hab
  let f' := fun v => 4*actualParisiContinuationR W β v-6*actualParisiContinuationThirdMoment W β v
  have HD : ∀ x ∈ Ico a b, HasDerivWithinAt (actualParisiContinuationR W β) (f' x) (Ici x) x := by
    intro x hx
    exact (actualParisiContinuationR_hasDerivWithinAt_right W β hβ x (ha.trans hx.1)).Ici_of_Ioi
  have H := image_le_of_deriv_right_le_deriv_boundary
    (continuous_actualParisiContinuationR W β).continuousOn HD
    (B := fun _ => actualParisiContinuationR W β a) (B' := fun _ => 0) (by rfl)
    continuous_const.continuousOn (fun x _ => hasDerivWithinAt_const _ _ _) (by
      intro x hx
      have h := actualParisiContinuationThirdMoment_ge_three_quarters W β hβ x (ha.trans hx.1)
      have hr := (actualParisiContinuationR_pos W β x).le
      dsimp only [f']
      linarith)
  exact H ⟨hab,le_rfl⟩

theorem actualParisiContinuationR_clamp (W : BrownianSystem Ω) (β v : ℝ) :
    actualParisiContinuationR W β (v.toNNReal : ℝ)=actualParisiContinuationR W β v := by
  simp only [actualParisiContinuationR,scalarContinuationR,Real.toNNReal_coe]

theorem actualParisiContinuationR_antitone
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) : Antitone (actualParisiContinuationR W β) := by
  intro a b hab
  have H := actualParisiContinuationR_antitoneOn W β hβ a.toNNReal.coe_nonneg b.toNNReal.coe_nonneg
    (show (a.toNNReal : ℝ) ≤ b.toNNReal from Real.toNNReal_mono hab)
  simpa only [actualParisiContinuationR_clamp] using H

theorem actualParisiContinuationR_le_inverse_beta_sq
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (v : ℝ) :
    actualParisiContinuationR W β v ≤ 1/β^2 := by
  have H := actualParisiContinuationR_antitoneOn W β hβ (show (0 : ℝ) ∈ Ici 0 from le_rfl)
    v.toNNReal.coe_nonneg v.toNNReal.coe_nonneg
  simpa only [actualParisiContinuationR_zero W β hβ,actualParisiContinuationR_clamp] using H

def actualParisiPostRho (W : BrownianSystem Ω) (β v : ℝ) : ℝ :=
  β*Real.sqrt (actualParisiContinuationR W β v)

theorem actualParisiPostRho_sq (W : BrownianSystem Ω) (β v : ℝ) :
    (actualParisiPostRho W β v)^2=β^2*actualParisiContinuationR W β v := by
  rw [actualParisiPostRho,mul_pow,Real.sq_sqrt (actualParisiContinuationR_pos W β v).le]

theorem actualParisiPostRho_bounds (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (v : ℝ) :
    actualParisiPostRho W β v ∈ Icc (0 : ℝ) 1 := by
  have hb : 0 < β := zero_lt_one.trans hβ
  have hp : 0 ≤ actualParisiPostRho W β v := mul_nonneg hb.le (Real.sqrt_nonneg _)
  have hs : (actualParisiPostRho W β v)^2 ≤ 1 := by
    rw [actualParisiPostRho_sq]
    calc
      _ ≤ β^2*(1/β^2) := mul_le_mul_of_nonneg_left
        (actualParisiContinuationR_le_inverse_beta_sq W β hβ v) (sq_nonneg β)
      _ = 1 := by field_simp
  exact ⟨hp,by nlinarith⟩

theorem actualParisiPostRho_zero (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) :
    actualParisiPostRho W β 0=1 := by
  have H := actualParisiPostRho_sq W β 0
  rw [actualParisiContinuationR_zero W β hβ] at H
  have hb : β ≠ 0 := (zero_lt_one.trans hβ).ne'
  have he : β^2*(1/β^2)=1 := by field_simp
  rw [he] at H
  have hp := (actualParisiPostRho_bounds W β hβ 0).1
  nlinarith

theorem actualParisiPostRho_antitone (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) :
    Antitone (actualParisiPostRho W β) := by
  intro a b hab
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (actualParisiContinuationR_antitone W β hβ hab))
    (zero_lt_one.trans hβ).le

def actualParisiQueryRho (W : BrownianSystem Ω) (β v : ℝ) : ℝ :=
  actualParisiPostRho W β (v-(parisiEquilibriumPhysicalEndpoint β : ℝ))

def actualParisiQuerySigma (W : BrownianSystem Ω) (β v : ℝ) : ℝ :=
  Real.sqrt (1-(actualParisiQueryRho W β v)^2)

theorem continuous_actualParisiQueryRho (W : BrownianSystem Ω) (β : ℝ) :
    Continuous (actualParisiQueryRho W β) :=
  ((continuous_actualParisiContinuationR W β).sqrt.const_mul β).comp (continuous_id.sub continuous_const)

theorem continuous_actualParisiQuerySigma (W : BrownianSystem Ω) (β : ℝ) :
    Continuous (actualParisiQuerySigma W β) :=
  (continuous_const.sub ((continuous_actualParisiQueryRho W β).pow 2)).sqrt

theorem actualParisiQueryRho_antitone (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) :
    Antitone (actualParisiQueryRho W β) := by
  intro a b hab
  exact actualParisiPostRho_antitone W β hβ (sub_le_sub_right hab _)

theorem actualParisiQueryRho_bounds (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (v : ℝ) :
    actualParisiQueryRho W β v ∈ Icc (0 : ℝ) 1 := actualParisiPostRho_bounds W β hβ _

theorem actualParisiQuerySigma_monotone (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) :
    Monotone (actualParisiQuerySigma W β) := by
  intro a b hab
  apply Real.sqrt_le_sqrt
  have H := pow_le_pow_left₀ (actualParisiQueryRho_bounds W β hβ b).1
    (actualParisiQueryRho_antitone W β hβ hab) 2
  linarith

theorem actualParisiQueryRhoSigma_unit (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (v : ℝ) :
    (actualParisiQueryRho W β v)^2+(actualParisiQuerySigma W β v)^2=1 := by
  have H := actualParisiQueryRho_bounds W β hβ v
  have hs : 0 ≤ 1-(actualParisiQueryRho W β v)^2 := by nlinarith [H.1,H.2]
  rw [actualParisiQuerySigma,Real.sq_sqrt hs]
  ring

theorem actualParisiQuerySigma_bounds (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (v : ℝ) :
    actualParisiQuerySigma W β v ∈ Icc (0 : ℝ) 1 := by
  have hp : 0 ≤ actualParisiQuerySigma W β v := Real.sqrt_nonneg _
  have H := actualParisiQueryRhoSigma_unit W β hβ v
  exact ⟨hp,by nlinarith [sq_nonneg (actualParisiQueryRho W β v)]⟩

theorem actualParisiQueryRho_eq_one_pre (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (v : ℝ) (hv : v ≤ (parisiEquilibriumPhysicalEndpoint β : ℝ)) :
    actualParisiQueryRho W β v=1 := by
  have he : actualParisiContinuationR W β (v-(parisiEquilibriumPhysicalEndpoint β : ℝ))=
      actualParisiContinuationR W β 0 := by
    rw [← actualParisiContinuationR_clamp W β (v-(parisiEquilibriumPhysicalEndpoint β : ℝ)),
      Real.toNNReal_eq_zero.mpr (sub_nonpos.mpr hv),NNReal.coe_zero]
  simpa only [actualParisiQueryRho,actualParisiPostRho,he] using actualParisiPostRho_zero W β hβ

theorem actualParisiQuerySigma_eq_zero_pre (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (v : ℝ) (hv : v ≤ (parisiEquilibriumPhysicalEndpoint β : ℝ)) :
    actualParisiQuerySigma W β v=0 := by
  simp only [actualParisiQuerySigma,actualParisiQueryRho_eq_one_pre W β hβ v hv,
    one_pow,sub_self,Real.sqrt_zero]

def actualParisiNegativeRhoStieltjes (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) :
    StieltjesFunction ℝ where
  toFun v := -actualParisiQueryRho W β v
  mono' := fun _ _ hab => neg_le_neg (actualParisiQueryRho_antitone W β hβ hab)
  right_continuous' := fun _ => (continuous_actualParisiQueryRho W β).neg.continuousAt.continuousWithinAt

def actualParisiSigmaStieltjes (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) : StieltjesFunction ℝ where
  toFun := actualParisiQuerySigma W β
  mono' := actualParisiQuerySigma_monotone W β hβ
  right_continuous' := fun _ => (continuous_actualParisiQuerySigma W β).continuousAt.continuousWithinAt

theorem continuous_actualParisiNegativeRhoStieltjes (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) :
    Continuous (actualParisiNegativeRhoStieltjes W β hβ) := (continuous_actualParisiQueryRho W β).neg

theorem continuous_actualParisiSigmaStieltjes (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) :
    Continuous (actualParisiSigmaStieltjes W β hβ) := continuous_actualParisiQuerySigma W β

theorem actualParisiStieltjesCoefficients_unit (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (v : ℝ) :
    (actualParisiNegativeRhoStieltjes W β hβ v)^2+(actualParisiSigmaStieltjes W β hβ v)^2=1 := by
  simpa only [actualParisiNegativeRhoStieltjes,actualParisiSigmaStieltjes,neg_sq] using
    actualParisiQueryRhoSigma_unit W β hβ v

end SKConstants
