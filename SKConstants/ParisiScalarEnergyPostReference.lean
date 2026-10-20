module

public import SKConstants.ParisiScalarEnergyPreReference

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.SK.Analytic ParisiFullSupport
variable {Ω : Type*} [MeasurableSpace Ω]

lemma actualParisiEnergyIntegrand_post (W : BrownianSystem Ω) (β : ℝ) (hβ : 1<β)
    (v : ℝ) (hv : 0≤v) :
    Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β
      ((parisiEquilibriumPhysicalEndpoint β:ℝ)+v))*
      actualParisiFullSusceptibilityExpected W β ((parisiEquilibriumPhysicalEndpoint β:ℝ)+v)*
      actualParisiQueryRho W β ((parisiEquilibriumPhysicalEndpoint β:ℝ)+v)=
        β*(actualParisiContinuationR W β v*actualParisiContinuationP W β v) := by
  have HR := actualParisiFullSusceptibilitySquareExpected_post W β hβ
    (parisiEquilibriumPhysicalEndpoint β+v.toNNReal) (le_add_of_nonneg_right (by positivity))
  simp only [NNReal.coe_add,Real.coe_toNNReal v hv,add_tsub_cancel_left] at HR
  rw [HR,actualParisiFullSusceptibilityExpected_post W β hβ v hv]
  simp only [actualParisiQueryRho,add_sub_cancel_left,actualParisiPostRho]
  calc
    Real.sqrt (actualParisiContinuationR W β v)*actualParisiContinuationP W β v*
      (β*Real.sqrt (actualParisiContinuationR W β v))=
        β*(Real.sqrt (actualParisiContinuationR W β v))^2*actualParisiContinuationP W β v := by ring
    _ = _ := by rw [Real.sq_sqrt (actualParisiContinuationR_pos W β v).le];ring

lemma actualParisiEntropyIntegrand_post (W : BrownianSystem Ω) (β : ℝ) (hβ : 1<β)
    (v : ℝ) (hv : 0≤v) :
    (actualParisiQueryRho W β ((parisiEquilibriumPhysicalEndpoint β:ℝ)+v))^2*
      actualParisiFullEntropyRateExpected W β ((parisiEquilibriumPhysicalEndpoint β:ℝ)+v)=
        β^2*(actualParisiContinuationR W β v*actualParisiContinuationP W β v) := by
  rw [actualParisiFullEntropyRateExpected_post W β hβ v hv]
  simp only [actualParisiQueryRho,add_sub_cancel_left,actualParisiPostRho_sq]
  ring

theorem actualParisiEnergyReference_post_increment (W : BrownianSystem Ω) (β : ℝ) (hβ : 1<β)
    (S : ℝ) (hS : 0≤S) :
    actualParisiEnergyReference W β ((parisiEquilibriumPhysicalEndpoint β:ℝ)+S)=
      actualParisiEnergyReference W β (parisiEquilibriumPhysicalEndpoint β)+
        β*(∫ v in 0..S,actualParisiContinuationR W β v*actualParisiContinuationP W β v) := by
  let V : ℝ := parisiEquilibriumPhysicalEndpoint β
  let f := fun v => Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β v)*
    actualParisiFullSusceptibilityExpected W β v*actualParisiQueryRho W β v
  have HI := intervalIntegral.integral_add_adjacent_intervals
    (actualParisiEnergyIntegrand_intervalIntegrable W β 0 V)
    (actualParisiEnergyIntegrand_intervalIntegrable W β V (V+S))
  have HP : (∫ v in V..V+S,f v)=β*(∫ v in 0..S,actualParisiContinuationR W β v*actualParisiContinuationP W β v) := by
    have HC := intervalIntegral.integral_comp_add_left (a:=0) (b:=S) f V
    simp only [add_zero] at HC
    rw [←HC,←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hS] at hv
    exact actualParisiEnergyIntegrand_post W β hβ v hv.1
  change (∫ v in 0..V+S,f v)=(∫ v in 0..V,f v)+_
  rw [←HI,HP]

theorem actualParisiEntropyReference_post_increment (W : BrownianSystem Ω) (β : ℝ) (hβ : 1<β)
    (S : ℝ) (hS : 0≤S) :
    actualParisiEntropyReference W β ((parisiEquilibriumPhysicalEndpoint β:ℝ)+S)=
      actualParisiEntropyReference W β (parisiEquilibriumPhysicalEndpoint β)+
        (β^2/2)*(∫ v in 0..S,actualParisiContinuationR W β v*actualParisiContinuationP W β v) := by
  let V : ℝ := parisiEquilibriumPhysicalEndpoint β
  let f := fun v => (actualParisiQueryRho W β v)^2*actualParisiFullEntropyRateExpected W β v
  have HI := intervalIntegral.integral_add_adjacent_intervals
    (actualParisiEntropyIntegrand_intervalIntegrable W β 0 V)
    (actualParisiEntropyIntegrand_intervalIntegrable W β V (V+S))
  have HP : (∫ v in V..V+S,f v)=β^2*(∫ v in 0..S,actualParisiContinuationR W β v*actualParisiContinuationP W β v) := by
    have HC := intervalIntegral.integral_comp_add_left (a:=0) (b:=S) f V
    simp only [add_zero] at HC
    rw [←HC,←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hS] at hv
    exact actualParisiEntropyIntegrand_post W β hβ v hv.1
  change (1/2:ℝ)*(∫ v in 0..V+S,f v)=(1/2:ℝ)*(∫ v in 0..V,f v)+_
  rw [←HI,HP]
  ring

theorem actualParisiContinuationRP_square_balance (W : BrownianSystem Ω) (β : ℝ) (hβ : 1<β)
    (S : ℝ) (hS : 0≤S) :
    (∫ v in 0..S,actualParisiContinuationR W β v*actualParisiContinuationP W β v)=
      ((actualParisiContinuationP W β 0)^2-(actualParisiContinuationP W β S)^2)/2 := by
  have HD (v : ℝ) (hv : v∈Ioo 0 S) :
      HasDerivWithinAt (fun u => (actualParisiContinuationP W β u)^2)
        (-2*(actualParisiContinuationR W β v*actualParisiContinuationP W β v)) (Ioi v) v := by
    convert (actualParisiContinuationP_hasDerivWithinAt_right W β hβ v hv.1.le).fun_pow 2 using 1
    simp only [Nat.cast_ofNat,Nat.reduceSub,pow_one]
    ring
  have H := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hS
    ((continuous_actualParisiContinuationP W β).pow 2).continuousOn HD
    ((((continuous_actualParisiContinuationR W β).mul (continuous_actualParisiContinuationP W β)).const_mul (-2)).intervalIntegrable 0 S)
  rw [intervalIntegral.integral_const_mul] at H
  change -2*(∫ v in 0..S,actualParisiContinuationR W β v*actualParisiContinuationP W β v)=
    (actualParisiContinuationP W β S)^2-(actualParisiContinuationP W β 0)^2 at H
  linarith

end SKConstants
