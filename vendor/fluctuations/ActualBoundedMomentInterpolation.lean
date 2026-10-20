module

public import Mathlib

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace OAI.SKFluctuations.Hierarchy

 theorem integral_square_interpolation_of_bounded {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (Z : Ω → ℝ)
    (hZ : Measurable Z) (hZ0 : ∀ x, 0≤Z x) {B p : ℝ}
    (hB : 0≤B) (hZB : ∀ x, Z x≤B) (hp : 2<p) :
    (∫ x, (Z x)^2 ∂μ) ≤
      (∫ x, Z x ∂μ)^((p-2)/(p-1))*(∫ x, (Z x)^p ∂μ)^(1/(p-1)) := by
  have hp1 : 0<p-1 := by linarith
  have hp2 : 0<p-2 := by linarith
  let a := (p-2)/(p-1)
  let b := p/(p-1)
  have ha : 0≤a := by dsimp [a]; positivity
  have hb : 0≤b := by dsimp [b]; positivity
  have hconj : ((p-1)/(p-2)).HolderConjugate (p-1) := by
    rw [Real.holderConjugate_iff]
    constructor
    · apply (one_lt_div hp2).mpr
      linarith
    · field_simp
      <;> ring
  have hFm : MemLp (fun x => (Z x)^a) (ENNReal.ofReal ((p-1)/(p-2))) μ := by
    apply MemLp.of_bound (hZ.pow_const a).aestronglyMeasurable (B^a)
    exact Eventually.of_forall fun x=>by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (hZ0 x) _)]
      exact Real.rpow_le_rpow (hZ0 x) (hZB x) ha
  have hGm : MemLp (fun x => (Z x)^b) (ENNReal.ofReal (p-1)) μ := by
    apply MemLp.of_bound (hZ.pow_const b).aestronglyMeasurable (B^b)
    exact Eventually.of_forall fun x=>by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (hZ0 x) _)]
      exact Real.rpow_le_rpow (hZ0 x) (hZB x) hb
  have H := integral_mul_le_Lp_mul_Lq_of_nonneg hconj
    (Eventually.of_forall fun x=>Real.rpow_nonneg (hZ0 x) a)
    (Eventually.of_forall fun x=>Real.rpow_nonneg (hZ0 x) b) hFm hGm
  have hab : a+b=2 := by dsimp [a,b]; field_simp; ring
  have haexp : a*((p-1)/(p-2))=1 := by dsimp [a]; field_simp
  have hbexp : b*(p-1)=p := by dsimp [b]; field_simp
  have hF (x : Ω) : ((Z x)^a)^((p-1)/(p-2))=Z x := by
    rw [←Real.rpow_mul (hZ0 x),haexp,Real.rpow_one]
  have hG (x : Ω) : ((Z x)^b)^(p-1)=(Z x)^p := by
    rw [←Real.rpow_mul (hZ0 x),hbexp]
  have hFG (x : Ω) : (Z x)^a*(Z x)^b=(Z x)^2 := by
    rw [←Real.rpow_add_of_nonneg (hZ0 x) ha hb,hab,Real.rpow_two]
  have hinv : 1/((p-1)/(p-2))=(p-2)/(p-1) := by field_simp
  simpa only [hF,hG,hFG,hinv] using H

end OAI.SKFluctuations.Hierarchy
