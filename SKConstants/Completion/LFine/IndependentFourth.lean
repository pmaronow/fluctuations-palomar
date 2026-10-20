module

public import SKConstants.Completion.LFine.ProjectionMoments
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace SKConstants.Completion.LFine
variable {Ω ι : Type*} [MeasurableSpace Ω]
local instance fineHolderFourFourTwo : ENNReal.HolderTriple 4 4 2 := ⟨by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add]⟩

theorem memLp_square_of_four (μ : Measure Ω) (X : Ω → ℝ) (hX : MemLp X 4 μ) :
    MemLp (fun ω => X ω^2) 2 μ := by
  have h : MemLp (X*X) 2 μ := hX.mul hX
  convert h using 1
  funext ω
  exact pow_two _

theorem integrable_fourth_of_memLp (μ : Measure Ω) (X : Ω → ℝ) (hX : MemLp X 4 μ) :
    Integrable (fun ω => X ω^4) μ := by
  have h := (memLp_square_of_four μ X hX).integrable_sq
  convert h using 1
  funext ω
  ring

theorem independent_add_fourth (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ) (hX : MemLp X 4 μ) (hY : MemLp Y 4 μ)
    (hind : IndepFun X Y μ) (hEX : (∫ ω, X ω ∂μ) = 0) (hEY : (∫ ω, Y ω ∂μ) = 0) :
    (∫ ω, (X ω+Y ω)^4 ∂μ) =
      (∫ ω, X ω^4 ∂μ) + 6*(∫ ω, X ω^2 ∂μ)*(∫ ω, Y ω^2 ∂μ) +
        (∫ ω, Y ω^4 ∂μ) := by
  have hX₂ := memLp_square_of_four μ X hX
  have hY₂ := memLp_square_of_four μ Y hY
  have hXY : MemLp (fun ω => X ω*Y ω) 2 μ := hX.mul hY
  have h31 : Integrable (fun ω => X ω^3*Y ω) μ := by
    have h := hX₂.integrable_mul hXY
    convert h using 1
    funext ω
    simp only [Pi.mul_apply]
    ring
  have h13 : Integrable (fun ω => X ω*Y ω^3) μ := by
    have h := hXY.integrable_mul hY₂
    convert h using 1
    funext ω
    simp only [Pi.mul_apply]
    ring
  have h22 : Integrable (fun ω => X ω^2*Y ω^2) μ := hX₂.integrable_mul hY₂
  have h31mean : (∫ ω, X ω^3*Y ω ∂μ) = 0 := by
    have h := (hind.comp (show Measurable (fun x : ℝ => x^3) from by fun_prop)
      measurable_id).integral_fun_mul_eq_mul_integral
        (hX.aestronglyMeasurable.pow 3) hY.aestronglyMeasurable
    change (∫ ω, X ω^3*Y ω ∂μ) = (∫ ω, X ω^3 ∂μ)*(∫ ω, Y ω ∂μ) at h
    simpa [hEY] using h
  have h13mean : (∫ ω, X ω*Y ω^3 ∂μ) = 0 := by
    have h := (hind.comp measurable_id
      (show Measurable (fun y : ℝ => y^3) from by fun_prop)).integral_fun_mul_eq_mul_integral
        hX.aestronglyMeasurable (hY.aestronglyMeasurable.pow 3)
    change (∫ ω, X ω*Y ω^3 ∂μ) = (∫ ω, X ω ∂μ)*(∫ ω, Y ω^3 ∂μ) at h
    simpa [hEX] using h
  have h22mean : (∫ ω, X ω^2*Y ω^2 ∂μ) =
      (∫ ω, X ω^2 ∂μ)*(∫ ω, Y ω^2 ∂μ) := by
    exact (hind.comp (show Measurable (fun x : ℝ => x^2) from by fun_prop)
      (show Measurable (fun y : ℝ => y^2) from by fun_prop)).integral_fun_mul_eq_mul_integral
        (hX.aestronglyMeasurable.pow 2) (hY.aestronglyMeasurable.pow 2)
  have hfun (ω : Ω) : (X ω+Y ω)^4 =
      X ω^4+4*(X ω^3*Y ω)+6*(X ω^2*Y ω^2)+4*(X ω*Y ω^3)+Y ω^4 := by ring
  simp_rw [hfun]
  have h4X := integrable_fourth_of_memLp μ X hX
  have h4Y := integrable_fourth_of_memLp μ Y hY
  rw [integral_add (f := fun ω => X ω^4+4*(X ω^3*Y ω)+6*(X ω^2*Y ω^2)+4*(X ω*Y ω^3))
      (g := fun ω => Y ω^4)
      (((h4X.add (h31.const_mul 4)).add (h22.const_mul 6)).add (h13.const_mul 4)) h4Y,
    integral_add (f := fun ω => X ω^4+4*(X ω^3*Y ω)+6*(X ω^2*Y ω^2))
      (g := fun ω => 4*(X ω*Y ω^3))
      ((h4X.add (h31.const_mul 4)).add (h22.const_mul 6)) (h13.const_mul 4),
    integral_add (f := fun ω => X ω^4+4*(X ω^3*Y ω))
      (g := fun ω => 6*(X ω^2*Y ω^2))
      (h4X.add (h31.const_mul 4)) (h22.const_mul 6),
    integral_add (f := fun ω => X ω^4) (g := fun ω => 4*(X ω^3*Y ω)) h4X (h31.const_mul 4)]
  simp only [integral_const_mul, h31mean, h13mean, h22mean]
  ring

variable [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem independent_centered_sum_fourth_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) (hm : ∀ i, Measurable (X i)) (hX : ∀ i, MemLp (X i) 4 μ)
    (hind : iIndepFun X μ) (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (v : ι → ℝ) (hv : ∀ i, 0 ≤ v i)
    (hsecond : ∀ i, (∫ ω, X i ω^2 ∂μ) ≤ v i)
    (hfourth : ∀ i, (∫ ω, X i ω^4 ∂μ) ≤ 3*v i^2)
    (s : Finset ι) :
    (∫ ω, (∑ i ∈ s, X i ω)^4 ∂μ) ≤ 3*(∑ i ∈ s, v i)^2 := by
  have hsecondSum (s : Finset ι) :
      (∫ ω, (∑ i ∈ s, X i ω)^2 ∂μ) ≤ ∑ i ∈ s, v i := by
    have hi : iIndepFun (fun i : s => X i) μ := hind.precomp Subtype.val_injective
    have he := centered_linear_second_moment μ (fun i : s => X i)
      (fun i => (hX i).mono_exponent (by norm_num)) hi (fun i => hcenter i)
      (fun _ => 1)
    simp only [one_pow, one_mul] at he
    have hbound : (∑ i : s, (∫ ω, X i ω^2 ∂μ)) ≤ ∑ i : s, v i :=
      Finset.sum_le_sum (fun i _ => hsecond i)
    have he' := he.trans_le hbound
    convert he' using 1
    · congr 1
      funext ω
      rw [Finset.sum_coe_sort s (fun i => X i ω)]
    · rw [Finset.sum_coe_sort s v]
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
    let S : Ω → ℝ := fun ω => ∑ j ∈ s, X j ω
    have hS : MemLp S 4 μ := memLp_finsetSum s (fun j _ => hX j)
    have hi := hind.indepFun_finsetSum_of_notMem hm his
    have hSfun : (∑ j ∈ s, X j) = S := by
      ext ω
      simp only [Finset.sum_apply, S]
    have hi' : IndepFun S (X i) μ := by rw [hSfun] at hi; exact hi
    have hmean : (∫ ω, S ω ∂μ) = 0 := by
      rw [show S = fun ω => ∑ j ∈ s, X j ω from rfl,
        integral_finsetSum _ (fun j _ => (hX j).integrable (by norm_num))]
      simp only [hcenter, Finset.sum_const_zero]
    have he := independent_add_fourth μ S (X i) hS (hX i) hi' hmean (hcenter i)
    have hfun : (fun ω => (∑ j ∈ insert i s, X j ω)^4) =
        (fun ω => (S ω+X i ω)^4) := by
      funext ω
      rw [Finset.sum_insert his, add_comm]
    rw [hfun, he, Finset.sum_insert his]
    have hsec : 0 ≤ ∫ ω, S ω^2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
    have hseci : 0 ≤ ∫ ω, X i ω^2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
    have hsum : 0 ≤ ∑ j ∈ s, v j := Finset.sum_nonneg (fun j _ => hv j)
    have hprod := mul_le_mul (hsecondSum s) (hsecond i) hseci hsum
    dsimp only [S] at he hsec hprod ⊢
    nlinarith [hfourth i]

theorem centered_linear_fourth_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : ι → Ω → ℝ) (hm : ∀ i, Measurable (T i)) (hT : ∀ i, MemLp (T i) 4 μ)
    (hind : iIndepFun T μ) (hcenter : ∀ i, ∫ ω, T i ω ∂μ = 0)
    (v : ℝ) (hv : 0 ≤ v)
    (hsecond : ∀ i, (∫ ω, T i ω^2 ∂μ) ≤ v)
    (hfourth : ∀ i, (∫ ω, T i ω^4 ∂μ) ≤ 3*v^2)
    (a : ι → ℝ) :
    (∫ ω, (∑ i, a i*T i ω)^4 ∂μ) ≤ 3*v^2*(∑ i, a i^2)^2 := by
  let X : ι → Ω → ℝ := fun i ω => a i*T i ω
  have hxmean (i : ι) : (∫ ω, X i ω ∂μ) = 0 := by
    rw [show X i = fun ω => a i*T i ω from rfl, integral_const_mul, hcenter, mul_zero]
  have hxsecond (i : ι) : (∫ ω, X i ω^2 ∂μ) ≤ v*a i^2 := by
    simp only [X, mul_pow, integral_const_mul]
    nlinarith [mul_le_mul_of_nonneg_left (hsecond i) (sq_nonneg (a i))]
  have hxfourth (i : ι) : (∫ ω, X i ω^4 ∂μ) ≤ 3*(v*a i^2)^2 := by
    simp only [X, mul_pow, integral_const_mul]
    nlinarith [mul_le_mul_of_nonneg_left (hfourth i) (show 0 ≤ a i^4 by positivity)]
  have hi : iIndepFun X μ := hind.comp (fun i t => a i*t) (fun i => by fun_prop)
  have he := independent_centered_sum_fourth_le μ X (fun i => (hm i).const_mul _)
    (fun i => (hT i).const_mul _) hi hxmean (fun i => v*a i^2)
    (fun i => mul_nonneg hv (sq_nonneg _)) hxsecond hxfourth Finset.univ
  simp only [← Finset.mul_sum] at he
  convert he using 1
  ring

theorem projection_fourth_moment_of_coordinates (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : ι → Ω → ℝ) (hm : ∀ i, Measurable (T i)) (hT : ∀ i, MemLp (T i) 4 μ)
    (hind : iIndepFun T μ) (hcenter : ∀ i, ∫ ω, T i ω ∂μ = 0)
    (v : ℝ) (hv : 0 ≤ v)
    (hsecond : ∀ i, (∫ ω, T i ω^2 ∂μ) ≤ v)
    (hfourth : ∀ i, (∫ ω, T i ω^4 ∂μ) ≤ 3*v^2)
    (r : ℕ) (E : Fin r → ι → ℝ) (hrow : ∀ j, ∑ i, E j i^2 = 1)
    (N : ℝ) :
    (∫ ω, (N⁻¹*∑ j, (∑ i, E j i*T i ω)^2)^2 ∂μ) ≤
      3*(r : ℝ)^2*v^2/N^2 := by
  let A : Fin r → Ω → ℝ := fun j ω => ∑ i, E j i*T i ω
  have hA (j : Fin r) : MemLp (A j) 4 μ :=
    memLp_finsetSum _ (fun i _ => (hT i).const_mul _)
  have hA₂ : MemLp (fun ω => ∑ j, A j ω^2) 2 μ :=
    memLp_finsetSum _ (fun j _ => memLp_square_of_four μ (A j) (hA j))
  apply projection_fourth_moment_le μ r A
    (fun j => integrable_fourth_of_memLp μ (A j) (hA j)) hA₂.integrable_sq v
  intro j
  simpa only [hrow, one_pow, mul_one] using
    centered_linear_fourth_le μ T hm hT hind hcenter v hv hsecond hfourth (E j)

end SKConstants.Completion.LFine
