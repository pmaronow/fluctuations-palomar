module

public import SKConstants.GaussianRotation
public import Mathlib.Analysis.Normed.Lp.PiLp

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
set_option maxHeartbeats 800000

namespace SKConstants.GaussianProposal

section Involution
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

def involutionSym (U : E ≃ₗᵢ[ℝ] E) : E →L[ℝ] E :=
  (1/2 : ℝ) • (ContinuousLinearMap.id ℝ E+U.toContinuousLinearEquiv.toContinuousLinearMap)

def involutionAnti (U : E ≃ₗᵢ[ℝ] E) : E →L[ℝ] E :=
  (1/2 : ℝ) • (ContinuousLinearMap.id ℝ E-U.toContinuousLinearEquiv.toContinuousLinearMap)

lemma involution_parts_norm_sq (U : E ≃ₗᵢ[ℝ] E) (t : E) :
    ‖involutionSym U t‖^2+‖involutionAnti U t‖^2 = ‖t‖^2 := by
  change ‖(1/2 : ℝ) • (t+U t)‖^2+‖(1/2 : ℝ) • (t-U t)‖^2 = _
  rw [norm_smul,norm_smul,mul_pow,mul_pow,norm_add_sq_real,norm_sub_sq_real,U.norm_map]
  norm_num
  ring

lemma involution_parts_dual (U : E ≃ₗᵢ[ℝ] E) (hU : ∀ x, U (U x)=x) (t : E) :
    (InnerProductSpace.toDualMap ℝ E t).comp (involutionSym U) =
        InnerProductSpace.toDualMap ℝ E (involutionSym U t) ∧
    (InnerProductSpace.toDualMap ℝ E t).comp (involutionAnti U) =
        InnerProductSpace.toDualMap ℝ E (involutionAnti U t) := by
  have hi (x : E) : U.symm x=U x := by
    apply U.injective
    rw [U.apply_symm_apply,hU]
  have hs (x : E) : ⟪t,U x⟫_ℝ=⟪U t,x⟫_ℝ := by
    calc
      _ = ⟪U x,t⟫_ℝ := real_inner_comm _ _
      _ = ⟪x,U.symm t⟫_ℝ := U.inner_map_eq_flip x t
      _ = _ := by rw [hi]; exact real_inner_comm _ _
  constructor <;> apply ContinuousLinearMap.ext <;> intro x
  · change ⟪t,(1/2 : ℝ) • (x+U x)⟫_ℝ = ⟪(1/2 : ℝ) • (t+U t),x⟫_ℝ
    simp only [inner_smul_right,real_inner_smul_left,inner_add_right,inner_add_left,hs]
  · change ⟪t,(1/2 : ℝ) • (x-U x)⟫_ℝ = ⟪(1/2 : ℝ) • (t-U t),x⟫_ℝ
    simp only [inner_smul_right,real_inner_smul_left,inner_sub_right,inner_sub_left,hs]

theorem stdGaussian_involution_split (U : E ≃ₗᵢ[ℝ] E) (hU : ∀ x, U (U x)=x) :
    ((stdGaussian E).prod (stdGaussian E)).map
      (fun p => involutionSym U p.1+involutionAnti U p.2) = stdGaussian E := by
  have hm : ((stdGaussian E).prod (stdGaussian E)).map
      (fun p => involutionSym U p.1+involutionAnti U p.2) =
      ((stdGaussian E).map (involutionSym U)) ∗ ((stdGaussian E).map (involutionAnti U)) := by
    rw [Measure.conv,Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [hm]
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_conv,charFun_eq_charFunDual_toDualMap,charFun_eq_charFunDual_toDualMap,
    charFunDual_map,charFunDual_map,(involution_parts_dual U hU t).1,
    (involution_parts_dual U hU t).2,charFunDual_stdGaussian,charFunDual_stdGaussian,
    charFun_stdGaussian,←Complex.exp_add]
  rw [←InnerProductSpace.toDual_apply_eq_toDualMap_apply,
    ←InnerProductSpace.toDual_apply_eq_toDualMap_apply]
  simp only [LinearIsometryEquiv.norm_map]
  congr 1
  have hn := congrArg Complex.ofReal (involution_parts_norm_sq U t)
  push_cast at hn
  linear_combination -(1/2 : ℂ)*hn

end Involution

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def matrixTransposeIsometry : EuclideanSpace ℝ (ι × ι) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (ι × ι) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.prodComm ι ι)

lemma matrixTransposeIsometry_apply (z : EuclideanSpace ℝ (ι × ι)) (i j : ι) :
    matrixTransposeIsometry z (i,j)=z (j,i) := rfl

def primitiveLift (sigma : ℝ) (W : Matrix ι ι ℝ) (A : EuclideanSpace ℝ (ι × ι)) :
    EuclideanSpace ℝ (ι × ι) :=
  WithLp.toLp 2 (fun p => W p.1 p.2/(2*sigma)+(A p-A (p.2,p.1))/2)

lemma measurable_primitiveLift (sigma : ℝ) :
    Measurable (Function.uncurry (primitiveLift (ι := ι) sigma)) := by
  apply (WithLp.measurable_toLp 2 _).comp
  apply Measurable.of_eval
  intro p
  have hW : Measurable (fun q : Matrix ι ι ℝ × EuclideanSpace ℝ (ι × ι) => q.1 p.1 p.2) :=
    by fun_prop
  have hA (r : ι × ι) : Measurable (fun q : Matrix ι ι ℝ × EuclideanSpace ℝ (ι × ι) => q.2 r) :=
    (EuclideanSpace.proj r).continuous.measurable.comp measurable_snd
  exact (hW.div_const (2*sigma)).add (((hA p).sub (hA (p.2,p.1))).div_const 2)

theorem goeMatrix_primitiveLift (sigma : ℝ) (hsigma : sigma ≠ 0)
    (W : Matrix ι ι ℝ) (hW : W.IsSymm) (A : EuclideanSpace ℝ (ι × ι)) :
    goeMatrix sigma (primitiveLift sigma W A)=W := by
  ext i j
  have hs : W j i=W i j := congrFun (congrFun hW i) j
  simp only [goeMatrix,primitiveLift,WithLp.ofLp_toLp]
  rw [hs]
  field_simp
  ring

theorem primitiveLift_goe_eq_split (sigma : ℝ) (hsigma : sigma ≠ 0)
    (g A : EuclideanSpace ℝ (ι × ι)) :
    primitiveLift sigma (goeMatrix sigma g) A =
      involutionSym matrixTransposeIsometry g+involutionAnti matrixTransposeIsometry A := by
  ext p
  rcases p with ⟨i,j⟩
  change sigma*(g (i,j)+g (j,i))/(2*sigma)+(A (i,j)-A (j,i))/2 =
    (1/2 : ℝ)*(g (i,j)+g (j,i))+(1/2 : ℝ)*(A (i,j)-A (j,i))
  field_simp

theorem primitiveLift_goe_law (sigma : ℝ) (hsigma : sigma ≠ 0) :
    (((primitiveGaussian (ι × ι)).map (goeMatrix sigma)).prod (primitiveGaussian (ι × ι))).map
      (Function.uncurry (primitiveLift sigma)) = primitiveGaussian (ι × ι) := by
  have hu (g : EuclideanSpace ℝ (ι × ι)) : matrixTransposeIsometry (matrixTransposeIsometry g)=g := by
    ext p
    rfl
  have hm : ((primitiveGaussian (ι × ι)).map (goeMatrix sigma)).prod (primitiveGaussian (ι × ι)) =
      ((primitiveGaussian (ι × ι)).prod (primitiveGaussian (ι × ι))).map (Prod.map (goeMatrix sigma) id) := by
    simpa only [Measure.map_id] using
      (Measure.map_prod_map (primitiveGaussian (ι × ι)) (primitiveGaussian (ι × ι))
        (continuous_goeMatrix sigma).measurable
        (measurable_id : Measurable (id : EuclideanSpace ℝ (ι × ι) → _)))
  have hprod : Measurable (Prod.map (goeMatrix (ι := ι) sigma)
      (id : EuclideanSpace ℝ (ι × ι) → EuclideanSpace ℝ (ι × ι))) :=
    (continuous_goeMatrix sigma).measurable.prodMap measurable_id
  rw [hm,Measure.map_map (measurable_primitiveLift sigma)
      hprod]
  have he : (Function.uncurry (primitiveLift sigma)) ∘ Prod.map (goeMatrix sigma) id =
      fun p : EuclideanSpace ℝ (ι × ι) × EuclideanSpace ℝ (ι × ι) =>
        involutionSym matrixTransposeIsometry p.1+involutionAnti matrixTransposeIsometry p.2 := by
    funext p
    exact primitiveLift_goe_eq_split sigma hsigma p.1 p.2
  rw [he]
  exact stdGaussian_involution_split (matrixTransposeIsometry (ι := ι)) hu

end SKConstants.GaussianProposal
