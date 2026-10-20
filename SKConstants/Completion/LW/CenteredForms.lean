module

public import SKConstants.Completion.LW.DyadicProductProducer
public import SKConstants.Completion.LW.SevenFamilies

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal InnerProductSpace

namespace SKConstants.Completion.LW
open Concentration
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem centeredObservable_const_mul (F : Ω → ℝ) (c : ℝ) (ω : Ω) :
    centeredObservable μ (fun z => c*F z) ω = c*centeredObservable μ F ω := by
  unfold centeredObservable
  rw [integral_const_mul]
  ring

theorem centeredObservable_finsetSum {ι : Type*} (I : Finset ι) (F : ι → Ω → ℝ)
    (hF : ∀ i ∈ I, Integrable (F i) μ) (ω : Ω) :
    centeredObservable μ (fun z => ∑ i ∈ I, F i z) ω =
      ∑ i ∈ I, centeredObservable μ (F i) ω := by
  unfold centeredObservable
  rw [integral_finsetSum I hF, Finset.sum_sub_distrib]

theorem projection_product_eq_sum {k : ℕ}
    (x y a b : EuclideanSpace ℝ (Fin k)) :
    ⟪x,a⟫_ℝ * ⟪y,b⟫_ℝ = ∑ i, ∑ j, (a i*b j)*(x i*y j) := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply, star_trivial]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

def centeredCrossMatrix {k : ℕ} (X Y : Ω → EuclideanSpace ℝ (Fin k))
    (μ : Measure Ω) (ω : Ω) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => X ω i*Y ω j - ∫ z, X z i*Y z j ∂μ

theorem centeredCrossMatrix_bilinear {k : ℕ}
    (X Y : Ω → EuclideanSpace ℝ (Fin k))
    (hInt : ∀ i j, Integrable (fun z => X z i*Y z j) μ)
    (a b : EuclideanSpace ℝ (Fin k)) (ω : Ω) :
    ⟪a,Matrix.toEuclideanCLM (𝕜 := ℝ) (centeredCrossMatrix X Y μ ω) b⟫_ℝ =
      centeredObservable μ (fun z => ⟪X z,a⟫_ℝ * ⟪Y z,b⟫_ℝ) ω := by
  have he := fun z => projection_product_eq_sum (X z) (Y z) a b
  simp_rw [he]
  rw [centeredObservable_finsetSum Finset.univ _ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => (hInt i j).const_mul _))]
  simp_rw [centeredObservable_finsetSum Finset.univ _ (fun j _ => (hInt _ j).const_mul _),
    centeredObservable_const_mul]
  rw [Matrix.inner_toEuclideanCLM]
  simp only [dotProduct, Matrix.mulVec, centeredCrossMatrix, Finset.mul_sum, centeredObservable]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem strictUpper_bilinear_eq_dyadic_blocks (r : ℕ)
    (M : Matrix (Fin (2^r)) (Fin (2^r)) ℝ)
    (a b : EuclideanSpace ℝ (Fin (2^r))) :
    ⟪a,Matrix.toEuclideanCLM (𝕜 := ℝ) (strictUpperTruncation M) b⟫_ℝ =
      ∑ i : DyadicCore.Node r, ⟪coordinateProjection (dyadicLeft r i) a,
        Matrix.toEuclideanCLM (𝕜 := ℝ) M (coordinateProjection (dyadicRight r i) b)⟫_ℝ := by
  rw [strictUpperTruncation_inner_eq]
  rw [← (dyadic_rectangle_cover r).2, Finset.sum_biUnion (dyadic_rectangle_cover r).1]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_product, coordinateProjection_eq_sum, coordinateProjection_eq_sum]
  simp only [map_sum, map_smul, sum_inner, inner_sum]
  exact Finset.sum_comm

theorem halfUpper_bilinear_eq_blocks (r : ℕ)
    (M : Matrix (Fin (2^r)) (Fin (2^r)) ℝ)
    (a b : EuclideanSpace ℝ (Fin (2^r))) :
    ⟪a,Matrix.toEuclideanCLM (𝕜 := ℝ) (halfUpperTruncation M) b⟫_ℝ =
      ∑ i : UpperProductIndex r, upperProductFactor r i *
        ⟪coordinateProjection (upperProductLeft r i) a,
          Matrix.toEuclideanCLM (𝕜 := ℝ) M (coordinateProjection (upperProductRight r i) b)⟫_ℝ := by
  rw [halfUpperTruncation_eq, map_add, add_apply, inner_add_right,
    strictUpper_bilinear_eq_dyadic_blocks]
  simp only [Fintype.sum_sum_type, upperProductLeft, upperProductRight, upperProductFactor,
    one_mul]
  congr 1
  rw [Matrix.inner_toEuclideanCLM]
  simp only [Matrix.mulVec_diagonal, dotProduct, coordinateProjection_singleton,
    map_smul, inner_smul_left, inner_smul_right, EuclideanSpace.inner_single_left,
    matrix_column_apply, map_one, one_mul]
  apply Finset.sum_congr rfl
  intro j _
  simp only [starRingEnd_apply, star_trivial]
  ring

theorem halfUpper_transpose_bilinear_eq_blocks (r : ℕ)
    (M : Matrix (Fin (2^r)) (Fin (2^r)) ℝ)
    (a b : EuclideanSpace ℝ (Fin (2^r))) :
    ⟪a,Matrix.toEuclideanCLM (𝕜 := ℝ) (halfUpperTruncation M).transpose b⟫_ℝ =
      ∑ i : UpperProductIndex r, upperProductFactor r i *
        ⟪coordinateProjection (upperProductRight r i) a,
          Matrix.toEuclideanCLM (𝕜 := ℝ) M.transpose (coordinateProjection (upperProductLeft r i) b)⟫_ℝ := by
  rw [real_inner_comm, matrix_transpose_inner,
    halfUpper_bilinear_eq_blocks]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  symm
  rw [real_inner_comm, matrix_transpose_inner]

theorem centeredCrossMatrix_self_symmetric {k : ℕ}
    (T : Ω → EuclideanSpace ℝ (Fin k)) (ω : Ω) :
    (centeredCrossMatrix T T μ ω).transpose = centeredCrossMatrix T T μ ω := by
  ext i j
  simp only [centeredCrossMatrix, Matrix.transpose_apply, mul_comm]

theorem centered_halfUpper_form_eq_productSum
    {μ : Measure Ω} (r : ℕ) (T : Ω → EuclideanSpace ℝ (Fin (2^r)))
    (hInt : ∀ i j, Integrable (fun z => T z i*T z j) μ)
    (a w : EuclideanSpace ℝ (Fin (2^r))) (J : Finset (Fin (2^r)))
    (transpose : Bool) (ω : Ω) :
    ⟪a,Matrix.toEuclideanCLM (𝕜 := ℝ)
      (if transpose then (halfUpperTruncation (centeredCrossMatrix T T μ ω)).transpose
        else halfUpperTruncation (centeredCrossMatrix T T μ ω)) (coordinateProjection J w)⟫_ℝ =
    centeredBlockProductSum T μ
      (if transpose then upperProductRight r else upperProductLeft r)
      (if transpose then upperProductLeft r else upperProductRight r)
      (upperProductFactor r) a w J ω := by
  cases transpose <;> simp only [Bool.false_eq_true, if_false, if_true]
  all_goals
    first | rw [halfUpper_bilinear_eq_blocks] | rw [halfUpper_transpose_bilinear_eq_blocks]
    simp only [centeredCrossMatrix_self_symmetric, coordinateProjection_inter,
      centeredCrossMatrix_bilinear T T hInt]
    unfold centeredBlockProductSum
    apply Finset.sum_congr rfl
    intro i _
    rw [← centeredObservable_const_mul]
    congr 1
    funext z
    ring

end SKConstants.Completion.LW
