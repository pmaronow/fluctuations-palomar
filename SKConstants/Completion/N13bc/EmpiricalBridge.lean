module

public import SKConstants.Completion.LW.ExplicitSevenConcentration
public import SKConstants.Completion.LGram.SevenErrors

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal RealInnerProductSpace Matrix.Norms.L2Operator

namespace SKConstants.Completion.N13bc
open LW

def matrixAverage {Ξ : Type*} {n k : ℕ}
    (M : Ξ → Matrix (Fin k) (Fin k) ℝ) (ω : Fin n → Ξ) :
    Matrix (Fin k) (Fin k) ℝ := (n : ℝ)⁻¹ • ∑ i, M (ω i)

theorem rowAverage_matrix_image {Ξ : Type*} {n k : ℕ}
    (M : Ξ → Matrix (Fin k) (Fin k) ℝ)
    (w : EuclideanSpace ℝ (Fin k)) (ω : Fin n → Ξ) :
    rowAverage (fun u => Matrix.toEuclideanCLM (𝕜 := ℝ) (M u) w) ω =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (matrixAverage M ω) w := by
  simp [rowAverage, matrixAverage, map_smul, map_sum]

theorem matrixAverage_transpose {Ξ : Type*} {n k : ℕ}
    (M : Ξ → Matrix (Fin k) (Fin k) ℝ) (ω : Fin n → Ξ) :
    matrixAverage (fun u => (M u).transpose) ω = (matrixAverage M ω).transpose := by
  ext i j
  simp [matrixAverage, Matrix.transpose_apply, Matrix.sum_apply]

theorem matrixAverage_halfUpper {Ξ : Type*} {n k : ℕ}
    (M : Ξ → Matrix (Fin k) (Fin k) ℝ) (ω : Fin n → Ξ) :
    matrixAverage (fun u => halfUpperTruncation (M u)) ω =
      halfUpperTruncation (matrixAverage M ω) := by
  ext i j
  by_cases hij : i < j
  · simp [matrixAverage, Matrix.sum_apply, halfUpperTruncation, hij]
  by_cases he : i = j
  · simp [matrixAverage, Matrix.sum_apply, halfUpperTruncation, he,
      Finset.sum_div, Finset.mul_sum, mul_div_assoc]
  · simp [matrixAverage, Matrix.sum_apply, halfUpperTruncation, hij, he]

theorem sum_rowAverage_images_sq {Ξ : Type*} {n : ℕ} (r : ℕ)
    (M : Ξ → Matrix (Fin (2^r)) (Fin (2^r)) ℝ)
    (s : EuclideanSpace ℝ (Fin (2^r))) (ω : Fin n → Ξ) :
    (∑ I : DyadicCore.Interval r,
      ‖rowAverage (fun u => Matrix.toEuclideanCLM (𝕜 := ℝ) (M u)
        (coordinateProjection (dyadicIntervalSets r I) s)) ω‖^2) =
      dyadicMatrixSeminorm r s (matrixAverage M ω)^2 := by
  simp_rw [rowAverage_matrix_image]
  exact (projectedMatrixSeminorm_sq (dyadicIntervalSets r) s (matrixAverage M ω)).symm

def sevenFeatures {Ξ : Type*} (r : ℕ)
    (EA EH : Ξ → Matrix (Fin (2^r)) (Fin (2^r)) ℝ)
    (s b : EuclideanSpace ℝ (Fin (2^r)))
    (eq ev : Ξ → EuclideanSpace ℝ (Fin (2^r))) :
    SevenIndex r → Ξ → EuclideanSpace ℝ (Fin (2^r))
  | .inl j => if j=0 then eq else ev
  | .inr (j,I) => fun u =>
    let L := halfUpperTruncation (EA u)
    let w := coordinateProjection (dyadicIntervalSets r I) s
    if j=0 then Matrix.toEuclideanCLM (𝕜 := ℝ) L w
    else if j=1 then Matrix.toEuclideanCLM (𝕜 := ℝ) L.transpose w
    else if j=2 then Matrix.toEuclideanCLM (𝕜 := ℝ) L
      (coordinateProjection (dyadicIntervalSets r I) b)
    else if j=3 then Matrix.toEuclideanCLM (𝕜 := ℝ) (EH u) w
    else Matrix.toEuclideanCLM (𝕜 := ℝ) (EH u).transpose w

theorem measurable_matrix_image {Ξ : Type*} [MeasurableSpace Ξ] {k : ℕ}
    (F : Ξ → Matrix (Fin k) (Fin k) ℝ) (hF : Measurable F)
    (w : EuclideanSpace ℝ (Fin k)) :
    Measurable (fun u => Matrix.toEuclideanCLM (𝕜 := ℝ) (F u) w) := by
  change Measurable (fun u => Matrix.toEuclideanCLM (𝕜 := ℝ) (F u) (WithLp.toLp 2 w.ofLp))
  simp_rw [Matrix.toEuclideanCLM_toLp]
  apply (WithLp.measurable_toLp 2 _).comp
  apply Measurable.of_eval
  intro i
  change Measurable (fun u => ∑ j, F u i j * w j)
  apply Finset.measurable_fun_sum
  intro j _
  exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hF)).mul_const _

theorem measurable_sevenFeatures {Ξ : Type*} [MeasurableSpace Ξ] (r : ℕ)
    (EA EH : Ξ → Matrix (Fin (2^r)) (Fin (2^r)) ℝ)
    (s b : EuclideanSpace ℝ (Fin (2^r)))
    (eq ev : Ξ → EuclideanSpace ℝ (Fin (2^r)))
    (hEA : Measurable EA) (hEH : Measurable EH)
    (heq : Measurable eq) (hev : Measurable ev) (i : SevenIndex r) :
    Measurable (sevenFeatures r EA EH s b eq ev i) := by
  have htrans (F : Ξ → Matrix (Fin (2^r)) (Fin (2^r)) ℝ) (hF : Measurable F) :
      Measurable (fun u => (F u).transpose) := by
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    exact (measurable_pi_apply i).comp ((measurable_pi_apply j).comp hF)
  have hL : Measurable (fun u => halfUpperTruncation (EA u)) :=
    (halfUpperCLM r).continuous.measurable.comp hEA
  cases i with
  | inl j =>
    dsimp only [sevenFeatures]
    split_ifs <;> assumption
  | inr p =>
    rcases p with ⟨j,I⟩
    fin_cases j <;> dsimp [sevenFeatures]
    · exact measurable_matrix_image _ hL _
    · exact measurable_matrix_image _ (htrans _ hL) _
    · exact measurable_matrix_image _ hL _
    · exact measurable_matrix_image _ hEH _
    · exact measurable_matrix_image _ (htrans _ hEH) _

theorem sum_sevenFeatures_sq_eq {Ξ : Type*} {n : ℕ} (r : ℕ)
    (EA EH : Ξ → Matrix (Fin (2^r)) (Fin (2^r)) ℝ)
    (s b : EuclideanSpace ℝ (Fin (2^r)))
    (eq ev : Ξ → EuclideanSpace ℝ (Fin (2^r))) (ω : Fin n → Ξ) :
    (∑ i : SevenIndex r, ‖rowAverage (sevenFeatures r EA EH s b eq ev i) ω‖^2) =
      LGram.sevenErrorSum r (matrixAverage EA ω) (matrixAverage EH ω)
        s (rowAverage eq ω) b (rowAverage ev ω) := by
  simp only [SevenIndex, Fintype.sum_sum_type, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue]
  simp only [sevenFeatures]
  norm_num [Fin.ext_iff]
  simp only [Finset.sum_add_distrib]
  simp_rw [rowAverage_matrix_image, matrixAverage_transpose, matrixAverage_halfUpper]
  simp only [LGram.sevenErrorSum, dyadicMatrixSeminorm, projectedMatrixSeminorm_sq]
  ring

end SKConstants.Completion.N13bc
