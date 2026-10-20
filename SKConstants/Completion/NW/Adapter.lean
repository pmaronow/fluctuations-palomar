module

public import SKConstants.Completion.N13bc.Node
public import SKConstants.Completion.N13A.Regularity

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators RealInnerProductSpace Matrix.Norms.L2Operator

namespace SKConstants.Completion.NW
open SKConstantsOAI.ZeroTemperatureSK Blueprint Blueprint4 N13A N13bc LGram LW LC5

variable {Ω : Type} [MeasurableSpace Ω]

theorem liftMatrix_eq_padMatrix {k q : ℕ} (E : Matrix (Fin k) (Fin k) ℝ) :
    liftMatrix (Nat.le_add_right k q) E = padMatrix q E 0 := by
  ext i j
  cases i using Fin.addCases <;> cases j using Fin.addCases <;>
    simp [liftMatrix, padMatrix, finSumFinEquiv]

theorem sevenErrorSumDim_lift {k d : ℕ} (r : ℕ) (hd : d = 2^r) (hk : k ≤ d)
    (EA EH : Matrix (Fin k) (Fin k) ℝ) (s eq b ev : EuclideanSpace ℝ (Fin k)) :
    sevenErrorSumDim r d hd (liftMatrix hk EA) (liftMatrix hk EH)
      (liftVector hk s) (liftVector hk eq) (liftVector hk b) (liftVector hk ev) =
    sevenErrorSum r (liftMatrix (hk.trans hd.le) EA) (liftMatrix (hk.trans hd.le) EH)
      (liftVector (hk.trans hd.le) s) (liftVector (hk.trans hd.le) eq)
      (liftVector (hk.trans hd.le) b) (liftVector (hk.trans hd.le) ev) := by
  subst d
  rfl

theorem rowS_eq_posteriorWeight (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (hδ : 0 < coarseMesh p n) :
    rowS W β hβ p n = posteriorWeight W β (growingQueryTime (coarseMesh p n))
      (coarseCount p n) := by
  ext j
  exact populationTargetSpin_eq_scale W W β hβ _ (growingQueryTime_strictMono _ hδ)
    _ _ _ ((growingQueryTime_strictMono _ hδ).monotone (Nat.le_succ _)) j

theorem rowB_eq_queryWeight (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (hδ : 0 < coarseMesh p n) :
    rowB W β hβ p n = queryWeight W β (growingQueryTime (coarseMesh p n))
      (coarseCount p n) := by
  ext j
  exact populationQuerySpin_eq_integral W W β hβ _ _
    ((growingQueryTime_strictMono _ hδ).monotone.comp (fun _ _ h => Nat.add_le_add_right h 1))
    _ _ le_rfl j

theorem rowH0_eq_cross_moment (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (i j : Fin (coarseCount p n)) :
    rowH0 W β hβ p n i j =
      ∫ u, posteriorRow W β (growingQueryTime (coarseMesh p n)) (coarseCount p n) u i *
        queryRow W W β hβ (growingQueryTime (coarseMesh p n)) (coarseCount p n) u j
        ∂linkedScalarLaw W W β (coarseTime p n) := by
  simp only [rowH0, populationCross, mixedPopulation, populationGram,
    Matrix.submatrix_apply, mixedRow_posterior, mixedRow_query, posteriorRow, queryRow]

theorem centered_average {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ) (c : ℝ) :
    (∑ i, f i) / n - c = (n : ℝ)⁻¹ * ∑ i, (f i - c) := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp

theorem matrixAverage_lift {Ξ : Type*} {n k d : ℕ} (h : k ≤ d)
    (E : Ξ → Matrix (Fin k) (Fin k) ℝ) (ω : Fin n → Ξ) :
    matrixAverage (fun u => liftMatrix h (E u)) ω = liftMatrix h (matrixAverage E ω) := by
  ext i j
  simp only [matrixAverage, liftMatrix, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  split_ifs <;> simp

theorem rowAverage_lift {Ξ : Type*} {n k d : ℕ} (h : k ≤ d)
    (E : Ξ → EuclideanSpace ℝ (Fin k)) (ω : Fin n → Ξ) :
    rowAverage (fun u => liftVector h (E u)) ω = liftVector h (rowAverage E ω) := by
  ext i
  by_cases hi : i.val < k <;>
    simp [rowAverage, liftVector, WithLp.ofLp_sum, Finset.sum_apply, hi]

theorem arrayEA_mixedRowsArray (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) {n : ℕ} (hn : 0 < n) (ω : Fin n → (Bool × Ω) × Ω) :
    arrayEA (mixedRowsArray W W β hβ (growingQueryTime (coarseMesh p n))
      (fun j => growingQueryTime (coarseMesh p n) (j+1)) (coarseCount p n) ω) =
    matrixAverage (posteriorGramError W β (growingQueryTime (coarseMesh p n))
      (coarseCount p n)) ω := by
  ext i j
  simpa only [arrayEA, N13e.empiricalCross, arrayT, mixedRowsArray,
    actualParisiFullMixedRows, mixedRow_posterior, posteriorRow, matrixAverage,
    Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.sum_apply,
    smul_eq_mul, posteriorGramError] using
    centered_average hn
      (fun l => posteriorRow W β (growingQueryTime (coarseMesh p n))
        (coarseCount p n) (ω l) i * posteriorRow W β (growingQueryTime (coarseMesh p n))
        (coarseCount p n) (ω l) j) (if i=j then 1 else 0)

theorem arrayEH_mixedRowsArray (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) {n : ℕ} (hn : 0 < n) (ω : Fin n → (Bool × Ω) × Ω) :
    arrayEH W β hβ (mixedRowsArray W W β hβ (growingQueryTime (coarseMesh p n))
      (fun j => growingQueryTime (coarseMesh p n) (j+1)) (coarseCount p n) ω) =
    matrixAverage (crossError W W β hβ (growingQueryTime (coarseMesh p n))
      (coarseTime p n) (coarseCount p n)) ω := by
  ext i j
  simpa only [arrayEH, N13e.empiricalCross, arrayT, arrayG, mixedRowsArray,
    actualParisiFullMixedRows, mixedRow_posterior, mixedRow_query, posteriorRow, queryRow,
    matrixAverage, Matrix.sub_apply, Matrix.smul_apply, Matrix.sum_apply,
    smul_eq_mul, crossError, rowH0_eq_cross_moment] using
    centered_average hn
      (fun l => posteriorRow W β (growingQueryTime (coarseMesh p n))
        (coarseCount p n) (ω l) i * queryRow W W β hβ (growingQueryTime (coarseMesh p n))
        (coarseCount p n) (ω l) j) (rowH0 W β hβ p n i j)

theorem arrayEq_mixedRowsArray (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) {n : ℕ} (hn : 0 < n) (hδ : 0 < coarseMesh p n)
    (ω : Fin n → (Bool × Ω) × Ω) :
    arrayEq W β hβ (mixedRowsArray W W β hβ (growingQueryTime (coarseMesh p n))
      (fun j => growingQueryTime (coarseMesh p n) (j+1)) (coarseCount p n) ω) =
    rowAverage (fun u => scalarHiddenSign u.1.1 • posteriorRow W β
      (growingQueryTime (coarseMesh p n)) (coarseCount p n) u -
        posteriorWeight W β (growingQueryTime (coarseMesh p n)) (coarseCount p n)) ω := by
  ext j
  simpa only [arrayEq, N13e.empiricalSpin, arrayT, arrayX, mixedRowsArray,
    actualParisiFullMixedRows, mixedRow_posterior, mixedRow_spin, posteriorRow,
    rowAverage, PiLp.sub_apply, PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_toLp,
    smul_eq_mul, rowS_eq_posteriorWeight W β hβ p n hδ, mul_comm] using
    centered_average hn
      (fun l => posteriorRow W β (growingQueryTime (coarseMesh p n))
        (coarseCount p n) (ω l) j * scalarHiddenSign (ω l).1.1)
      (posteriorWeight W β (growingQueryTime (coarseMesh p n)) (coarseCount p n) j)

theorem arrayEv_mixedRowsArray (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) {n : ℕ} (hn : 0 < n) (hδ : 0 < coarseMesh p n)
    (ω : Fin n → (Bool × Ω) × Ω) :
    arrayEv W β hβ (mixedRowsArray W W β hβ (growingQueryTime (coarseMesh p n))
      (fun j => growingQueryTime (coarseMesh p n) (j+1)) (coarseCount p n) ω) =
    rowAverage (fun u => scalarHiddenSign u.1.1 • queryRow W W β hβ
      (growingQueryTime (coarseMesh p n)) (coarseCount p n) u -
        queryWeight W β (growingQueryTime (coarseMesh p n)) (coarseCount p n)) ω := by
  ext j
  simpa only [arrayEv, N13e.empiricalSpin, arrayG, arrayX, mixedRowsArray,
    actualParisiFullMixedRows, mixedRow_query, mixedRow_spin, queryRow,
    rowAverage, PiLp.sub_apply, PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_toLp,
    smul_eq_mul, rowB_eq_queryWeight W β hβ p n hδ, mul_comm] using
    centered_average hn
      (fun l => queryRow W W β hβ (growingQueryTime (coarseMesh p n))
        (coarseCount p n) (ω l) j * scalarHiddenSign (ω l).1.1)
      (queryWeight W β (growingQueryTime (coarseMesh p n)) (coarseCount p n) j)

theorem weightedSq_mixedRowsArray (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) {n : ℕ} (hn : 0 < n) (ω : Fin n → (Bool × Ω) × Ω) :
    weightedSq W β hβ (mixedRowsArray W W β hβ (growingQueryTime (coarseMesh p n))
      (fun j => growingQueryTime (coarseMesh p n) (j+1)) (coarseCount p n) ω) =
    actualPaddedWeightedSq W W β hβ (growingQueryTime (coarseMesh p n)) (coarseTime p n)
      (coarseCount p n) (paddingDepth (coarseCount p n))
      (Nat.le_pow_clog (by norm_num) (coarseCount p n)) ω := by
  have hδ : 0 < coarseMesh p n := paperGrowingQueryMeshSize_pos p.a n hn
  rw [weightedSq, arrayEA_mixedRowsArray W β hβ p hn,
    arrayEH_mixedRowsArray W β hβ p hn, arrayEq_mixedRowsArray W β hβ p hn hδ,
    arrayEv_mixedRowsArray W β hβ p hn hδ,
    rowS_eq_posteriorWeight W β hβ p n hδ, rowB_eq_queryWeight W β hβ p n hδ]
  simp_rw [← liftMatrix_eq_padMatrix, ← liftVector_eq_padVector]
  rw [sevenErrorSumDim_lift]
  simp only [actualPaddedWeightedSq, matrixAverage_lift, rowAverage_lift]

end SKConstants.Completion.NW
