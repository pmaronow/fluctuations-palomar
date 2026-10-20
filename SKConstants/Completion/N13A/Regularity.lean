module

public import SKConstants.Completion.N13A.Statements
public import SKConstants.Completion.NReplay.ThresholdLink
public import SKConstants.Completion.LM1b.TraceMeasurability
public import SKConstants.Completion.LM3.GibbsTilt

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology RealInnerProductSpace Matrix.Norms.L2Operator

namespace SKConstants.Completion.N13A
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal Blueprint Blueprint4 LC5 LGram

variable {Ω : Type} [MeasurableSpace Ω]

@[fun_prop] theorem continuous_halfUpper (k : ℕ) :
    Continuous (halfUpperTruncation (ι := Fin k) : Matrix (Fin k) (Fin k) ℝ → _) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  unfold halfUpperTruncation
  split_ifs <;> fun_prop

@[fun_prop] theorem continuous_fullUpper (k : ℕ) :
    Continuous (fullUpperTruncation (ι := Fin k) : Matrix (Fin k) (Fin k) ℝ → _) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  unfold fullUpperTruncation
  split_ifs <;> fun_prop

@[fun_prop] theorem continuous_padMatrix (k m : ℕ) (a : ℝ) :
    Continuous (fun M : Matrix (Fin k) (Fin k) ℝ => padMatrix m M a) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  cases i <;> cases j <;> simp only [padMatrix, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂] <;> fun_prop

@[fun_prop] theorem continuous_padVector (k m : ℕ) :
    Continuous (padVector (k := k) m) := by
  unfold padVector
  apply Continuous.comp (by fun_prop : Continuous (WithLp.toLp 2 (V := Fin (k+m) → ℝ)))
  apply continuous_pi
  intro i
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  cases i <;> simp only [Function.comp_def, Equiv.symm_apply_apply, Sum.elim_inl,
    Sum.elim_inr] <;> fun_prop

theorem measurable_sharpReplayInput (p : Parameters) (n : ℕ) :
    Measurable (sharpReplayInput p n) := by
  have hM : Measurable (fun y : SharpInput p n =>
      castMatrix (rankCount_add p.a p.b n) (physical n y.2.1)) :=
    (continuous_castMatrix _).measurable.comp ((continuous_goeMatrix _).measurable.comp
      measurable_snd.fst)
  exact (measurable_replayInput _ _ _).comp (hM.prodMk measurable_snd.snd)

theorem measurable_sharpField (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (t : ℝ≥0) : Measurable (sharpField W β hβ p n t) :=
  (measurable_castVec _).comp ((M1.measurable_ReplayField W β hβ _ _ _ t).comp
    (measurable_sharpReplayInput p n))

def baseField (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (t : ℝ≥0) (y : Prim n × N13a.CoarseAux p n) : Fin n → ℝ :=
  sharpField W β hβ p n t ((fun _ => false), y)

theorem measurable_baseField (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (t : ℝ≥0) : Measurable (baseField W β hβ p n t) :=
  (measurable_sharpField W β hβ p n t).comp (measurable_const.prodMk measurable_id)

theorem sharpField_eq_baseField (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (t : ℝ≥0) (y : SharpInput p n) :
    sharpField W β hβ p n t y = baseField W β hβ p n t y.2 := rfl

theorem sharpLinkedLaw_eq_terminal (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) :
    sharpLinkedLaw W β hβ p n = M1.TerminalLinkedLaw β (coarseTime p n)
      ((primLaw n).prod (replayAuxLaw W (coarseMesh p n) (coarseRank p n) (coarseCount p n)))
      (baseField W β hβ p n (coarseTime p n)) := by
  rw [M1.TerminalLinkedLaw, LM3.spinPrior_eq_uniformSpinLaw]
  rfl

instance sharpLinkedLaw_probability (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) : IsProbabilityMeasure (sharpLinkedLaw W β hβ p n) := by
  rw [sharpLinkedLaw_eq_terminal]
  exact M1.terminalLinkedLaw_probability _ _ _ _ (measurable_baseField W β hβ p n _)

theorem measurable_sharpRows (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) : Measurable (sharpRows W β hβ p n) := by
  have hT := (M1.measurable_ReplayTargets W β hβ (coarseMesh p n) (coarseRank p n)
    (coarseCount p n)).comp (measurable_sharpReplayInput p n)
  have hG := (M1.measurable_ReplayEndpoints W β hβ (coarseMesh p n) (coarseRank p n)
    (coarseCount p n)).comp (measurable_sharpReplayInput p n)
  apply Measurable.of_eval
  intro i
  apply (WithLp.measurable_toLp 2 _).comp
  apply Measurable.of_eval
  intro j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simpa only [Function.comp_def, Fin.append_left] using
      ((measurable_pi_apply (Fin.cast (rankCount_add p.a p.b n).symm i)).comp
        ((measurable_pi_apply j).comp hT))
  · refine Fin.addCases (fun j => ?_) (fun _ => ?_) j
    · simpa only [Function.comp_def, Fin.append_right, Fin.append_left] using
        ((measurable_pi_apply (Fin.cast (rankCount_add p.a p.b n).symm i)).comp
          ((measurable_pi_apply j).comp hG))
    · simpa only [Fin.append_right] using
        (show Measurable (fun y : SharpInput p n => scalarHiddenSign (y.1 i)) from
          (measurable_of_finite scalarHiddenSign).comp
            ((measurable_pi_apply i).comp measurable_fst))

theorem continuous_sevenErrorSumDim (R d : ℕ) (hdim : d = 2^R)
    (s b : EuclideanSpace ℝ (Fin d)) :
    Continuous (fun z : Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ ×
      EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        sevenErrorSumDim R d hdim z.1 z.2.1 s z.2.2.1 b z.2.2.2) := by
  subst d
  unfold sevenErrorSumDim sevenErrorSum
  simp only [dyadicMatrixSeminorm, projectedMatrixSeminorm_sq]
  fun_prop

theorem measurable_weightedSq (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) : Measurable (weightedSq W β hβ (p := p) (n := n)) := by
  apply Continuous.measurable
  exact (continuous_sevenErrorSumDim (paddingDepth (coarseCount p n)) _
    (padding_size _) (padVector _ (rowS W β hβ p n))
      (padVector _ (rowB W β hβ p n))).comp
    (show Continuous (fun z : RowArray p n =>
      (padMatrix _ (arrayEA z) 0, padMatrix _ (arrayEH W β hβ z) 0,
        padVector _ (arrayEq W β hβ z), padVector _ (arrayEv W β hβ z))) from by
      unfold arrayEA arrayEH arrayEq arrayEv N13e.empiricalCross N13e.empiricalSpin
        arrayT arrayG arrayX
      fun_prop)

theorem measurable_linearEnergy (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) : Measurable (linearEnergy W β hβ (p := p) (n := n)) := by
  apply Continuous.measurable
  unfold linearEnergy N13e.energyLinearPart arrayEA arrayEH arrayEq arrayEv
    N13e.empiricalCross N13e.empiricalSpin arrayT arrayG arrayX
  fun_prop

theorem measurableSet_gramGood (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) : MeasurableSet (gramGood W β hβ p n) :=
  measurableSet_rowGramEvent _ _ _

end SKConstants.Completion.N13A
