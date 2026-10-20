module

public import SKConstants.Completion.NW.Adapter
public import SKConstants.Completion.NW.Rates

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology BigOperators RealInnerProductSpace Matrix.Norms.L2Operator

namespace SKConstants.Completion.NW
open SKConstantsOAI.ZeroTemperatureSK Blueprint Blueprint4 N13A N13bc LGram LW

variable {Ω : Type} [MeasurableSpace Ω]

theorem weightedAdapter_holds (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) {n : ℕ} (hn : 0 < n) (ω : Fin n → (Bool × Ω) × Ω) :
    weightedSq W β hβ (mixedRowsArray W W β hβ (growingQueryTime (coarseMesh p n))
      (fun j => growingQueryTime (coarseMesh p n) (j+1)) (coarseCount p n) ω) =
    actualPaddedWeightedSq W W β hβ (growingQueryTime (coarseMesh p n)) (coarseTime p n)
      (coarseCount p n) (paddingDepth (coarseCount p n))
      (Nat.le_pow_clog (by norm_num) (coarseCount p n)) ω :=
  weightedSq_mixedRowsArray W β hβ p hn ω

theorem canonicalArray_weightedSq_tail (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) {n : ℕ} (hn : 0 < n)
    (hsmall : ∀ j < coarseCount p n, LQ.meshDuration (coarseMesh p n) j ≤ 1)
    {η : ℝ} (hη : 0 < η) :
    (canonicalArrayLaw W β hβ p n).real
      {z | 4*η^2*(2+5*(paddingDepth (coarseCount p n)+1 : ℝ)*
        (growingQueryTime (coarseMesh p n) (coarseCount p n) : ℝ)) < weightedSq W β hβ z} ≤
    sevenTailBudget n (paddingDepth (coarseCount p n)) (Real.exp (1/8))
      (actualParisiPosteriorRowMGFProxy W β (coarseTime p n)) η := by
  rw [canonicalArrayLaw, mixedVectorRowsLaw, map_measureReal_apply
    (measurable_mixedRowsArray W W β hβ _ _ _)
    (measurableSet_lt measurable_const (measurable_weightedSq W β hβ p n))]
  change (linkedScalarRowsLaw W W β (coarseTime p n) n).real
    {ω | 4*η^2*(2+5*(paddingDepth (coarseCount p n)+1 : ℝ)*
      (growingQueryTime (coarseMesh p n) (coarseCount p n) : ℝ)) <
      weightedSq W β hβ (mixedRowsArray W W β hβ (growingQueryTime (coarseMesh p n))
        (fun j => growingQueryTime (coarseMesh p n) (j+1)) (coarseCount p n) ω)} ≤ _
  simp_rw [weightedAdapter_holds W β hβ p hn]
  exact growingPaddedWeightedStatement_holds W W β hβ (coarseMesh p n)
    (paperGrowingQueryMeshSize_pos p.a n hn) (coarseCount p n)
    (paddingDepth (coarseCount p n)) (Nat.le_pow_clog (by norm_num) _)
    hsmall n hn η hη

theorem sharpWeightedStatement_holds : N13A.SharpWeightedStatement := by
  intro Ω _ W β hβ p hf hb
  obtain ⟨C,hC,hthreshold⟩ := coarseWeightedThreshold_eventually p hf hb
  refine ⟨C,hC,2,?_⟩
  intro M hM
  have ha1 : p.a < 1 := by linarith [hf.2.2.1, hf.2.2.2.2.2]
  filter_upwards [hthreshold,
    coarseWeightedBudget_eventually W β hβ p hf hb (Real.exp (1/8)) M (Real.exp_pos _) hM,
    schedule_eventually p.a p.b hb.1 hb.2.2.1.le ha1] with n hthreshold hbudget hsched
  have hn : 0 < n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hη : 0 < (n : ℝ)^(-p.gamma) := Real.rpow_pos_of_pos (by positivity) _
  have hsmall : ∀ j < coarseCount p n, LQ.meshDuration (coarseMesh p n) j ≤ 1 := by
    intro j hj
    change (growingQueryDuration (coarseMesh p n) j : ℝ) ≤ 1
    exact (duration_bound p.a p.b hb.1 n hsched.1 hsched.2.1 j hj.le).trans
      (Real.rpow_le_one_of_one_le_of_nonpos hnR (by linarith [hb.2.2.1]))
  letI : IsProbabilityMeasure (canonicalArrayLaw W β hβ p n) := by
    dsimp [canonicalArrayLaw, mixedVectorRowsLaw]
    infer_instance
  have hsub : {z : RowArray p n | C*(n : ℝ)^(-2*p.gamma)*(Real.log (n : ℝ))^2 < weightedSq W β hβ z} ⊆
      {z | 4*((n : ℝ)^(-p.gamma))^2*(2+5*(paddingDepth (coarseCount p n)+1 : ℝ)*
        (growingQueryTime (coarseMesh p n) (coarseCount p n) : ℝ)) < weightedSq W β hβ z} := by
    intro z hz
    exact hthreshold.trans_lt hz
  exact (measureReal_mono hsub).trans
    ((canonicalArray_weightedSq_tail W β hβ p hn hsmall hη).trans hbudget)

end SKConstants.Completion.NW
