module
public import SKConstants.BrownianVectorPredictableLikelihood

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology
namespace SKConstants

def brownianVectorCoordinateSum {A ι Ω : Type*} (D : ℝ≥0 → Ω → ℝ)
    (t : ℕ → ℝ≥0) (H : BrownianVectorPredictableCoefficient A ι t) (i : ι) :=
  predictableGaussianSum (fun k u => brownianVectorMeshIncrement D t k u.2 i)
    (fun k u => brownianVectorStaticCoefficient D t H k u i)

def brownianVectorCoordinateVariation {A ι Ω : Type*} (D : ℝ≥0 → Ω → ℝ)
    (t : ℕ → ℝ≥0) (H : BrownianVectorPredictableCoefficient A ι t) (i : ι) :=
  predictableGaussianVariation (brownianMeshVariance t)
    (fun k u => brownianVectorStaticCoefficient D t H k u i)

def brownianVectorCoordinatePastSum {A ι : Type*} (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : BrownianVectorPredictableCoefficient A ι t) (i : ι) (n : ℕ)
    (u : A × (Iic (t n) → ι → ℝ)) : ℝ :=
  ∑ k : Fin n,H k (u.1,brownianVectorPastRestrict (ht (Nat.le_of_lt k.isLt)) u.2) i*
    (u.2 ⟨t (k+1),ht (by omega)⟩ i-u.2 ⟨t k,ht (Nat.le_of_lt k.isLt)⟩ i)

def brownianVectorCoordinatePastVariation {A ι : Type*} (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : BrownianVectorPredictableCoefficient A ι t) (i : ι) (n : ℕ)
    (u : A × (Iic (t n) → ι → ℝ)) : ℝ :=
  ∑ k : Fin n,H k (u.1,brownianVectorPastRestrict (ht (Nat.le_of_lt k.isLt)) u.2) i^2*
    (brownianMeshVariance t k : ℝ)

lemma measurable_brownianVectorCoordinatePastSum {A ι : Type*} [MeasurableSpace A]
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : BrownianVectorPredictableCoefficient A ι t)
    (hH : ∀ k, Measurable (H k)) (i : ι) (n : ℕ) :
    Measurable (brownianVectorCoordinatePastSum t ht H i n) := by
  apply Finset.measurable_sum
  intro k _
  apply Measurable.mul
  · exact (measurable_pi_apply i).comp ((hH k).comp (measurable_fst.prodMk
      ((measurable_brownianVectorPastRestrict _).comp measurable_snd)))
  · fun_prop

lemma measurable_brownianVectorCoordinatePastVariation {A ι : Type*} [MeasurableSpace A]
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : BrownianVectorPredictableCoefficient A ι t)
    (hH : ∀ k, Measurable (H k)) (i : ι) (n : ℕ) :
    Measurable (brownianVectorCoordinatePastVariation t ht H i n) := by
  apply Finset.measurable_sum
  intro k _
  exact (((measurable_pi_apply i).comp ((hH k).comp (measurable_fst.prodMk
    ((measurable_brownianVectorPastRestrict _).comp measurable_snd)))).pow_const 2).mul_const _

theorem brownianVectorCoordinate_state_indep_increment {A ι Ω : Type*}
    [MeasurableSpace A] [Fintype ι] [MeasurableSpace Ω]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (D : ℝ≥0 → Ω → ℝ) (hD : IsPreBrownianReal D Q) (hmD : ∀ s, Measurable (D s))
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : BrownianVectorPredictableCoefficient A ι t)
    (hH : ∀ k, Measurable (H k)) (i : ι) (n : ℕ) :
    IndepFun (fun u => (brownianVectorCoordinateSum D t H i n u,
      brownianVectorStaticCoefficient D t H n u i,brownianVectorCoordinateVariation D t H i n u))
      (fun u : A × (ι → Ω) => brownianVectorMeshIncrement D t n u.2 i)
      (P.prod (Measure.pi (fun _ : ι => Q))) := by
  let Φ := fun u : A × (Iic (t n) → ι → ℝ) =>
    (brownianVectorCoordinatePastSum t ht H i n u,H n u i,
      brownianVectorCoordinatePastVariation t ht H i n u)
  have hΦ : Measurable Φ := (measurable_brownianVectorCoordinatePastSum t ht H hH i n).prodMk
    (((measurable_pi_apply i).comp (hH n)).prodMk
      (measurable_brownianVectorCoordinatePastVariation t ht H hH i n))
  have hi := brownianVectorStaticPast_indep_increment (ι := ι) P Q D hD hmD t ht n
  convert hi.comp hΦ (measurable_pi_apply i) using 1
  · funext u
    rw [brownianVectorCoordinateSum,predictableGaussianSum_eq_fin_sum,
      brownianVectorCoordinateVariation,predictableGaussianVariation_eq_fin_sum]
    rfl
  · rfl

theorem brownianVectorCoordinateSum_L2_isometry {A ι Ω : Type*}
    [MeasurableSpace A] [Fintype ι] [MeasurableSpace Ω]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (D : ℝ≥0 → Ω → ℝ) (hD : IsPreBrownianReal D Q) (hmD : ∀ s, Measurable (D s))
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : BrownianVectorPredictableCoefficient A ι t)
    (hH : ∀ k, Measurable (H k)) (i : ι)
    (hHsq : ∀ k, Integrable (fun u => brownianVectorStaticCoefficient D t H k u i ^ 2)
      (P.prod (Measure.pi (fun _ : ι => Q)))) (n : ℕ) :
    Integrable (fun u => brownianVectorCoordinateSum D t H i n u ^ 2)
      (P.prod (Measure.pi (fun _ : ι => Q))) ∧
    Integrable (brownianVectorCoordinateVariation D t H i n)
      (P.prod (Measure.pi (fun _ : ι => Q))) ∧
    (∫ u, brownianVectorCoordinateSum D t H i n u ^ 2 ∂P.prod (Measure.pi (fun _ : ι => Q))) =
      ∫ u, brownianVectorCoordinateVariation D t H i n u ∂P.prod (Measure.pi (fun _ : ι => Q)) := by
  have hsnd : HasLaw (Prod.snd : A × (ι → Ω) → (ι → Ω))
      (Measure.pi (fun _ : ι => Q)) (P.prod (Measure.pi (fun _ : ι => Q))) :=
    ⟨measurable_snd.aemeasurable,measurePreserving_snd.map_eq⟩
  exact predictableGaussianSum_L2_isometry _ _ _ _
    (fun k => ((measurePreserving_eval (fun _ : ι => gaussianReal 0 (brownianMeshVariance t k)) i).hasLaw.comp
      (brownianVectorMeshIncrement_hasLaw (ι := ι) Q D hD t ht k)).comp hsnd)
    (fun k => ((measurable_pi_apply i).comp
      (measurable_brownianVectorStaticCoefficient D hmD t H hH k)).aemeasurable)
    hHsq (brownianVectorCoordinate_state_indep_increment P Q D hD hmD t ht H hH i) n

lemma brownianVectorPredictableSum_eq_sum_coordinate {A ι Ω : Type*} [Fintype ι]
    (D : ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0)
    (H : BrownianVectorPredictableCoefficient A ι t) (n : ℕ) (u : A × (ι → Ω)) :
    brownianVectorPredictableSum D t H n u = ∑ i,brownianVectorCoordinateSum D t H i n u := by
  rw [brownianVectorPredictableSum,predictableGaussianVectorSum_eq_fin_sum]
  simp_rw [brownianVectorCoordinateSum,predictableGaussianSum_eq_fin_sum]
  exact Finset.sum_comm

end SKConstants
