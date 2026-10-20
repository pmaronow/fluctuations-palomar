module
public import SKConstants.GaussianCenteredSquareIsometry
public import SKConstants.BrownianQuadraticVariation

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology
namespace SKConstants

def brownianStaticCenteredSquareSum {A Ω : Type*} (D : ℝ≥0 → Ω → ℝ)
    (t : ℕ → ℝ≥0) (H : BrownianStaticPredictableCoefficient A t) :=
  predictableGaussianCenteredSquareSum (fun k u => brownianMeshIncrement D t k u.2)
    (brownianStaticCoefficient D t H) (brownianMeshVariance t)

def brownianStaticPastCenteredSquareSum {A : Type*} (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : BrownianStaticPredictableCoefficient A t) (n : ℕ)
    (u : A × (Iic (t n) → ℝ)) : ℝ :=
  ∑ i : Fin n,H i (u.1,brownianPastRestrict (ht (Nat.le_of_lt i.isLt)) u.2)*
    ((u.2 ⟨t (i+1),ht (by omega)⟩-u.2 ⟨t i,ht (Nat.le_of_lt i.isLt)⟩)^2-
      (brownianMeshVariance t i : ℝ))

lemma measurable_brownianStaticPastCenteredSquareSum {A : Type*} [MeasurableSpace A]
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : BrownianStaticPredictableCoefficient A t)
    (hH : ∀ k,Measurable (H k)) (n : ℕ) :
    Measurable (brownianStaticPastCenteredSquareSum t ht H n) := by
  apply Finset.measurable_sum
  intro i _
  apply Measurable.mul
  · exact (hH i).comp (measurable_fst.prodMk
      ((measurable_brownianPastRestrict _).comp measurable_snd))
  · fun_prop

lemma brownianStaticFullPast_indep_increment {A Ω : Type*}
    [MeasurableSpace A] [MeasurableSpace Ω]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (D : ℝ≥0 → Ω → ℝ) (hD : IsPreBrownianReal D Q) (hmD : ∀ s,Measurable (D s))
    (t : ℕ → ℝ≥0) (ht : Monotone t) (n : ℕ) :
    IndepFun (fun u : A × Ω => (u.1,brownianFullPast D (t n) u.2))
      (fun u => brownianMeshIncrement D t n u.2) (P.prod Q) := by
  have he : t n+brownianMeshVariance t n=t (n+1) := add_tsub_cancel_of_le (ht (by omega))
  have hi : IndepFun (brownianFullPast D (t n)) (brownianMeshIncrement D t n) Q := by
    change IndepFun (fun ω (s : Iic (t n)) => D s ω)
      (fun ω => D (t (n+1)) ω-D (t n) ω) Q
    simpa only [Function.comp_def,Function.id_def,he] using
      ((hD.indepFun_shift (t n)).comp (φ := fun f : ℝ≥0 → ℝ => f (brownianMeshVariance t n))
        (ψ := id) (measurable_pi_apply _) measurable_id).symm
  exact indepFun_static_prod_left P Q
    ((Measurable.of_eval (fun s : Iic (t n) => hmD s)).aemeasurable)
    ((hD.aemeasurable _).sub (hD.aemeasurable _)) hi

lemma brownianStaticCenteredSquare_state_indep_increment {A Ω : Type*}
    [MeasurableSpace A] [MeasurableSpace Ω]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (D : ℝ≥0 → Ω → ℝ) (hD : IsPreBrownianReal D Q) (hmD : ∀ s,Measurable (D s))
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : BrownianStaticPredictableCoefficient A t)
    (hH : ∀ k,Measurable (H k)) (n : ℕ) :
    IndepFun (fun u => (brownianStaticCenteredSquareSum D t H n u,
      brownianStaticCoefficient D t H n u))
      (fun u : A × Ω => brownianMeshIncrement D t n u.2) (P.prod Q) := by
  let Φ := fun u : A × (Iic (t n) → ℝ) => (brownianStaticPastCenteredSquareSum t ht H n u,H n u)
  have hΦ : Measurable Φ := (measurable_brownianStaticPastCenteredSquareSum t ht H hH n).prodMk (hH n)
  convert (brownianStaticFullPast_indep_increment P Q D hD hmD t ht n).comp hΦ measurable_id using 1
  · funext u
    simp only [brownianStaticCenteredSquareSum,predictableGaussianCenteredSquareSum,
      predictableGaussianSum_eq_fin_sum]
    rfl
  · rfl

theorem brownianStaticCenteredSquareSum_L2_isometry {A Ω : Type*}
    [MeasurableSpace A] [MeasurableSpace Ω]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (D : ℝ≥0 → Ω → ℝ) (hD : IsPreBrownianReal D Q) (hmD : ∀ s,Measurable (D s))
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : BrownianStaticPredictableCoefficient A t)
    (hH : ∀ k,Measurable (H k))
    (hHsq : ∀ k,Integrable (fun u => brownianStaticCoefficient D t H k u^2) (P.prod Q)) (n : ℕ) :
    Integrable (fun u => brownianStaticCenteredSquareSum D t H n u^2) (P.prod Q) ∧
      (∫ u,brownianStaticCenteredSquareSum D t H n u^2 ∂P.prod Q) =
        ∑ k∈Finset.range n,2*(brownianMeshVariance t k : ℝ)^2*
          (∫ u,brownianStaticCoefficient D t H k u^2 ∂P.prod Q) := by
  have hsnd : HasLaw (Prod.snd : A × Ω → Ω) Q (P.prod Q) :=
    ⟨measurable_snd.aemeasurable,measurePreserving_snd.map_eq⟩
  exact predictableGaussianCenteredSquareSum_L2_isometry (P.prod Q) _ _ _
    (fun k => (brownianMeshIncrement_hasLaw hD t ht k).comp hsnd)
    (aemeasurable_brownianStaticCoefficient P Q D hD hmD t H hH) hHsq
    (brownianStaticCenteredSquare_state_indep_increment P Q D hD hmD t ht H hH) n

theorem brownianCenteredSquare_refining_meanSquare_bound {A Ω : Type*}
    [MeasurableSpace A] [MeasurableSpace Ω]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (D : ℝ≥0 → Ω → ℝ) (hD : IsPreBrownianReal D Q) (hmD : ∀ s,Measurable (D s))
    (H : BrownianContinuousPastCoefficient A) (hH : ∀ s,Measurable (H s))
    (C : ℝ) (hC : ∀ s u,‖H s u‖≤C) (G : ScalarDyadicNestedGrid) (k l : ℕ)
    (η : ℝ) (hwidth : ∀ i,i<k*2^l → (G.time l (i+1) : ℝ)-G.time l i≤η) :
    0 ≤ (∫ u,brownianStaticCenteredSquareSum D (G.time l)
      (brownianContinuousMeshCoefficient H (G.time l)) (k*2^l) u^2 ∂P.prod Q) ∧
    (∫ u,brownianStaticCenteredSquareSum D (G.time l)
      (brownianContinuousMeshCoefficient H (G.time l)) (k*2^l) u^2 ∂P.prod Q) ≤
        2*C^2*η*(G.time 0 k : ℝ) := by
  have hi := integrable_brownianStaticCoefficient_sq_of_bounded P Q D hD hmD
    (G.time l) (brownianContinuousMeshCoefficient H (G.time l)) (fun i => hH _) C
    (fun i u => hC _ _)
  have he := brownianStaticCenteredSquareSum_L2_isometry P Q D hD hmD (G.time l)
    (G.monotone l) (brownianContinuousMeshCoefficient H (G.time l)) (fun i => hH _) hi (k*2^l)
  constructor
  · exact integral_nonneg (fun u => sq_nonneg _)
  · rw [he.2]
    calc
      _ ≤ ∑ i∈Finset.range (k*2^l),2*C^2*η*(brownianMeshVariance (G.time l) i : ℝ) := by
        apply Finset.sum_le_sum
        intro i hiR
        have hb : (∫ u,brownianStaticCoefficient D (G.time l)
            (brownianContinuousMeshCoefficient H (G.time l)) i u^2 ∂P.prod Q) ≤ C^2 := by
          calc
            _ ≤ ∫ _ : A × Ω,C^2 ∂P.prod Q := by
              apply integral_mono (hi i) (integrable_const _)
              intro u
              have hc := hC (G.time l i) (u.1,brownianFullPast D (G.time l i) u.2)
              rw [Real.norm_eq_abs] at hc
              change (H (G.time l i) (u.1,brownianFullPast D (G.time l i) u.2))^2≤C^2
              nlinarith [abs_nonneg (H (G.time l i) (u.1,brownianFullPast D (G.time l i) u.2)),
                sq_abs (H (G.time l i) (u.1,brownianFullPast D (G.time l i) u.2))]
            _ = C^2 := by simp
        have hv0 : 0≤(brownianMeshVariance (G.time l) i : ℝ) := NNReal.coe_nonneg _
        have hv : (brownianMeshVariance (G.time l) i : ℝ)≤η := by
          rw [brownianMeshVariance,NNReal.coe_sub (G.monotone l (by omega))]
          exact hwidth i (Finset.mem_range.mp hiR)
        calc
          _ ≤ 2*(brownianMeshVariance (G.time l) i : ℝ)^2*C^2 :=
            mul_le_mul_of_nonneg_left hb (by positivity)
          _ ≤ 2*C^2*η*(brownianMeshVariance (G.time l) i : ℝ) := by
            nlinarith [mul_nonneg (sq_nonneg C) (mul_nonneg hv0 (sub_nonneg.mpr hv))]
      _ = 2*C^2*η*(G.time 0 k : ℝ) := by
        rw [← Finset.mul_sum,G.variance_sum]

theorem brownianCenteredSquare_refining_tendsto_L2 {A Ω : Type*}
    [MeasurableSpace A] [MeasurableSpace Ω]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (D : ℝ≥0 → Ω → ℝ) (hD : IsPreBrownianReal D Q) (hmD : ∀ s,Measurable (D s))
    (H : BrownianContinuousPastCoefficient A) (hH : ∀ s,Measurable (H s))
    (C : ℝ) (hC : ∀ s u,‖H s u‖≤C) (G : ScalarDyadicNestedGrid) (k : ℕ)
    (η : ℕ → ℝ) (hη : Tendsto η atTop (𝓝 0))
    (hwidth : ∀ l i,i<k*2^l → (G.time l (i+1) : ℝ)-G.time l i≤η l) :
    Tendsto (fun l => ∫ u,brownianStaticCenteredSquareSum D (G.time l)
      (brownianContinuousMeshCoefficient H (G.time l)) (k*2^l) u^2 ∂P.prod Q) atTop (𝓝 0) := by
  have hb := fun l => brownianCenteredSquare_refining_meanSquare_bound
    P Q D hD hmD H hH C hC G k l (η l) (hwidth l)
  apply squeeze_zero (fun l => (hb l).1) (fun l => (hb l).2)
  simpa using (hη.const_mul (2*C^2)).mul_const (G.time 0 k : ℝ)

end SKConstants
