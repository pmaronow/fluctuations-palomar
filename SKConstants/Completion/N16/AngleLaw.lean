module

public import SKConstants.Completion.N16.AuxRotation
public import SKConstants.Completion.LM6.Regression
public import SKConstants.Completion.Blueprint.NodesLower

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open SKConstantsOAI.ZeroTemperatureSK
open scoped NNReal Topology unitInterval
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SKConstants.N16
open Blueprint GaussianProposal
variable {Ω : Type*} [MeasurableSpace Ω]

theorem matrix_pair_regression (p : Parameters) (n : ℕ) (θ : ℝ)
    (hδ : (smoothing p n : ℝ) ≤ 1) :
    ((outerLaw n).prod (outerLaw n)).map
      (fun z => (z.1.1, Real.sqrt (1 - (smoothing p n : ℝ)) • baseMatrix p n z.1 +
        Real.sqrt (smoothing p n : ℝ) • (Real.cos θ • z.2.1 + Real.sin θ • z.2.2))) =
    (outerLaw n).map (fun z => (z.1, (1 - (smoothing p n : ℝ)) • z.1 +
      Real.sqrt ((smoothing p n : ℝ) * (2 - (smoothing p n : ℝ))) • z.2)) := by
  have h := M6.coupledMatrix_target_pair_law n (smoothing p n : ℝ) θ
    (smoothing p n).coe_nonneg hδ
  rw [gaussianEuclideanSmoothing_compProd_eq_affine_map,
    Real.coe_toNNReal _ (mul_nonneg (smoothing p n).coe_nonneg (by linarith))] at h
  have ha := (measurePreserving_prodAssoc (primLaw n) (primLaw n) (outerLaw n)).map_eq
  have hh := congrArg (fun μ => μ.map (fun z =>
    (z.1, M6.coupledMatrixInput (smoothing p n : ℝ) θ z))) ha
  rw [Measure.map_map (by unfold M6.coupledMatrixInput; fun_prop) (by fun_prop)] at hh
  exact hh.trans h

theorem auxiliary_threshold_law (W : BrownianSystem Ω) (p : Parameters)
    (n : ℕ) (θ : ℝ) (k : ℕ) :
    (((fineAuxLaw W p n).prod (fineAuxLaw W p n)).prod
      (Measure.infinitePi (fun _ : ℕ => thresholdLaw n))).map
      (fun z => (combineAux (Real.cos θ) (Real.sin θ) z.1.1 z.1.2, z.2 k)) =
    (fineAuxLaw W p n).prod (thresholdLaw n) := by
  have h := Measure.map_prod_map
    ((fineAuxLaw W p n).prod (fineAuxLaw W p n))
    (Measure.infinitePi (fun _ : ℕ => thresholdLaw n))
    (measurable_combineAux (Real.cos θ) (Real.sin θ)) (measurable_pi_apply k)
  rw [replayAux_rotation W _ _ _ _ _ (by nlinarith [Real.sin_sq_add_cos_sq θ]),
    Measure.infinitePi_map_eval] at h
  exact h.symm

theorem angle_joint_law (W : BrownianSystem Ω) (p : Parameters)
    (n : ℕ) (θ : ℝ) (k : ℕ) (hδ : (smoothing p n : ℝ) ≤ 1) :
    (experimentLaw W p n).map (fun z => (z.1.1, angleInput p n θ k z)) =
      (angleLaw W p n).map (regressionInput p n) := by
  let M := (outerLaw n).prod (outerLaw n)
  let A := ((fineAuxLaw W p n).prod (fineAuxLaw W p n)).prod
    (Measure.infinitePi (fun _ : ℕ => thresholdLaw n))
  let F : (Outer n × Outer n) → Prim n × Prim n := fun z =>
    (z.1.1, Real.sqrt (1 - (smoothing p n : ℝ)) • baseMatrix p n z.1 +
      Real.sqrt (smoothing p n : ℝ) • (Real.cos θ • z.2.1 + Real.sin θ • z.2.2))
  let B : (FineAux p n × FineAux p n) × (ℕ → Fin n → I) →
      FineAux p n × (Fin n → I) := fun z =>
    (combineAux (Real.cos θ) (Real.sin θ) z.1.1 z.1.2, z.2 k)
  let R : (Prim n × Prim n) → Prim n × Prim n := fun z =>
    (z.1, (1 - (smoothing p n : ℝ)) • z.1 +
      Real.sqrt ((smoothing p n : ℝ) * (2 - (smoothing p n : ℝ))) • z.2)
  let T : (Prim n × Prim n) × (FineAux p n × (Fin n → I)) →
      Prim n × RunInput p n := fun z => (z.1.1, (z.1.2, z.2))
  have hF : Measurable F := by dsimp [F, baseMatrix, gaussianRotation]; fun_prop
  have hB : Measurable B := (measurable_combineAux _ _).comp
    measurable_fst |>.prodMk ((measurable_pi_apply k).comp measurable_snd)
  have hR : Measurable R := by fun_prop
  have hT : Measurable T := by fun_prop
  have hsplit : (experimentLaw W p n).map
      (fun z => ((z.1, z.2.1), z.2.2)) = M.prod A := by
    exact (measurePreserving_prodAssoc (outerLaw n) (outerLaw n) A).symm.map_eq
  have hprod : (M.prod A).map (Prod.map F B) =
      ((outerLaw n).map R).prod ((fineAuxLaw W p n).prod (thresholdLaw n)) := by
    rw [← Measure.map_prod_map _ _ hF hB,
      matrix_pair_regression p n θ hδ, auxiliary_threshold_law W p n θ k]
  calc
    _ = ((M.prod A).map (Prod.map F B)).map T := by
      rw [Measure.map_map hT (hF.prodMap hB), ← hsplit,
        Measure.map_map (hT.comp (hF.prodMap hB)) (by fun_prop)]
      rfl
    _ = (((outerLaw n).map R).prod ((fineAuxLaw W p n).prod (thresholdLaw n))).map T := by
      rw [hprod]
    _ = _ := by
      have ht := Measure.map_prod_map (outerLaw n)
        ((fineAuxLaw W p n).prod (thresholdLaw n)) hR measurable_id
      rw [Measure.map_id] at ht
      rw [ht, Measure.map_map hT (hR.prodMap measurable_id)]
      rfl

theorem angle_run_law (W : BrownianSystem Ω) (p : Parameters)
    (n : ℕ) (θ : ℝ) (k : ℕ) (hδ : (smoothing p n : ℝ) ≤ 1) :
    (experimentLaw W p n).map (angleInput p n θ k) = runLaw W p n := by
  have h := congrArg (fun μ : Measure (Prim n × RunInput p n) => μ.map Prod.snd)
    (angle_joint_law W p n θ k hδ)
  have hm : Measurable (angleInput p n θ k) :=
    (measurable_angleMatrix p n θ).prodMk
      ((measurable_angleAux p n θ).prodMk (measurable_thresholdAt p n k))
  have hr : Measurable (regressionInput p n) := by unfold regressionInput; fun_prop
  rw [Measure.map_map measurable_snd (measurable_fst.fst.prodMk hm),
    Measure.map_map measurable_snd hr] at h
  have hunit : (1 - (smoothing p n : ℝ)) ^ 2 +
      (Real.sqrt ((smoothing p n : ℝ) * (2 - (smoothing p n : ℝ)))) ^ 2 = 1 := by
    rw [Real.sq_sqrt (mul_nonneg (smoothing p n).coe_nonneg (by linarith))]
    ring
  have hrot := M6.primitiveGaussian_normalized_sum_law (ι := Fin n × Fin n)
    (1 - (smoothing p n : ℝ))
    (Real.sqrt ((smoothing p n : ℝ) * (2 - (smoothing p n : ℝ)))) hunit
  have hout : (angleLaw W p n).map
      (fun y => ((1 - (smoothing p n : ℝ)) • y.1.1 +
        Real.sqrt ((smoothing p n : ℝ) * (2 - (smoothing p n : ℝ))) • y.1.2, y.2)) =
      runLaw W p n := by
    have ht := Measure.map_prod_map (outerLaw n)
      ((fineAuxLaw W p n).prod (thresholdLaw n))
      (show Measurable (fun z : Outer n => (1 - (smoothing p n : ℝ)) • z.1 +
        Real.sqrt ((smoothing p n : ℝ) * (2 - (smoothing p n : ℝ))) • z.2) by fun_prop)
      measurable_id
    rw [hrot, Measure.map_id] at ht
    exact ht.symm
  exact h.trans hout

end SKConstants.N16
