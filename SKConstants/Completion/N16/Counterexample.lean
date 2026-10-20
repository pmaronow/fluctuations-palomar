module

public import SKConstants.Completion.N16.AngleLaw

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open SKConstantsOAI.ZeroTemperatureSK
open scoped NNReal Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SKConstants.N16
open Blueprint

theorem stdGaussian_smul_ne {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Nontrivial E] (a : ℝ) (ha : a ^ 2 ≠ 1) :
    (stdGaussian E).map (fun x => a • x) ≠ stdGaussian E := by
  intro h
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  let L : StrongDual ℝ E := innerSL ℝ v
  have hvar := congrArg (fun μ : Measure E => Var[L; μ]) h
  rw [variance_map (by fun_prop) (by fun_prop)] at hvar
  have he : L ∘ (fun x : E => a • x) = fun x => a * L x := by
    funext x
    exact L.map_smul a x
  rw [he, variance_const_mul, variance_dual_stdGaussian] at hvar
  have hpos : 0 < ‖L‖ ^ 2 := by
    change 0 < ‖innerSL ℝ v‖ ^ 2
    rw [innerSL_apply_norm]
    exact sq_pos_of_pos (norm_pos_iff.mpr hv)
  exact ha (mul_right_cancel₀ (ne_of_gt hpos) (hvar.trans (one_mul _).symm))

theorem angle_matrix_law_of_smoothing_ge_one {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (p : Parameters) (n : ℕ) (θ : ℝ)
    (hδ : 1 ≤ (smoothing p n : ℝ)) :
    (experimentLaw W p n).map (fun z => angleMatrix p n θ z.1 z.2) =
      (primLaw n).map (fun g => Real.sqrt (smoothing p n : ℝ) • g) := by
  have hs : Real.sqrt (1 - (smoothing p n : ℝ)) = 0 :=
    Real.sqrt_eq_zero_of_nonpos (by linarith)
  have hm : (experimentLaw W p n).map (fun z => z.2.1) = outerLaw n := by
    exact ((measurePreserving_fst (μ := outerLaw n)
      (ν := ((fineAuxLaw W p n).prod (fineAuxLaw W p n)).prod
        (Measure.infinitePi (fun _ : ℕ => thresholdLaw n)))).comp
      (measurePreserving_snd (μ := outerLaw n) (ν := internalLaw W p n))).map_eq
  have h := congrArg (fun μ : Measure (Outer n) => μ.map
    (fun z => Real.sqrt (smoothing p n : ℝ) •
      (Real.cos θ • z.1 + Real.sin θ • z.2))) hm
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at h
  have hrot := congrArg (fun μ : Measure (Prim n) => μ.map
    (fun g => Real.sqrt (smoothing p n : ℝ) • g))
    (M6.primitiveGaussian_rotation_law (ι := Fin n × Fin n) θ)
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at hrot
  simpa only [Function.comp_def, angleMatrix, hs, zero_smul, zero_add] using h.trans hrot

theorem angle_run_law_ne_of_smoothing_gt_one {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (p : Parameters) (n : ℕ) (θ : ℝ) (k : ℕ)
    (hn : 0 < n) (hδ : 1 < (smoothing p n : ℝ)) :
    (experimentLaw W p n).map (angleInput p n θ k) ≠ runLaw W p n := by
  intro h
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hm : Measurable (angleInput p n θ k) :=
    (measurable_angleMatrix p n θ).prodMk
      ((measurable_angleAux p n θ).prodMk (measurable_thresholdAt p n k))
  have hp := congrArg (fun μ : Measure (RunInput p n) => μ.map Prod.fst) h
  rw [Measure.map_map measurable_fst hm, runLaw, Measure.map_fst_prod,
    measure_univ, one_smul] at hp
  have he : (primLaw n).map (fun g => Real.sqrt (smoothing p n : ℝ) • g) = primLaw n :=
    (angle_matrix_law_of_smoothing_ge_one W p n θ hδ.le).symm.trans hp
  exact stdGaussian_smul_ne (Real.sqrt (smoothing p n : ℝ))
    (by rw [Real.sq_sqrt (smoothing p n).coe_nonneg]; linarith) he

theorem not_PerAngleLawStatement {Ω : Type} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) : ¬ PerAngleLawStatement := by
  intro h
  let p : Parameters := { g0Parameters with D := -1 }
  obtain ⟨n, hn, hangle⟩ := ((eventually_ge_atTop (2 : ℕ)).and (h p W)).exists
  have hδ : 1 < (smoothing p n : ℝ) := by
    simp only [smoothing, p, neg_neg, Real.rpow_one,
      Real.coe_toNNReal _ (Nat.cast_nonneg n)]
    exact_mod_cast (show 1 < n by omega)
  exact angle_run_law_ne_of_smoothing_gt_one W p n 0 0 (by omega) hδ (hangle 0 0).2

end SKConstants.N16
