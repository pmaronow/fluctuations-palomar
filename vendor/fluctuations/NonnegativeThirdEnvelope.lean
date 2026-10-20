module

public import VaryingProfileSmallClock

@[expose] public section

noncomputable section
set_option maxHeartbeats 1000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

theorem scalarThirdGaussianEnvelope_parameter_tendsto {T q : ℝ} (hT : 0 < T)
    {α : ℕ → boundedMassProfiles} {β : boundedMassProfiles}
    (hα : Tendsto α atTop (𝓝 β)) (hq : 0 < q) (a : ℝ) :
    Tendsto (fun n => scalarThirdGaussianEnvelope hT (α n) a q) atTop
      (𝓝 (scalarThirdGaussianEnvelope hT β a q)) := by
  let B : ℝ := ReplicaTree.attachmentCount 1 2
  have hG : Continuous (gaussianLinearEnvelope (T*q) a) :=
    (realGaussianKernel_continuous _).mul (Real.continuous_exp.comp (continuous_abs.const_mul a))
  have hG0 (x : ℝ) : 0 ≤ gaussianLinearEnvelope (T*q) a x :=
    mul_nonneg (realGaussianKernel_pos (mul_pos hT hq) x).le (Real.exp_nonneg _)
  have hj := scalarTailSpatialJet_parameter_tendsto hT hα q 3
  have ht := tendsto_integral_filter_of_dominated_convergence
    (F := fun n x => gaussianLinearEnvelope (T*q) a x*(scalarTailSpatialJet hT (α n) 3 q (fun _ => x))^2)
    (f := fun x => gaussianLinearEnvelope (T*q) a x*(scalarTailSpatialJet hT β 3 q (fun _ => x))^2)
    (bound := fun x => gaussianLinearEnvelope (T*q) a x*B^2)
    (Eventually.of_forall (fun n => by
      have hp : Continuous (fun x : ℝ => (fun _ : Fin 1 => x)) := continuous_pi (fun _ => continuous_id)
      have hc0 := (scalarTailSpatialJet_smooth hT (α n) 2 q).continuous.comp hp
      have hc : Continuous (fun x : ℝ => scalarTailSpatialJet hT (α n) 3 q (fun _ => x)) := by
        simpa only [Function.comp_def] using hc0
      exact (hG.mul (hc.pow 2)).aestronglyMeasurable))
    (Eventually.of_forall (fun n => Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hG0 x) (sq_nonneg _))]
      apply mul_le_mul_of_nonneg_left _ (hG0 x)
      have hb : |scalarTailSpatialJet hT (α n) 3 q (fun _ => x)| ≤ B :=
        scalarProfileJet_bound (rescaledMassProfile (α n) hT)
          (fun s => ((α n).property.1 (s/T)).2) (T*q) (Real.toNNReal (T*(1-q))) 2 x
      have hh := pow_le_pow_left₀ (abs_nonneg _) hb 2
      simpa only [sq_abs, B] using hh)))
    ((gaussianLinearEnvelope_integrable (mul_pos hT hq) a).mul_const (B^2))
    (Eventually.of_forall (fun x => by
      simpa only [Function.comp_def] using ((hj.tendsto_at (fun _ => x)).pow 2).const_mul
        (gaussianLinearEnvelope (T*q) a x)))
  exact ht.div_const q

private def positiveMassRegularization (α : boundedMassProfiles) (n : ℕ) : boundedMassProfiles :=
  ⟨fun s => max (α.val s) (1/(n+2:ℝ)), by
    constructor
    · intro s
      exact ⟨(α.property.1 s).1.trans (le_max_left _ _), max_le (α.property.1 s).2 (by
        apply (div_le_one₀ (by positivity : (0:ℝ)<n+2)).mpr
        linarith [Nat.cast_nonneg (α := ℝ) n])⟩
    · exact α.property.2.max monotone_const⟩

private theorem positiveMassRegularization_tendsto (α : boundedMassProfiles) :
    Tendsto (positiveMassRegularization α) atTop (𝓝 α) := by
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro s
  have ht : Tendsto (fun n : ℕ => 1/(n+2:ℝ)) atTop (𝓝 0) := by
    convert (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ)).comp
      (tendsto_add_atTop_nat 2) using 1 <;> simp [Function.comp_def, Nat.cast_add]
  simpa only [positiveMassRegularization, max_eq_left (α.property.1 s).1] using
    ((tendsto_const_nhds (x := α.val s)).max ht)

theorem scalarPlantedThirdSquare_envelope_nonnegative {T q : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (hq : 0 < q) (hq1 : q ≤ 1)
    (hc : ∀ x ∈ Ico (0:ℝ) q, ContinuousWithinAt α.val (Ici x) x) :
    scalarThirdGaussianEnvelope hT α (-2) q/gaussianLinearEnvelopeMass (T*q) 2 ≤
      scalarPlantedJetPower hT α 2 2 q/q ∧
    scalarPlantedJetPower hT α 2 2 q/q ≤
      scalarThirdGaussianEnvelope hT α 2 q/gaussianLinearEnvelopeMass (T*q) (-2) := by
  have ha := positiveMassRegularization_tendsto α
  have he (n : ℕ) := scalarPlantedThirdSquare_envelope hT (positiveMassRegularization α n) hq hq1
    (by exact (by positivity : (0:ℝ)<1/(n+2:ℝ)).trans_le (le_max_right _ _))
    (fun x hx => (hc x hx).max continuousWithinAt_const)
  have hl := (scalarThirdGaussianEnvelope_parameter_tendsto hT ha hq (-2)).div_const
    (gaussianLinearEnvelopeMass (T*q) 2)
  have hu := (scalarThirdGaussianEnvelope_parameter_tendsto hT ha hq 2).div_const
    (gaussianLinearEnvelopeMass (T*q) (-2))
  have hp := (scalarPlantedJetPower_parameter_tendsto hT ha 2 2 q).div_const q
  exact ⟨le_of_tendsto_of_tendsto hl hp (Eventually.of_forall (fun n => (he n).1)),
    le_of_tendsto_of_tendsto hp hu (Eventually.of_forall (fun n => (he n).2))⟩

theorem scalarPlantedThirdSquare_joint_smallClock_tendsto {T : ℝ} (hT : 0 < T)
    {α : ℕ → boundedMassProfiles} {β : boundedMassProfiles}
    (hα : Tendsto α atTop (𝓝 β)) {q : ℕ → ℝ}
    (hq : Tendsto q atTop (𝓝 0)) (hqp : ∀ᶠ n in atTop, 0 < q n)
    (hc : ∀ n x, ContinuousWithinAt (α n).val (Ici x) x) :
    Tendsto (fun n => scalarPlantedJetPower hT (α n) 2 2 (q n)/(q n)) atTop
      (𝓝 (T*(scalarTailSpatialJet hT β 4 0 0)^2)) := by
  have hqw : Tendsto q atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr ⟨hq, hqp⟩
  have hl := (scalarThirdGaussianEnvelope_joint_smallClock_tendsto hT hα hq hqp (-2)).div
    ((gaussianLinearEnvelopeMass_tendsto hT 2).comp hqw) one_ne_zero
  have hu := (scalarThirdGaussianEnvelope_joint_smallClock_tendsto hT hα hq hqp 2).div
    ((gaussianLinearEnvelopeMass_tendsto hT (-2)).comp hqw) one_ne_zero
  simp only [div_one] at hl hu
  have he : ∀ᶠ n in atTop,
      scalarThirdGaussianEnvelope hT (α n) (-2) (q n)/gaussianLinearEnvelopeMass (T*q n) 2 ≤
        scalarPlantedJetPower hT (α n) 2 2 (q n)/(q n) ∧
      scalarPlantedJetPower hT (α n) 2 2 (q n)/(q n) ≤
        scalarThirdGaussianEnvelope hT (α n) 2 (q n)/gaussianLinearEnvelopeMass (T*q n) (-2) := by
    filter_upwards [hqp, hq.eventually (gt_mem_nhds zero_lt_one)] with n hn hn1
    exact scalarPlantedThirdSquare_envelope_nonnegative hT (α n) hn hn1.le (fun x _ => hc n x)
  exact hl.squeeze' hu (he.mono (fun _ hx => hx.1)) (he.mono (fun _ hx => hx.2))

end OAI.SKFluctuations.LaplaceWindowFormalization
