module

public import ScalarLowClockCalibration

@[expose] public section

noncomputable section
set_option maxHeartbeats 1000000

namespace OAI.SKFluctuations.LaplaceWindowFormalization

open MeasureTheory ProbabilityTheory Filter Set Hierarchy GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

theorem scalarProfileJet_joint_parameter_window_tendsto
    {α : ℕ → boundedMassProfiles} {β : boundedMassProfiles}
    (hα : Tendsto α atTop (𝓝 β))
    {l : ℕ → ℝ} {t : ℕ → ℝ≥0} {L : ℝ} {T : ℝ≥0}
    (hl : Tendsto l atTop (𝓝 L)) (ht : Tendsto t atTop (𝓝 T)) (k : ℕ) :
    TendstoUniformly (fun n => scalarProfileJet (boundedNonnegativeProfile (α n)) (l n) (t n) k)
      (scalarProfileJet (boundedNonnegativeProfile β) L T k) atTop := by
  apply jet_tendstoUniformly_of_limit
    (fun n j => scalarProfileJet (boundedNonnegativeProfile (α n)) (l n) (t n) j)
    (scalarProfileJet (boundedNonnegativeProfile β) L T)
    (fun n j x => scalarProfileJet_hasDerivAt _ (fun s => ((α n).property.1 s).2) _ _ j x)
    (fun j => ⟨(ReplicaTree.attachmentCount 1 j:ℝ), fun n x =>
      scalarProfileJet_bound _ (fun s => ((α n).property.1 s).2) _ _ j x⟩)
    (scalarProfileJet_hasDerivAt _ (fun s => (β.property.1 s).2) L T)
  have hparam := scalarTerminal.profile_parameter_tendstoUniformly hα L T
  have hwindow : Tendsto (fun n => |l n-L|+(3/2:ℝ)*|(t n:ℝ)-T|) atTop (𝓝 0) := by
    have hc : Tendsto (fun n => (t n:ℝ)) atTop (𝓝 (T:ℝ)) := (NNReal.continuous_coe.tendsto T).comp ht
    simpa only [sub_self, abs_zero, mul_zero, add_zero] using
      ((hl.sub_const L).abs.add ((hc.sub_const (T:ℝ)).abs.const_mul (3/2:ℝ)))
  rw [Metric.tendstoUniformly_iff] at hparam ⊢
  intro ε hε
  filter_upwards [hwindow.eventually (gt_mem_nhds (half_pos hε)), hparam (ε/2) (half_pos hε)] with n hn hp x
  rw [Real.dist_eq, scalarProfileJet_zero _ (fun s => (β.property.1 s).2),
    scalarProfileJet_zero _ (fun s => ((α n).property.1 s).2)]
  have hw := HeatJet.profile_window_stability scalarTerminal_admissible
    (boundedNonnegativeProfile (α n)) (fun s => ((α n).property.1 s).2) (l n) L (t n) T (fun _ => x)
  have hp' : |scalarTerminal.nonnegativeProfileValue (boundedNonnegativeProfile (α n)) L T (fun _ => x)-
      scalarTerminal.nonnegativeProfileValue (boundedNonnegativeProfile β) L T (fun _ => x)| < ε/2 := by
    simpa only [Real.dist_eq, abs_sub_comm] using hp (fun _ => x)
  have ha := abs_sub_le
    (scalarTerminal.nonnegativeProfileValue (boundedNonnegativeProfile β) L T (fun _ => x))
    (scalarTerminal.nonnegativeProfileValue (boundedNonnegativeProfile (α n)) L T (fun _ => x))
    (scalarTerminal.nonnegativeProfileValue (boundedNonnegativeProfile (α n)) (l n) (t n) (fun _ => x))
  rw [abs_sub_comm] at hw
  rw [abs_sub_comm] at hp'
  linarith

theorem scalarTailSpatialJet_joint_parameter_window_tendsto {T : ℝ} (hT : 0 < T)
    {α : ℕ → boundedMassProfiles} {β : boundedMassProfiles}
    (hα : Tendsto α atTop (𝓝 β)) {q : ℕ → ℝ} {r : ℝ}
    (hq : Tendsto q atTop (𝓝 r)) (k : ℕ) :
    TendstoUniformly (fun n => scalarTailSpatialJet hT (α n) k (q n))
      (scalarTailSpatialJet hT β k r) atTop := by
  have hr := (continuous_rescaledBoundedProfile hT).tendsto β |>.comp hα
  have hl := hq.const_mul T
  have ht := continuous_real_toNNReal.tendsto (T*(1-r)) |>.comp
    ((tendsto_const_nhds.sub hq).const_mul T)
  have hh := scalarProfileJet_joint_parameter_window_tendsto hr hl ht k
  rw [Metric.tendstoUniformly_iff] at hh ⊢
  intro ε hε
  filter_upwards [hh ε hε] with n hn x
  exact hn (x 0)

theorem scalarThirdSlope_joint_parameter_smallClock_tendsto {T : ℝ} (hT : 0 < T)
    {α : ℕ → boundedMassProfiles} {β : boundedMassProfiles}
    (hα : Tendsto α atTop (𝓝 β)) {q z : ℕ → ℝ}
    (hq : Tendsto q atTop (𝓝 0)) (hz : Tendsto z atTop (𝓝 0)) :
    Tendsto (fun n => scalarThirdSlope hT (α n) (q n) (z n)) atTop
      (𝓝 (scalarTailSpatialJet hT β 4 0 0)) := by
  have hj := scalarTailSpatialJet_joint_parameter_window_tendsto hT hα hq 4
  have ht := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (F := fun n u => scalarTailSpatialJet hT (α n) 4 (q n) (fun _ => u*z n))
    (f := fun _ => scalarTailSpatialJet hT β 4 0 0)
    (μ := volume) (a := (0:ℝ)) (b := 1)
    (fun _ => (ReplicaTree.attachmentCount 1 3:ℝ))
    (Eventually.of_forall (fun n => by
      exact ((scalarTailSpatialJet_smooth hT (α n) 3 (q n)).continuous.comp
        (continuous_pi (fun _ => continuous_id.mul continuous_const))).aestronglyMeasurable))
    (Eventually.of_forall (fun n => Eventually.of_forall (fun u _ => by
      rw [Real.norm_eq_abs]
      exact scalarProfileJet_bound (rescaledMassProfile (α n) hT)
        (fun s => ((α n).property.1 (s/T)).2) _ _ 3 (u*z n))))
    intervalIntegrable_const (Eventually.of_forall (by
      intro u _
      have hzu : Tendsto (fun n => (fun _ : Fin 1 => u*z n)) atTop (𝓝 0) := by
        apply tendsto_pi_nhds.mpr
        intro i
        simpa using hz.const_mul u
      exact hj.tendsto_comp (scalarTailSpatialJet_smooth hT β 3 0).continuous.continuousAt hzu))
  simpa only [scalarThirdSlope, intervalIntegral.integral_const, sub_zero, one_smul] using ht

theorem scalarThirdGaussianEnvelope_joint_smallClock_tendsto {T : ℝ} (hT : 0 < T)
    {α : ℕ → boundedMassProfiles} {β : boundedMassProfiles}
    (hα : Tendsto α atTop (𝓝 β)) {q : ℕ → ℝ}
    (hq : Tendsto q atTop (𝓝 0)) (hqp : ∀ᶠ n in atTop, 0 < q n) (a : ℝ) :
    Tendsto (fun n => scalarThirdGaussianEnvelope hT (α n) a (q n)) atTop
      (𝓝 (T*(scalarTailSpatialJet hT β 4 0 0)^2)) := by
  let F := fun (n : ℕ) (x : ℝ) => x^2*(scalarThirdSlope hT (α n) (q n) (Real.sqrt (T*q n)*x))^2*
    Real.exp (a*Real.sqrt (T*q n)*|x|)
  let B : ℝ := ReplicaTree.attachmentCount 1 3
  have hsqrt : Tendsto (fun n => Real.sqrt (T*q n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp (by simpa only [mul_zero] using hq.const_mul T)
  have hs : ∀ᶠ n in atTop, 0 ≤ Real.sqrt (T*q n) ∧ Real.sqrt (T*q n) ≤ 1 := by
    filter_upwards [hsqrt.eventually (gt_mem_nhds (zero_lt_one : (0:ℝ) < 1))] with n hn
    exact ⟨Real.sqrt_nonneg _, hn.le⟩
  have ht := tendsto_integral_filter_of_dominated_convergence
    (F := F) (f := fun x => x^2*(scalarTailSpatialJet hT β 4 0 0)^2)
    (μ := gaussianReal 0 1) (bound := fun x => B^2*(x^2*Real.exp (|a| * |x|)))
    (Eventually.of_forall (fun n => by
      have hcont : Continuous (F n) := by
        dsimp only [F]
        have hp : Continuous (fun x : ℝ => (q n, Real.sqrt (T*q n)*x)) := by fun_prop
        have hc0 := (scalarThirdSlope_continuous hT (α n)).comp hp
        have hc : Continuous (fun x : ℝ => scalarThirdSlope hT (α n) (q n) (Real.sqrt (T*q n)*x)) := by
          simpa only [Function.comp_def] using hc0
        have he : Continuous (fun x : ℝ => Real.exp (a*Real.sqrt (T*q n)*|x|)) :=
          Real.continuous_exp.comp (continuous_abs.const_mul (a*Real.sqrt (T*q n)))
        have hprod := ((continuous_pow 2).mul (hc.pow 2)).mul he
        convert hprod using 1
      exact hcont.aestronglyMeasurable)) (by
      filter_upwards [hs] with n hsn
      apply Eventually.of_forall
      intro x
      change ‖F n x‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (Real.exp_nonneg _))]
      have he : a*Real.sqrt (T*q n) ≤ |a| :=
        (mul_le_mul_of_nonneg_right (le_abs_self a) hsn.1).trans
          (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hsn.2 (abs_nonneg a))
      have hr := pow_le_pow_left₀
        (abs_nonneg (scalarThirdSlope hT (α n) (q n) (Real.sqrt (T*q n)*x)))
        (scalarThirdSlope_bound hT (α n) (q n) (Real.sqrt (T*q n)*x)) 2
      rw [sq_abs] at hr
      calc
        F n x ≤ x^2*B^2*Real.exp (|a| * |x|) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hr (sq_nonneg _))
            (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right he (abs_nonneg _)))
            (Real.exp_nonneg _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        _ = _ := by ring)
    ((gaussianStandard_expabs_sq_integrable |a|).const_mul (B^2)) (Eventually.of_forall (by
      intro x
      have hsl := scalarThirdSlope_joint_parameter_smallClock_tendsto hT hα hq
        (by simpa using hsqrt.mul_const x)
      have hexp : Tendsto (fun n => Real.exp (a*Real.sqrt (T*q n)*|x|)) atTop (𝓝 1) := by
        have ha : Tendsto (fun n => a*Real.sqrt (T*q n)*|x|) atTop (𝓝 0) := by
          simpa only [mul_zero, zero_mul] using (hsqrt.const_mul a).mul_const |x|
        simpa only [Function.comp_def, mul_zero, zero_mul, Real.exp_zero] using
          (Real.continuous_exp.tendsto 0).comp ha
      simpa only [F, mul_one] using ((hsl.pow 2).const_mul (x^2)).mul hexp))
  rw [integral_mul_const, gaussianStandard_sq_integral, one_mul] at ht
  apply (ht.const_mul T).congr'
  filter_upwards [hqp] with n hn
  exact (scalarThirdGaussianEnvelope_rescale hT (α n) a hn).symm

end OAI.SKFluctuations.LaplaceWindowFormalization
