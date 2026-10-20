module

public import ComparisonPerturbedEndpointBand
public import ComparisonMacroscopicScalarAttainment

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal

theorem initialShellMatrixClock_l1_constant {T epsilon shell : ℝ}
    (hepsilon : 0 ≤ epsilon) (hshell : shell ∈ Icc (0:ℝ) 1) :
    (∫u in (0:ℝ)..1, |initialShellMatrixClock T epsilon shell u-T|)=shell*epsilon := by
  have heq : (∫u in (0:ℝ)..1, |initialShellMatrixClock T epsilon shell u-T|)=
      ∫u in (0:ℝ)..1, (Iic shell).indicator (fun _ : ℝ=>epsilon) u := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne shell] with u hu _
    by_cases hus : u < shell
    · simp [initialShellMatrixClock,hus,hus.le,
        show T-epsilon-T = -epsilon by ring,abs_of_nonneg hepsilon]
    · have hsu : shell < u := lt_of_le_of_ne (le_of_not_gt hus) (Ne.symm hu)
      simp [initialShellMatrixClock,hus,not_le.mpr hsu]
  rw [heq]
  change (∫u in (0:ℝ)..1, {u : ℝ | u ≤ shell}.indicator (fun _=>epsilon) u)=_
  rw [intervalIntegral.integral_indicator hshell]
  simp

theorem shell_comparisonEndpointL1Cost {T epsilon shell : ℝ}
    (hepsilon : 0 ≤ epsilon) (hshell : shell ∈ Icc (0:ℝ) 1) :
    comparisonEndpointL1Cost T (initialShellMatrixClock T epsilon shell) (fun _=>0)=
      shell*epsilon/4 := by
  unfold comparisonEndpointL1Cost
  rw [initialShellMatrixClock_l1_constant hepsilon hshell]
  simp only [abs_zero,intervalIntegral.integral_zero,mul_zero,add_zero]
  ring

theorem shell_clock_l1_tendsto_zero {T E : ℝ} {epsilon shell : ℕ→ℝ}
    (hepsilon : ∀n,epsilon n ∈ Icc (0:ℝ) E)
    (hshell : ∀n,shell n ∈ Icc (0:ℝ) 1)
    (hlim : Tendsto shell atTop (𝓝 0)) :
    Tendsto (fun n=>∫u in (0:ℝ)..1,
      |initialShellMatrixClock T (epsilon n) (shell n) u-T|) atTop (𝓝 0) := by
  have hupper : Tendsto (fun n=>shell n*E) atTop (𝓝 0) := by
    simpa only [zero_mul] using hlim.mul_const E
  apply squeeze_zero (fun n=>by
    rw [initialShellMatrixClock_l1_constant (hepsilon n).1 (hshell n)]
    exact mul_nonneg (hshell n).1 (hepsilon n).1) (fun n=>by
    rw [initialShellMatrixClock_l1_constant (hepsilon n).1 (hshell n)]
    exact mul_le_mul_of_nonneg_left (hepsilon n).2 (hshell n).1) hupper

theorem shell_endpoint_cost_tendsto_zero {T E : ℝ} {epsilon shell : ℕ→ℝ}
    (hepsilon : ∀n,epsilon n ∈ Icc (0:ℝ) E)
    (hshell : ∀n,shell n ∈ Icc (0:ℝ) 1)
    (hlim : Tendsto shell atTop (𝓝 0)) :
    Tendsto (fun n=>comparisonEndpointL1Cost T
      (initialShellMatrixClock T (epsilon n) (shell n)) (fun _=>0)) atTop (𝓝 0) := by
  simpa only [comparisonEndpointL1Cost,abs_zero,intervalIntegral.integral_zero,mul_zero,
    add_zero,mul_zero] using (shell_clock_l1_tendsto_zero hepsilon hshell hlim).const_mul (1/4:ℝ)

theorem fixed_shell_pressure_tendsto_scalarMinimum {T epsilon shell : ℝ}
    (hepsilon : 0 ≤ epsilon) (hgap : 0 < T-epsilon) :
    Tendsto (fun n=>realOrderedSKPathPressure n
      (initialShellMatrixClock T epsilon shell) (fun _=>0) 0) atTop
      (𝓝 (generalScalarMinimum (initialShellMatrixClock T epsilon shell) (fun _=>0))) := by
  have hT : 0 < T := by linarith
  apply generalMacroPressure_tendsto_on _ _ hT hgap
    ((initialShellMatrixClock_monotone T shell hepsilon).monotoneOn _)
    (fun _ _ _ _ _=>le_rfl)
  · intro u _
    unfold initialShellMatrixClock
    split_ifs <;> constructor <;> linarith
  · intro u _
    unfold initialShellMatrixClock
    split_ifs <;> linarith
  · intro _ _; exact le_rfl

theorem fixed_shell_scalarMinimum_attained {T epsilon shell : ℝ}
    (hepsilon : 0 ≤ epsilon) (hgap : 0 ≤ T-epsilon) :
    ∃q ∈ unitMassQuantiles,
      generalScalarQuantileValue (initialShellMatrixClock T epsilon shell) (fun _=>0) q=
        generalScalarMinimum (initialShellMatrixClock T epsilon shell) (fun _=>0) := by
  have hT : 0 ≤ T := by linarith
  apply macroScalarMinimum_attained _ _ hT
    ((initialShellMatrixClock_monotone T shell hepsilon).monotoneOn _)
    (fun _ _ _ _ _=>le_rfl) _ le_rfl
  intro u _
  unfold initialShellMatrixClock
  split_ifs <;> constructor <;> linarith

end OAI.SKFluctuations.LaplaceWindowFormalization
