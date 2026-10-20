module

public import CavityActualScalarRowHessian
public import SKFluctuationsOAI.Probability.SKFluctuations.ScalarFiniteInvariant

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem scalar_boundary_hessian_uniform_bounds {as : List PositiveMass}
    (ho : MassOrdered 0 as) (q : ℕ → ℝ) (hq : Monotone q)
    (hq0 : q 0 = 0) {B : ℝ} (hB : q as.length ≤ B) :
    Real.exp (-4*B) ≤ (scalarTerminal.schedule (scalarBoundaryClocks as q)).H 0 0 ∧
      (scalarTerminal.schedule (scalarBoundaryClocks as q)).H 0 0 ≤ 1 := by
  let cs := scalarBoundaryClocks as q
  have hsum (ds : List HeatClock) :
      (ds.map (fun c => (c.time : ℝ))).sum = (scheduleDuration ds : ℝ) := by
    induction ds with
    | nil => rfl
    | cons c ds ih => simp only [List.map_cons, List.sum_cons, scheduleDuration,
        NNReal.coe_add, ih]
  have hs : (cs.map (fun c => (c.time : ℝ))).sum = q as.length := by
    have hd := scalarBoundaryClocks_duration as q hq
    rw [hq0, sub_zero] at hd
    exact (hsum cs).trans hd
  have hc := scalarBoundaryClocks_ordered ho q
  have hl := scalar_schedule_curvature_lower cs
    (fun c hc' => (scalar_schedule_ordered_masses hc c hc').2) 0
  have hu := scalarSourceJet_schedule_curvature_le_one cs hc 0
  rw [scalarSourceJet_two_schedule cs hc] at hu
  constructor
  · calc
      Real.exp (-4*B) ≤ Real.exp (-4*q as.length) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ _ := by simpa [hs, Scalar.curvature] using hl
  · simpa only [cs, Pi.zero_def] using hu

theorem native_full_gamma_row_uniform_bounds (n : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n × Bool) as) (ho : MassOrdered 0 as)
    (a : ℝ) (hoa : MassOrdered a as) (U : ℕ) (hU0 : 0 < U)
    (hU : U ≤ as.length) (K : ℕ → ℝ) (hK : Monotone K)
    (hK0 : ∀ j, 0 ≤ K j) {B : ℝ} (hB : K as.length ≤ B) (s : T.Slot) :
    Real.exp (-4*B) ≤
      ((T.markedAttach a).map (fun p => p.coeff *
        fullScalarCutGamma p.tree U K (p.embed s) p.mark)).sum ∧
    ((T.markedAttach a).map (fun p => p.coeff *
        fullScalarCutGamma p.tree U K (p.embed s) p.mark)).sum ≤ 1 := by
  rw [native_full_gamma_row_hessian n T ho a hoa U hU0 K s]
  apply scalar_boundary_hessian_uniform_bounds ho (relocatedClock U 0 K)
  · exact relocatedClock_monotone U (by norm_num : (0 : ℝ) ∈ Icc 0 1) hK hK0
  · simp [relocatedClock, hU0]
  · simpa [relocatedClock, not_lt.mpr hU] using hB

theorem susceptibility_feedback_absorption {J x W C eta : ℝ}
    (hx : 0 ≤ x) (hW : 0 < W) (hxW : x ≤ W)
    (heta : 0 ≤ eta) (hsmall : eta ≤ 1/2)
    (hresponse : |J| ≤ C*W^2 + eta*x^2 + eta * |J| * x^2/W^2) :
    |J| ≤ 2*(C+eta)*W^2 := by
  have hW2 : 0 < W^2 := sq_pos_of_pos hW
  have hx2 : x^2 ≤ W^2 := pow_le_pow_left₀ hx hxW 2
  have hterm : eta * |J| * x^2/W^2 ≤ eta * |J| := by
    apply (div_le_iff₀ hW2).mpr
    exact mul_le_mul_of_nonneg_left hx2 (mul_nonneg heta (abs_nonneg J))
  have hbudget : eta*x^2 ≤ eta*W^2 := mul_le_mul_of_nonneg_left hx2 heta
  have hhalf : eta * |J| ≤ (1/2) * |J| :=
    mul_le_mul_of_nonneg_right hsmall (abs_nonneg J)
  nlinarith

theorem native_full_gamma_row_inverse_bounds (n : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n × Bool) as) (ho : MassOrdered 0 as)
    (a : ℝ) (hoa : MassOrdered a as) (U : ℕ) (hU0 : 0 < U)
    (hU : U ≤ as.length) (K : ℕ → ℝ) (hK : Monotone K)
    (hK0 : ∀ j, 0 ≤ K j) {B : ℝ} (hB : K as.length ≤ B) (s : T.Slot) :
    let chi := ((T.markedAttach a).map (fun p => p.coeff *
      fullScalarCutGamma p.tree U K (p.embed s) p.mark)).sum
    0 < chi ∧ 1 ≤ chi⁻¹ ∧ chi⁻¹ ≤ (Real.exp (-4*B))⁻¹ := by
  dsimp only
  obtain ⟨hl, hu⟩ := native_full_gamma_row_uniform_bounds n T ho a hoa U hU0 hU K hK hK0 hB s
  have hp := (Real.exp_pos (-4*B)).trans_le hl
  exact ⟨hp, (by simpa using one_div_le_one_div_of_le hp hu),
    (by simpa using one_div_le_one_div_of_le (Real.exp_pos _) hl)⟩

theorem native_full_gamma_recursion_coefficient_bound (n : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n × Bool) as) (ho : MassOrdered 0 as)
    (a : ℝ) (hoa : MassOrdered a as) (U : ℕ) (hU0 : 0 < U)
    (hU : U ≤ as.length) (K : ℕ → ℝ) (hK : Monotone K)
    (hK0 : ∀ j, 0 ≤ K j) {B : ℝ} (hB : K as.length ≤ B) (s : T.Slot)
    {W c k beta Cb : ℝ} (hW : 0 < W) (hc : 0 < c)
    (hk : c*W ≤ k) (hbeta : |beta| ≤ Cb) :
    let chi := ((T.markedAttach a).map (fun p => p.coeff *
      fullScalarCutGamma p.tree U K (p.embed s) p.mark)).sum
    |beta/(chi*k)| ≤ Cb/((Real.exp (-4*B))*c*W) := by
  dsimp only
  obtain ⟨hl, hu⟩ := native_full_gamma_row_uniform_bounds n T ho a hoa U hU0 hU K hK hK0 hB s
  let chi := ((T.markedAttach a).map (fun p => p.coeff *
      fullScalarCutGamma p.tree U K (p.embed s) p.mark)).sum
  have hp : 0 < chi := (Real.exp_pos _).trans_le hl
  have hkp : 0 < k := (mul_pos hc hW).trans_le hk
  have hden : Real.exp (-4*B)*c*W ≤ chi*k := by
    simpa only [mul_assoc] using mul_le_mul hl hk (mul_pos hc hW).le hp.le
  rw [abs_div, abs_of_pos (mul_pos hp hkp)]
  exact div_le_div₀ ((abs_nonneg beta).trans hbeta) hbeta
    (by positivity : 0 < Real.exp (-4*B)*c*W) hden

end OAI.SKFluctuations.Cavity
