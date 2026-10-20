module

public import ComparisonSignedCavityTwoLevelIncomingProduct

@[expose] public section

noncomputable section
set_option maxHeartbeats 14000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy

theorem native_root_test_four_saved_bound (n : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n) as) {a : ℝ} (ho : MassOrdered a as)
    (q : ℕ→RestCoordinate n→ℝ≥0) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (x : P→RestCoordinate n→ℝ) (hx : Measurable x)
    (A B E Y : P→T.Assignment→ℝ)
    (hA : ∀σ,Measurable (fun z=>A z σ)) (hB : ∀σ,Measurable (fun z=>B z σ))
    (hE : ∀σ,Measurable (fun z=>E z σ)) (hY : ∀σ,Measurable (fun z=>Y z σ))
    (CA CB CE CY : ℝ) (hCA : 0 ≤ CA) (hCB : 0 ≤ CB) (hCE : 0 ≤ CE) (hCY : 0 ≤ CY)
    (hAb : ∀z σ,|A z σ| ≤ CA) (hBb : ∀z σ,|B z σ| ≤ CB)
    (hEb : ∀z σ,|E z σ| ≤ CE) (hYb : ∀z σ,|Y z σ| ≤ CY) :
    |nativeRootTestExpect n T q μ x (fun z σ=>A z σ*B z σ*E z σ*Y z σ)| ≤
      Real.sqrt (Real.sqrt (
        nativeRootTestExpect n T q μ x (fun z σ=>A z σ^4)*
        nativeRootTestExpect n T q μ x (fun z σ=>B z σ^4))*
        Real.sqrt (nativeRootTestExpect n T q μ x (fun z σ=>E z σ^4)*
          nativeRootTestExpect n T q μ x (fun z σ=>Y z σ^4))) := by
  have H:=native_root_test_three_saved_bound n T ho q μ x hx A B (fun z σ=>E z σ*Y z σ)
    hA hB (fun σ=>(hE σ).mul (hY σ)) CA CB (CE*CY) hCA hCB (mul_nonneg hCE hCY)
    hAb hBb (fun z σ=>by rw [abs_mul];exact mul_le_mul (hEb z σ) (hYb z σ) (abs_nonneg _) hCE)
  have HE:=native_root_test_mul_abs_le_sqrt n T ho q μ x hx
    (fun z σ=>E z σ^2) (fun z σ=>Y z σ^2)
    (fun σ=>(hE σ).pow_const 2) (fun σ=>(hY σ).pow_const 2)
    (CE^2) (CY^2) (sq_nonneg _) (sq_nonneg _)
    (fun z σ=>by simpa only [abs_pow] using pow_le_pow_left₀ (abs_nonneg _) (hEb z σ) 2)
    (fun z σ=>by simpa only [abs_pow] using pow_le_pow_left₀ (abs_nonneg _) (hYb z σ) 2)
  have hE4:(fun z σ=>(E z σ^2)^2)=(fun z σ=>E z σ^4):=by funext z σ;ring
  have hY4:(fun z σ=>(Y z σ^2)^2)=(fun z σ=>Y z σ^4):=by funext z σ;ring
  rw [hE4,hY4,abs_of_nonneg (native_root_test_expect_nonneg n T ho q μ x _
    (fun z σ=>mul_nonneg (sq_nonneg _) (sq_nonneg _)))] at HE
  simp only [mul_pow] at H
  simp only [mul_assoc] at H ⊢
  apply H.trans
  apply Real.sqrt_le_sqrt
  exact mul_le_mul_of_nonneg_left HE (Real.sqrt_nonneg _)

theorem native_four_saved_moment_scales {a b e y A B E Y : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hy : 0 ≤ y)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E) (hY : 0 ≤ Y)
    (haA : a ≤ A^4) (hbB : b ≤ B^4) (heE : e ≤ E^4) (hyY : y ≤ Y^4) :
    Real.sqrt (Real.sqrt (a*b)*Real.sqrt (e*y)) ≤ A*B*E*Y := by
  have HE:Real.sqrt (e*y) ≤ (E*Y)^2:=by
    apply (Real.sqrt_le_sqrt (mul_le_mul heE hyY hy (by positivity))).trans_eq
    rw [←mul_pow,show (E*Y)^4=((E*Y)^2)^2 by ring,Real.sqrt_sq (sq_nonneg _)]
  have H:=two_level_incoming_moment_scales (a:=a) (b:=b) (c:=Real.sqrt (e*y))
    (A:=A) (B:=B) (C:=E*Y) ha hb (Real.sqrt_nonneg _) hA hB
    (mul_nonneg hE hY) haA hbB HE
  simpa only [mul_assoc] using H

end OAI.SKFluctuations.Cavity
