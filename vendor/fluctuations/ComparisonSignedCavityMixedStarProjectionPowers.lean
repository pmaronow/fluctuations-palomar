module

public import ComparisonSignedCavityActualStarProjectionPowers

@[expose] public section

noncomputable section
set_option maxHeartbeats 9000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem native_star_projection_mixed_power_second_le (n j k : ℕ)
    {as : List PositiveMass} (T : ClockTree (Spin n) as) {a : ℝ}
    (ho : MassOrdered a as) (q : ℕ → RestCoordinate n → ℝ≥0)
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P → RestCoordinate n → ℝ) (hx : Measurable x) (center : ℝ) (s t : T.Slot)
    (rho : ℝ) (hrho : 0 ≤ rho)
    (hs : nativeRootTestExpect n T q μ x
      (fun z σ=>|nativeStarCenteredProjection n as q center (x z) (T.atSlot σ s)|^(4*j)) ≤ rho^(4*j))
    (ht : nativeRootTestExpect n T q μ x
      (fun z σ=>|nativeStarCenteredProjection n as q center (x z) (T.atSlot σ t)|^(4*k)) ≤ rho^(4*k)) :
    nativeRootTestExpect n T q μ x
      (fun z σ=>(nativeStarCenteredProjection n as q center (x z) (T.atSlot σ s)^j*
        nativeStarCenteredProjection n as q center (x z) (T.atSlot σ t)^k)^2) ≤ rho^(2*(j+k)) := by
  let A:=fun z σ=>nativeStarCenteredProjection n as q center (x z) (T.atSlot σ s)
  let B:=fun z σ=>nativeStarCenteredProjection n as q center (x z) (T.atSlot σ t)
  have hA (σ) : Measurable (fun z=>A z σ):=
    (native_star_centered_projection_smooth n ho q center (T.atSlot σ s) 0).continuous.measurable.comp hx
  have hB (σ) : Measurable (fun z=>B z σ):=
    (native_star_centered_projection_smooth n ho q center (T.atSlot σ t) 0).continuous.measurable.comp hx
  have hAb (z) (σ) : |A z σ^(2*j)| ≤ (1+|center|)^(2*j) := by
    simpa only [A,abs_pow] using pow_le_pow_left₀ (abs_nonneg _)
      (native_star_centered_projection_bound n ho q center (x z) (T.atSlot σ s)) (2*j)
  have hBb (z) (σ) : |B z σ^(2*k)| ≤ (1+|center|)^(2*k) := by
    simpa only [B,abs_pow] using pow_le_pow_left₀ (abs_nonneg _)
      (native_star_centered_projection_bound n ho q center (x z) (T.atSlot σ t)) (2*k)
  have H:=native_root_test_mul_abs_le_sqrt n T ho q μ x hx
    (fun z σ=>A z σ^(2*j)) (fun z σ=>B z σ^(2*k))
    (fun σ=>(hA σ).pow_const _) (fun σ=>(hB σ).pow_const _)
    ((1+|center|)^(2*j)) ((1+|center|)^(2*k)) (by positivity) (by positivity) hAb hBb
  have heA : (fun z σ=>(A z σ^(2*j))^2)=(fun z σ=>|A z σ|^(4*j)) := by
    funext z σ
    rw [←pow_mul,show (2*j)*2=4*j by omega,show 4*j=2*(2*j) by omega,(even_two_mul (2*j)).pow_abs]
  have heB : (fun z σ=>(B z σ^(2*k))^2)=(fun z σ=>|B z σ|^(4*k)) := by
    funext z σ
    rw [←pow_mul,show (2*k)*2=4*k by omega,show 4*k=2*(2*k) by omega,(even_two_mul (2*k)).pow_abs]
  rw [heA,heB] at H
  have hBn:=native_root_test_expect_nonneg n T ho q μ x (fun z σ=>|B z σ|^(4*k))
    (fun _ _=>by positivity)
  have Hnum:=Real.sqrt_le_sqrt (mul_le_mul hs ht hBn (pow_nonneg hrho _))
  have hnum : Real.sqrt (rho^(4*j)*rho^(4*k))=rho^(2*(j+k)) := by
    rw [←pow_add,show 4*j+4*k=(2*(j+k))*2 by omega,pow_mul,
      Real.sqrt_sq (pow_nonneg hrho _)]
  rw [hnum] at Hnum
  have Hfinal:=H.trans Hnum
  have he : (fun z σ=>(A z σ^j*B z σ^k)^2)=(fun z σ=>A z σ^(2*j)*B z σ^(2*k)) := by
    funext z σ
    rw [mul_pow,←pow_mul,←pow_mul,Nat.mul_comm j 2,Nat.mul_comm k 2]
  change nativeRootTestExpect n T q μ x (fun z σ=>(A z σ^j*B z σ^k)^2) ≤ _
  rw [he]
  exact (le_abs_self _).trans Hfinal

end OAI.SKFluctuations.Cavity
