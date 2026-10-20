module

public import ComparisonSignedCavityActualHighSourceLinearity
public import ComparisonSignedCavityActualResourceRestReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 16000000

def nativeActualHigherHighPart (part : Fin 3) (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (P : T.Assignment→ℝ)
    (a z : T.Slot) (l t : ℝ) : ℝ :=
  if part.val=0 then nativeCenteredFixedLowHigh n q U b h K T P a z 2 1 t else
  if part.val=1 then nativeCenteredFixedLowHigh n q U b h K T P a z 1 2 t else
    nativeCenteredTransientHighThird n q U b h K T P a z l t

theorem native_actual_higher_HIGH_part_add_test (part : Fin 3) (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (P Q : T.Assignment→ℝ)
    (a z : T.Slot) (l t : ℝ) :
    nativeActualHigherHighPart part n q U b h K T (fun σ=>P σ+Q σ) a z l t=
      nativeActualHigherHighPart part n q U b h K T P a z l t+
      nativeActualHigherHighPart part n q U b h K T Q a z l t := by
  fin_cases part <;> simp only [nativeActualHigherHighPart,ite_true,actual_nativeCenteredFixedLowHigh_add_test,
    actual_nativeCenteredTransientHighThird_add_test] <;> norm_num

theorem native_actual_higher_HIGH_part_const_mul_test (part : Fin 3) (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (P : T.Assignment→ℝ)
    (a z : T.Slot) (l t c : ℝ) :
    nativeActualHigherHighPart part n q U b h K T (fun σ=>c*P σ) a z l t=
      c*nativeActualHigherHighPart part n q U b h K T P a z l t := by
  fin_cases part <;> simp only [nativeActualHigherHighPart,ite_true,actual_nativeCenteredFixedLowHigh_const_mul_test,
    actual_nativeCenteredTransientHighThird_const_mul_test] <;> norm_num

theorem actual_higher_HIGH_part_original_centered_resource_eq_two_terms
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (P : NativeResourceTerm i star T) (ho : MassOrdered 0 as) (part : Fin 3)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K C : ℕ→ℝ)
    (a z : T.Slot) (l t : ℝ) :
    let qfull:=cutFullVariance n q U 1 1 b h K
    let R:=fun σ τ : Spin n×Bool=>deletedOverlap n (joinSpin σ) (joinSpin τ)
    let Pc:=nativeOriginalCenteredRestTest n q U b h K T
      (nativeActualResourceRestValue P 0 qfull 0 C)
    nativeActualHigherHighPart part n q U b h K T (fun σ=>Pc (T.cavityAssignment σ).1) a z l t=
      nativeActualHigherHighPart part n q U b h K T
        (P.value (fullWeight n) (fullFeature n) 0 qfull R C 0) a z l t+
      nativeActualHigherHighPart part n q U b h K T
        (P.freeze.value (fullWeight n) (fullFeature n) 0 qfull R C 0) a z l t := by
  dsimp only
  rw [native_actual_resource_original_centered_readout]
  have HE :
      (fun σ=>P.value (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 1 1 b h K)
        (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C 0 σ-
        T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 1 1 b h K)
          (P.value (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 1 1 b h K)
            (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C 0) 0)=
      fun σ=>P.value (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 1 1 b h K)
        (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C 0 σ+
        P.freeze.value (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 1 1 b h K)
          (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C 0 σ := by
    funext σ
    rw [P.freeze_value (fullWeight_pos n) (fullFeature n) ho]
    ring
  rw [HE,native_actual_higher_HIGH_part_add_test]

end OAI.SKFluctuations.Cavity
