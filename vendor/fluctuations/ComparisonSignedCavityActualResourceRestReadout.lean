module

public import ComparisonSignedCavityActualMinimumOriginalOneStep
public import ComparisonSignedCavityActualProjectionSpine

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 10000000

def nativeActualResourceRestValue {n : ℕ} {as : List PositiveMass} {i star : ℕ}
    {T : ClockTree (Spin n×Bool) as} (P : NativeResourceTerm i star T)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (C : ℕ→ℝ) (σ : T.cavityLeft.Assignment) : ℝ :=
  P.scalar (fullWeight n) (fullFeature n) v₀ q₀
    (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C x₀*
      nativeRestGeneratedTestValue T P.live.test
        (fun σ τ=>(∑j,spinValue (σ j)*spinValue (τ j))/(n+1:ℕ)) C σ

theorem native_actual_resource_rest_value_eq_full {n : ℕ} {as : List PositiveMass} {i star : ℕ}
    {T : ClockTree (Spin n×Bool) as} (P : NativeResourceTerm i star T)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (C : ℕ→ℝ) (σ : T.Assignment) :
    nativeActualResourceRestValue P v₀ q₀ x₀ C (T.cavityAssignment σ).1=
      P.value (fullWeight n) (fullFeature n) v₀ q₀
        (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C x₀ σ := by
  unfold nativeActualResourceRestValue NativeResourceTerm.value
  rw [native_rest_generated_value_eq_full]
  have HR : (fun σ τ : Spin n×Bool=>(∑j,spinValue (σ.1 j)*spinValue (τ.1 j))/(n+1:ℕ))=
      fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ) := by
    funext σ τ
    simp only [deletedOverlap,joinSpin,Fin.lastCases_castSucc]
  rw [HR]

theorem native_actual_resource_rest_function_eq_full {n : ℕ} {as : List PositiveMass} {i star : ℕ}
    {T : ClockTree (Spin n×Bool) as} (P : NativeResourceTerm i star T)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (C : ℕ→ℝ) :
    (fun σ=>nativeActualResourceRestValue P v₀ q₀ x₀ C (T.cavityAssignment σ).1)=
      P.value (fullWeight n) (fullFeature n) v₀ q₀
        (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C x₀ := by
  funext σ
  exact native_actual_resource_rest_value_eq_full P v₀ q₀ x₀ C σ

theorem native_actual_resource_original_centered_readout {n : ℕ} {as : List PositiveMass} {i star : ℕ}
    {T : ClockTree (Spin n×Bool) as} (P : NativeResourceTerm i star T)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (C : ℕ→ℝ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ) :
    let F:=P.value (fullWeight n) (fullFeature n) v₀ q₀
      (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C x₀
    (fun σ=>nativeOriginalCenteredRestTest n q U b h K T
      (nativeActualResourceRestValue P v₀ q₀ x₀ C) (T.cavityAssignment σ).1)=
    fun σ=>F σ-T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cutFullVariance n q U 1 1 b h K) F 0 := by
  dsimp only
  unfold nativeOriginalCenteredRestTest nativeOriginalRestTestExpectation
  rw [native_actual_resource_rest_function_eq_full P v₀ q₀ x₀ C]
  funext σ
  rw [native_actual_resource_rest_value_eq_full P v₀ q₀ x₀ C σ]

end OAI.SKFluctuations.Cavity
