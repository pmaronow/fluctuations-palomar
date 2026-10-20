module

public import ComparisonSignedCavityJointHighRestorationLinearity
public import ComparisonSignedCavityActualFourOtherSourceCategories

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000

inductive NativeJointHighRestorationKind where
  | lowTwoHigh
  | fourGLow
  deriving DecidableEq

instance : Fintype NativeJointHighRestorationKind where
  elems := [.lowTwoHigh,.fourGLow].toFinset
  complete kind := by cases kind <;> simp

def NativeJointHighRestorationKind.category : NativeJointHighRestorationKind→NativeActualOtherSourceCategory
  | .lowTwoHigh=>.jointLowTwoHigh
  | .fourGLow=>.fourGLowRestoration

def nativeJointHighRestorationSource (kind : NativeJointHighRestorationKind) (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K S : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (P : T.cavityLeft.Assignment→ℝ)
    (a z : T.Slot) : ℝ :=
  match kind with
  | .lowTwoHigh=>nativeCenteredLowGammaHighSecondRemainder n q U b h K S T P a z
  | .fourGLow=>nativeOriginalGKernelLowRestoration n q U b h K S T P a z (restCenteredLowKernel n U b S)

theorem native_joint_HIGH_restoration_source_test_linear (kind : NativeJointHighRestorationKind) (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K S : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P Q : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) (α β : ℝ)
    (hq0 : ∀j i,0 ≤ q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    nativeJointHighRestorationSource kind n q U b h K S T (fun σ=>α*P σ+β*Q σ) a z=
      α*nativeJointHighRestorationSource kind n q U b h K S T P a z+
      β*nativeJointHighRestorationSource kind n q U b h K S T Q a z := by
  cases kind with
  | lowTwoHigh=>
    exact native_centered_low_gamma_HIGH_second_test_linear n q U b h K S T ho P Q a z α β
      hq0 hq hb hh hK hbm hhm hKm
  | fourGLow=>
    exact native_original_four_G_LOW_restoration_test_linear n q U b h K S T ho P Q a z α β
      hq0 hq hb hh hK hbm hhm hKm

end OAI.SKFluctuations.Cavity
