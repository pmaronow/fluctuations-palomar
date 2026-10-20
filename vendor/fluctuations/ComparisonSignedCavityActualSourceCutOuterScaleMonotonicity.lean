module

public import ComparisonSignedCavityActualStrongSharpSourceCuts

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity NativeOverlapMinimum

theorem ActualSharpSourceCutGeometry.mono_outer_scale
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    {M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {W radius cFirst cK A A' : ℝ} {w : ActualSlowWindowChoice}
    {high outer : PositiveMass}
    (H : ActualSharpSourceCutGeometry M W w high outer radius cFirst cK A)
    (hW : 0 ≤ W) (hA : A ≤ A') :
    ActualSharpSourceCutGeometry M W w high outer radius cFirst cK A' :=
  { H with outer_scale := H.outer_scale.trans (mul_le_mul_of_nonneg_right hA hW) }

theorem ActualStrongSharpSourceCutGeometry.mono_outer_scale
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    {M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {W radius cFirst cK A A' Rmacro Cx : ℝ} {w : ActualSlowWindowChoice}
    {high outer : PositiveMass}
    (H : ActualStrongSharpSourceCutGeometry M W w high outer radius cFirst cK A Rmacro Cx)
    (hW : 0 ≤ W) (hA : A ≤ A') :
    ActualStrongSharpSourceCutGeometry M W w high outer radius cFirst cK A' Rmacro Cx :=
  { H with toActualSharpSourceCutGeometry := H.toActualSharpSourceCutGeometry.mono_outer_scale hW hA }

end OAI.SKFluctuations.LaplaceWindowFormalization
