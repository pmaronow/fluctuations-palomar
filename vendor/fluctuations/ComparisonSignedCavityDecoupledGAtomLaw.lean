module

public import ComparisonSignedCavityActualOriginalGPairingTransport
public import ComparisonSignedCavityObservedDiagramReadout

@[expose] public section

noncomputable section
set_option maxHeartbeats 16000000
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S B : Type} {as : List PositiveMass}

theorem native_replace_cavityLeft_actual (T : ClockTree (S×B) as)
    (s : T.Slot) (σ : T.Assignment) (u : S×B) :
    (T.cavityAssignment (nativeReplaceAtSlot T s σ u)).1=
      nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot s) (T.cavityAssignment σ).1 u.1 := by
  classical
  apply T.cavityLeft.assignment_ext
  intro c
  obtain ⟨d,rfl⟩:=T.cavityLeftSlot.surjective c
  rw [T.atSlot_cavityLeft,nativeReplaceAtSlot_at,nativeReplaceAtSlot_at,
    T.cavityLeftSlot.injective.eq_iff,T.atSlot_cavityLeft]
  split_ifs <;> rfl

end OAI.SKFluctuations.Hierarchy.ClockTree
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree

theorem native_decoupled_original_G_atom_expect (n : ℕ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (hU : U ≤ as.length)
    (b h K C : ℕ→ℝ) (hKC : ∀j,K j=h j+b j*C j)
    (a c e f : T.Slot) (P : T.cavityLeft.Assignment→ℝ) :
    T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 0 0 b h K)
      (fun σ=>P (T.cavityAssignment σ).1*nativeOriginalHighGAtom T U K b C a c e f σ) 0=
      (1/2:ℝ)*fullScalarCutConnected4 T U K a c e f*
      T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
        (fun σ=>P σ*restHighKernel n U b h K (T.splitIndex e f)
          (T.cavityLeft.atSlot σ (T.cavityLeftSlot e))
          (T.cavityLeft.atSlot σ (T.cavityLeftSlot f))) 0 := by
  have HF : (fun σ : T.Assignment=>P (T.cavityAssignment σ).1*
        nativeOriginalHighGAtom T U K b C a c e f σ)=
      (fun σ=>(1/2:ℝ)*fullScalarCutConnected4 T U K a c e f*
        (P (T.cavityAssignment σ).1*restHighKernel n U b h K (T.splitIndex e f)
          (T.cavityLeft.atSlot (T.cavityAssignment σ).1 (T.cavityLeftSlot e))
          (T.cavityLeft.atSlot (T.cavityAssignment σ).1 (T.cavityLeftSlot f)))) := by
    funext σ
    rw [native_original_high_G_atom_eq_unmasked_rest_kernel T ho U b h K C hKC a c e f hU,
      T.atSlot_cavityLeft,T.atSlot_cavityLeft]
    ring
  rw [HF,T.disorderExpect_const_mul (fullWeight_pos n) (fullFeature n) ho]
  apply congrArg (fun z=>(1/2:ℝ)*fullScalarCutConnected4 T U K a c e f*z)
  exact native_decoupled_rest_expect n q U b h K T ho
    (fun σ=>P σ*restHighKernel n U b h K (T.splitIndex e f)
      (T.cavityLeft.atSlot σ (T.cavityLeftSlot e)) (T.cavityLeft.atSlot σ (T.cavityLeftSlot f)))

end OAI.SKFluctuations.Cavity
