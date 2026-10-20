module

public import ComparisonSignedCavityDecoupledGAtomLaw
public import ComparisonSignedCavityOriginalGSpineDiagram

@[expose] public section

noncomputable section
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree

def nativeRestGSpineDiagramValue {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (base : NativeGeneratedTest T)
    (star U : ℕ) (q : ℕ→RestCoordinate n→ℝ) (b h K C : ℕ→ℝ)
    (A R : Spin n→Spin n→ℝ) (D : NativeObservedDiagram T) : ℝ :=
  match D.marks with
  | f::e::c::rest=>match rest.reverse with
    | t::teeth=>(1/2:ℝ)*fullScalarCutConnected4 D.tree U K (D.embed base.target) c e f*
        D.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (fun σ=>
            let spinAt:=fun d=>D.tree.cavityLeft.atSlot σ (D.tree.cavityLeftSlot d)
            let a:=T.cavityLeft.atSlot (D.restRead σ) (T.cavityLeftSlot base.target)
            (A (spinAt c) (spinAt t)-A a (spinAt t))*
              (nativeRestGeneratedTestValue T base R C (D.restRead σ)*
                (teeth.map (fun d=>R a (spinAt d)-C star)).prod-
              nativeRestGeneratedTestValue T base R C
                (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot base.target) (D.restRead σ) (spinAt c))*
                (teeth.map (fun d=>R (spinAt c) (spinAt d)-C star)).prod)*
              restHighKernel n U b h K (D.tree.splitIndex e f) (spinAt e) (spinAt f)) 0
    | []=>0
  | _=>0

theorem native_original_G_spine_diagram_decoupled_eq_rest
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (base : NativeGeneratedTest T) (ho : MassOrdered 0 as) (star U : ℕ) (hU : U ≤ as.length)
    (q : ℕ→RestCoordinate n→ℝ) (b h K C : ℕ→ℝ) (hKC : ∀j,K j=h j+b j*C j)
    (A R : Spin n→Spin n→ℝ) (D : NativeObservedDiagram T) (hD : D.ValidRead) :
    nativeOriginalGSpineDiagramValue T base star U K b C 0
      (cutFullVariance n q U 0 0 b h K) 0 (fun u v=>A u.1 v.1) (fun u v=>R u.1 v.1) D=
      nativeRestGSpineDiagramValue T base star U q b h K C A R D := by
  unfold nativeOriginalGSpineDiagramValue nativeRestGSpineDiagramValue
  split
  · rename_i f e c rest hm
    simp only [hm]
    split
    · rename_i t teeth hr
      simp only [hr]
      let J : D.tree.cavityLeft.Assignment→ℝ:=fun σ=>
        let spinAt:=fun d=>D.tree.cavityLeft.atSlot σ (D.tree.cavityLeftSlot d)
        let a:=T.cavityLeft.atSlot (D.restRead σ) (T.cavityLeftSlot base.target)
        (A (spinAt c) (spinAt t)-A a (spinAt t))*
          (nativeRestGeneratedTestValue T base R C (D.restRead σ)*
            (teeth.map (fun d=>R a (spinAt d)-C star)).prod-
          nativeRestGeneratedTestValue T base R C
            (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot base.target) (D.restRead σ) (spinAt c))*
            (teeth.map (fun d=>R (spinAt c) (spinAt d)-C star)).prod)
      have HF : (fun σ : D.tree.Assignment=>
          (A (D.tree.atSlot σ c).1 (D.tree.atSlot σ t).1-
            A (T.atSlot (D.read σ) base.target).1 (D.tree.atSlot σ t).1)*
          (base.value (fun u v=>R u.1 v.1) C (D.read σ)*
            (teeth.map (fun d=>R (T.atSlot (D.read σ) base.target).1 (D.tree.atSlot σ d).1-C star)).prod-
          base.value (fun u v=>R u.1 v.1) C
            (nativeReplaceAtSlot T base.target (D.read σ) (D.tree.atSlot σ c))*
            (teeth.map (fun d=>R (D.tree.atSlot σ c).1 (D.tree.atSlot σ d).1-C star)).prod))=
          (fun σ=>J (D.tree.cavityAssignment σ).1) := by
        funext σ
        dsimp only [J]
        rw [hD.restRead_actual]
        simp only [D.tree.atSlot_cavityLeft,T.atSlot_cavityLeft]
        rw [←native_rest_generated_value_eq_full base R C (D.read σ),
          ←native_rest_generated_value_eq_full base R C
            (nativeReplaceAtSlot T base.target (D.read σ) (D.tree.atSlot σ c)),
          native_replace_cavityLeft_actual]
      have HF2:=congrArg (fun L : D.tree.Assignment→ℝ=>fun σ=>L σ*
        nativeOriginalHighGAtom D.tree U K b C (D.embed base.target) c e f σ) HF
      rw [HF2]
      exact native_decoupled_original_G_atom_expect n D.tree ho q U hU b h K C hKC
        (D.embed base.target) c e f J
    · rename_i hr
      simp only [hr]
  · rename_i hshort
    split
    · rename_i f e c rest he
      exact False.elim (hshort f e c rest he)
    · rfl

end OAI.SKFluctuations.Cavity
