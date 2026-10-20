module

public import ComparisonSignedCavityForestTwinFreshFactory
public import ComparisonSignedCavityTwinPrefixNativeLaw

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
variable [MeasurableSpace S] [StandardBorelSpace S]

def NativeActualFreshTwoArmLaw
    (pre mid tail : List PositiveMass) (T : ClockTree S (pre++(mid++tail))) (s b : T.Slot)
    (a : ℝ) (w : S → ℝ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ) : Prop :=
    let p:=nativeFreshAtSlot T a b (pre.length+mid.length)
    ∃(A : ClockTree S (mid++tail)) (Bold D : ClockTree S tail)
      (read : A.Assignment → Bold.Assignment → D.Assignment → T.Assignment)
      (targetB : Bold.Slot) (targetD : D.Slot),
      (∀η β δ,T.atSlot (read η β δ) b=Bold.atSlot β targetB) ∧
      (∀η β δ,T.atSlot (read η β δ) s=D.atSlot δ targetD) ∧
      (∀c,pre.length+mid.length<T.splitIndex s c → ∃d : D.Slot,
        (∀η β δ,T.atSlot (read η β δ) c=D.atSlot δ d) ∧
        pre.length+mid.length+D.splitIndex targetD d=T.splitIndex s c) ∧
      (∀Q : T.Assignment → S → ℝ,
        p.tree.disorderExpect w φ v q (fun σ=>Q (p.restrict σ) (p.spin σ)) x=
          (nativeTwinForestTree pre mid A (Bold.fork (single tail)) D).disorderExpect w φ v q
            (nativeTwinForestRead pre mid A (Bold.fork (single tail)) D
              (fun η β δ=>Q (read η β.1 δ) (singleEquiv (S:=S) tail β.2))) x) ∧
      (∀Q : T.Assignment → S → ℝ,
        p.tree.disorderExpect w φ v q (fun σ=>Q (p.restrict σ) (p.spin σ)) x=
          ∫z,nativeTwinForestConditionalTest A (Bold.fork (single tail)) D w φ
            (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j))
            (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+(mid.length+j)))
            (fun η β δ=>Q (read η β.1 δ) (singleEquiv (S:=S) tail β.2))
            (twinPrefixSharedRoot z) (twinPrefixBRoot z) (twinPrefixDRoot z)
            ∂nativeTwinPrefixDisorderRootLaw w φ pre mid tail v q x)

theorem native_actual_fresh_two_arm_disorder_factory
    (pre mid tail : List PositiveMass) (T : ClockTree S (pre++(mid++tail))) (s b : T.Slot)
    {U : ℕ} (hmid : 0 < mid.length) (hU : pre.length+mid.length<U)
    (hT : NativePersistentLowForks pre.length (pre.length+mid.length) U T)
    (hsb : T.splitIndex s b=pre.length)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a (pre++(mid++tail)))
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ) :
    NativeActualFreshTwoArmLaw pre mid tail T s b a w φ v q x := by
  unfold NativeActualFreshTwoArmLaw
  let p:=nativeFreshAtSlot T a b (pre.length+mid.length)
  obtain ⟨A,Bold,D,R,tb,td,htB,htD,hh,hFactory⟩:=native_two_arm_fresh_factory
    pre mid tail T s b hmid hU hT hsb hw φ ho
  have hExact (Q : T.Assignment → S → ℝ) :
      p.tree.disorderExpect w φ v q (fun σ=>Q (p.restrict σ) (p.spin σ)) x=
        (nativeTwinForestTree pre mid A (Bold.fork (single tail)) D).disorderExpect w φ v q
          (nativeTwinForestRead pre mid A (Bold.fork (single tail)) D
            (fun η β δ=>Q (R η β.1 δ) (singleEquiv (S:=S) tail β.2))) x := by
    have hSpinLaw (q' : ℕ → ι → ℝ≥0) (y : ι → ℝ) :
        p.tree.expect w φ q' (fun σ=>Q (p.restrict σ) (p.spin σ)) y=
          (nativeTwinForestTree pre mid A (Bold.fork (single tail)) D).expect w φ q'
            (nativeTwinForestRead pre mid A (Bold.fork (single tail)) D
              (fun η β δ=>Q (R η β.1 δ) (singleEquiv (S:=S) tail β.2))) y :=
      (native_trunk_projected_eq_fresh_graft hw φ T ho b (pre.length+mid.length) q' Q y).symm.trans
        (hFactory q' Q y)
    rw [p.tree.disorderExpect_integral hw φ ho,
      (nativeTwinForestTree pre mid A (Bold.fork (single tail)) D).disorderExpect_integral hw φ ho]
    unfold zeroContinuation
    apply integral_congr_ae
    exact Eventually.of_forall (fun y=>hSpinLaw _ (x+y))
  refine ⟨A,Bold,D,R,tb,td,htB,htD,hh,hExact,?_⟩
  intro Q
  rw [hExact]
  exact nativeTwinForest_disorder_law_eq_conditional pre mid A (Bold.fork (single tail)) D hw φ ho v q
    (fun η β δ=>Q (R η β.1 δ) (singleEquiv (S:=S) tail β.2)) x

end OAI.SKFluctuations.Cavity
