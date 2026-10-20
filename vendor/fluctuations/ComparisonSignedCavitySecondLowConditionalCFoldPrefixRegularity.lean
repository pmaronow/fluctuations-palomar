module

public import ComparisonSignedCavitySecondLowClassifiedConditionalCFold
public import ComparisonSignedCavitySecondLowCompleteCFoldRegularity

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
set_option maxHeartbeats 40000000
set_option backward.isDefEq.respectTransparency false
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

theorem native_classified_conditional_c_fold_mid_prefix_smooth0
    (mid tail : List PositiveMass) (Ei : ClockTree S (mid++tail)) (Es D : ClockTree S tail)
    (d : D.Slot) (U : ℕ) (hmid : mid.length < U) (hU : U ≤ (mid++tail).length)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a (mid++tail)) (q : ℕ→ι→ℝ≥0)
    (P : Ei.Assignment→Es.Assignment→D.Assignment→ℝ)
    (outsideF outsideZ : Ei.Assignment→Es.Assignment→S) (Q : S→S→S→ℝ) :
    BddSmooth 0 (fun xi=>prefixTest (clockSteps mid q)
      (gaussianHierarchy w φ (clockSteps tail (fun j=>q (mid.length+j))))
      (fun xs=>nativeExteriorCompleteCFold Ei Es D w φ d (U-mid.length)
        (partitionPoint a (mid++tail) mid.length) q (fun j=>q (mid.length+j)) P outsideF outsideZ Q (xi,xs)) xi) := by
  let V:=Ei.fork (exteriorPrepend mid (Es.fork D))
  let target:V.Slot:=.inr ((exteriorPrependSlotEquiv mid (Es.fork D)).symm (.inr d))
  let H:=fun σ:V.Assignment=>let δ:=exteriorPrependAssignmentEquiv mid (Es.fork D) σ.2;
    P σ.1 δ.1 δ.2*Q (outsideF σ.1 δ.1) (D.atSlot δ.2 d) (outsideZ σ.1 δ.1)
  let Hnew:=fun (σ:V.Assignment) new=>let δ:=exteriorPrependAssignmentEquiv mid (Es.fork D) σ.2;
    P σ.1 δ.1 δ.2*Q (outsideF σ.1 δ.1) new (outsideZ σ.1 δ.1)
  have HE : (fun xi=>nativeJointAttachmentRow w φ q (nativeHighMarkedRows V target (U-1) a) Hnew xi-
      partitionPoint a (mid++tail) U*V.expect w φ q H xi)=
      fun xi=>prefixTest (clockSteps mid q)
        (gaussianHierarchy w φ (clockSteps tail (fun j=>q (mid.length+j))))
        (fun xs=>nativeExteriorCompleteCFold Ei Es D w φ d (U-mid.length)
          (partitionPoint a (mid++tail) mid.length) q (fun j=>q (mid.length+j)) P outsideF outsideZ Q (xi,xs)) xi := by
    funext xi
    have HH:=native_classified_forest_c_replacement_eq_conditional_prefix [] mid tail Ei Es D d U
      (by simpa only [List.length_nil,Nat.zero_add] using hmid) (by simpa only [List.nil_append] using hU)
      a hw φ ho q P outsideF outsideZ Q xi
    have HR : nativeExteriorForestRead [] mid Ei Es D
        (fun η ζ δ=>P η ζ δ*Q (outsideF η ζ) (D.atSlot δ d) (outsideZ η ζ))=H := by
      funext σ
      rfl
    have HM : nativeClassifiedConditionalCFold Ei Es D d (U-mid.length)
        (partitionPoint a (mid++tail) mid.length) w φ q (fun j=>q (mid.length+j)) P outsideF outsideZ Q xi=
        fun xs=>nativeExteriorCompleteCFold Ei Es D w φ d (U-mid.length)
          (partitionPoint a (mid++tail) mid.length) q (fun j=>q (mid.length+j)) P outsideF outsideZ Q (xi,xs) := by
      funext xs
      rfl
    simp only [nativeExteriorForestTree,nativeClassifiedForestOccupiedSlot,nativeClassifiedSourceRead,
      exteriorPrepend,exteriorPrependSlotEquiv,exteriorPrependAssignmentEquiv,
      List.nil_append,List.length_nil,Nat.zero_add,clockSteps,prefixTest,
      Equiv.refl_symm,Equiv.refl_apply] at HH
    rw [HR,HM] at HH
    exact HH
  rw [←HE]
  exact (nativeJointAttachmentRow_smooth0 V hw φ ho q _ Hnew).sub
    ((V.nativeAnchor_expect_smooth hw φ ho q H 0).const_mul _)

end OAI.SKFluctuations.Cavity
