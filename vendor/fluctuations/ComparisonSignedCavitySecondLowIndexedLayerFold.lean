module

public import ComparisonSignedCavitySecondLowIndexedCloneMomentLedger

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
set_option maxHeartbeats 30000000
set_option backward.isDefEq.respectTransparency false
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

def nativeScalarIndexedCutLayerFold (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) :
    {as : List PositiveMass}→(T : ClockTree S as)→ℕ→ℝ→ℝ→ℝ→(ℕ→ι→ℝ≥0)→
      (T.Assignment→ℝ)→(S→ℝ)→(ι→ℝ)→ℝ
  | _,T,0,a,v,z,q,P,F,x=>nativeJointActualCutRow T w φ a z q (fun σ s=>P σ*F s) x-
      nativeJointActualCutRow T w φ a v q (fun σ s=>P σ*F s) x
  | _,.leaf,_+1,a,v,z,q,P,F,x=>nativeJointActualCutRow .leaf w φ a z q (fun σ s=>P σ*F s) x-
      nativeJointActualCutRow .leaf w φ a v q (fun σ s=>P σ*F s) x
  | _::as,.step b T,cut+1,_,v,z,q,P,F,x=>
      shiftedMean (Measure.pi fun i=>gaussianReal 0 (q 0 i)) b.val
        (gaussianHierarchy w φ (clockSteps as (fun j=>q (j+1))))
        (nativeScalarIndexedCutLayerFold w φ T cut b.val v z (fun j=>q (j+1)) P F) x
  | _,.fork T E,cut+1,a,v,z,q,P,F,x=>
      E.expect w φ q (fun e=>nativeScalarIndexedCutLayerFold w φ T (cut+1) a v z q
        (fun σ=>P (σ,e)) F x) x+
      T.expect w φ q (fun σ=>nativeScalarIndexedCutLayerFold w φ E (cut+1) a v z q
        (fun e=>P (σ,e)) F x) x

private theorem indexed_scalar_cut_row_realize {as : List PositiveMass} (T : ClockTree S as)
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (a v : ℝ) (q : ℕ→ι→ℝ≥0)
    (P : T.Assignment→ℝ) (F : S→ℝ) (x : ι→ℝ) :
    nativeJointActualCutRow T w φ a v q (fun σ s=>P σ*F s) x=
      actualCutRow (T.realize q) w φ a v (fun σ=>P ((T.assignmentEquiv q).symm σ)) F x := by
  classical
  rw [nativeJointActualCutRow_eq_realized]
  rfl

theorem native_scalar_indexed_cut_layer_fold_eq_realized {as : List PositiveMass}
    (T : ClockTree S as) (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (cut : ℕ) (a v z : ℝ) (q : ℕ→ι→ℝ≥0) (P : T.Assignment→ℝ) (F : S→ℝ) (x : ι→ℝ) :
    nativeScalarIndexedCutLayerFold w φ T cut a v z q P F x=
      actualIndexedCutLayerFold w φ (T.realize q) cut a v z
        (fun σ=>P ((T.assignmentEquiv q).symm σ)) F x := by
  classical
  induction T generalizing cut a q x with
  | leaf=>
    cases cut <;> simp only [nativeScalarIndexedCutLayerFold,actualIndexedCutLayerFold,
      indexed_scalar_cut_row_realize,ClockTree.realize]
  | step b T ih=>
    cases cut with
    | zero=>simp only [nativeScalarIndexedCutLayerFold,actualIndexedCutLayerFold,
        indexed_scalar_cut_row_realize]
    | succ cut=>
      change T.Assignment→ℝ at P
      change shiftedMean _ b.val (gaussianHierarchy w φ (clockSteps _ _))
        (nativeScalarIndexedCutLayerFold w φ T cut b.val v z (fun j=>q (j+1)) P F) x=_
      have HI:nativeScalarIndexedCutLayerFold w φ T cut b.val v z (fun j=>q (j+1)) P F=
          actualIndexedCutLayerFold w φ (T.realize (fun j=>q (j+1))) cut b.val v z
            (fun σ=>P ((T.assignmentEquiv (fun j=>q (j+1))).symm σ)) F:=
        funext fun y=>ih cut b.val (fun j=>q (j+1)) P y
      rw [HI]
      rfl
  | fork T E ihT ihE=>
    cases cut with
    | zero=>simp only [nativeScalarIndexedCutLayerFold,actualIndexedCutLayerFold,
        indexed_scalar_cut_row_realize]
    | succ cut=>
      change T.Assignment×E.Assignment→ℝ at P
      change E.expect w φ q (fun e=>nativeScalarIndexedCutLayerFold w φ T (cut+1) a v z q
          (fun σ=>P (σ,e)) F x) x+
        T.expect w φ q (fun σ=>nativeScalarIndexedCutLayerFold w φ E (cut+1) a v z q
          (fun e=>P (σ,e)) F x) x=_
      simp_rw [ihT (cut+1) a q,ihE (cut+1) a q]
      rw [E.expect_realize w φ q,T.expect_realize w φ q]
      rfl

theorem native_scalar_indexed_cut_layer_fold_eq_original {as : List PositiveMass}
    (T : ClockTree S as) {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (cut : ℕ) {a v z : ℝ} (ho : MassOrdered a as) (hcut : cut ≤ as.length)
    (q : ℕ→ι→ℝ≥0) (hp : ∀st∈(clockSteps as q).take cut,st.1 ≤ v) (hvz : v ≤ z)
    (P : T.Assignment→ℝ) (F : S→ℝ) (x : ι→ℝ) :
    nativeScalarIndexedCutLayerFold w φ T cut a v z q P F x=
      nativeJointActualCutRow T w φ a z q (fun σ s=>P σ*F s) x-
        nativeJointActualCutRow T w φ a v q (fun σ s=>P σ*F s) x := by
  classical
  rw [native_scalar_indexed_cut_layer_fold_eq_realized,indexed_scalar_cut_row_realize,
    indexed_scalar_cut_row_realize]
  exact actualIndexedCutLayerFold_eq_original hw φ (T.realize q) cut (clockSteps_ordered ho q)
    (by simpa only [length_clockSteps] using hcut) hp hvz _ F x

end OAI.SKFluctuations.Cavity
