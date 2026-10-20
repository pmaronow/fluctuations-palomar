module

public import ComparisonSignedCavityFreshGraft
public import SKFluctuationsOAI.Probability.SKFluctuations.ClockZeroRefinement

@[expose] public section

noncomputable section
set_option maxHeartbeats 5500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

def nativeFreshRootMean (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (q : ℕ→ι→ℝ≥0)
    (Q : T.Assignment→S→ℝ) (x : ι→ℝ) : ℝ :=
  T.expect w φ q (fun σ=>gaussianHierarchyMean w φ (Q σ) (clockSteps as q) x) x

def nativeTrunkProjectedMean (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) :
    {as : List PositiveMass} → (T : ClockTree S as) → T.Slot → ℕ →
    (ℕ→ι→ℝ≥0) → (T.Assignment→S→ℝ) → (ι→ℝ) → ℝ
  | _,.leaf,_,_,q,Q,x => nativeFreshRootMean w φ .leaf q Q x
  | _,.step b T,_,0,q,Q,x => nativeFreshRootMean w φ (T.step b) q Q x
  | _::as,.step b T,s,j+1,q,Q,x =>
      shiftedMean (Measure.pi fun i=>gaussianReal 0 (q 0 i)) b.val
        (gaussianHierarchy w φ (clockSteps as (fun k=>q (k+1))))
        (nativeTrunkProjectedMean w φ T s j (fun k=>q (k+1)) Q) x
  | _,.fork T V,_,0,q,Q,x => nativeFreshRootMean w φ (T.fork V) q Q x
  | _,.fork T V,s,j+1,q,Q,x => match (s : T.Slot ⊕ V.Slot) with
      | Sum.inl s => ∑ τ,V.weight w φ q τ x*
          nativeTrunkProjectedMean w φ T s (j+1) q (fun σ d=>Q (σ,τ) d) x
      | Sum.inr s => ∑ σ,T.weight w φ q σ x*
          nativeTrunkProjectedMean w φ V s (j+1) q (fun τ d=>Q (σ,τ) d) x

theorem native_fresh_root_expect_eq_conditional_mean {w : S→ℝ} (hw : ∀σ,0<w σ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) {as : List PositiveMass} (T : ClockTree S as)
    {a c : ℝ} (ho : MassOrdered a as) (q : ℕ→ι→ℝ≥0)
    (Q : T.Assignment→S→ℝ) (x : ι→ℝ) :
    (MarkedPlacement.fresh T c).tree.expect w φ q
      (fun σ=>Q ((MarkedPlacement.fresh T c).restrict σ) ((MarkedPlacement.fresh T c).spin σ)) x=
      nativeFreshRootMean w φ T q Q x := by
  change (T.fork (single as)).expect w φ q (fun σ=>Q σ.1 (singleEquiv (S:=S) as σ.2)) x=_
  rw [expect_fork]
  unfold nativeFreshRootMean expect
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  exact congrFun (singleMean_eq_hierarchy hw φ ho q (Q σ)) x

theorem native_fork_expect_external_left (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {as : List PositiveMass} (T V : ClockTree S as) (q : ℕ→ι→ℝ≥0)
    (P : (T.fork V).Assignment→ℝ) (x : ι→ℝ) :
    (T.fork V).expect w φ q P x=
      ∑ τ,V.weight w φ q τ x*T.expect w φ q (fun σ=>P (σ,τ)) x := by
  simp only [expect,weight_fork,Fintype.sum_prod_type,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro τ _
  apply Finset.sum_congr rfl
  intro σ _
  ring

theorem native_trunk_projected_eq_fresh_graft {w : S→ℝ} (hw : ∀σ,0<w σ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) {as : List PositiveMass} (T : ClockTree S as)
    {a : ℝ} (ho : MassOrdered a as) (s : T.Slot) (j : ℕ)
    (q : ℕ→ι→ℝ≥0) (Q : T.Assignment→S→ℝ) (x : ι→ℝ) :
    nativeTrunkProjectedMean w φ T s j q Q x=
      (nativeFreshAtSlot T a s j).tree.expect w φ q
        (fun σ=>Q ((nativeFreshAtSlot T a s j).restrict σ) ((nativeFreshAtSlot T a s j).spin σ)) x := by
  induction T generalizing a j q x with
  | leaf => exact (native_fresh_root_expect_eq_conditional_mean (c:=a-1) hw φ .leaf ho q Q x).symm
  | step b T ih =>
    cases j with
    | zero => exact (native_fresh_root_expect_eq_conditional_mean (c:=a-b.val) hw φ (T.step b) ho q Q x).symm
    | succ j =>
      change shiftedMean _ _ _ _ x=
        ((nativeFreshAtSlot T b.val s j).tree.step b).expect w φ q
          (fun σ=>Q ((nativeFreshAtSlot T b.val s j).restrict σ)
            ((nativeFreshAtSlot T b.val s j).spin σ)) x
      rw [expect_step hw φ b _ ho.2.2]
      congr 1
      funext y
      exact ih ho.2.2 s j (fun k=>q (k+1)) Q y
  | fork T V ihT ihV =>
    cases j with
    | zero => exact (native_fresh_root_expect_eq_conditional_mean (c:=-a) hw φ (T.fork V) ho q Q x).symm
    | succ j => cases s with
      | inl s =>
        change (∑ τ,V.weight w φ q τ x*nativeTrunkProjectedMean w φ T s (j+1) q
            (fun σ d=>Q (σ,τ) d) x)=
          ((nativeFreshAtSlot T a s (j+1)).tree.fork V).expect w φ q
            (fun σ=>Q ((nativeFreshAtSlot T a s (j+1)).restrict σ.1,σ.2)
              ((nativeFreshAtSlot T a s (j+1)).spin σ.1)) x
        rw [native_fork_expect_external_left]
        apply Finset.sum_congr rfl
        intro τ _
        congr 1
        exact ihT ho s (j+1) q (fun σ d=>Q (σ,τ) d) x
      | inr s =>
        change (∑ σ,T.weight w φ q σ x*nativeTrunkProjectedMean w φ V s (j+1) q
            (fun τ d=>Q (σ,τ) d) x)=
          (T.fork (nativeFreshAtSlot V a s (j+1)).tree).expect w φ q
            (fun (σ : T.Assignment×(nativeFreshAtSlot V a s (j+1)).tree.Assignment)=>
              Q (σ.1,(nativeFreshAtSlot V a s (j+1)).restrict σ.2)
              ((nativeFreshAtSlot V a s (j+1)).spin σ.2)) x
        rw [expect_fork]
        unfold expect
        apply Finset.sum_congr rfl
        intro σ _
        congr 1
        exact ihV ho s (j+1) q (fun τ d=>Q (σ,τ) d) x

theorem native_trunk_disorder_eq_fresh_graft {w : S→ℝ} (hw : ∀σ,0<w σ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (ho : MassOrdered 0 as) (s : T.Slot) (j : ℕ)
    (q : ℕ→ι→ℝ) (Q : T.Assignment→S→ℝ) :
    (∫ x,nativeTrunkProjectedMean w φ T s j
      (cumulativeIncrements (q 0) (fun k=>q (k+1))) Q x
      ∂Measure.pi (fun i=>gaussianReal 0 (Real.toNNReal (q 0 i))))=
      (nativeFreshAtSlot T 0 s j).tree.disorderExpect w φ 0 q
        (fun σ=>Q ((nativeFreshAtSlot T 0 s j).restrict σ) ((nativeFreshAtSlot T 0 s j).spin σ)) 0 := by
  rw [(nativeFreshAtSlot T 0 s j).tree.disorderExpect_integral hw φ ho]
  simp only [zeroContinuation,Pi.zero_apply,sub_zero,zero_add]
  apply integral_congr_ae
  exact Eventually.of_forall fun x=>native_trunk_projected_eq_fresh_graft hw φ T ho s j _ Q x

theorem native_two_trunk_projections_eq_two_fresh_grafts {w : S→ℝ} (hw : ∀σ,0<w σ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) {as : List PositiveMass} (T : ClockTree S as)
    {a : ℝ} (ho : MassOrdered a as) (s t : T.Slot) (j : ℕ)
    (q : ℕ→ι→ℝ≥0) (Q : T.Assignment→S→S→ℝ) (x : ι→ℝ) :
    let p := nativeFreshAtSlot T a s j
    let r := nativeFreshAtSlot p.tree a (p.embed t) j
    nativeTrunkProjectedMean w φ p.tree (p.embed t) j q
      (fun σ e=>Q (p.restrict σ) (p.spin σ) e) x=
      r.tree.expect w φ q (fun σ=>Q (p.restrict (r.restrict σ))
        (p.spin (r.restrict σ)) (r.spin σ)) x := by
  dsimp only
  exact native_trunk_projected_eq_fresh_graft hw φ (nativeFreshAtSlot T a s j).tree ho
    ((nativeFreshAtSlot T a s j).embed t) j q
    (fun σ e=>Q ((nativeFreshAtSlot T a s j).restrict σ)
      ((nativeFreshAtSlot T a s j).spin σ) e) x

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations
open Hierarchy

theorem native_fresh_root_mean_affine_overlap (n : ℕ)
    {as : List PositiveMass} (T : ClockTree (Spin n) as) {a : ℝ}
    (ho : MassOrdered a as) (q : ℕ→FeatureIndex n→ℝ≥0)
    (P : T.Assignment→ℝ) (s : T.Slot) (h b : ℝ) (x : FeatureIndex n→ℝ) :
    T.nativeFreshRootMean (uniformWeight n) (finiteFeature n) q
      (fun σ d=>P σ*(h+b*orderedOverlap n (T.atSlot σ s) d)) x=
      T.expect (uniformWeight n) (finiteFeature n) q
        (fun σ=>P σ*(h+b*physicalProjectedBoundaryOverlap n (clockSteps as q) (T.atSlot σ s) x)) x := by
  unfold ClockTree.nativeFreshRootMean ClockTree.expect
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  dsimp only
  rw [physical_projected_overlap_eq_fresh_mean n _ (clockSteps_ordered ho q)]
  rw [gaussianHierarchyMean_atoms (uniformWeight_pos n) (finiteFeature n) _ (clockSteps_ordered ho q),
    gaussianHierarchyMean_atoms (uniformWeight_pos n) (finiteFeature n) _ (clockSteps_ordered ho q)]
  calc
    (∑ d:Spin n,P σ*(h+b*orderedOverlap n (T.atSlot σ s) d)*
        hierarchyAtom (uniformWeight n) (finiteFeature n) (clockSteps as q) d x) =
      P σ*h*(∑ d:Spin n,hierarchyAtom (uniformWeight n) (finiteFeature n) (clockSteps as q) d x)+
      P σ*b*(∑ d:Spin n,orderedOverlap n (T.atSlot σ s) d*
        hierarchyAtom (uniformWeight n) (finiteFeature n) (clockSteps as q) d x) := by
      rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro d _
      ring
    _ = _ := by
      rw [hierarchyAtom_sum (uniformWeight_pos n) (finiteFeature n) _ (clockSteps_ordered ho q)]
      ring

end OAI.SKFluctuations
