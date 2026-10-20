module

public import ComparisonSignedCavityTrunkProjection

@[expose] public section

noncomputable section
set_option maxHeartbeats 7500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

def nativeSharedRowsRootMean (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (q : ℕ→ι→ℝ≥0)
    (P : T.Assignment→ℝ) (s t : T.Slot) (F₁ F₂ : S→S→ℝ) (x : ι→ℝ) : ℝ :=
  T.expect w φ q (fun σ=>P σ*
    gaussianHierarchyMean w φ (F₁ (T.atSlot σ s)) (clockSteps as q) x*
    gaussianHierarchyMean w φ (F₂ (T.atSlot σ t)) (clockSteps as q) x) x

def nativeSharedTrunkRowsMean (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) :
    {as : List PositiveMass} → (T : ClockTree S as) → T.Slot → T.Slot → ℕ →
    (ℕ→ι→ℝ≥0) → (T.Assignment→ℝ) → (S→S→ℝ) → (S→S→ℝ) → (ι→ℝ) → ℝ
  | _,.leaf,s,t,_,q,P,F₁,F₂,x => nativeSharedRowsRootMean w φ .leaf q P s t F₁ F₂ x
  | _,.step b T,s,t,0,q,P,F₁,F₂,x => nativeSharedRowsRootMean w φ (T.step b) q P s t F₁ F₂ x
  | _::as,.step b T,s,t,j+1,q,P,F₁,F₂,x =>
      shiftedMean (Measure.pi fun i=>gaussianReal 0 (q 0 i)) b.val
        (gaussianHierarchy w φ (clockSteps as (fun k=>q (k+1))))
        (nativeSharedTrunkRowsMean w φ T s t j (fun k=>q (k+1)) P F₁ F₂) x
  | _,.fork T V,s,t,0,q,P,F₁,F₂,x => nativeSharedRowsRootMean w φ (T.fork V) q P s t F₁ F₂ x
  | _,.fork T V,s,t,j+1,q,P,F₁,F₂,x => match (s : T.Slot⊕V.Slot),(t : T.Slot⊕V.Slot) with
      | Sum.inl s,Sum.inl t => ∑ τ,V.weight w φ q τ x*
          nativeSharedTrunkRowsMean w φ T s t (j+1) q (fun σ=>P (σ,τ)) F₁ F₂ x
      | Sum.inr s,Sum.inr t => ∑ σ,T.weight w φ q σ x*
          nativeSharedTrunkRowsMean w φ V s t (j+1) q (fun τ=>P (σ,τ)) F₁ F₂ x
      | _,_ => 0

def nativeDoubleFreshRowsMean (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (a : ℝ) (s t : T.Slot) (j : ℕ)
    (q : ℕ→ι→ℝ≥0) (P : T.Assignment→ℝ) (F₁ F₂ : S→S→ℝ) (x : ι→ℝ) : ℝ :=
  let p:=nativeFreshAtSlot T a s j
  let r:=nativeFreshAtSlot p.tree a (p.embed t) j
  r.tree.expect w φ q (fun σ=>
    let old:=p.restrict (r.restrict σ)
    P old*F₁ (T.atSlot old s) (p.spin (r.restrict σ))*F₂ (T.atSlot old t) (r.spin σ)) x

theorem native_double_root_rows_eq_conditional_product {w : S→ℝ} (hw : ∀σ,0<w σ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) {as : List PositiveMass} (T : ClockTree S as)
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ→ι→ℝ≥0)
    (P : T.Assignment→ℝ) (s t : T.Slot) (F₁ F₂ : S→S→ℝ) (x : ι→ℝ) :
    ((T.fork (single as)).fork (single as)).expect w φ q
      (fun σ=>P σ.1.1*F₁ (T.atSlot σ.1.1 s) (singleEquiv (S:=S) as σ.1.2)*
        F₂ (T.atSlot σ.1.1 t) (singleEquiv (S:=S) as σ.2)) x=
      nativeSharedRowsRootMean w φ T q P s t F₁ F₂ x := by
  unfold nativeSharedRowsRootMean
  simp_rw [←singleMean_eq_hierarchy hw φ ho q]
  simp only [expect,weight_fork,Fintype.sum_prod_type,singleMean,
    Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem native_shared_trunk_rows_eq_two_fresh_grafts {w : S→ℝ} (hw : ∀σ,0<w σ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) {as : List PositiveMass} (T : ClockTree S as)
    {a : ℝ} (ho : MassOrdered a as) (s t : T.Slot) (j : ℕ)
    (hj : j≤T.splitIndex s t) (q : ℕ→ι→ℝ≥0)
    (P : T.Assignment→ℝ) (F₁ F₂ : S→S→ℝ) (x : ι→ℝ) :
    nativeSharedTrunkRowsMean w φ T s t j q P F₁ F₂ x=
      nativeDoubleFreshRowsMean w φ T a s t j q P F₁ F₂ x := by
  induction T generalizing a j q x with
  | leaf =>
    have hj0 : j=0 := by change j≤0 at hj;omega
    subst j
    simpa only [nativeSharedTrunkRowsMean,nativeDoubleFreshRowsMean,nativeFreshAtSlot,
      MarkedPlacement.fresh] using
      (native_double_root_rows_eq_conditional_product hw φ .leaf ho q P s t F₁ F₂ x).symm
  | step b T ih =>
    cases j with
    | zero =>
      simpa only [nativeSharedTrunkRowsMean,nativeDoubleFreshRowsMean,nativeFreshAtSlot,
        MarkedPlacement.fresh] using
        (native_double_root_rows_eq_conditional_product hw φ (T.step b) ho q P s t F₁ F₂ x).symm
    | succ j =>
      have hj' : j≤T.splitIndex s t := by change j+1≤1+T.splitIndex s t at hj;omega
      dsimp only [nativeSharedTrunkRowsMean,nativeDoubleFreshRowsMean,nativeFreshAtSlot,MarkedPlacement.step]
      rw [expect_step hw φ b _ ho.2.2]
      congr 1
      funext y
      exact ih ho.2.2 s t j hj' (fun k=>q (k+1)) P y
  | fork T V ihT ihV =>
    cases j with
    | zero =>
      simpa only [nativeSharedTrunkRowsMean,nativeDoubleFreshRowsMean,nativeFreshAtSlot,
        MarkedPlacement.fresh] using
        (native_double_root_rows_eq_conditional_product hw φ (T.fork V) ho q P s t F₁ F₂ x).symm
    | succ j => cases s with
      | inl s => cases t with
        | inl t =>
          have hj' : j+1≤T.splitIndex s t := hj
          dsimp only [nativeSharedTrunkRowsMean,nativeDoubleFreshRowsMean,nativeFreshAtSlot,
            MarkedPlacement.left,Sum.map,Sum.elim,Function.comp_def,atSlot]
          rw [native_fork_expect_external_left]
          apply Finset.sum_congr rfl
          intro τ _
          congr 1
          exact ihT ho s t (j+1) hj' q (fun σ=>P (σ,τ)) x
        | inr t => have h : j+1≤0 := hj;omega
      | inr s => cases t with
        | inl t => have h : j+1≤0 := hj;omega
        | inr t =>
          have hj' : j+1≤V.splitIndex s t := hj
          dsimp only [nativeSharedTrunkRowsMean,nativeDoubleFreshRowsMean,nativeFreshAtSlot,
            MarkedPlacement.right,Sum.map,Sum.elim,Function.comp_def,atSlot]
          rw [expect_fork]
          change (∑ σ,T.weight w φ q σ x*nativeSharedTrunkRowsMean w φ V s t (j+1) q
              (fun τ=>P (σ,τ)) F₁ F₂ x)=_
          unfold expect
          apply Finset.sum_congr rfl
          intro σ _
          congr 1
          exact ihV ho s t (j+1) hj' q (fun τ=>P (σ,τ)) x

theorem native_shared_trunk_rows_disorder_eq_two_fresh_grafts {w : S→ℝ} (hw : ∀σ,0<w σ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (ho : MassOrdered 0 as) (s t : T.Slot) (j : ℕ) (hj : j≤T.splitIndex s t)
    (q : ℕ→ι→ℝ) (P : T.Assignment→ℝ) (F₁ F₂ : S→S→ℝ) :
    let p:=nativeFreshAtSlot T 0 s j
    let r:=nativeFreshAtSlot p.tree 0 (p.embed t) j
    (∫ x,nativeSharedTrunkRowsMean w φ T s t j
      (cumulativeIncrements (q 0) (fun k=>q (k+1))) P F₁ F₂ x
      ∂Measure.pi (fun i=>gaussianReal 0 (Real.toNNReal (q 0 i))))=
      r.tree.disorderExpect w φ 0 q (fun σ=>
        let old:=p.restrict (r.restrict σ)
        P old*F₁ (T.atSlot old s) (p.spin (r.restrict σ))*F₂ (T.atSlot old t) (r.spin σ)) 0 := by
  dsimp only
  rw [((nativeFreshAtSlot (nativeFreshAtSlot T 0 s j).tree 0
    ((nativeFreshAtSlot T 0 s j).embed t) j).tree).disorderExpect_integral hw φ ho]
  simp only [zeroContinuation,Pi.zero_apply,sub_zero,zero_add]
  apply integral_congr_ae
  exact Eventually.of_forall fun x=>native_shared_trunk_rows_eq_two_fresh_grafts hw φ T ho s t j hj _ P F₁ F₂ x

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations
open Hierarchy

theorem physical_fresh_affine_row_mean (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps)
    (σ : Spin n) (h b : ℝ) (x : FeatureIndex n→ℝ) :
    gaussianHierarchyMean (uniformWeight n) (finiteFeature n)
      (fun d=>h+b*orderedOverlap n σ d) steps x=
      h+b*physicalProjectedBoundaryOverlap n steps σ x := by
  rw [physical_projected_overlap_eq_fresh_mean n steps ha]
  rw [gaussianHierarchyMean_atoms (uniformWeight_pos n) (finiteFeature n) steps ha,
    gaussianHierarchyMean_atoms (uniformWeight_pos n) (finiteFeature n) steps ha]
  calc
    (∑ d:Spin n,(h+b*orderedOverlap n σ d)*hierarchyAtom (uniformWeight n) (finiteFeature n) steps d x)=
      h*(∑ d:Spin n,hierarchyAtom (uniformWeight n) (finiteFeature n) steps d x)+
      b*(∑ d:Spin n,orderedOverlap n σ d*hierarchyAtom (uniformWeight n) (finiteFeature n) steps d x) := by
      rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro d _
      ring
    _ = _ := by rw [hierarchyAtom_sum (uniformWeight_pos n) (finiteFeature n) steps ha];ring

theorem native_shared_rows_root_affine_overlap (n : ℕ)
    {as : List PositiveMass} (T : ClockTree (Spin n) as) {a : ℝ}
    (ho : MassOrdered a as) (q : ℕ→FeatureIndex n→ℝ≥0)
    (P : T.Assignment→ℝ) (s t : T.Slot) (h₁ b₁ h₂ b₂ : ℝ) (x : FeatureIndex n→ℝ) :
    T.nativeSharedRowsRootMean (uniformWeight n) (finiteFeature n) q P s t
      (fun σ d=>h₁+b₁*orderedOverlap n σ d) (fun σ d=>h₂+b₂*orderedOverlap n σ d) x=
      T.expect (uniformWeight n) (finiteFeature n) q (fun σ=>P σ*
        (h₁+b₁*physicalProjectedBoundaryOverlap n (clockSteps as q) (T.atSlot σ s) x)*
        (h₂+b₂*physicalProjectedBoundaryOverlap n (clockSteps as q) (T.atSlot σ t) x)) x := by
  unfold ClockTree.nativeSharedRowsRootMean
  simp_rw [physical_fresh_affine_row_mean n _ (clockSteps_ordered ho q)]

end OAI.SKFluctuations
