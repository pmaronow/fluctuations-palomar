module

public import ComparisonSignedCavityForestObservedHighGeometry
public import ComparisonSignedCavityTrunkProjection

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

theorem nativeGroupRootForest_trunk_projected {as : List PositiveMass}
    (T : ClockTree S as) (s : T.Slot) (j : ℕ) (hj : 0 < j)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ → ι → ℝ≥0)
    (Q : T.Assignment → S → ℝ) (x : ι → ℝ) :
    let g:=nativeGroupRootForest T s
    nativeTrunkProjectedMean w φ T s j q Q x=
      g.exterior.expect w φ q (fun η=>nativeTrunkProjectedMean w φ g.occupied g.target j q
        (fun σ d=>Q (g.read η σ) d) x) x := by
  induction T generalizing a with
  | leaf=>
    dsimp only [nativeGroupRootForest,NativeRootForestGrouping.trivial]
    exact (expect_const hw φ (single []) ho q _ x).symm
  | step b T ih=>
    dsimp only [nativeGroupRootForest,NativeRootForestGrouping.trivial]
    exact (expect_const hw φ (single _) ho q _ x).symm
  | fork T V ihT ihV=>
    cases j with
    | zero=>omega
    | succ j=>
      cases s with
      | inl s=>
        dsimp only [nativeGroupRootForest,NativeRootForestGrouping.left]
        simp only [nativeTrunkProjectedMean,expect_fork]
        unfold expect at ⊢
        apply Finset.sum_congr rfl
        intro τ _
        congr 1
        exact ihT s ho (fun σ d=>Q (σ,τ) d)
      | inr s=>
        dsimp only [nativeGroupRootForest,NativeRootForestGrouping.right]
        simp only [nativeTrunkProjectedMean,expect_fork]
        unfold expect at ⊢
        apply Finset.sum_congr rfl
        intro σ _
        congr 1
        exact ihV s ho (fun τ d=>Q (σ,τ) d)

theorem exteriorPrepend_trunk_projected_map_congr
    (pre : List PositiveMass) {tail : List PositiveMass}
    (T V : ClockTree S tail) (s : T.Slot) (j : ℕ)
    (read : V.Assignment → T.Assignment) (spin : V.Assignment → S)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a (pre++tail))
    (hCore : ∀(q : ℕ → ι → ℝ≥0) (Q : T.Assignment → S → ℝ) (x : ι → ℝ),
      nativeTrunkProjectedMean w φ T s j q Q x=V.expect w φ q (fun σ=>Q (read σ) (spin σ)) x)
    (q : ℕ → ι → ℝ≥0) (Q : (exteriorPrepend pre T).Assignment → S → ℝ) (x : ι → ℝ) :
    nativeTrunkProjectedMean w φ (exteriorPrepend pre T)
      ((exteriorPrependSlotEquiv pre T).symm.toFun s) (pre.length+j) q Q x=
      (exteriorPrepend pre V).expect w φ q (fun σ=>
        let z:=(exteriorPrependAssignmentEquiv pre V).toFun σ
        Q ((exteriorPrependAssignmentEquiv pre T).symm.toFun (read z)) (spin z)) x := by
  induction pre generalizing a q x with
  | nil=>
    dsimp only [exteriorPrepend,exteriorPrependSlotEquiv,exteriorPrependAssignmentEquiv,
      Equiv.symm,Equiv.refl,List.length_nil,Nat.zero_add] at Q ⊢
    simpa only [id_eq,Nat.zero_add] using hCore q Q x
  | cons b pre ih=>
    have hj : (b::pre).length+j=pre.length+j+1 := by simp only [List.length_cons];omega
    rw [hj]
    dsimp only [exteriorPrepend,exteriorPrependSlotEquiv,exteriorPrependAssignmentEquiv] at Q ⊢
    rw [nativeTrunkProjectedMean.eq_def]
    dsimp only
    rw [expect_step hw φ b _ ho.2.2]
    congr 1
    funext y
    exact ih ho.2.2 (fun k=>q (k+1)) Q y

theorem exteriorPrepend_trunk_projected_eq_fresh_tail
    (pre : List PositiveMass) {tail : List PositiveMass} (T : ClockTree S tail) (s : T.Slot)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a (pre++tail))
    (q : ℕ → ι → ℝ≥0) (Q : (exteriorPrepend pre T).Assignment → S → ℝ) (x : ι → ℝ) :
    nativeTrunkProjectedMean w φ (exteriorPrepend pre T)
      ((exteriorPrependSlotEquiv pre T).symm.toFun s) pre.length q Q x=
      (exteriorPrepend pre (T.fork (single tail))).expect w φ q (fun σ=>
        let z:=(exteriorPrependAssignmentEquiv pre (T.fork (single tail))).toFun σ
        Q ((exteriorPrependAssignmentEquiv pre T).symm.toFun z.1)
          (singleEquiv (S:=S) tail z.2)) x := by
  have hCore : ∀(q' : ℕ → ι → ℝ≥0) (P : T.Assignment → S → ℝ) (y : ι → ℝ),
      nativeTrunkProjectedMean w φ T s 0 q' P y=
        (T.fork (single tail)).expect w φ q' (fun σ=>P σ.1 (singleEquiv (S:=S) tail σ.2)) y := by
    intro q' P y
    have hFresh:=native_fresh_root_expect_eq_conditional_mean (c:=0) hw φ T ho.suffix_end q' P y
    have hRoot : nativeTrunkProjectedMean w φ T s 0 q' P y=nativeFreshRootMean w φ T q' P y := by
      cases T <;> rfl
    rw [hRoot]
    exact hFresh.symm
  simpa only [Nat.add_zero] using exteriorPrepend_trunk_projected_map_congr pre T
    (T.fork (single tail)) s 0 Prod.fst (fun σ=>singleEquiv (S:=S) tail σ.2)
    hw φ ho hCore q Q x

end OAI.SKFluctuations.Hierarchy.ClockTree
