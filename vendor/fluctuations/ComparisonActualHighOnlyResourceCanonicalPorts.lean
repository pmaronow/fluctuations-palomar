module

public import ComparisonActualHighOnlyOriginalTaylorProfiles
public import ComparisonSignedCavityGRestorationWords
public import ComparisonSignedCavityUnbondedLowGMarkedSource

@[expose] public section

noncomputable section
set_option maxHeartbeats 16000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators

private theorem highOnly_onMarked_canonical_product
    {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (G : ActualNaturalBoundaryShape n a T) (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (forms : Fin a→NativeSourceFactorForm) (σ : p.tree.Assignment) :
    ((G.onMarked p hp).canonicalHighOnlySource M forms).product σ=
      (G.canonicalHighOnlySource M forms).product (p.restrict σ) := by
  unfold ActualNaturalBoundaryShape.product fullBoundaryAffineProduct
  apply Finset.prod_congr rfl
  intro e _
  simp only [ActualNaturalBoundaryShape.canonicalHighOnlySource]
  rw [G.onMarked_sourceLowMass p hp e]
  simp only [ActualNaturalBoundaryShape.onMarked,p.restrict_at]

private theorem highOnly_canonicalOldShape_product
    {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (g : NativeOriginalGMarkedWord T) (G : ActualNaturalBoundaryShape n a T)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (forms : Fin a→NativeSourceFactorForm) (σ : g.tree.Assignment) :
    ((g.canonicalOldShape G).canonicalHighOnlySource M forms).product σ=
      (G.canonicalHighOnlySource M forms).product (g.p.restrict (g.r.restrict (g.z.restrict σ))) := by
  dsimp only [NativeOriginalGMarkedWord.canonicalOldShape]
  exact (highOnly_onMarked_canonical_product ((G.onMarked g.p g.hp).onMarked g.r g.hr)
    g.z g.hz M forms σ).trans
    ((highOnly_onMarked_canonical_product (G.onMarked g.p g.hp) g.r g.hr M forms (g.z.restrict σ)).trans
      (highOnly_onMarked_canonical_product G g.p g.hp M forms (g.r.restrict (g.z.restrict σ))))

theorem NativeOriginalGMarkedWord.originalRestorationTest_canonical_high_only
    {n aDegree : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (g : NativeOriginalGMarkedWord T) (G : ActualNaturalBoundaryShape n aDegree T)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (forms : Fin aDegree→NativeSourceFactorForm) (U : ℕ) (K b S : ℕ→ℝ) (a : T.Slot) :
    g.originalRestorationTest U K b S (G.canonicalHighOnlySource M forms).product a=
      fun σ=>((g.canonicalOldShape G).canonicalHighOnlySource M forms).product σ*
        nativeOriginalHighGAtom g.tree U K b S
          (g.z.embed (g.r.embed (g.p.embed a))) (g.z.embed (g.r.embed g.p.mark))
          (g.z.embed g.r.mark) g.z.mark σ := by
  funext σ
  rw [highOnly_canonicalOldShape_product g G M forms σ]
  rfl

theorem ActualNaturalBoundaryShape.native_double_marked_unbonded_low_pair_test_high_only
    {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (G : ActualNaturalBoundaryShape n a T)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (forms : Fin a→NativeSourceFactorForm) (S : ℕ→ℝ) (u z : T.Slot)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0) :
    (fun σ=>(G.canonicalHighOnlySource M forms).restProduct
        (p.restRestrict (r.restRestrict (r.tree.cavityAssignment σ).1))*
      (deletedOverlap n
        (joinSpin (T.cavityLeft.atSlot (p.restRestrict (r.restRestrict (r.tree.cavityAssignment σ).1)) (T.cavityLeftSlot u),false))
        (joinSpin (T.cavityLeft.atSlot (p.restRestrict (r.restRestrict (r.tree.cavityAssignment σ).1)) (T.cavityLeftSlot z),false))-
          S (T.splitIndex u z)))=
    fun σ=>(((G.nativeCMarkedLift p hp).nativeCMarkedLift r hr).canonicalHighOnlySource M forms).product σ*
      (deletedOverlap n (joinSpin (r.tree.atSlot σ (r.embed (p.embed u))))
          (joinSpin (r.tree.atSlot σ (r.embed (p.embed z))))-
          S (r.tree.splitIndex (r.embed (p.embed u)) (r.embed (p.embed z)))) := by
  funext σ
  rw [G.nativeCDoubleMarkedLift_canonical_product_high_only M forms p hp r hr]
  rw [(p.tree.markedAttach_embed_preserves 0 r hr).2,(T.markedAttach_embed_preserves 0 p hp).2]
  simp only [p.restRestrict_at,r.restRestrict_at,r.tree.atSlot_cavityLeft]
  simp [deletedOverlap,joinSpin]

end OAI.SKFluctuations.Cavity
