module

public import ComparisonSignedCavityActualFourOtherSourceCategories
public import ComparisonSignedCavityActualFrozenResourceSiteDifference
public import ComparisonSignedCavityActualFreshPairMomentResourceLaw

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 20000000
set_option backward.isDefEq.respectTransparency false

theorem native_original_deleted_site_centered_source (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (s : T.Slot) (star : ℕ) :
    let g:=nativeFreshAtSlot T 0 s star
    let Pc:=nativeOriginalCenteredRestTest n q U b h K T P
    nativeActualOriginalOtherSourceCategory .deletedSite n q U b h K C T Pc s star=
      -g.tree.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 1 1 b h K)
        (fun σ=>(spinValue (g.tree.atSlot σ (g.embed s)).2*spinValue (g.tree.atSlot σ g.mark).2-
          deletedOverlap n (joinSpin (g.tree.atSlot σ (g.embed s))) (joinSpin (g.tree.atSlot σ g.mark)))*
          Pc (g.restRestrict (g.tree.cavityAssignment σ).1)) 0 := by
  dsimp only
  let g:=nativeFreshAtSlot T 0 s star
  let Pc:=nativeOriginalCenteredRestTest n q U b h K T P
  have Hmean:=native_original_rest_test_marked_mean n q U b h K T ho Pc g
    (nativeFreshAtSlot_mem T 0 s star)
  rw [native_original_centered_rest_test_mean_zero n q U b h K T ho P] at Hmean
  unfold nativeActualOriginalOtherSourceCategory nativeOriginalSitePairExpectation
    nativeActualOriginalFreshPairMoment
  dsimp only
  simp_rw [MarkedPlacement.restrict_at]
  simp_rw [sitePair_apply]
  unfold nativeOriginalRestTestExpectation ClockTree.disorderExpect at Hmean
  unfold ClockTree.disorderExpect
  dsimp only [g,Pc,MarkedPlacement.spin] at Hmean ⊢
  simp only [MarkedPlacement.spin_at]
  simp only [mul_sub,sub_mul,Finset.sum_sub_distrib] at Hmean ⊢
  simp only [mul_comm,mul_assoc] at Hmean ⊢
  simp only [←Finset.mul_sum] at Hmean ⊢
  linear_combination -(C star)*Hmean

theorem native_actual_original_deleted_site_eq_two_resources
    {n : ℕ} {as : List PositiveMass} {i star : ℕ}
    (U : ℕ) (b h K C : ℕ→ℝ) (T : ClockTree (Spin n×Bool) as)
    (P : NativeResourceTerm i star T) (ho : MassOrdered 0 as) :
    let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    let qfull:=cutFullVariance n q U 1 1 b h K
    let g:=nativeFreshAtSlot T 0 P.live.test.target star
    let Pc:=nativeOriginalCenteredRestTest n q U b h K T
      (nativeActualResourceRestValue P 0 qfull 0 C)
    nativeActualOriginalOtherSourceCategory .deletedSite n q U b h K C T Pc P.live.test.target star=
      -(nativeOriginalResourceSiteDeletedDifference (P.retarget 0) 0 qfull 0 U b h K C
          (g.embed P.live.test.target) g.mark+
        nativeOriginalResourceSiteDeletedDifference (P.retarget 0).freeze 0 qfull 0 U b h K C
          (g.embed P.live.test.target) g.mark) := by
  dsimp only
  rw [native_original_deleted_site_centered_source n _ U b h K C T ho]
  simp_rw [native_actual_centered_fresh_resource_readout _ b h K C T P ho]
  unfold nativeOriginalResourceSiteDeletedDifference ClockTree.disorderExpect
  have HQ : cavityPath n U 1 1 (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) b h K=
      cutFullVariance n (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) U 1 1 b h K:=rfl
  rw [HQ]
  simp only [mul_add,Finset.sum_add_distrib]

end OAI.SKFluctuations.Cavity
