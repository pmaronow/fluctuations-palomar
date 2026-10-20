module

public import ComparisonSignedCavitySecondLowNativeSharedLayerMomentLaw

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
set_option maxHeartbeats 30000000
set_option backward.isDefEq.respectTransparency false
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

private theorem shared_clock_expect_smooth {as : List PositiveMass} (T : ClockTree S as)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ→ι→ℝ≥0) (P : T.Assignment→ℝ) :
    BddSmooth 0 (T.expect w φ q P) := by
  have H:T.expect w φ q P=(T.realize q).expect w φ
      (fun σ=>P ((T.assignmentEquiv q).symm σ)):=funext (T.expect_realize w φ q P)
  rw [H]
  exact (T.realize q).expect_smooth hw φ (clockSteps_ordered ho q) _ 0

omit [Fintype ι] in
private theorem shared_prefix_positive (pre : List PositiveMass) (q : ℕ→ι→ℝ≥0) :
    ∀st∈clockSteps pre q,0 < st.1 := by
  induction pre generalizing q with
  | nil=>simp [clockSteps]
  | cons b pre ih=>
    intro st hst
    rcases List.mem_cons.mp hst with rfl|hst
    · exact b.property
    · exact ih (fun j=>q (j+1)) st hst

theorem nativeSharedPrefixOldMoment_smooth0
    (pre : List PositiveMass) (hpre : pre≠[]) {tail : List PositiveMass}
    (A : ClockTree S tail) (E : ClockTree S (pre++tail)) (s : A.Slot)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a (pre++tail)) (q : ℕ→ι→ℝ≥0)
    (P : A.Assignment→E.Assignment→ℝ) :
    BddSmooth 0 (nativeSharedPrefixOldMoment pre A E w φ q P) := by
  let T:=(exteriorPrepend pre A).fork E
  let target:T.Slot:=.inl ((exteriorPrependSlotEquiv pre A).symm s)
  let Q:=fun σ τ:T.Assignment=>(P (exteriorPrependAssignmentEquiv pre A σ.1) σ.2-
    P (exteriorPrependAssignmentEquiv pre A τ.1) τ.2)^2
  have H:nativeSharedPrefixOldMoment pre A E w φ q P=
      (nativeCloneBlockAtSlot T target pre.length).tree.expect w φ q
        (fun σ=>Q ((nativeCloneBlockAtSlot T target pre.length).oldRestrict σ)
          ((nativeCloneBlockAtSlot T target pre.length).newRestrict σ)):=by
    funext x
    rw [native_shared_prefix_old_moment_eq_original_clone pre hpre A E s w φ q P x]
    exact nativeRetainedCloneCutMean_eq_clone hw φ T ho target pre.length q Q x
  rw [H]
  exact shared_clock_expect_smooth _ hw φ ho q _

theorem nativeSharedPrefixNewMoment_smooth0
    (pre : List PositiveMass) (hpre : pre≠[]) {tail : List PositiveMass}
    (A : ClockTree S tail) (E : ClockTree S (pre++tail)) (s : A.Slot)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a (pre++tail)) (q : ℕ→ι→ℝ≥0)
    (F : E.Assignment→S→ℝ) :
    BddSmooth 0 (nativeSharedPrefixNewMoment pre A E s w φ q F) := by
  let T:=(exteriorPrepend pre A).fork E
  let target:T.Slot:=.inl ((exteriorPrependSlotEquiv pre A).symm s)
  let F0:=fun σ:T.Assignment=>F σ.2 ((exteriorPrepend pre A).atSlot σ.1
    ((exteriorPrependSlotEquiv pre A).symm s))
  let Q:=fun σ τ:T.Assignment=>(F0 σ-F0 τ)^2
  have H:nativeSharedPrefixNewMoment pre A E s w φ q F=
      (nativeCloneBlockAtSlot T target pre.length).tree.expect w φ q
        (fun σ=>Q ((nativeCloneBlockAtSlot T target pre.length).oldRestrict σ)
          ((nativeCloneBlockAtSlot T target pre.length).newRestrict σ)):=by
    funext x
    rw [native_shared_prefix_new_moment_eq_original_clone pre hpre A E s w φ q F x]
    exact nativeRetainedCloneCutMean_eq_clone hw φ T ho target pre.length q Q x
  rw [H]
  exact shared_clock_expect_smooth _ hw φ ho q _

theorem nativeSharedPrefixLayer_smooth0
    (pre : List PositiveMass) {tail : List PositiveMass}
    (A : ClockTree S tail) (E : ClockTree S (pre++tail))
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a (pre++tail)) (v z : ℝ) (q : ℕ→ι→ℝ≥0)
    (P : A.Assignment→E.Assignment→ℝ) (F : E.Assignment→S→ℝ) :
    BddSmooth 0 (nativeSharedPrefixLayer pre A E w φ a v z q P F) := by
  let qt:=fun j=>q (pre.length+j)
  let cs:=clockSteps pre q
  let ts:=clockSteps tail qt
  have Hfull:OrderedSteps a (cs++ts):=by
    have HH:=clockSteps_ordered ho q
    rw [clockSteps_append] at HH
    exact HH
  have Htail:=prefixEndMass_ordered cs ts Hfull
  obtain ⟨L,hL⟩:=gaussianHierarchy_lipschitz hw φ ts Htail
  unfold nativeSharedPrefixLayer ClockTree.expect
  apply BddSmooth.sum Finset.univ
  intro e _
  exact (E.weight_smooth hw φ ho q e 0).mul
    (prefixTest_smooth0 hL
      ((actualCutRow_smooth hw φ (A.realize qt) Htail z
        (fun σ=>P ((A.assignmentEquiv qt).symm σ) e) (F e) 0).sub
       (actualCutRow_smooth hw φ (A.realize qt) Htail v
        (fun σ=>P ((A.assignmentEquiv qt).symm σ) e) (F e) 0)) cs (shared_prefix_positive pre q))

theorem native_shared_prefix_incoming_layer_sq_le
    (pre : List PositiveMass) (hpre : pre≠[]) {tail : List PositiveMass}
    (A : ClockTree S tail) (E : ClockTree S (pre++tail)) (s : A.Slot)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a v z : ℝ} (ho : MassOrdered a (pre++tail)) (hav : a ≤ v)
    (q : ℕ→ι→ℝ≥0) (hp : ∀st∈clockSteps pre q,st.1 ≤ v) (hvz : v ≤ z) (hz : z ≤ 2*v)
    (P : A.Assignment→E.Assignment→ℝ) (F : E.Assignment→S→ℝ)
    (μ : Measure (ι→ℝ)) [IsProbabilityMeasure μ] :
    (∫x,nativeSharedPrefixLayer pre A E w φ a v z q P F x ∂μ)^2 ≤
      (3*(A.leaves:ℝ)*v)^2*(∫x,nativeSharedPrefixOldMoment pre A E w φ q P x ∂μ)*
        (∫x,nativeSharedPrefixNewMoment pre A E s w φ q F x ∂μ) := by
  have hIP:Integrable (nativeSharedPrefixOldMoment pre A E w φ q P) μ:=by
    simpa only [zero_add] using
      (nativeSharedPrefixOldMoment_smooth0 pre hpre A E s hw φ ho q P).integrable_zero_shift (ν:=μ) 0
  have hIF:Integrable (nativeSharedPrefixNewMoment pre A E s w φ q F) μ:=by
    simpa only [zero_add] using
      (nativeSharedPrefixNewMoment_smooth0 pre hpre A E s hw φ ho q F).integrable_zero_shift (ν:=μ) 0
  have hIL:Integrable (nativeSharedPrefixLayer pre A E w φ a v z q P F) μ:=by
    simpa only [zero_add] using
      (nativeSharedPrefixLayer_smooth0 pre A E hw φ ho v z q P F).integrable_zero_shift (ν:=μ) 0
  apply actual_original_root_gram_sq_le μ hIP hIF hIL
  · intro x
    rw [native_shared_prefix_old_moment_eq_original_clone pre hpre A E s w φ q P x,
      nativeRetainedCloneCutMean_eq_clone hw φ _ ho]
    rw [ClockTree.expect_realize]
    exact ReplicaTree.expect_nonneg hw φ _ (clockSteps_ordered ho q) (fun _=>sq_nonneg _) x
  · intro x
    rw [native_shared_prefix_new_moment_eq_original_clone pre hpre A E s w φ q F x,
      nativeRetainedCloneCutMean_eq_clone hw φ _ ho]
    rw [ClockTree.expect_realize]
    exact ReplicaTree.expect_nonneg hw φ _ (clockSteps_ordered ho q) (fun _=>sq_nonneg _) x
  · intro x
    exact native_shared_prefix_layer_sq_le pre A E s hw φ ho hav q hp hvz hz P F x

end OAI.SKFluctuations.Cavity
