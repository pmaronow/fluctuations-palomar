module

public import CavityCutLayerCovariance

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

private theorem actualCutRow_eq_rowList {steps : List (GaussianStep ι)}
    (T : ReplicaTree ι S steps) (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (a v : ℝ) (P : T.Assignment → ℝ) (F : S → ℝ) (x : ι → ℝ) :
    actualCutRow T w φ a v P F x = ReplicaTree.rowList w φ
      ((T.cutMarkedAttach a v).map (fun p => p.toPlacement)) P F x := by
  simp only [actualCutRow, ReplicaTree.rowList, List.map_map]
  rfl

private theorem forget_step {tail : List (GaussianStep ι)} (T : ReplicaTree ι S tail)
    (st : GaussianStep ι) (ps : List (ReplicaTree.MarkedPlacement T)) :
    (ps.map (ReplicaTree.MarkedPlacement.step st)).map (fun p => p.toPlacement) =
    (ps.map (fun p => p.toPlacement)).map (ReplicaTree.Placement.step st) := by
  simp only [List.map_map]
  rfl

private theorem forget_left {steps : List (GaussianStep ι)} (T U : ReplicaTree ι S steps)
    (ps : List (ReplicaTree.MarkedPlacement T)) :
    (ps.map (ReplicaTree.MarkedPlacement.left U)).map (fun p => p.toPlacement) =
    (ps.map (fun p => p.toPlacement)).map (ReplicaTree.Placement.left U) := by
  simp only [List.map_map]
  rfl

private theorem forget_right {steps : List (GaussianStep ι)} (T U : ReplicaTree ι S steps)
    (ps : List (ReplicaTree.MarkedPlacement U)) :
    (ps.map (ReplicaTree.MarkedPlacement.right T)).map (fun p => p.toPlacement) =
    (ps.map (fun p => p.toPlacement)).map (ReplicaTree.Placement.right T) := by
  simp only [List.map_map]
  rfl

private theorem rowList_cons (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} {T : ReplicaTree ι S steps}
    (p : ReplicaTree.Placement T) (ps : List (ReplicaTree.Placement T))
    (P : T.Assignment → ℝ) (F : S → ℝ) (x : ι → ℝ) :
    ReplicaTree.rowList w φ (p::ps) P F x =
      p.coeff*p.eval w φ P F x+ReplicaTree.rowList w φ ps P F x := rfl

private theorem rowList_append (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} {T : ReplicaTree ι S steps}
    (ps qs : List (ReplicaTree.Placement T)) (P : T.Assignment → ℝ) (F : S → ℝ) (x : ι → ℝ) :
    ReplicaTree.rowList w φ (ps++qs) P F x =
      ReplicaTree.rowList w φ ps P F x+ReplicaTree.rowList w φ qs P F x := by
  simp only [ReplicaTree.rowList, List.map_append, List.sum_append]

theorem actualCutRow_smooth {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)}
    (T : ReplicaTree ι S steps) {a : ℝ} (ho : OrderedSteps a steps) (v : ℝ)
    (P : T.Assignment → ℝ) (F : S → ℝ) (r : ℕ) :
    BddSmooth r (actualCutRow T w φ a v P F) := by
  have he : actualCutRow T w φ a v P F = ReplicaTree.rowList w φ
      ((T.cutMarkedAttach a v).map (fun p => p.toPlacement)) P F :=
    funext (fun x => actualCutRow_eq_rowList T w φ a v P F x)
  rw [he]
  exact ReplicaTree.rowList_smooth hw φ _ ho P F r

theorem actual_cut_row_step_before {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {tail : List (GaussianStep ι)}
    (T : ReplicaTree ι S tail) (m : ℝ) (q : ι → ℝ≥0) {a v : ℝ}
    (ho : OrderedSteps a ((m,q)::tail)) (hv : v < m)
    (P : T.Assignment → ℝ) (F : S → ℝ) (x : ι → ℝ) :
    actualCutRow (T.step (m,q)) w φ a v P F x =
      a*(T.step (m,q)).expect w φ P x*gaussianHierarchyMean w φ F ((m,q)::tail) x := by
  simp only [actualCutRow, ReplicaTree.cutMarkedAttach, if_pos hv, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil]
  change a*(ReplicaTree.Placement.fresh (T.step (m,q)) a).eval w φ P F x+0 = _
  rw [ReplicaTree.Placement.eval_fresh hw φ _ ho]
  ring

theorem actual_cut_row_step_after {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {tail : List (GaussianStep ι)}
    (T : ReplicaTree ι S tail) (m : ℝ) (q : ι → ℝ≥0) {a v : ℝ}
    (ho : OrderedSteps a ((m,q)::tail)) (hv : m ≤ v)
    (P : T.Assignment → ℝ) (F : S → ℝ) (x : ι → ℝ) :
    actualCutRow (T.step (m,q)) w φ a v P F x =
      (a-m)*(T.step (m,q)).expect w φ P x*gaussianHierarchyMean w φ F ((m,q)::tail) x+
      shiftedMean (Measure.pi (fun i => gaussianReal 0 (q i))) m
        (gaussianHierarchy w φ tail) (actualCutRow T w φ m v P F) x := by
  rw [actualCutRow_eq_rowList]
  simp only [ReplicaTree.cutMarkedAttach, if_neg (not_lt.mpr hv), List.map_cons,
    forget_step]
  rw [rowList_cons]
  change (a-m)*(ReplicaTree.Placement.fresh (T.step (m,q)) (a-m)).eval w φ P F x+
    ReplicaTree.rowList w φ
      (((T.cutMarkedAttach m v).map (fun p => p.toPlacement)).map
        (ReplicaTree.Placement.step (m,q))) P F x = _
  rw [ReplicaTree.Placement.eval_fresh hw φ _ ho,
    ReplicaTree.rowList_map_step hw φ _ m q ho.2.2.2]
  have he : actualCutRow T w φ m v P F = ReplicaTree.rowList w φ
      ((T.cutMarkedAttach m v).map (fun p => p.toPlacement)) P F :=
    funext (fun y => actualCutRow_eq_rowList T w φ m v P F y)
  rw [← he]
  ring

theorem actual_cut_layer_shared_step {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {tail : List (GaussianStep ι)}
    (T : ReplicaTree ι S tail) (m : ℝ) (q : ι → ℝ≥0) {a v z : ℝ}
    (ho : OrderedSteps a ((m,q)::tail)) (hv : m ≤ v) (hvz : v ≤ z)
    (P : T.Assignment → ℝ) (F : S → ℝ) (x : ι → ℝ) :
    actualCutRow (T.step (m,q)) w φ a z P F x-
      actualCutRow (T.step (m,q)) w φ a v P F x =
    shiftedMean (Measure.pi (fun i => gaussianReal 0 (q i))) m
      (gaussianHierarchy w φ tail)
      (fun y => actualCutRow T w φ m z P F y-actualCutRow T w φ m v P F y) x := by
  rw [actual_cut_row_step_after hw φ T m q ho (hv.trans hvz),
    actual_cut_row_step_after hw φ T m q ho hv,
    shiftedMean_sub (actualCutRow_smooth hw φ T ho.2.2.2 z P F 0)
      (actualCutRow_smooth hw φ T ho.2.2.2 v P F 0)
      (gaussianHierarchy_integrable hw φ tail ho.2.2.2 m q x)]
  ring

theorem actual_cut_layer_crossed_step {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {tail : List (GaussianStep ι)}
    (T : ReplicaTree ι S tail) (m : ℝ) (q : ι → ℝ≥0) {a v z : ℝ}
    (ho : OrderedSteps a ((m,q)::tail)) (hv : v < m) (hz : m ≤ z)
    (P : T.Assignment → ℝ) (F : S → ℝ) (x : ι → ℝ) :
    actualCutRow (T.step (m,q)) w φ a z P F x-
      actualCutRow (T.step (m,q)) w φ a v P F x =
    ((T.cutMarkedAttach m z).map (fun p => p.coeff*
      ((p.toPlacement.step (m,q)).eval w φ P F x-
        (ReplicaTree.Placement.fresh (T.step (m,q)) m).eval w φ P F x))).sum := by
  rw [actual_cut_row_step_before hw φ T m q ho hv,
    actual_cut_row_step_after hw φ T m q ho hz]
  have hs (ps : List (ReplicaTree.MarkedPlacement T)) :
      (ps.map (fun p => p.coeff*
        ((p.toPlacement.step (m,q)).eval w φ P F x-
          (ReplicaTree.Placement.fresh (T.step (m,q)) m).eval w φ P F x))).sum =
      ReplicaTree.rowList w φ ((ps.map (fun p => p.toPlacement)).map
        (ReplicaTree.Placement.step (m,q))) P F x-
      (ps.map (fun p => p.coeff)).sum*
        (ReplicaTree.Placement.fresh (T.step (m,q)) m).eval w φ P F x := by
    induction ps with
    | nil => simp [ReplicaTree.rowList]
    | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons, ReplicaTree.rowList] at ih ⊢
      rw [ih]
      have hc : (p.toPlacement.step (m,q)).coeff = p.coeff := rfl
      rw [hc]
      ring
  rw [hs, T.cutMarkedAttach_mass,
    ReplicaTree.rowList_map_step hw φ _ m q ho.2.2.2,
    ReplicaTree.Placement.eval_fresh hw φ _ ho]
  have he : actualCutRow T w φ m z P F = ReplicaTree.rowList w φ
      ((T.cutMarkedAttach m z).map (fun p => p.toPlacement)) P F :=
    funext (fun y => actualCutRow_eq_rowList T w φ m z P F y)
  rw [← he]
  ring

theorem actual_crossed_step_preserves {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {tail : List (GaussianStep ι)}
    (T : ReplicaTree ι S tail) (m : ℝ) (q : ι → ℝ≥0)
    (ho : OrderedSteps m tail) (z : ℝ) (p : ReplicaTree.MarkedPlacement T)
    (hp : p ∈ T.cutMarkedAttach m z) :
    (p.toPlacement.step (m,q)).Preserves w φ :=
  ReplicaTree.Placement.step_preserves hw φ (m,q) ho
    (T.cutMarkedAttach_preserves hw φ ho z p hp)

theorem actual_cut_row_fork {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)}
    (T U : ReplicaTree ι S steps) {a : ℝ} (ho : OrderedSteps a steps) (v : ℝ)
    (P : (T.fork U).Assignment → ℝ) (F : S → ℝ) (x : ι → ℝ) :
    actualCutRow (T.fork U) w φ a v P F x =
      (-a)*(T.fork U).expect w φ P x*gaussianHierarchyMean w φ F steps x+
      (U.expect w φ (fun τ => actualCutRow T w φ a v (fun σ => P (σ,τ)) F x) x+
       T.expect w φ (fun σ => actualCutRow U w φ a v (fun τ => P (σ,τ)) F x) x) := by
  rw [actualCutRow_eq_rowList]
  simp only [ReplicaTree.cutMarkedAttach, List.map_cons, List.map_append,
    forget_left, forget_right]
  rw [rowList_cons, rowList_append]
  change (-a)*(ReplicaTree.Placement.fresh (T.fork U) (-a)).eval w φ P F x+
    (ReplicaTree.rowList w φ
      (((T.cutMarkedAttach a v).map (fun p => p.toPlacement)).map (ReplicaTree.Placement.left U)) P F x+
     ReplicaTree.rowList w φ
      (((U.cutMarkedAttach a v).map (fun p => p.toPlacement)).map (ReplicaTree.Placement.right T)) P F x) = _
  rw [ReplicaTree.Placement.eval_fresh hw φ _ ho,
    ReplicaTree.rowList_map_left, ReplicaTree.rowList_map_right]
  simp_rw [← actualCutRow_eq_rowList]
  ring

private theorem expect_sub (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    (P Q : T.Assignment → ℝ) (x : ι → ℝ) :
    T.expect w φ (fun σ => P σ-Q σ) x = T.expect w φ P x-T.expect w φ Q x := by
  simp only [ReplicaTree.expect, mul_sub, Finset.sum_sub_distrib]

theorem actual_cut_layer_fork {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)}
    (T U : ReplicaTree ι S steps) {a : ℝ} (ho : OrderedSteps a steps) (v z : ℝ)
    (P : (T.fork U).Assignment → ℝ) (F : S → ℝ) (x : ι → ℝ) :
    actualCutRow (T.fork U) w φ a z P F x-actualCutRow (T.fork U) w φ a v P F x =
      U.expect w φ (fun τ => actualCutRow T w φ a z (fun σ => P (σ,τ)) F x-
        actualCutRow T w φ a v (fun σ => P (σ,τ)) F x) x+
      T.expect w φ (fun σ => actualCutRow U w φ a z (fun τ => P (σ,τ)) F x-
        actualCutRow U w φ a v (fun τ => P (σ,τ)) F x) x := by
  rw [actual_cut_row_fork hw φ T U ho, actual_cut_row_fork hw φ T U ho,
    expect_sub, expect_sub]
  ring

theorem actual_cut_layer_leaf {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {a v z : ℝ} (ho : OrderedSteps a ([] : List (GaussianStep ι)))
    (hv : v < 1) (hz : 1 ≤ z) (P F : S → ℝ) (x : ι → ℝ) :
    actualCutRow (ReplicaTree.leaf (ι := ι)) w φ a z P F x-
      actualCutRow (ReplicaTree.leaf (ι := ι)) w φ a v P F x =
    (ReplicaTree.Placement.coincide (ι := ι)).eval w φ P F x-
      (ReplicaTree.Placement.fresh (ReplicaTree.leaf (ι := ι)) 1).eval w φ P F x := by
  simp only [actualCutRow, ReplicaTree.cutMarkedAttach, if_pos hv, if_neg (not_lt.mpr hz),
    ReplicaTree.markedAttach, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  change 1*(ReplicaTree.Placement.coincide (ι := ι)).eval w φ P F x+
    ((a-1)*(ReplicaTree.Placement.fresh (ReplicaTree.leaf (ι := ι)) (a-1)).eval w φ P F x+0)-
    (a*(ReplicaTree.Placement.fresh (ReplicaTree.leaf (ι := ι)) a).eval w φ P F x+0) = _
  rw [ReplicaTree.Placement.eval_fresh hw φ _ ho,
    ReplicaTree.Placement.eval_fresh hw φ _ ho,
    ReplicaTree.Placement.eval_fresh hw φ _ ho]
  ring

end OAI.SKFluctuations.Cavity
