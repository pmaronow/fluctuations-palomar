module

public import CavityJointAttachmentGrouping
public import CavityLocalForkLayer
public import CavityActualBoundaryPrefixLaw
public import CavityMomentAllocation
public import SKFluctuationsOAI.Probability.SKFluctuations.ClockZeroRefinement

@[expose] public section

noncomputable section
set_option maxHeartbeats 3000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S] [DecidableEq S]

def jointActualCutRow {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ) (a v : ℝ)
    (H : T.Assignment → S → ℝ) (x : ι → ℝ) : ℝ :=
  jointAttachmentRow w φ (T.cutMarkedAttach a v) H x

def jointActualFresh {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (H : T.Assignment → S → ℝ) (x : ι → ℝ) : ℝ :=
  (T.fork (ReplicaTree.single (S := S) steps)).expect w φ
    (fun σ => H σ.1 (ReplicaTree.singleEquiv (S := S) steps σ.2)) x

theorem jointActualCutRow_eq_spin_sum {steps : List (GaussianStep ι)}
    (T : ReplicaTree ι S steps) (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (a v : ℝ) (H : T.Assignment → S → ℝ) (x : ι → ℝ) :
    jointActualCutRow T w φ a v H x =
      ∑ s, actualCutRow T w φ a v (fun σ => H σ s)
        (fun τ => if τ = s then 1 else 0) x := by
  classical
  rw [jointActualCutRow, jointAttachmentRow_eq_spin_sum]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [actualCutRow, ReplicaTree.rowList, List.map_map]
  rfl

theorem jointActualFresh_eq_spin_sum {steps : List (GaussianStep ι)}
    {w : S → ℝ} (hw : ∀ σ, 0<w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (T : ReplicaTree ι S steps) {a : ℝ} (ho : OrderedSteps a steps)
    (H : T.Assignment → S → ℝ) (x : ι → ℝ) :
    jointActualFresh T w φ H x =
      ∑ s, T.expect w φ (fun σ => H σ s) x *
        gaussianHierarchyMean w φ (fun τ => if τ=s then 1 else 0) steps x := by
  classical
  have he : jointActualFresh T w φ H x =
      jointAttachmentRow w φ [ReplicaTree.MarkedPlacement.fresh T 1] H x := by
    simp only [jointActualFresh,jointAttachmentRow,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,ReplicaTree.MarkedPlacement.fresh,
      ReplicaTree.Placement.fresh,one_mul,add_zero]
  rw [he]
  rw [jointAttachmentRow_eq_spin_sum]
  simp only [List.map_cons,List.map_nil,ReplicaTree.rowList,List.sum_cons,List.sum_nil,
    ReplicaTree.MarkedPlacement.fresh,ReplicaTree.Placement.fresh,one_mul,add_zero]
  apply Finset.sum_congr rfl
  intro s hs
  exact ReplicaTree.Placement.eval_fresh hw φ T ho _ _ 1 x

theorem jointActualCutRow_smooth {steps : List (GaussianStep ι)}
    {w : S → ℝ} (hw : ∀ σ, 0<w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (T : ReplicaTree ι S steps) {a : ℝ} (ho : OrderedSteps a steps)
    (v : ℝ) (H : T.Assignment → S → ℝ) (r : ℕ) :
    BddSmooth r (jointActualCutRow T w φ a v H) := by
  classical
  have he : jointActualCutRow T w φ a v H = fun x =>
      ∑ s, actualCutRow T w φ a v (fun σ => H σ s)
        (fun τ => if τ=s then 1 else 0) x :=
    funext (jointActualCutRow_eq_spin_sum T w φ a v H)
  rw [he]
  exact BddSmooth.sum Finset.univ fun s _ => actualCutRow_smooth hw φ T ho v _ _ r

theorem jointActualCutRow_old_marginal {steps : List (GaussianStep ι)}
    {w : S → ℝ} (hw : ∀ σ, 0<w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (T : ReplicaTree ι S steps) {a : ℝ} (ho : OrderedSteps a steps)
    (v : ℝ) (P : T.Assignment → ℝ) (x : ι → ℝ) :
    jointActualCutRow T w φ a v (fun σ _ => P σ) x = a*T.expect w φ P x := by
  unfold jointActualCutRow jointAttachmentRow
  have he : ((T.cutMarkedAttach a v).map (fun p => p.coeff*p.tree.expect w φ
      (fun σ => P (p.restrict σ)) x)).sum =
      ((T.cutMarkedAttach a v).map (fun p => p.coeff*T.expect w φ P x)).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    rw [T.cutMarkedAttach_preserves hw φ ho v p hp P x]
  rw [he, List.sum_map_mul_right, T.cutMarkedAttach_mass]

theorem jointActualCutRow_step_before {tail : List (GaussianStep ι)}
    {w : S → ℝ} (hw : ∀ σ, 0<w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (T : ReplicaTree ι S tail) (m : ℝ) (q : ι → ℝ≥0) {a v : ℝ}
    (ho : OrderedSteps a ((m,q)::tail)) (hv : v < m)
    (H : T.Assignment → S → ℝ) (x : ι → ℝ) :
    jointActualCutRow (T.step (m,q)) w φ a v H x =
      a*jointActualFresh (T.step (m,q)) w φ H x := by
  classical
  rw [jointActualCutRow_eq_spin_sum, jointActualFresh_eq_spin_sum hw φ _ ho]
  simp_rw [actual_cut_row_step_before hw φ T m q ho hv]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  ring

theorem jointActualCutRow_step_after {tail : List (GaussianStep ι)}
    {w : S → ℝ} (hw : ∀ σ, 0<w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (T : ReplicaTree ι S tail) (m : ℝ) (q : ι → ℝ≥0) {a v : ℝ}
    (ho : OrderedSteps a ((m,q)::tail)) (hv : m≤v)
    (H : T.Assignment → S → ℝ) (x : ι → ℝ) :
    jointActualCutRow (T.step (m,q)) w φ a v H x =
      (a-m)*jointActualFresh (T.step (m,q)) w φ H x +
      shiftedMean (Measure.pi (fun i => gaussianReal 0 (q i))) m
        (gaussianHierarchy w φ tail) (jointActualCutRow T w φ m v H) x := by
  classical
  rw [jointActualCutRow_eq_spin_sum, jointActualFresh_eq_spin_sum hw φ _ ho]
  simp_rw [actual_cut_row_step_after hw φ T m q ho hv]
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro s hs
    ring
  · have he : jointActualCutRow T w φ m v H = fun y =>
        ∑ s, actualCutRow T w φ m v (fun σ => H σ s)
          (fun τ => if τ=s then 1 else 0) y :=
      funext (jointActualCutRow_eq_spin_sum T w φ m v H)
    rw [he, shiftedMean_sum]
    · intro s
      exact actualCutRow_smooth hw φ T ho.2.2.2 v _ _ 0
    · exact gaussianHierarchy_integrable hw φ tail ho.2.2.2 m q x

theorem jointActualCutLayer_shared_step {tail : List (GaussianStep ι)}
    {w : S → ℝ} (hw : ∀ σ, 0<w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (T : ReplicaTree ι S tail) (m : ℝ) (q : ι → ℝ≥0) {a v z : ℝ}
    (ho : OrderedSteps a ((m,q)::tail)) (hv : m≤v) (hvz : v≤z)
    (H : T.Assignment → S → ℝ) (x : ι → ℝ) :
    jointActualCutRow (T.step (m,q)) w φ a z H x-
      jointActualCutRow (T.step (m,q)) w φ a v H x =
      shiftedMean (Measure.pi (fun i => gaussianReal 0 (q i))) m
        (gaussianHierarchy w φ tail)
        (fun y => jointActualCutRow T w φ m z H y-jointActualCutRow T w φ m v H y) x := by
  rw [jointActualCutRow_step_after hw φ T m q ho (hv.trans hvz),
    jointActualCutRow_step_after hw φ T m q ho hv,
    shiftedMean_sub (jointActualCutRow_smooth hw φ T ho.2.2.2 z H 0)
      (jointActualCutRow_smooth hw φ T ho.2.2.2 v H 0)
      (gaussianHierarchy_integrable hw φ tail ho.2.2.2 m q x)]
  ring

theorem jointActualCutRow_fork {steps : List (GaussianStep ι)}
    {w : S → ℝ} (hw : ∀ σ, 0<w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (T U : ReplicaTree ι S steps) {a : ℝ} (ho : OrderedSteps a steps)
    (v : ℝ) (H : (T.fork U).Assignment → S → ℝ) (x : ι → ℝ) :
    jointActualCutRow (T.fork U) w φ a v H x =
      (-a)*jointActualFresh (T.fork U) w φ H x +
      U.expect w φ (fun τ => jointActualCutRow T w φ a v
        (fun σ s => H (σ,τ) s) x) x +
      T.expect w φ (fun σ => jointActualCutRow U w φ a v
        (fun τ s => H (σ,τ) s) x) x := by
  classical
  rw [jointActualCutRow_eq_spin_sum, jointActualFresh_eq_spin_sum hw φ _ ho]
  simp_rw [actual_cut_row_fork hw φ T U ho]
  simp only [Finset.sum_add_distrib, Finset.mul_sum]
  have hu : U.expect w φ (fun τ => jointActualCutRow T w φ a v
      (fun σ s => H (σ,τ) s) x) x =
      ∑ s, U.expect w φ (fun τ => actualCutRow T w φ a v
        (fun σ => H (σ,τ) s) (fun r => if r=s then 1 else 0) x) x := by
    simp_rw [jointActualCutRow_eq_spin_sum]
    simp only [ReplicaTree.expect, Finset.mul_sum]
    rw [Finset.sum_comm]
  have ht : T.expect w φ (fun σ => jointActualCutRow U w φ a v
      (fun τ s => H (σ,τ) s) x) x =
      ∑ s, T.expect w φ (fun σ => actualCutRow U w φ a v
        (fun τ => H (σ,τ) s) (fun r => if r=s then 1 else 0) x) x := by
    simp_rw [jointActualCutRow_eq_spin_sum]
    simp only [ReplicaTree.expect, Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [hu, ht]
  simp only [mul_assoc]
  ring

private theorem expect_sub_joint (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    (P Q : T.Assignment → ℝ) (x : ι → ℝ) :
    T.expect w φ (fun σ => P σ-Q σ) x=T.expect w φ P x-T.expect w φ Q x := by
  simp only [ReplicaTree.expect, mul_sub, Finset.sum_sub_distrib]

theorem jointActualCutLayer_fork {steps : List (GaussianStep ι)}
    {w : S → ℝ} (hw : ∀ σ, 0<w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (T U : ReplicaTree ι S steps) {a : ℝ} (ho : OrderedSteps a steps)
    (v z : ℝ) (H : (T.fork U).Assignment → S → ℝ) (x : ι → ℝ) :
    jointActualCutRow (T.fork U) w φ a z H x-
      jointActualCutRow (T.fork U) w φ a v H x =
      U.expect w φ (fun τ => jointActualCutRow T w φ a z (fun σ s => H (σ,τ) s) x-
        jointActualCutRow T w φ a v (fun σ s => H (σ,τ) s) x) x +
      T.expect w φ (fun σ => jointActualCutRow U w φ a z (fun τ s => H (σ,τ) s) x-
        jointActualCutRow U w φ a v (fun τ s => H (σ,τ) s) x) x := by
  rw [jointActualCutRow_fork hw φ T U ho, jointActualCutRow_fork hw φ T U ho,
    expect_sub_joint, expect_sub_joint]
  ring

theorem jointAttachmentRow_left_exterior {steps : List (GaussianStep ι)}
    (T E : ReplicaTree ι S steps) (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (ps : List (ReplicaTree.MarkedPlacement T))
    (H : (T.fork E).Assignment → S → ℝ) (x : ι → ℝ) :
    jointAttachmentRow w φ (ps.map (ReplicaTree.MarkedPlacement.left E)) H x =
      E.expect w φ (fun e => jointAttachmentRow w φ ps (fun σ s => H (σ,e) s) x) x := by
  classical
  rw [jointAttachmentRow_eq_spin_sum]
  have he : (ps.map (ReplicaTree.MarkedPlacement.left E)).map
      ReplicaTree.MarkedPlacement.toPlacement =
      (ps.map ReplicaTree.MarkedPlacement.toPlacement).map
        (ReplicaTree.Placement.left E) := by
    simp only [List.map_map]
    rfl
  rw [he]
  simp_rw [ReplicaTree.rowList_map_left,jointAttachmentRow_eq_spin_sum]
  simp only [ReplicaTree.expect,Finset.mul_sum]
  rw [Finset.sum_comm]

def jointActualLeftCutLayer {steps : List (GaussianStep ι)}
    (T E : ReplicaTree ι S steps) (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (a v z : ℝ)
    (H : (T.fork E).Assignment → S → ℝ) (x : ι → ℝ) : ℝ :=
  jointAttachmentRow w φ
    ((T.cutMarkedAttach a z).map (ReplicaTree.MarkedPlacement.left E)) H x-
  jointAttachmentRow w φ
    ((T.cutMarkedAttach a v).map (ReplicaTree.MarkedPlacement.left E)) H x

def actualSharedExteriorLayer {steps : List (GaussianStep ι)}
    (A E : ReplicaTree ι S steps) (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (a v z : ℝ)
    (P : A.Assignment → E.Assignment → ℝ) (F : E.Assignment → S → ℝ)
    (x : ι → ℝ) : ℝ :=
  E.expect w φ (fun e => actualCutRow A w φ a z (fun σ => P σ e) (F e) x-
    actualCutRow A w φ a v (fun σ => P σ e) (F e) x) x

theorem jointActualLeftCutLayer_eq_shared {steps : List (GaussianStep ι)}
    (A E : ReplicaTree ι S steps) (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (a v z : ℝ)
    (P : A.Assignment → E.Assignment → ℝ) (F : E.Assignment → S → ℝ)
    (x : ι → ℝ) :
    jointActualLeftCutLayer A E w φ a v z
      (fun σ s => P σ.1 σ.2*F σ.2 s) x =
      actualSharedExteriorLayer A E w φ a v z P F x := by
  unfold jointActualLeftCutLayer actualSharedExteriorLayer
  rw [jointAttachmentRow_left_exterior,jointAttachmentRow_left_exterior,
    expect_sub_joint]
  congr 1

def actualSharedExteriorOldMoment {steps : List (GaussianStep ι)}
    (A E : ReplicaTree ι S steps) (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (P : A.Assignment → E.Assignment → ℝ) (x : ι → ℝ) : ℝ :=
  (E.fork (A.fork A)).expect w φ (fun σ => (P σ.2.1 σ.1-P σ.2.2 σ.1)^2) x

def actualSharedExteriorNewMoment {steps : List (GaussianStep ι)}
    (E : ReplicaTree ι S steps) (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (F : E.Assignment → S → ℝ) (x : ι → ℝ) : ℝ :=
  (E.fork ((ReplicaTree.single (S := S) steps).fork (ReplicaTree.single (S := S) steps))).expect w φ
    (fun σ => (F σ.1 (ReplicaTree.singleEquiv (S := S) steps σ.2.1)-
      F σ.1 (ReplicaTree.singleEquiv (S := S) steps σ.2.2))^2) x

private theorem quadratic_of_gram {A B C : ℝ} (hA : 0≤A) (hB : 0≤B)
    (h : C^2≤A*B) (t : ℝ) : 0≤t^2*A-2*t*C+B := by
  obtain rfl | hA := hA.eq_or_lt
  · have hc : C=0 := by nlinarith [sq_nonneg C]
    simp only [hc,mul_zero,sub_zero,zero_add]
    exact hB
  · have hh : 0≤A*(t^2*A-2*t*C+B) := by nlinarith [sq_nonneg (t*A-C)]
    exact (mul_nonneg_iff_of_pos_left hA).mp hh

private theorem gram_of_quadratic {A B C : ℝ} (hA : 0≤A) (hB : 0≤B)
    (h : ∀ t : ℝ,0≤t^2*A-2*t*C+B) : C^2≤A*B := by
  obtain rfl | hA := hA.eq_or_lt
  · by_cases hc : C=0
    · simp [hc]
    · have hh := h ((B+1)/(2*C))
      have he : ((B+1)/(2*C))^2*0-2*((B+1)/(2*C))*C+B = -1 := by
        field_simp
        <;> ring
      rw [he] at hh
      norm_num at hh
  · have hh := mul_nonneg hA.le (h (C/A))
    have he : A*((C/A)^2*A-2*(C/A)*C+B)=A*B-C^2 := by
      field_simp
      <;> ring
    rw [he] at hh
    linarith

theorem actualExterior_expect_gram_sq_le {steps : List (GaussianStep ι)}
    {w : S → ℝ} (hw : ∀ σ,0<w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (E : ReplicaTree ι S steps) {a : ℝ} (ho : OrderedSteps a steps)
    (A B C : E.Assignment → ℝ) (k : ℝ) (hA : ∀ e,0≤A e) (hB : ∀ e,0≤B e)
    (hC : ∀ e,(C e)^2≤k^2*A e*B e) (x : ι → ℝ) :
    (E.expect w φ C x)^2≤k^2*E.expect w φ A x*E.expect w φ B x := by
  have hQ (t : ℝ) : 0≤t^2*E.expect w φ A x-2*t*E.expect w φ C x+
      k^2*E.expect w φ B x := by
    have hlocal (e : E.Assignment) : 0≤t^2*A e-2*t*C e+k^2*B e :=
      quadratic_of_gram (hA e) (mul_nonneg (sq_nonneg k) (hB e))
        (by nlinarith [hC e]) t
    have hh := E.expect_nonneg hw φ ho hlocal x
    simpa only [ReplicaTree.expect, mul_add, mul_sub, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc, mul_left_comm] using hh
  have hh := gram_of_quadratic (E.expect_nonneg hw φ ho hA x)
    (mul_nonneg (sq_nonneg k) (E.expect_nonneg hw φ ho hB x)) hQ
  convert hh using 1
  ring

theorem actualSharedExteriorLayer_sq_le {steps : List (GaussianStep ι)}
    {w : S → ℝ} (hw : ∀ σ,0<w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (A E : ReplicaTree ι S steps) {a v z : ℝ} (ho : OrderedSteps a steps)
    (hav : a≤v) (hvz : v≤z) (hz : z≤2*v)
    (P : A.Assignment → E.Assignment → ℝ) (F : E.Assignment → S → ℝ)
    (x : ι → ℝ) :
    (actualSharedExteriorLayer A E w φ a v z P F x)^2≤
      (3*(A.leaves:ℝ)*v)^2*actualSharedExteriorOldMoment A E w φ P x*
        actualSharedExteriorNewMoment E w φ F x := by
  unfold actualSharedExteriorLayer actualSharedExteriorOldMoment actualSharedExteriorNewMoment
  rw [ReplicaTree.expect_fork,ReplicaTree.expect_fork]
  apply actualExterior_expect_gram_sq_le hw φ E ho
    (fun e => actualForkResamplingSquare A w φ (fun σ => P σ e) x)
    (fun e => actualSingleResamplingSquare steps w φ (F e) x)
    (fun e => actualCutRow A w φ a z (fun σ => P σ e) (F e) x-
      actualCutRow A w φ a v (fun σ => P σ e) (F e) x)
    (3*(A.leaves:ℝ)*v)
  · intro e
    exact (A.fork A).expect_nonneg hw φ ho (fun _=>sq_nonneg _) x
  · intro e
    exact ((ReplicaTree.single (S := S) steps).fork (ReplicaTree.single (S := S) steps)).expect_nonneg
      hw φ ho (fun _=>sq_nonneg _) x
  · intro e
    exact actual_cut_layer_resampling_sq_le hw φ A ho hav hvz hz _ _ x

theorem actualSharedExteriorLayer_smooth {steps : List (GaussianStep ι)}
    {w : S → ℝ} (hw : ∀ σ,0<w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (A E : ReplicaTree ι S steps) {a : ℝ} (ho : OrderedSteps a steps)
    (v z : ℝ) (P : A.Assignment → E.Assignment → ℝ)
    (F : E.Assignment → S → ℝ) (r : ℕ) :
    BddSmooth r (actualSharedExteriorLayer A E w φ a v z P F) := by
  unfold actualSharedExteriorLayer ReplicaTree.expect
  apply BddSmooth.sum Finset.univ
  intro e he
  exact (E.weight_smooth hw φ ho r e).mul
    ((actualCutRow_smooth hw φ A ho z _ _ r).sub
      (actualCutRow_smooth hw φ A ho v _ _ r))

theorem actualSharedExteriorOldMoment_smooth {steps : List (GaussianStep ι)}
    {w : S → ℝ} (hw : ∀ σ,0<w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (A E : ReplicaTree ι S steps) {a : ℝ} (ho : OrderedSteps a steps)
    (P : A.Assignment → E.Assignment → ℝ) (r : ℕ) :
    BddSmooth r (actualSharedExteriorOldMoment A E w φ P) :=
  (E.fork (A.fork A)).expect_smooth hw φ ho _ r

theorem actualSharedExteriorNewMoment_smooth {steps : List (GaussianStep ι)}
    {w : S → ℝ} (hw : ∀ σ,0<w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (E : ReplicaTree ι S steps) {a : ℝ} (ho : OrderedSteps a steps)
    (F : E.Assignment → S → ℝ) (r : ℕ) :
    BddSmooth r (actualSharedExteriorNewMoment E w φ F) :=
  (E.fork ((ReplicaTree.single (S := S) steps).fork (ReplicaTree.single (S := S) steps))).expect_smooth hw φ ho _ r

def actualInheritedExteriorLayer {steps : List (GaussianStep ι)}
    (pre : List (GaussianStep ι)) (A : ReplicaTree ι S steps)
    (E : ReplicaTree ι S (pre++steps)) (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (a v z : ℝ)
    (P : A.Assignment → E.Assignment → ℝ) (F : E.Assignment → S → ℝ)
    (x : ι → ℝ) : ℝ :=
  E.expect w φ (fun e => prefixTest pre (gaussianHierarchy w φ steps)
    (fun y => actualCutRow A w φ (prefixEndMass a pre) z (fun σ => P σ e) (F e) y-
      actualCutRow A w φ (prefixEndMass a pre) v (fun σ => P σ e) (F e) y) x) x

theorem actualSharedExteriorLayer_eq_inherited {steps : List (GaussianStep ι)}
    {w : S → ℝ} (hw : ∀ σ,0<w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (pre : List (GaussianStep ι)) (A : ReplicaTree ι S steps)
    (E : ReplicaTree ι S (pre++steps)) {a v z : ℝ}
    (ho : OrderedSteps a (pre++steps)) (hp : ∀ st∈pre, st.1≤v) (hvz : v≤z)
    (P : A.Assignment → E.Assignment → ℝ) (F : E.Assignment → S → ℝ)
    (x : ι → ℝ) :
    actualSharedExteriorLayer (prependReplicaTree pre A) E w φ a v z
      (fun σ e => P (prependAssignmentEquiv pre A σ) e) F x =
      actualInheritedExteriorLayer pre A E w φ a v z P F x := by
  unfold actualSharedExteriorLayer actualInheritedExteriorLayer
  congr 1
  funext e
  exact actual_retained_prefix_cut_layer hw φ A pre ho hp hvz (fun σ=>P σ e) (F e) x

def actualRetainedExteriorOldMoment {steps : List (GaussianStep ι)}
    (pre : List (GaussianStep ι)) (A : ReplicaTree ι S steps)
    (E : ReplicaTree ι S (pre++steps)) (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (P : A.Assignment → E.Assignment → ℝ) (x : ι → ℝ) : ℝ :=
  (E.fork (prependReplicaTree pre (A.fork A))).expect w φ
    (fun σ => let cs := prependAssignmentEquiv pre (A.fork A) σ.2;
      (P cs.1 σ.1-P cs.2 σ.1)^2) x

def actualRetainedExteriorNewMoment {steps : List (GaussianStep ι)}
    (pre : List (GaussianStep ι)) (E : ReplicaTree ι S (pre++steps)) (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (F : E.Assignment → S → ℝ) (x : ι → ℝ) : ℝ :=
  (E.fork (prependReplicaTree pre
    ((ReplicaTree.single (S := S) steps).fork (ReplicaTree.single (S := S) steps)))).expect w φ
    (fun σ =>
      let cs := prependAssignmentEquiv pre
        ((ReplicaTree.single (S := S) steps).fork (ReplicaTree.single (S := S) steps)) σ.2
      (F σ.1 (ReplicaTree.singleEquiv (S:=S) steps cs.1)-
        F σ.1 (ReplicaTree.singleEquiv (S:=S) steps cs.2))^2) x

theorem actualInheritedExteriorLayer_sq_le {steps : List (GaussianStep ι)}
    {w : S → ℝ} (hw : ∀ σ,0<w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (pre : List (GaussianStep ι)) (A : ReplicaTree ι S steps)
    (E : ReplicaTree ι S (pre++steps)) {a v z : ℝ}
    (ho : OrderedSteps a (pre++steps)) (hp : ∀ st∈pre,st.1≤v)
    (hav : a≤v) (hvz : v≤z) (hz : z≤2*v)
    (P : A.Assignment → E.Assignment → ℝ) (F : E.Assignment → S → ℝ)
    (x : ι → ℝ) :
    (actualInheritedExteriorLayer pre A E w φ a v z P F x)^2≤
      (3*(A.leaves:ℝ)*v)^2*actualRetainedExteriorOldMoment pre A E w φ P x*
        actualRetainedExteriorNewMoment pre E w φ F x := by
  have ht := prefixEndMass_ordered pre steps ho
  have hOld (e : E.Assignment) :
      (prependReplicaTree pre (A.fork A)).expect w φ
        (fun σ => let cs := prependAssignmentEquiv pre (A.fork A) σ;
          (P cs.1 e-P cs.2 e)^2) x =
      prefixTest pre (gaussianHierarchy w φ steps)
        (actualForkResamplingSquare A w φ (fun σ=>P σ e)) x := by
    exact actual_prepend_expect hw φ pre (A.fork A) ho
      (fun cs => (P cs.1 e-P cs.2 e)^2) x
  have hNew (e : E.Assignment) :
      (prependReplicaTree pre
        ((ReplicaTree.single (S:=S) steps).fork (ReplicaTree.single (S:=S) steps))).expect w φ
        (fun σ =>
          let cs := prependAssignmentEquiv pre
            ((ReplicaTree.single (S:=S) steps).fork (ReplicaTree.single (S:=S) steps)) σ
          (F e (ReplicaTree.singleEquiv (S:=S) steps cs.1)-
            F e (ReplicaTree.singleEquiv (S:=S) steps cs.2))^2) x =
      prefixTest pre (gaussianHierarchy w φ steps)
        (actualSingleResamplingSquare steps w φ (F e)) x := by
    exact actual_prepend_expect hw φ pre
      ((ReplicaTree.single (S:=S) steps).fork (ReplicaTree.single (S:=S) steps)) ho
      (fun cs => (F e (ReplicaTree.singleEquiv (S:=S) steps cs.1)-
        F e (ReplicaTree.singleEquiv (S:=S) steps cs.2))^2) x
  unfold actualInheritedExteriorLayer actualRetainedExteriorOldMoment actualRetainedExteriorNewMoment
  rw [ReplicaTree.expect_fork,ReplicaTree.expect_fork]
  simp_rw [hOld,hNew]
  apply actualExterior_expect_gram_sq_le hw φ E ho
    (fun e => prefixTest pre (gaussianHierarchy w φ steps)
      (actualForkResamplingSquare A w φ (fun σ=>P σ e)) x)
    (fun e => prefixTest pre (gaussianHierarchy w φ steps)
      (actualSingleResamplingSquare steps w φ (F e)) x)
    (fun e => prefixTest pre (gaussianHierarchy w φ steps)
      (fun y=>actualCutRow A w φ (prefixEndMass a pre) z (fun σ=>P σ e) (F e) y-
        actualCutRow A w φ (prefixEndMass a pre) v (fun σ=>P σ e) (F e) y) x)
    (3*(A.leaves:ℝ)*v)
  · intro e
    obtain ⟨L,hL⟩ := gaussianHierarchy_lipschitz hw φ steps ht
    exact prefixTest_nonneg hL
      (fun y=>(A.fork A).expect_nonneg hw φ ht (fun _=>sq_nonneg _) y) pre
      (fun st hst=>ho.mem_pos st (List.mem_append_left steps hst)) x
  · intro e
    obtain ⟨L,hL⟩ := gaussianHierarchy_lipschitz hw φ steps ht
    exact prefixTest_nonneg hL
      (fun y=>((ReplicaTree.single (S := S) steps).fork (ReplicaTree.single (S := S) steps)).expect_nonneg
        hw φ ht (fun _=>sq_nonneg _) y) pre
      (fun st hst=>ho.mem_pos st (List.mem_append_left steps hst)) x
  · intro e
    exact actual_prefix_cut_layer_resampling_sq_le hw φ A ht
      (prefixEndMass_le pre hav hp) hvz hz pre
      (fun st hst=>ho.mem_pos st (List.mem_append_left steps hst)) _ _ x

theorem actualRetainedExteriorOldMoment_smooth {steps : List (GaussianStep ι)}
    {w : S → ℝ} (hw : ∀ σ,0<w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (pre : List (GaussianStep ι)) (A : ReplicaTree ι S steps)
    (E : ReplicaTree ι S (pre++steps)) {a : ℝ} (ho : OrderedSteps a (pre++steps))
    (P : A.Assignment → E.Assignment → ℝ) (r : ℕ) :
    BddSmooth r (actualRetainedExteriorOldMoment pre A E w φ P) :=
  (E.fork (prependReplicaTree pre (A.fork A))).expect_smooth hw φ ho _ r

theorem actualRetainedExteriorNewMoment_smooth {steps : List (GaussianStep ι)}
    {w : S → ℝ} (hw : ∀ σ,0<w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (pre : List (GaussianStep ι)) (E : ReplicaTree ι S (pre++steps))
    {a : ℝ} (ho : OrderedSteps a (pre++steps))
    (F : E.Assignment → S → ℝ) (r : ℕ) :
    BddSmooth r (actualRetainedExteriorNewMoment pre E w φ F) :=
  (E.fork (prependReplicaTree pre
    ((ReplicaTree.single (S:=S) steps).fork (ReplicaTree.single (S:=S) steps)))).expect_smooth hw φ ho _ r

theorem actualInheritedExteriorLayer_smooth {steps : List (GaussianStep ι)}
    {w : S → ℝ} (hw : ∀ σ,0<w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (pre : List (GaussianStep ι)) (A : ReplicaTree ι S steps)
    (E : ReplicaTree ι S (pre++steps)) {a v z : ℝ}
    (ho : OrderedSteps a (pre++steps)) (hp : ∀ st∈pre,st.1≤v) (hvz : v≤z)
    (P : A.Assignment → E.Assignment → ℝ) (F : E.Assignment → S → ℝ) (r : ℕ) :
    BddSmooth r (actualInheritedExteriorLayer pre A E w φ a v z P F) := by
  have he : actualInheritedExteriorLayer pre A E w φ a v z P F =
      actualSharedExteriorLayer (prependReplicaTree pre A) E w φ a v z
        (fun σ e => P (prependAssignmentEquiv pre A σ) e) F :=
    funext fun x => (actualSharedExteriorLayer_eq_inherited hw φ pre A E ho hp hvz P F x).symm
  rw [he]
  exact actualSharedExteriorLayer_smooth hw φ _ E ho v z _ F r

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Hierarchy.ClockTree
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
variable {ι S : Type}

def nativeCutMarkedAttach : {as : List PositiveMass} → (T : ClockTree S as) →
    ℝ → ℝ → List (ClockTree.MarkedPlacement T)
  | _, .leaf, a, v => if v<1 then [MarkedPlacement.fresh .leaf a] else
      (.leaf : ClockTree S []).markedAttach a
  | _, .step b T, a, v => if v<b.val then [MarkedPlacement.fresh (T.step b) a] else
      MarkedPlacement.fresh (T.step b) (a-b.val) ::
        (nativeCutMarkedAttach T b.val v).map (MarkedPlacement.step b)
  | _, .fork T U, a, v => MarkedPlacement.fresh (T.fork U) (-a) ::
      ((nativeCutMarkedAttach T a v).map (MarkedPlacement.left U) ++
        (nativeCutMarkedAttach U a v).map (MarkedPlacement.right T))

theorem nativeCutMarkedAttach_realize {as : List PositiveMass}
    (T : ClockTree S as) (a v : ℝ) (q : ℕ → ι → ℝ≥0) :
    (nativeCutMarkedAttach T a v).map (fun p=>p.realize q) =
      (T.realize q).cutMarkedAttach a v := by
  induction T generalizing a q with
  | leaf =>
    by_cases hv : v < 1
    · simp only [nativeCutMarkedAttach,if_pos hv,List.map_cons,List.map_nil]
      rw [MarkedPlacement.realize_fresh]
      have hr : ((.leaf : ClockTree S []).realize q).cutMarkedAttach a v =
          [ReplicaTree.MarkedPlacement.fresh ((.leaf : ClockTree S []).realize q) a] := by
        change (.leaf : ReplicaTree ι S []).cutMarkedAttach a v = _
        simp only [ReplicaTree.cutMarkedAttach,if_pos hv]
        rfl
      exact hr.symm
    · simp only [nativeCutMarkedAttach,if_neg hv]
      have hr : ((.leaf : ClockTree S []).realize q).cutMarkedAttach a v =
          ((.leaf : ClockTree S []).realize q).markedAttach a := by
        change (.leaf : ReplicaTree ι S []).cutMarkedAttach a v = _
        simp only [ReplicaTree.cutMarkedAttach,if_neg hv]
        rfl
      rw [hr]
      exact markedAttach_realize (.leaf : ClockTree S []) a q
  | step b T ih =>
    by_cases hv : v < b.val
    · simp only [nativeCutMarkedAttach,if_pos hv,List.map_cons,List.map_nil]
      rw [MarkedPlacement.realize_fresh]
      have hr : ((T.step b).realize q).cutMarkedAttach a v =
          [ReplicaTree.MarkedPlacement.fresh ((T.step b).realize q) a] := by
        change ((T.realize (fun j=>q (j+1))).step (b.val,q 0)).cutMarkedAttach a v = _
        simp only [ReplicaTree.cutMarkedAttach,if_pos hv]
        rfl
      exact hr.symm
    · simp only [nativeCutMarkedAttach,if_neg hv,List.map_cons]
      rw [List.map_map,MarkedPlacement.realize_fresh]
      have hr : ((T.step b).realize q).cutMarkedAttach a v =
          ReplicaTree.MarkedPlacement.fresh ((T.step b).realize q) (a-b.val) ::
            ((T.realize (fun j=>q (j+1))).cutMarkedAttach b.val v).map
              (ReplicaTree.MarkedPlacement.step (b.val,q 0)) := by
        change ((T.realize (fun j=>q (j+1))).step (b.val,q 0)).cutMarkedAttach a v = _
        simp only [ReplicaTree.cutMarkedAttach,if_neg hv]
        rfl
      rw [hr]
      congr 1
      rw [←ih b.val (fun j=>q (j+1))]
      dsimp only [ClockTree.realize,clockSteps]
      simp only [List.map_map]
      apply List.map_congr_left
      intro p hp
      exact MarkedPlacement.realize_step b p q
  | fork T U ihT ihU =>
    change (MarkedPlacement.fresh (T.fork U) (-a)).realize q ::
      (((nativeCutMarkedAttach T a v).map (MarkedPlacement.left U) ++
        (nativeCutMarkedAttach U a v).map (MarkedPlacement.right T)).map
          (fun p=>p.realize q)) = _
    rw [List.map_append,List.map_map,List.map_map,MarkedPlacement.realize_fresh]
    change _ :: _ = _ :: _
    congr 1
    rw [←ihT a q,←ihU a q,List.map_map,List.map_map]
    congr 1
    · apply List.map_congr_left
      intro p hp
      exact MarkedPlacement.realize_left U p q
    · apply List.map_congr_left
      intro p hp
      exact MarkedPlacement.realize_right T p q

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Cavity
open Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S] [DecidableEq S]

def nativeJointAttachmentRow {as : List PositiveMass} {T : ClockTree S as}
    (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ) (q : ℕ → ι → ℝ≥0)
    (ps : List (ClockTree.MarkedPlacement T)) (H : T.Assignment → S → ℝ)
    (x : ι → ℝ) : ℝ :=
  (ps.map (fun p=>p.coeff*p.tree.expect w φ q
    (fun σ=>H (p.restrict σ) (p.spin σ)) x)).sum

theorem nativeJointAttachmentRow_eq_realized {as : List PositiveMass}
    {T : ClockTree S as} (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (q : ℕ → ι → ℝ≥0) (ps : List (ClockTree.MarkedPlacement T))
    (H : T.Assignment → S → ℝ) (x : ι → ℝ) :
    nativeJointAttachmentRow w φ q ps H x =
      jointAttachmentRow w φ (ps.map (fun p=>p.realize q))
        (fun σ s=>H ((T.assignmentEquiv q).symm σ) s) x := by
  unfold nativeJointAttachmentRow jointAttachmentRow
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  rw [p.tree.expect_realize]
  simp only [Function.comp_apply,ClockTree.MarkedPlacement.realize,Equiv.symm_apply_apply]

def nativeJointActualCutRow {as : List PositiveMass} (T : ClockTree S as)
    (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ) (a v : ℝ)
    (q : ℕ → ι → ℝ≥0) (H : T.Assignment → S → ℝ) (x : ι → ℝ) : ℝ :=
  nativeJointAttachmentRow w φ q (T.nativeCutMarkedAttach a v) H x

theorem nativeJointActualCutRow_eq_realized {as : List PositiveMass}
    (T : ClockTree S as) (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ) (a v : ℝ)
    (q : ℕ → ι → ℝ≥0) (H : T.Assignment → S → ℝ) (x : ι → ℝ) :
    nativeJointActualCutRow T w φ a v q H x =
      jointActualCutRow (T.realize q) w φ a v
        (fun σ s=>H ((T.assignmentEquiv q).symm σ) s) x := by
  unfold nativeJointActualCutRow jointActualCutRow
  rw [nativeJointAttachmentRow_eq_realized,T.nativeCutMarkedAttach_realize a v q]

def nativeJointActualLeftCutLayer {as : List PositiveMass} (T E : ClockTree S as)
    (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ) (a v z : ℝ)
    (q : ℕ → ι → ℝ≥0) (H : (T.fork E).Assignment → S → ℝ) (x : ι → ℝ) : ℝ :=
  nativeJointAttachmentRow w φ q
    ((T.nativeCutMarkedAttach a z).map (ClockTree.MarkedPlacement.left E)) H x-
  nativeJointAttachmentRow w φ q
    ((T.nativeCutMarkedAttach a v).map (ClockTree.MarkedPlacement.left E)) H x

theorem nativeJointActualLeftCutLayer_eq_realized {as : List PositiveMass}
    (T E : ClockTree S as) (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ) (a v z : ℝ)
    (q : ℕ → ι → ℝ≥0) (H : (T.fork E).Assignment → S → ℝ) (x : ι → ℝ) :
    nativeJointActualLeftCutLayer T E w φ a v z q H x =
      jointActualLeftCutLayer (T.realize q) (E.realize q) w φ a v z
        (fun σ s=>H (((T.fork E).assignmentEquiv q).symm σ) s) x := by
  have he (u : ℝ) : ((T.nativeCutMarkedAttach a u).map
      (ClockTree.MarkedPlacement.left E)).map (fun p=>p.realize q) =
      ((T.realize q).cutMarkedAttach a u).map
        (ReplicaTree.MarkedPlacement.left (E.realize q)) := by
    rw [←T.nativeCutMarkedAttach_realize a u q,List.map_map,List.map_map]
    apply List.map_congr_left
    intro p hp
    exact ClockTree.MarkedPlacement.realize_left E p q
  unfold nativeJointActualLeftCutLayer jointActualLeftCutLayer
  rw [nativeJointAttachmentRow_eq_realized,nativeJointAttachmentRow_eq_realized,he,he]
  rfl

theorem nativeJointActualLeftCutLayer_product_eq_shared {as : List PositiveMass}
    (T E : ClockTree S as) (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ) (a v z : ℝ)
    (q : ℕ → ι → ℝ≥0) (P : T.Assignment → E.Assignment → ℝ)
    (F : E.Assignment → S → ℝ) (x : ι → ℝ) :
    nativeJointActualLeftCutLayer T E w φ a v z q
      (fun σ s=>P σ.1 σ.2*F σ.2 s) x =
      actualSharedExteriorLayer (T.realize q) (E.realize q) w φ a v z
        (fun σ e=>P ((T.assignmentEquiv q).symm σ) ((E.assignmentEquiv q).symm e))
        (fun e s=>F ((E.assignmentEquiv q).symm e) s) x := by
  rw [nativeJointActualLeftCutLayer_eq_realized]
  change jointActualLeftCutLayer (T.realize q) (E.realize q) w φ a v z
    (fun σ s=>P ((T.assignmentEquiv q).symm σ.1) ((E.assignmentEquiv q).symm σ.2)*
      F ((E.assignmentEquiv q).symm σ.2) s) x = _
  exact jointActualLeftCutLayer_eq_shared (T.realize q) (E.realize q) w φ a v z
    (fun σ e=>P ((T.assignmentEquiv q).symm σ) ((E.assignmentEquiv q).symm e))
    (fun e s=>F ((E.assignmentEquiv q).symm e) s) x

theorem nativeCutMarkedAttach_preserves {as : List PositiveMass}
    {w : S → ℝ} (hw : ∀ σ,0<w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (T : ClockTree S as) {a : ℝ} (ho : MassOrdered a as) (v : ℝ)
    (p : ClockTree.MarkedPlacement T) (hp : p∈T.nativeCutMarkedAttach a v)
    (q : ℕ → ι → ℝ≥0) (P : T.Assignment → ℝ) (x : ι → ℝ) :
    p.tree.expect w φ q (fun σ=>P (p.restrict σ)) x=T.expect w φ q P x := by
  have hm : p.realize q∈(T.realize q).cutMarkedAttach a v := by
    rw [←T.nativeCutMarkedAttach_realize a v q]
    exact List.mem_map.mpr ⟨p,hp,rfl⟩
  have h := (T.realize q).cutMarkedAttach_preserves hw φ (clockSteps_ordered ho q)
    v (p.realize q) hm (fun σ=>P ((T.assignmentEquiv q).symm σ)) x
  rw [p.tree.expect_realize,T.expect_realize]
  simpa only [ClockTree.MarkedPlacement.realize,Equiv.symm_apply_apply] using h

end OAI.SKFluctuations.Cavity
