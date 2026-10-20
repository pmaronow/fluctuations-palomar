module

public import ComparisonSignedCavitySecondLowIndexedLayerIntegral
public import ComparisonSignedCavitySecondLowSharedExteriorReplacement

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
set_option maxHeartbeats 60000000
set_option backward.isDefEq.respectTransparency false
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

private theorem virtual_layer_root_incoming_eq {as : List PositiveMass}
    (T : ClockTree S as) {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a b : ℝ} (ha : MassOrdered a as) (hb : MassOrdered b as) (v z : ℝ)
    (q : ℕ→ι→ℝ≥0) (P : T.Assignment→ℝ) (F : S→ℝ) (x : ι→ℝ) :
    nativeScalarIndexedCutLayerFold w φ T 0 a v z q P F x=
      nativeScalarIndexedCutLayerFold w φ T 0 b v z q P F x := by
  classical
  rw [native_scalar_indexed_cut_layer_fold_eq_realized,
    native_scalar_indexed_cut_layer_fold_eq_realized]
  simp only [actualIndexedCutLayerFold]
  have Hz := actual_cut_row_incoming_difference hw φ (T.realize q)
    (clockSteps_ordered ha q) (clockSteps_ordered hb q) z
    (fun σ=>P ((T.assignmentEquiv q).symm σ)) F x
  have Hv := actual_cut_row_incoming_difference hw φ (T.realize q)
    (clockSteps_ordered ha q) (clockSteps_ordered hb q) v
    (fun σ=>P ((T.assignmentEquiv q).symm σ)) F x
  linarith only [Hz,Hv]

theorem native_scalar_indexed_cut_layer_fold_incoming_eq {as : List PositiveMass}
    (T : ClockTree S as) {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (cut : ℕ) {a b : ℝ} (ha : MassOrdered a as) (hb : MassOrdered b as) (v z : ℝ)
    (q : ℕ→ι→ℝ≥0) (P : T.Assignment→ℝ) (F : S→ℝ) (x : ι→ℝ) :
    nativeScalarIndexedCutLayerFold w φ T cut a v z q P F x=
      nativeScalarIndexedCutLayerFold w φ T cut b v z q P F x := by
  induction T generalizing cut a b q with
  | leaf=>
    cases cut <;> exact virtual_layer_root_incoming_eq .leaf hw φ ha hb v z q P F x
  | step d T ih=>
    cases cut with
    | zero=>exact virtual_layer_root_incoming_eq (T.step d) hw φ ha hb v z q P F x
    | succ cut=>rfl
  | fork T E ihT ihE=>
    cases cut with
    | zero=>exact virtual_layer_root_incoming_eq (T.fork E) hw φ ha hb v z q P F x
    | succ cut=>
      change T.Assignment×E.Assignment→ℝ at P
      simp only [nativeScalarIndexedCutLayerFold,
        ihT (cut+1) ha hb q,ihE (cut+1) ha hb q]

private theorem virtual_layer_root_smooth {as : List PositiveMass}
    (T : ClockTree S as) {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a as) (v z : ℝ) (q : ℕ→ι→ℝ≥0)
    (P : T.Assignment→ℝ) (F : S→ℝ) :
    BddSmooth 0 (nativeScalarIndexedCutLayerFold w φ T 0 a v z q P F) := by
  classical
  have H : nativeScalarIndexedCutLayerFold w φ T 0 a v z q P F=
      fun x=>actualCutRow (T.realize q) w φ a z (fun σ=>P ((T.assignmentEquiv q).symm σ)) F x-
        actualCutRow (T.realize q) w φ a v (fun σ=>P ((T.assignmentEquiv q).symm σ)) F x:=by
    funext x
    rw [native_scalar_indexed_cut_layer_fold_eq_realized]
    simp only [actualIndexedCutLayerFold]
  rw [H]
  exact (actualCutRow_smooth hw φ (T.realize q) (clockSteps_ordered ho q) z _ F 0).sub
    (actualCutRow_smooth hw φ (T.realize q) (clockSteps_ordered ho q) v _ F 0)

theorem nativeScalarIndexedCutLayerFold_virtual_smooth0 {as : List PositiveMass}
    (T : ClockTree S as) {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (cut : ℕ) {a : ℝ} (ho : MassOrdered a as) (v z : ℝ) (q : ℕ→ι→ℝ≥0)
    (P : T.Assignment→ℝ) (F : S→ℝ) :
    BddSmooth 0 (nativeScalarIndexedCutLayerFold w φ T cut a v z q P F) := by
  induction T generalizing cut a q with
  | leaf=>
    cases cut <;> exact virtual_layer_root_smooth .leaf hw φ ho v z q P F
  | @step b as T ih=>
    cases cut with
    | zero=>exact virtual_layer_root_smooth (T.step b) hw φ ho v z q P F
    | succ cut=>
      change T.Assignment→ℝ at P
      obtain ⟨L,hL⟩:=gaussianHierarchy_lipschitz hw φ _ (clockSteps_ordered ho.2.2 (fun j=>q (j+1)))
      have H:=prefixTest_smooth0 hL (ih cut ho.2.2 (fun j=>q (j+1)) P)
        [(b.val,q 0)] (by intro st hst; have he : st = (b.val,q 0) := List.mem_singleton.mp hst; subst st; exact b.property)
      simpa only [prefixTest,prefixContinuation,List.append_nil,nativeScalarIndexedCutLayerFold] using H
  | fork T E ihT ihE=>
    cases cut with
    | zero=>exact virtual_layer_root_smooth (T.fork E) hw φ ho v z q P F
    | succ cut=>
      change T.Assignment×E.Assignment→ℝ at P
      change BddSmooth 0 (fun x=>E.expect w φ q (fun e=>
        nativeScalarIndexedCutLayerFold w φ T (cut+1) a v z q (fun σ=>P (σ,e)) F x) x+
        T.expect w φ q (fun σ=>nativeScalarIndexedCutLayerFold w φ E (cut+1) a v z q (fun e=>P (σ,e)) F x) x)
      apply BddSmooth.add
      · unfold ClockTree.expect
        apply BddSmooth.sum Finset.univ
        intro e _
        exact (E.weight_smooth hw φ ho q e 0).mul (ihT (cut+1) ho q (fun σ=>P (σ,e)))
      · unfold ClockTree.expect
        apply BddSmooth.sum Finset.univ
        intro σ _
        exact (T.weight_smooth hw φ ho q σ 0).mul (ihE (cut+1) ho q (fun e=>P (σ,e)))
private theorem virtual_indexed_expect_gram {as : List PositiveMass} (E : ClockTree S as)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ→ι→ℝ≥0)
    (A B C : E.Assignment→ℝ) (k : ℝ) (hA : ∀e,0 ≤ A e) (hB : ∀e,0 ≤ B e)
    (hC : ∀e,(C e)^2 ≤ k^2*A e*B e) (x : ι→ℝ) :
    (E.expect w φ q C x)^2 ≤ k^2*E.expect w φ q A x*E.expect w φ q B x := by
  classical
  simp_rw [E.expect_realize w φ q]
  exact actualExterior_expect_gram_sq_le hw φ (E.realize q) (clockSteps_ordered ho q)
    (fun e=>A ((E.assignmentEquiv q).symm e)) (fun e=>B ((E.assignmentEquiv q).symm e))
    (fun e=>C ((E.assignmentEquiv q).symm e)) k
    (fun e=>hA _) (fun e=>hB _) (fun e=>hC _) x

private theorem virtual_indexed_expect_nonneg {as : List PositiveMass} (E : ClockTree S as)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ→ι→ℝ≥0)
    (P : E.Assignment→ℝ) (hP : ∀e,0 ≤ P e) (x : ι→ℝ) :
    0 ≤ E.expect w φ q P x := by
  rw [E.expect_realize]
  exact (E.realize q).expect_nonneg hw φ (clockSteps_ordered ho q) (fun _=>hP _) x

theorem native_scalar_indexed_virtual_cut_layer_clone_gram_sq_le {as : List PositiveMass}
    (T : ClockTree S as) {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (cut : ℕ) {a v z : ℝ} (ho : MassOrdered a as) (hv : 0 ≤ v) (hcut : cut ≤ as.length)
    (q : ℕ→ι→ℝ≥0) (hvz : v ≤ z) (hz : z ≤ 2*v)
    (P : T.Assignment→ℝ) (F : S→ℝ) (x : ι→ℝ) :
    (nativeScalarIndexedCutLayerFold w φ T cut a v z q P F x)^2 ≤
      (3*(T.leaves:ℝ)*v)^2*nativeRetainedOldCloneSquareSum T w φ cut q P x*
        nativeRetainedNewCloneSquareSum T w φ cut q F x := by
  classical
  have hbase {as : List PositiveMass} (T : ClockTree S as) {a : ℝ} (ho : MassOrdered a as)
      (q : ℕ→ι→ℝ≥0) (P : T.Assignment→ℝ) (x : ι→ℝ) :
      (nativeScalarIndexedCutLayerFold w φ T 0 a v z q P F x)^2 ≤
        (3*(T.leaves:ℝ)*v)^2*nativeRetainedOldCloneSquareSum T w φ 0 q P x*
          nativeRetainedNewCloneSquareSum T w φ 0 q F x := by
    have ha0 : 0 ≤ a := (clockSteps_ordered ho q).nonneg
    have ho0 := ho.lower (by norm_num) ha0
    rw [native_scalar_indexed_cut_layer_fold_incoming_eq T hw φ 0 ho ho0 v z q P F x]
    exact native_scalar_indexed_cut_layer_clone_gram_sq_le T hw φ 0 ho0 hv (Nat.zero_le _) q
      (by simp only [List.take_zero,List.not_mem_nil,forall_false,implies_true]) hvz hz P F x
  induction T generalizing cut a q x with
  | leaf=>
    have hc:cut=0:=by simpa [List.length_nil] using hcut
    subst cut
    exact hbase .leaf ho q P x
  | @step b as T ih=>
    cases cut with
    | zero=>exact hbase (T.step b) ho q P x
    | succ cut=>
      change T.Assignment→ℝ at P
      have hcutT:cut ≤ as.length:=by simpa only [List.length_cons,Nat.succ_le_succ_iff] using hcut
      obtain ⟨L,hL⟩:=gaussianHierarchy_lipschitz hw φ _ (clockSteps_ordered ho.2.2 (fun j=>q (j+1)))
      have Hlift:=actual_prefix_gram_sq_le hL
        (nativeRetainedOldCloneSquareSum_smooth0 T hw φ ho.2.2 cut (fun j=>q (j+1)) P)
        (nativeRetainedNewCloneSquareSum_smooth0 T hw φ ho.2.2 cut (fun j=>q (j+1)) F)
        (nativeScalarIndexedCutLayerFold_virtual_smooth0 T hw φ cut ho.2.2 v z (fun j=>q (j+1)) P F)
        (fun y=>nativeRetainedOldCloneSquareSum_nonneg T hw φ ho.2.2 cut (fun j=>q (j+1)) P y)
        (fun y=>nativeRetainedNewCloneSquareSum_nonneg T hw φ ho.2.2 cut (fun j=>q (j+1)) F y)
        (fun y=>ih cut ho.2.2 hcutT (fun j=>q (j+1)) P y)
        [(b.val,q 0)] (by intro st hst; have he : st = (b.val, q 0) := List.mem_singleton.mp hst; subst st; exact b.property) x
      rw [native_retained_old_clone_sum_step T b hw φ ho cut q P x,
        native_retained_new_clone_sum_step T b hw φ ho cut q F x]
      change (shiftedMean _ b.val (gaussianHierarchy w φ (clockSteps _ _))
        (nativeScalarIndexedCutLayerFold w φ T cut b.val v z (fun j=>q (j+1)) P F) x)^2 ≤ _
      simpa only [prefixTest,prefixContinuation,List.append_nil,ClockTree.leaves] using Hlift
  | fork T E ihT ihE=>
    cases cut with
    | zero=>exact hbase (T.fork E) ho q P x
    | succ cut=>
      change T.Assignment×E.Assignment→ℝ at P
      let PL:=E.expect w φ q (fun e=>nativeRetainedOldCloneSquareSum T w φ (cut+1) q (fun σ=>P (σ,e)) x) x
      let PR:=T.expect w φ q (fun σ=>nativeRetainedOldCloneSquareSum E w φ (cut+1) q (fun e=>P (σ,e)) x) x
      let FL:=E.expect w φ q (fun _=>nativeRetainedNewCloneSquareSum T w φ (cut+1) q F x) x
      let FR:=T.expect w φ q (fun _=>nativeRetainedNewCloneSquareSum E w φ (cut+1) q F x) x
      let LL:=E.expect w φ q (fun e=>nativeScalarIndexedCutLayerFold w φ T (cut+1) a v z q (fun σ=>P (σ,e)) F x) x
      let LR:=T.expect w φ q (fun σ=>nativeScalarIndexedCutLayerFold w φ E (cut+1) a v z q (fun e=>P (σ,e)) F x) x
      let kAll:=3*((T.leaves+E.leaves:ℕ):ℝ)*v
      have hv0:0 ≤ v:=hv
      have hPL:0 ≤ PL:=virtual_indexed_expect_nonneg E hw φ ho q _
        (fun e=>nativeRetainedOldCloneSquareSum_nonneg T hw φ ho (cut+1) q (fun σ=>P (σ,e)) x) x
      have hPR:0 ≤ PR:=virtual_indexed_expect_nonneg T hw φ ho q _
        (fun σ=>nativeRetainedOldCloneSquareSum_nonneg E hw φ ho (cut+1) q (fun e=>P (σ,e)) x) x
      have hFL:0 ≤ FL:=virtual_indexed_expect_nonneg E hw φ ho q _
        (fun _=>nativeRetainedNewCloneSquareSum_nonneg T hw φ ho (cut+1) q F x) x
      have hFR:0 ≤ FR:=virtual_indexed_expect_nonneg T hw φ ho q _
        (fun _=>nativeRetainedNewCloneSquareSum_nonneg E hw φ ho (cut+1) q F x) x
      have HL:LL^2 ≤ (3*(T.leaves:ℝ)*v)^2*PL*FL:=virtual_indexed_expect_gram E hw φ ho q _ _ _ _
        (fun e=>nativeRetainedOldCloneSquareSum_nonneg T hw φ ho (cut+1) q (fun σ=>P (σ,e)) x)
        (fun _=>nativeRetainedNewCloneSquareSum_nonneg T hw φ ho (cut+1) q F x)
        (fun e=>ihT (cut+1) ho hcut q (fun σ=>P (σ,e)) x) x
      have HR:LR^2 ≤ (3*(E.leaves:ℝ)*v)^2*PR*FR:=virtual_indexed_expect_gram T hw φ ho q _ _ _ _
        (fun σ=>nativeRetainedOldCloneSquareSum_nonneg E hw φ ho (cut+1) q (fun e=>P (σ,e)) x)
        (fun _=>nativeRetainedNewCloneSquareSum_nonneg E hw φ ho (cut+1) q F x)
        (fun σ=>ihE (cut+1) ho hcut q (fun e=>P (σ,e)) x) x
      have HLL:=native_numeric_gram_coefficient_mono PL FL (3*(T.leaves:ℝ)*v) kAll LL hPL hFL (by positivity)
        (by dsimp [kAll];push_cast; nlinarith) HL
      have HLR:=native_numeric_gram_coefficient_mono PR FR (3*(E.leaves:ℝ)*v) kAll LR hPR hFR (by positivity)
        (by dsimp [kAll];push_cast; nlinarith) HR
      have Hsum:=native_numeric_two_gram_add PL PR FL FR kAll LL LR hPL hPR hFL hFR HLL HLR
      rw [native_retained_old_clone_sum_fork,native_retained_new_clone_sum_fork]
      exact Hsum

end OAI.SKFluctuations.Cavity
