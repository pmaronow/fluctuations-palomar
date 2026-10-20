module

public import ComparisonSignedCavitySecondLowIndexedVirtualLayerIntegral
public import ComparisonSignedCavitySecondLowNativeCSourceFold
public import ComparisonSignedCavitySecondLowUnobservedEntry

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
set_option maxHeartbeats 60000000
set_option backward.isDefEq.respectTransparency false
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

private theorem prefix_telescope_root {as : List PositiveMass}
    (T : ClockTree S as) (c : T.Slot) {w : S→ℝ} (hw : ∀σ,0 < w σ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) {a : ℝ} (ho : MassOrdered a as)
    (q : ℕ→ι→ℝ≥0) (P : T.Assignment→ℝ) (f z : S) (Q : S→S→S→ℝ) (x : ι→ℝ) :
    nativeSecondLowCCouplingFold w φ T c 0 a q P (.fixed f) (.fixed z) Q x=
      nativeScalarIndexedCutLayerFold w φ T 0 a (a/2) 1 q P (fun s=>Q f s z) x-
        (a/2)*nativeRetainedCloneCutMean w φ T c 0 q
          (fun σ τ=>(P σ-P τ)*(Q f (T.atSlot σ c) z-Q f (T.atSlot τ c) z)) x := by
  classical
  have ha0 : 0 ≤ a := (clockSteps_ordered ho q).nonneg
  have ho0 := ho.lower (by norm_num) ha0
  rw [native_scalar_indexed_cut_layer_fold_incoming_eq T hw φ 0 ho ho0]
  rw [native_scalar_indexed_cut_layer_fold_eq_realized]
  simp only [actualIndexedCutLayerFold]
  rw [native_retained_clone_root_eq_fork,(T.fork T).expect_realize]
  have Hat : ∀σ,(T.realize q).atSlot σ (T.slotEquiv q c)=
      T.atSlot ((T.assignmentEquiv q).symm σ) c := by
    intro σ
    have H:=T.realize_atSlot q ((T.assignmentEquiv q).symm σ) c
    simpa only [Equiv.apply_symm_apply] using H
  simp only [nativeSecondLowCCouplingFold,nativeSecondLowCClusterRoot,
    nativeSecondLowCClusterCouplingRoot,Hat]
  rfl

theorem native_second_low_complete_c_fold_eq_indexed_layer_sub_retained_covariance
    {as : List PositiveMass} (T : ClockTree S as) (c : T.Slot)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (U : ℕ) {a : ℝ} (ho : MassOrdered a as)
    (hblock : ∀d:T.Slot,U ≤ T.splitIndex c d)
    (q : ℕ→ι→ℝ≥0) (P : T.Assignment→ℝ) (f z : S) (Q : S→S→S→ℝ) (x : ι→ℝ) :
    nativeSecondLowCCouplingFold w φ T c U a q P (.fixed f) (.fixed z) Q x=
      nativeScalarIndexedCutLayerFold w φ T U a (partitionPoint a as U/2) 1 q P (fun s=>Q f s z) x-
        (partitionPoint a as U/2)*nativeRetainedCloneCutMean w φ T c U q
          (fun σ τ=>(P σ-P τ)*(Q f (T.atSlot σ c) z-Q f (T.atSlot τ c) z)) x := by
  induction T generalizing U a q x with
  | leaf=>
    have hU : U=0 := by have H:=hblock c; simp only [ClockTree.splitIndex] at H;omega
    subst U
    simpa only [partitionPoint,partitionValues_zero,id_eq] using
      prefix_telescope_root .leaf c hw φ ho q P f z Q x
  | @step b as T ih=>
    cases U with
    | zero=>
      simpa only [partitionPoint,partitionValues_zero,id_eq] using
        prefix_telescope_root (T.step b) c hw φ ho q P f z Q x
    | succ U=>
      change T.Assignment→ℝ at P
      have hb : ∀d:T.Slot,U ≤ T.splitIndex c d := by
        intro d
        have H:=hblock d
        simp only [ClockTree.splitIndex] at H
        omega
      let q1:=fun j=>q (j+1)
      let v:=partitionPoint b.val as U/2
      have HC:nativeSecondLowCCouplingFold w φ T c U b.val q1 P (.fixed f) (.fixed z) Q=
          fun y=>nativeScalarIndexedCutLayerFold w φ T U b.val v 1 q1 P (fun s=>Q f s z) y-
            v*nativeRetainedCloneCutMean w φ T c U q1
              (fun σ τ=>(P σ-P τ)*(Q f (T.atSlot σ c) z-Q f (T.atSlot τ c) z)) y :=
        funext fun y=>ih c U ho.2.2 hb q1 P y
      have hL:=nativeScalarIndexedCutLayerFold_virtual_smooth0 T hw φ U ho.2.2 v 1 q1 P (fun s=>Q f s z)
      have hC:=nativeRetainedCloneCutMean_smooth0 T hw φ ho.2.2 c U q1
        (fun σ τ=>(P σ-P τ)*(Q f (T.atSlot σ c) z-Q f (T.atSlot τ c) z))
      have hi:=gaussianHierarchy_integrable hw φ (clockSteps as q1) (clockSteps_ordered ho.2.2 q1) b.val (q 0) x
      change shiftedMean _ b.val (gaussianHierarchy w φ (clockSteps as q1))
          (nativeSecondLowCCouplingFold w φ T c U b.val q1 P (.fixed f) (.fixed z) Q) x=_
      rw [HC,shiftedMean_sub hL (hC.const_mul v) hi,shiftedMean_const_mul]
      rfl
  | fork T E ihT ihE=>
    cases U with
    | zero=>
      simpa only [partitionPoint,partitionValues_zero,id_eq] using
        prefix_telescope_root (T.fork E) c hw φ ho q P f z Q x
    | succ U=>
      cases c with
      | inl c=>
        have H:=hblock (.inr (nativeSecondLowEntryWitness E))
        simp only [ClockTree.splitIndex,Sum.elim_inl,Sum.elim_inr] at H
        omega
      | inr c=>
        have H:=hblock (.inl (nativeSecondLowEntryWitness T))
        simp only [ClockTree.splitIndex,Sum.elim_inl,Sum.elim_inr] at H
        omega

theorem native_scalar_indexed_cut_layer_fold_add {as : List PositiveMass}
    (T : ClockTree S as) {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (cut : ℕ) {a : ℝ} (ho : MassOrdered a as) (u v z : ℝ) (q : ℕ→ι→ℝ≥0)
    (P : T.Assignment→ℝ) (F : S→ℝ) (x : ι→ℝ) :
    nativeScalarIndexedCutLayerFold w φ T cut a u v q P F x+
      nativeScalarIndexedCutLayerFold w φ T cut a v z q P F x=
        nativeScalarIndexedCutLayerFold w φ T cut a u z q P F x := by
  classical
  have hroot {as : List PositiveMass} (T : ClockTree S as) (a : ℝ)
      (q : ℕ→ι→ℝ≥0) (P : T.Assignment→ℝ) (x : ι→ℝ) :
      nativeScalarIndexedCutLayerFold w φ T 0 a u v q P F x+
        nativeScalarIndexedCutLayerFold w φ T 0 a v z q P F x=
          nativeScalarIndexedCutLayerFold w φ T 0 a u z q P F x := by
    simp only [nativeScalarIndexedCutLayerFold]
    ring
  induction T generalizing cut a q x with
  | leaf=>cases cut <;> exact hroot .leaf a q P x
  | @step b as T ih=>
    cases cut with
    | zero=>exact hroot (T.step b) a q P x
    | succ cut=>
      change T.Assignment→ℝ at P
      let q1:=fun j=>q (j+1)
      have H:(fun y=>nativeScalarIndexedCutLayerFold w φ T cut b.val u v q1 P F y+
          nativeScalarIndexedCutLayerFold w φ T cut b.val v z q1 P F y)=
        nativeScalarIndexedCutLayerFold w φ T cut b.val u z q1 P F:=
          funext fun y=>ih cut ho.2.2 q1 P y
      have hi:=gaussianHierarchy_integrable hw φ (clockSteps as q1) (clockSteps_ordered ho.2.2 q1) b.val (q 0) x
      change shiftedMean _ b.val (gaussianHierarchy w φ (clockSteps as q1))
        (nativeScalarIndexedCutLayerFold w φ T cut b.val u v q1 P F) x+
          shiftedMean _ b.val (gaussianHierarchy w φ (clockSteps as q1))
            (nativeScalarIndexedCutLayerFold w φ T cut b.val v z q1 P F) x=_
      rw [←shiftedMean_add
        (nativeScalarIndexedCutLayerFold_virtual_smooth0 T hw φ cut ho.2.2 u v q1 P F)
        (nativeScalarIndexedCutLayerFold_virtual_smooth0 T hw φ cut ho.2.2 v z q1 P F) hi,H]
      rfl
  | fork T E ihT ihE=>
    cases cut with
    | zero=>exact hroot (T.fork E) a q P x
    | succ cut=>
      change T.Assignment×E.Assignment→ℝ at P
      simp only [nativeScalarIndexedCutLayerFold]
      simp_rw [←ihT (cut+1) ho q,←ihE (cut+1) ho q]
      unfold ClockTree.expect
      simp only [mul_add,Finset.sum_add_distrib]
      ring

theorem native_scalar_indexed_cut_layers_telescope {as : List PositiveMass}
    (T : ClockTree S as) {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (cut : ℕ) {a : ℝ} (ho : MassOrdered a as) (cuts : ℕ→ℝ) (count : ℕ) (q : ℕ→ι→ℝ≥0)
    (P : T.Assignment→ℝ) (F : S→ℝ) (x : ι→ℝ) :
    (∑j∈Finset.range count,nativeScalarIndexedCutLayerFold w φ T cut a (cuts j) (cuts (j+1)) q P F x)=
      nativeScalarIndexedCutLayerFold w φ T cut a (cuts 0) (cuts count) q P F x := by
  induction count with
  | zero=>
    simp only [Finset.range_zero,Finset.sum_empty]
    have H:=native_scalar_indexed_cut_layer_fold_add T hw φ cut ho (cuts 0) (cuts 0) (cuts 0) q P F x
    linarith only [H]
  | succ count ih=>
    rw [Finset.sum_range_succ,ih,native_scalar_indexed_cut_layer_fold_add T hw φ cut ho]

theorem native_second_low_complete_c_fold_eq_grouped_indexed_layers_sub_retained_covariance
    {as : List PositiveMass} (T : ClockTree S as) (c : T.Slot)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (U : ℕ) {a : ℝ} (ho : MassOrdered a as)
    (hblock : ∀d:T.Slot,U ≤ T.splitIndex c d)
    (q : ℕ→ι→ℝ≥0) (P : T.Assignment→ℝ) (f z : S) (Q : S→S→S→ℝ)
    (cuts : ℕ→ℝ) (count : ℕ) (index : ℕ→ℕ)
    (hfirst : cuts 0=partitionPoint a as U/2) (hlast : cuts count=1) (hindex0 : index 0=U)
    (hindex : ∀j < count,index j ≤ as.length)
    (hprefix : ∀j,1 ≤ j → j < count → ∀st∈(clockSteps as q).take (index j),st.1 ≤ cuts j)
    (hsource : ∀j,1 ≤ j → j < count → ∀st∈(clockSteps as q).take U,st.1 ≤ cuts j)
    (hmono : ∀j < count,cuts j ≤ cuts (j+1)) (x : ι→ℝ) :
    nativeSecondLowCCouplingFold w φ T c U a q P (.fixed f) (.fixed z) Q x=
      (∑j∈Finset.range count,nativeScalarIndexedCutLayerFold w φ T (index j) 0 (cuts j) (cuts (j+1))
        q P (fun s=>Q f s z) x)-
        (partitionPoint a as U/2)*nativeRetainedCloneCutMean w φ T c U q
          (fun σ τ=>(P σ-P τ)*(Q f (T.atSlot σ c) z-Q f (T.atSlot τ c) z)) x := by
  have hU : U ≤ as.length := by simpa only [T.splitIndex_self] using hblock c
  have ha0 : 0 ≤ a := (clockSteps_ordered ho q).nonneg
  have ho0 := ho.lower (by norm_num) ha0
  have HR : (∑j∈Finset.range count,nativeScalarIndexedCutLayerFold w φ T (index j) 0 (cuts j) (cuts (j+1))
      q P (fun s=>Q f s z) x)=
      ∑j∈Finset.range count,nativeScalarIndexedCutLayerFold w φ T U 0 (cuts j) (cuts (j+1))
        q P (fun s=>Q f s z) x := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjc:=Finset.mem_range.mp hj
    cases j with
    | zero=>rw [hindex0]
    | succ j=>
      rw [native_scalar_indexed_cut_layer_fold_eq_original T hw φ (index (j+1)) ho0 (hindex _ hjc) q
          (hprefix _ (by omega) hjc) (hmono _ hjc),
        native_scalar_indexed_cut_layer_fold_eq_original T hw φ U ho0 hU q
          (hsource _ (by omega) hjc) (hmono _ hjc)]
  rw [HR,native_scalar_indexed_cut_layers_telescope T hw φ U ho0,hfirst,hlast]
  rw [native_second_low_complete_c_fold_eq_indexed_layer_sub_retained_covariance T c hw φ U ho hblock]
  rw [native_scalar_indexed_cut_layer_fold_incoming_eq T hw φ U ho ho0]

end OAI.SKFluctuations.Cavity
