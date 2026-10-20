module

public import ComparisonSignedCavityActualGroupedLayers

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped BigOperators Topology NNReal
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
set_option maxHeartbeats 18000000

omit [Fintype ι] [Fintype S] [Nonempty S] in
private theorem second_low_cut_rows_full {steps : List (GaussianStep ι)}
    (T : ReplicaTree ι S steps) {a : ℝ} (ho : OrderedSteps a steps) :
    T.cutMarkedAttach a 1=T.markedAttach a := by
  induction T generalizing a with
  | leaf=>simp only [ReplicaTree.cutMarkedAttach,lt_self_iff_false,ite_false]
  | step st T ih=>
    have hs:st.1 ≤ 1:=ho.2.2.2.bounds.2
    simp only [ReplicaTree.cutMarkedAttach,not_lt.mpr hs,ite_false,ReplicaTree.markedAttach,
      ih ho.2.2.2]
  | fork T E ihT ihE=>simp only [ReplicaTree.cutMarkedAttach,ReplicaTree.markedAttach,ihT ho,ihE ho]

omit [Nonempty S] in
private theorem second_low_cut_row_full
    {w : S→ℝ} (_hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    {a : ℝ} (ho : OrderedSteps a steps) (P : T.Assignment→ℝ) (F : S→ℝ) (x : ι→ℝ) :
    actualCutRow T w φ a 1 P F x=T.row w φ a P F x := by
  unfold actualCutRow ReplicaTree.row ReplicaTree.rowList
  rw [second_low_cut_rows_full T ho,←T.markedAttach_forget a]
  simp only [List.map_map]
  rfl

omit [Nonempty S] in
private theorem second_low_expect_const_factor
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (P : T.Assignment→ℝ)
    (c : ℝ) (x : ι→ℝ) :
    T.expect w φ (fun σ=>P σ*c) x=T.expect w φ P x*c := by
  rw [ReplicaTree.expect,ReplicaTree.expect,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ _
  ring

omit [Nonempty S] in
private theorem second_low_expect_sub
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (P Q : T.Assignment→ℝ) (x : ι→ℝ) :
    T.expect w φ (fun σ=>P σ-Q σ) x=T.expect w φ P x-T.expect w φ Q x := by
  simp only [ReplicaTree.expect,mul_sub,Finset.sum_sub_distrib]

omit [Nonempty S] in
private theorem second_low_expect_scale
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (P : T.Assignment→ℝ)
    (c d : ℝ) (x : ι→ℝ) :
    T.expect w φ (fun σ=>c*P σ*d) x=c*T.expect w φ P x*d := by
  have he:(fun σ=>c*P σ*d)=(fun σ=>c*(P σ*d)):=by funext σ;ring
  rw [he,ReplicaTree.expect_const_mul,second_low_expect_const_factor]
  ring

omit [Nonempty S] in
private theorem second_low_expect_fork_external_left
    {steps : List (GaussianStep ι)} (T E : ReplicaTree ι S steps)
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (P : (T.fork E).Assignment→ℝ) (x : ι→ℝ) :
    (T.fork E).expect w φ P x=E.expect w φ (fun τ=>T.expect w φ (fun σ=>P (σ,τ)) x) x := by
  simp only [ReplicaTree.expect,ReplicaTree.weight,Fintype.sum_prod_type,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro τ _
  apply Finset.sum_congr rfl
  intro σ _
  ring

theorem actual_cut_row_before_all_steps
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    {a v : ℝ} (ho : OrderedSteps a steps) (hv : v<1)
    (hsteps : ∀st∈steps,v<st.1) (P : T.Assignment→ℝ) (F : S→ℝ) (x : ι→ℝ) :
    actualCutRow T w φ a v P F x=
      a*T.expect w φ P x*gaussianHierarchyMean w φ F steps x := by
  induction T with
  | leaf =>
    simp only [actualCutRow,ReplicaTree.cutMarkedAttach,ite_eq_left hv,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil]
    change a*(ReplicaTree.Placement.fresh (.leaf : ReplicaTree ι S []) a).eval w φ P F x+0=_
    rw [ReplicaTree.Placement.eval_fresh hw φ _ ho]
    ring
  | @step st tail T ih =>
    exact actual_cut_row_step_before hw φ T st.1 st.2 ho (hsteps st List.mem_cons_self) P F x
  | fork T E ihT ihE =>
    rw [actual_cut_row_fork hw φ T E ho]
    simp_rw [ihT ho hsteps,ihE ho hsteps]
    rw [second_low_expect_scale,second_low_expect_scale,
      ←second_low_expect_fork_external_left,←ReplicaTree.expect_fork]
    ring

theorem actual_cut_row_incoming_difference
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    {a b : ℝ} (ha : OrderedSteps a steps) (hb : OrderedSteps b steps)
    (v : ℝ) (P : T.Assignment→ℝ) (F : S→ℝ) (x : ι→ℝ) :
    actualCutRow T w φ a v P F x-actualCutRow T w φ b v P F x=
      (a-b)*T.expect w φ P x*gaussianHierarchyMean w φ F steps x := by
  induction T generalizing a b with
  | leaf =>
    by_cases hv:v<1
    · rw [actual_cut_row_before_all_steps hw φ _ ha hv (by simp),
        actual_cut_row_before_all_steps hw φ _ hb hv (by simp)]
      ring
    · simp only [actualCutRow,ReplicaTree.cutMarkedAttach,ite_eq_right hv,ReplicaTree.markedAttach,
        List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
      change (1*(ReplicaTree.Placement.coincide (ι:=ι)).eval w φ P F x+
        ((a-1)*(ReplicaTree.Placement.fresh (.leaf : ReplicaTree ι S []) (a-1)).eval w φ P F x+0))-
        (1*(ReplicaTree.Placement.coincide (ι:=ι)).eval w φ P F x+
        ((b-1)*(ReplicaTree.Placement.fresh (.leaf : ReplicaTree ι S []) (b-1)).eval w φ P F x+0))=_
      rw [ReplicaTree.Placement.eval_fresh hw φ _ ha,ReplicaTree.Placement.eval_fresh hw φ _ hb]
      ring
  | @step st tail T ih =>
    by_cases hv:v<st.1
    · rw [actual_cut_row_step_before hw φ T st.1 st.2 ha hv,
        actual_cut_row_step_before hw φ T st.1 st.2 hb hv]
      ring
    · rw [actual_cut_row_step_after hw φ T st.1 st.2 ha (not_lt.mp hv),
        actual_cut_row_step_after hw φ T st.1 st.2 hb (not_lt.mp hv)]
      ring
  | @fork tail T E ihT ihE =>
    rw [actual_cut_row_fork hw φ T E ha,actual_cut_row_fork hw φ T E hb]
    have HT:E.expect w φ (fun τ=>actualCutRow T w φ a v (fun σ=>P (σ,τ)) F x) x-
        E.expect w φ (fun τ=>actualCutRow T w φ b v (fun σ=>P (σ,τ)) F x) x=
        (a-b)*(T.fork E).expect w φ P x*gaussianHierarchyMean w φ F tail x:=by
      rw [←second_low_expect_sub]
      simp_rw [ihT ha hb]
      rw [second_low_expect_scale,←second_low_expect_fork_external_left]
    have HE:T.expect w φ (fun σ=>actualCutRow E w φ a v (fun τ=>P (σ,τ)) F x) x-
        T.expect w φ (fun σ=>actualCutRow E w φ b v (fun τ=>P (σ,τ)) F x) x=
        (a-b)*(T.fork E).expect w φ P x*gaussianHierarchyMean w φ F tail x:=by
      rw [←second_low_expect_sub]
      simp_rw [ihE ha hb]
      rw [second_low_expect_scale,←ReplicaTree.expect_fork]
    nlinarith only [HT,HE]

theorem actual_whole_subtree_covariance_eq_half_resampling
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {steps : List (GaussianStep ι)} (A : ReplicaTree ι S steps)
    {a : ℝ} (ho : OrderedSteps a steps) (c : A.Slot)
    (P : A.Assignment→ℝ) (F : S→ℝ) (x : ι→ℝ) :
    A.expect w φ (fun σ=>P σ*F (A.atSlot σ c)) x-
      A.expect w φ P x*gaussianHierarchyMean w φ F steps x=
      (1/2:ℝ)*(A.fork A).expect w φ (fun σ=>
        (P σ.1-P σ.2)*(F (A.atSlot σ.1 c)-F (A.atSlot σ.2 c))) x := by
  have Hm:=A.expect_atSlot hw φ ho c F x
  have Hfun:(fun σ:(A.fork A).Assignment=>
      (P σ.1-P σ.2)*(F (A.atSlot σ.1 c)-F (A.atSlot σ.2 c)))=
      fun σ=>P σ.1*F (A.atSlot σ.1 c)+P σ.2*F (A.atSlot σ.2 c)-
        P σ.1*F (A.atSlot σ.2 c)-P σ.2*F (A.atSlot σ.1 c):=by funext σ;ring
  rw [Hfun]
  simp only [second_low_expect_sub,ReplicaTree.expect_add]
  have Hleft:(A.fork A).expect w φ (fun σ=>P σ.1*F (A.atSlot σ.1 c)) x=
      A.expect w φ (fun σ=>P σ*F (A.atSlot σ c)) x:=by
    rw [ReplicaTree.expect_fork]
    simp only [A.expect_const hw φ ho]
  have Hright:(A.fork A).expect w φ (fun σ=>P σ.2*F (A.atSlot σ.2 c)) x=
      A.expect w φ (fun σ=>P σ*F (A.atSlot σ c)) x:=by
    rw [ReplicaTree.expect_fork]
    simp only [A.expect_const hw φ ho]
  have Hcross:(A.fork A).expect w φ (fun σ=>P σ.2*F (A.atSlot σ.1 c)) x=
      A.expect w φ P x*A.expect w φ (fun σ=>F (A.atSlot σ c)) x:=by
    have HH:=ReplicaTree.expect_fork_product w φ A A (fun σ=>F (A.atSlot σ c)) P x
    simpa only [mul_comm] using HH
  have Hcross1:=ReplicaTree.expect_fork_product w φ A A P (fun σ=>F (A.atSlot σ c)) x
  rw [Hleft,Hright,Hcross1,Hcross,Hm]
  ring

def actualSharedExteriorMarkedReplacement {steps : List (GaussianStep ι)}
    (A E : ReplicaTree ι S steps) (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (a : ℝ) (c : A.Slot) (P : A.Assignment→E.Assignment→ℝ)
    (F : E.Assignment→S→ℝ) (x : ι→ℝ) : ℝ :=
  E.expect w φ (fun e=>A.row w φ a (fun σ=>P σ e) (F e) x-
    a*A.expect w φ (fun σ=>P σ e*F e (A.atSlot σ c)) x) x

def actualSharedExteriorWholeProductCovariance {steps : List (GaussianStep ι)}
    (A E : ReplicaTree ι S steps) (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (c : A.Slot) (P : A.Assignment→E.Assignment→ℝ)
    (F : E.Assignment→S→ℝ) (x : ι→ℝ) : ℝ :=
  (E.fork (A.fork A)).expect w φ (fun σ=>
    (P σ.2.1 σ.1-P σ.2.2 σ.1)*
      (F σ.1 (A.atSlot σ.2.1 c)-F σ.1 (A.atSlot σ.2.2 c))) x

omit [Fintype ι] [Fintype S] [Nonempty S] in
private theorem second_low_ordered_step_lower {a : ℝ} {steps : List (GaussianStep ι)}
    (ho : OrderedSteps a steps) (st : GaussianStep ι) (hst : st∈steps) : a ≤ st.1 := by
  induction steps generalizing a with
  | nil=>simp at hst
  | cons t ts ih=>
    rcases List.mem_cons.mp hst with rfl|hst
    · exact ho.2.1
    · exact ho.2.1.trans (ih ho.2.2.2 hst)

theorem actual_shared_exterior_replacement_eq_layer_sub_whole_covariance
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {steps : List (GaussianStep ι)} (A E : ReplicaTree ι S steps)
    {a : ℝ} (ho : OrderedSteps a steps) (ha : 0<a) (ha1 : a ≤ 1)
    (c : A.Slot) (P : A.Assignment→E.Assignment→ℝ)
    (F : E.Assignment→S→ℝ) (x : ι→ℝ) :
    actualSharedExteriorMarkedReplacement A E w φ a c P F x=
      actualSharedExteriorLayer A E w φ 0 (a/2) 1 P F x-
        (a/2)*actualSharedExteriorWholeProductCovariance A E w φ c P F x := by
  have ho0:OrderedSteps 0 steps:=ho.lower (by norm_num) ha.le
  have Hbefore:∀e,actualCutRow A w φ a (a/2) (fun σ=>P σ e) (F e) x=
      a*A.expect w φ (fun σ=>P σ e) x*gaussianHierarchyMean w φ (F e) steps x:=by
    intro e
    apply actual_cut_row_before_all_steps hw φ A ho (by linarith)
    intro st hst
    have HH:=second_low_ordered_step_lower ho st hst
    linarith
  have Hlayer:∀e,actualCutRow A w φ 0 1 (fun σ=>P σ e) (F e) x-
      actualCutRow A w φ 0 (a/2) (fun σ=>P σ e) (F e) x=
      A.row w φ a (fun σ=>P σ e) (F e) x-
        a*A.expect w φ (fun σ=>P σ e) x*gaussianHierarchyMean w φ (F e) steps x:=by
    intro e
    have H1:=actual_cut_row_incoming_difference hw φ A ho ho0 1 (fun σ=>P σ e) (F e) x
    have H0:=actual_cut_row_incoming_difference hw φ A ho ho0 (a/2) (fun σ=>P σ e) (F e) x
    rw [second_low_cut_row_full hw φ A ho] at H1
    rw [Hbefore e] at H0
    linarith only [H1,H0]
  unfold actualSharedExteriorMarkedReplacement actualSharedExteriorLayer
    actualSharedExteriorWholeProductCovariance
  rw [ReplicaTree.expect_fork]
  simp only [Hlayer]
  have Hpoint:∀e,A.row w φ a (fun σ=>P σ e) (F e) x-
      a*A.expect w φ (fun σ=>P σ e*F e (A.atSlot σ c)) x=
      (A.row w φ a (fun σ=>P σ e) (F e) x-
        a*A.expect w φ (fun σ=>P σ e) x*gaussianHierarchyMean w φ (F e) steps x)-
      (a/2)*(A.fork A).expect w φ (fun σ=>
        (P σ.1 e-P σ.2 e)*(F e (A.atSlot σ.1 c)-F e (A.atSlot σ.2 c))) x:=by
    intro e
    have HH:=actual_whole_subtree_covariance_eq_half_resampling hw φ A ho c (fun σ=>P σ e) (F e) x
    linear_combination -a*HH
  simp only [Hpoint,second_low_expect_sub,ReplicaTree.expect_const_mul]

omit [Nonempty S] in
theorem actual_shared_exterior_layer_add
    {steps : List (GaussianStep ι)} (A E : ReplicaTree ι S steps)
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (a u v z : ℝ)
    (P : A.Assignment→E.Assignment→ℝ) (F : E.Assignment→S→ℝ) (x : ι→ℝ) :
    actualSharedExteriorLayer A E w φ a u v P F x+
      actualSharedExteriorLayer A E w φ a v z P F x=
      actualSharedExteriorLayer A E w φ a u z P F x := by
  simp only [actualSharedExteriorLayer,second_low_expect_sub]
  ring

omit [Nonempty S] in
theorem actual_shared_exterior_layers_telescope
    {steps : List (GaussianStep ι)} (A E : ReplicaTree ι S steps)
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (a : ℝ) (cuts : ℕ→ℝ) (k : ℕ)
    (P : A.Assignment→E.Assignment→ℝ) (F : E.Assignment→S→ℝ) (x : ι→ℝ) :
    (∑j∈Finset.range k,actualSharedExteriorLayer A E w φ a (cuts j) (cuts (j+1)) P F x)=
      actualSharedExteriorLayer A E w φ a (cuts 0) (cuts k) P F x := by
  induction k with
  | zero=>simp [actualSharedExteriorLayer,ReplicaTree.expect]
  | succ k ih=>
    rw [Finset.sum_range_succ,ih,actual_shared_exterior_layer_add]

theorem actual_shared_exterior_replacement_eq_grouped_layers_sub_whole_covariance
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {steps : List (GaussianStep ι)} (A E : ReplicaTree ι S steps)
    {a : ℝ} (ho : OrderedSteps a steps) (ha : 0<a) (ha1 : a≤1)
    (c : A.Slot) (P : A.Assignment→E.Assignment→ℝ)
    (F : E.Assignment→S→ℝ) (cuts : ℕ→ℝ) (k : ℕ)
    (hfirst : cuts 0=a/2) (hlast : cuts k=1) (x : ι→ℝ) :
    actualSharedExteriorMarkedReplacement A E w φ a c P F x=
      (∑j∈Finset.range k,actualSharedExteriorLayer A E w φ 0 (cuts j) (cuts (j+1)) P F x)-
        (a/2)*actualSharedExteriorWholeProductCovariance A E w φ c P F x := by
  rw [actual_shared_exterior_layers_telescope,hfirst,hlast]
  exact actual_shared_exterior_replacement_eq_layer_sub_whole_covariance hw φ A E ho ha ha1 c P F x

end OAI.SKFluctuations.Cavity
