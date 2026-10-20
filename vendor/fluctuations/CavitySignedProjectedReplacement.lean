module

public import CavityWeightedExteriorClock
public import CavityScalarRowBridge

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ReplicaTree
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

theorem identical_fork_expect_swap (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    (Q : T.Assignment → T.Assignment → ℝ) (x : ι → ℝ) :
    (T.fork T).expect w φ (fun σ=>Q σ.1 σ.2) x=
      (T.fork T).expect w φ (fun σ=>Q σ.2 σ.1) x := by
  simp only [expect,weight,Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro τ _
  ring

theorem single_marked_expect_exchange {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (hs : OrderedSteps a steps)
    (p : MarkedPlacement (single (S := S) steps)) (hp : p∈(single steps).markedAttach a)
    (Q : S → S → ℝ) (x : ι → ℝ) :
    p.tree.expect w φ (fun σ=>Q (singleEquiv (S := S) steps (p.restrict σ)) (p.spin σ)) x=
      p.tree.expect w φ (fun σ=>Q (p.spin σ) (singleEquiv (S := S) steps (p.restrict σ))) x := by
  induction steps generalizing a x with
  | nil =>
    rcases List.mem_cons.mp hp with rfl|hp
    · rfl
    · obtain rfl := List.mem_singleton.mp hp
      exact identical_fork_expect_swap w φ leaf Q x
  | cons st tail ih =>
    rcases List.mem_cons.mp hp with rfl|hp
    · exact identical_fork_expect_swap w φ (single (st::tail))
        (fun σ τ=>Q (singleEquiv (S := S) (st::tail) σ) (singleEquiv (S := S) (st::tail) τ)) x
    · obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
      change (q.tree.step st).expect w φ
        (fun σ=>Q (singleEquiv (S := S) tail (q.restrict σ)) (q.spin σ)) x=
        (q.tree.step st).expect w φ
          (fun σ=>Q (q.spin σ) (singleEquiv (S := S) tail (q.restrict σ))) x
      rw [expect_step hw φ q.tree st.1 st.2 hs.2.2.2,
        expect_step hw φ q.tree st.1 st.2 hs.2.2.2]
      congr 1
      funext y
      exact ih hs.2.2.2 q hq y

theorem single_marked_external_exchange {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)}
    (E : ReplicaTree ι S steps) {a : ℝ} (hs : OrderedSteps a steps)
    (p : MarkedPlacement (single (S := S) steps)) (hp : p∈(single steps).markedAttach a)
    (Q : E.Assignment → S → S → ℝ) (x : ι → ℝ) :
    (E.fork p.tree).expect w φ
      (fun σ=>Q σ.1 (singleEquiv (S := S) steps (p.restrict σ.2)) (p.spin σ.2)) x=
    (E.fork p.tree).expect w φ
      (fun σ=>Q σ.1 (p.spin σ.2) (singleEquiv (S := S) steps (p.restrict σ.2))) x := by
  rw [expect_fork,expect_fork]
  congr 1
  funext σ
  exact single_marked_expect_exchange hw φ steps hs p hp (Q σ) x

theorem signed_single_projected_replacement {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)}
    (E : ReplicaTree ι S steps) {a : ℝ} (hs : OrderedSteps a steps)
    (g : MarkedPlacement (single (S := S) steps) → ℝ)
    (Y : S → ℝ) (P : E.Assignment → S → ℝ) (x : ι → ℝ) :
    (((single steps).markedAttach a).map fun p=>p.coeff*g p*
      (E.fork p.tree).expect w φ (fun σ=>
        (Y (p.spin σ.2)-Y (singleEquiv (S := S) steps (p.restrict σ.2)))*
          P σ.1 (singleEquiv (S := S) steps (p.restrict σ.2))) x).sum=
    (1/2:ℝ)*(((single steps).markedAttach a).map fun p=>p.coeff*g p*
      (E.fork p.tree).expect w φ (fun σ=>
        (Y (p.spin σ.2)-Y (singleEquiv (S := S) steps (p.restrict σ.2)))*
          (P σ.1 (singleEquiv (S := S) steps (p.restrict σ.2))-P σ.1 (p.spin σ.2))) x).sum := by
  rw [←List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  have he := single_marked_external_exchange hw φ E hs p hp
    (fun σ u v=>(Y v-Y u)*P σ u) x
  have hn : (E.fork p.tree).expect w φ (fun σ=>
      (Y (singleEquiv (S := S) steps (p.restrict σ.2))-Y (p.spin σ.2))*P σ.1 (p.spin σ.2)) x=
      -(E.fork p.tree).expect w φ (fun σ=>
        (Y (p.spin σ.2)-Y (singleEquiv (S := S) steps (p.restrict σ.2)))*P σ.1 (p.spin σ.2)) x := by
    unfold expect
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro σ _
    ring
  rw [hn] at he
  have hsplit : (E.fork p.tree).expect w φ (fun σ=>
      (Y (p.spin σ.2)-Y (singleEquiv (S := S) steps (p.restrict σ.2)))*
        (P σ.1 (singleEquiv (S := S) steps (p.restrict σ.2))-P σ.1 (p.spin σ.2))) x=
    (E.fork p.tree).expect w φ (fun σ=>
      (Y (p.spin σ.2)-Y (singleEquiv (S := S) steps (p.restrict σ.2)))*P σ.1 (singleEquiv (S := S) steps (p.restrict σ.2))) x-
      (E.fork p.tree).expect w φ (fun σ=>
        (Y (p.spin σ.2)-Y (singleEquiv (S := S) steps (p.restrict σ.2)))*P σ.1 (p.spin σ.2)) x := by
    unfold expect
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro σ _
    ring
  rw [hsplit,he]
  ring

theorem signed_single_projected_replacement_abs_le {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)}
    (E : ReplicaTree ι S steps) {a : ℝ} (hs : OrderedSteps a steps)
    (g : MarkedPlacement (single (S := S) steps) → ℝ)
    (Y : S → ℝ) (P : E.Assignment → S → ℝ) (x : ι → ℝ) :
    |(((single steps).markedAttach a).map fun p=>p.coeff*g p*
      (E.fork p.tree).expect w φ (fun σ=>
        (Y (p.spin σ.2)-Y (singleEquiv (S := S) steps (p.restrict σ.2)))*
          P σ.1 (singleEquiv (S := S) steps (p.restrict σ.2))) x).sum|≤
    (1/2:ℝ)*(((single steps).markedAttach a).map fun p=>|p.coeff*g p| *
      Real.sqrt ((E.fork p.tree).expect w φ (fun σ=>
        (Y (p.spin σ.2)-Y (singleEquiv (S := S) steps (p.restrict σ.2)))^2) x*
        (E.fork p.tree).expect w φ (fun σ=>
          (P σ.1 (singleEquiv (S := S) steps (p.restrict σ.2))-P σ.1 (p.spin σ.2))^2) x)).sum := by
  rw [signed_single_projected_replacement hw φ E hs g Y P x,abs_mul,
    abs_of_nonneg (by norm_num : (0:ℝ)≤1/2)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply list_weighted_absolute_bound
  intro p _
  exact (E.fork p.tree).expect_mul_abs_le_sqrt hw φ hs
    (fun σ=>Y (p.spin σ.2)-Y (singleEquiv (S := S) steps (p.restrict σ.2)))
    (fun σ=>P σ.1 (singleEquiv (S := S) steps (p.restrict σ.2))-P σ.1 (p.spin σ.2)) x

end OAI.SKFluctuations.Hierarchy.ReplicaTree
