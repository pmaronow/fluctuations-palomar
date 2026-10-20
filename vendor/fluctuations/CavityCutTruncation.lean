module

public import CavityAttachmentCoupling

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ReplicaTree
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*}

def cutMarkedAttach : {steps : List (GaussianStep ι)} →
    (T : ReplicaTree ι S steps) → ℝ → ℝ → List (MarkedPlacement T)
  | _, .leaf, a, v => if v < 1 then [MarkedPlacement.fresh .leaf a]
      else (ReplicaTree.leaf (ι := ι) (S := S)).markedAttach a
  | _, @ReplicaTree.step _ _ st tail T, a, v =>
      if v < st.1 then [MarkedPlacement.fresh (T.step st) a]
      else MarkedPlacement.fresh (T.step st) (a-st.1) ::
        (T.cutMarkedAttach st.1 v).map (MarkedPlacement.step st)
  | _, .fork T U, a, v => MarkedPlacement.fresh (T.fork U) (-a) ::
      ((T.cutMarkedAttach a v).map (MarkedPlacement.left U) ++
       (U.cutMarkedAttach a v).map (MarkedPlacement.right T))

theorem cutMarkedAttach_mass {steps : List (GaussianStep ι)}
    (T : ReplicaTree ι S steps) (a v : ℝ) :
    ((T.cutMarkedAttach a v).map (fun p => p.coeff)).sum = a := by
  induction T generalizing a with
  | leaf =>
    unfold cutMarkedAttach
    split
    · simp [MarkedPlacement.fresh, Placement.fresh]
    · exact markedAttach_mass _ a
  | step st T ih =>
    unfold cutMarkedAttach
    split
    · simp [MarkedPlacement.fresh, Placement.fresh]
    · simp only [List.map_cons, List.sum_cons, List.map_map,
        MarkedPlacement.fresh, MarkedPlacement.step, Placement.fresh, Placement.step]
      change a-st.1+((T.cutMarkedAttach st.1 v).map (fun p => p.coeff)).sum = a
      rw [ih]
      ring
  | fork T U ihT ihU =>
    simp only [cutMarkedAttach, List.map_cons, List.sum_cons, List.map_append,
      List.sum_append, List.map_map, MarkedPlacement.fresh, MarkedPlacement.left,
      MarkedPlacement.right, Placement.fresh, Placement.left, Placement.right]
    change -a+(((T.cutMarkedAttach a v).map (fun p => p.coeff)).sum+
      ((U.cutMarkedAttach a v).map (fun p => p.coeff)).sum) = a
    rw [ihT, ihU]
    ring

theorem cutMarkedAttach_variation_le {steps : List (GaussianStep ι)}
    (T : ReplicaTree ι S steps) {a v : ℝ} (ho : OrderedSteps a steps)
    (hav : a ≤ v) :
    ((T.cutMarkedAttach a v).map (fun p => |p.coeff|)).sum ≤ 2*(T.leaves:ℝ)*v-a := by
  induction T generalizing a with
  | leaf =>
    unfold cutMarkedAttach
    split
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        MarkedPlacement.fresh, Placement.fresh, ReplicaTree.leaves, Nat.cast_one]
      rw [abs_of_nonneg ho.bounds.1]
      linarith
    · simp only [markedAttach, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, MarkedPlacement.coincide, MarkedPlacement.fresh,
        Placement.coincide, Placement.fresh, abs_one, ReplicaTree.leaves, Nat.cast_one]
      rw [abs_of_nonpos (sub_nonpos.mpr ho.bounds.2)]
      rename_i hv
      linarith
  | step st T ih =>
    unfold cutMarkedAttach
    split
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        MarkedPlacement.fresh, Placement.fresh, ReplicaTree.leaves]
      rw [abs_of_nonneg ho.bounds.1]
      have hq : (1:ℝ) ≤ T.leaves := by exact_mod_cast T.leaves_pos
      have hv : 0 ≤ v := ho.bounds.1.trans hav
      nlinarith
    · rename_i hv
      have htail := ih ho.2.2.2 (le_of_not_gt hv)
      simp only [List.map_cons, List.sum_cons, List.map_map,
        MarkedPlacement.fresh, MarkedPlacement.step, Placement.fresh, Placement.step]
      change |a-st.1|+((T.cutMarkedAttach st.1 v).map (fun p => |p.coeff|)).sum ≤ _
      rw [abs_of_nonpos (sub_nonpos.mpr ho.2.1)]
      change _ ≤ 2*(T.leaves:ℝ)*v-a
      linarith
  | fork T U ihT ihU =>
    have hT := ihT ho hav
    have hU := ihU ho hav
    simp only [cutMarkedAttach, List.map_cons, List.sum_cons, List.map_append,
      List.sum_append, List.map_map, MarkedPlacement.fresh, MarkedPlacement.left,
      MarkedPlacement.right, Placement.fresh, Placement.left, Placement.right]
    change |-a|+(((T.cutMarkedAttach a v).map (fun p => |p.coeff|)).sum+
      ((U.cutMarkedAttach a v).map (fun p => |p.coeff|)).sum) ≤ _
    rw [abs_neg, abs_of_nonneg ho.bounds.1]
    simp only [ReplicaTree.leaves, Nat.cast_add]
    linarith

variable [Fintype ι] [Fintype S] [Nonempty S]

theorem cutMarkedAttach_preserves {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)}
    (T : ReplicaTree ι S steps) {a : ℝ} (ho : OrderedSteps a steps)
    (v : ℝ) (p : MarkedPlacement T) (hp : p ∈ T.cutMarkedAttach a v) :
    p.toPlacement.Preserves w φ := by
  induction T generalizing a with
  | leaf =>
    unfold cutMarkedAttach at hp
    split at hp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst p
      exact Placement.fresh_preserves hw φ _ ho _
    · exact markedAttach_preserves hw φ _ ho p hp
  | step st T ih =>
    unfold cutMarkedAttach at hp
    split at hp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst p
      exact Placement.fresh_preserves hw φ _ ho _
    · simp only [List.mem_cons, List.mem_map] at hp
      rcases hp with rfl | ⟨p,hp,rfl⟩
      · exact Placement.fresh_preserves hw φ _ ho _
      · exact Placement.step_preserves hw φ st ho.2.2.2 (ih ho.2.2.2 p hp)
  | fork T U ihT ihU =>
    simp only [cutMarkedAttach, List.mem_cons, List.mem_append, List.mem_map] at hp
    rcases hp with rfl | (⟨p,hp,rfl⟩ | ⟨p,hp,rfl⟩)
    · exact Placement.fresh_preserves hw φ _ ho _
    · exact Placement.left_preserves _ φ U (ihT ho p hp)
    · exact Placement.right_preserves _ φ T (ihU ho p hp)

theorem cutMarkedAttach_layer_variation_le {steps : List (GaussianStep ι)}
    (T : ReplicaTree ι S steps) {a v z : ℝ} (ho : OrderedSteps a steps)
    (hav : a ≤ v) (hvz : v ≤ z) (hz : z ≤ 2*v) :
    ((T.cutMarkedAttach a v).map (fun p => |p.coeff|)).sum+
      ((T.cutMarkedAttach a z).map (fun p => |p.coeff|)).sum ≤ 6*(T.leaves:ℝ)*v := by
  have h1 := T.cutMarkedAttach_variation_le ho hav
  have h2 := T.cutMarkedAttach_variation_le ho (hav.trans hvz)
  have hq : 0 ≤ (T.leaves:ℝ) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hz (by positivity : 0 ≤ 2*(T.leaves:ℝ))
  have ha := ho.bounds.1
  nlinarith

end OAI.SKFluctuations.Hierarchy.ReplicaTree
