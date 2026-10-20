module

public import ComparisonSignedCavitySecondLowFullClockPairSymmetry
public import ComparisonSignedCavityHighRowsCommutation

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal Topology
variable {ι : Type*} {S : Type} [Fintype ι] [Fintype S] [Nonempty S]
set_option maxHeartbeats 30000000
set_option backward.isDefEq.respectTransparency false

private theorem native_second_low_clock_expect_smooth
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T : ClockTree S as) {a : ℝ} (ho : MassOrdered a as)
    (q : ℕ → ι → ℝ≥0) (P : T.Assignment → ℝ) : BddSmooth 0 (T.expect w φ q P) := by
  have HE : T.expect w φ q P = (T.realize q).expect w φ
      (fun σ => P ((T.assignmentEquiv q).symm σ)) := funext (T.expect_realize w φ q P)
  rw [HE]
  exact (T.realize q).expect_smooth hw φ (clockSteps_ordered ho q) _ 0

private theorem native_second_low_list_sum_smooth {α : Type*}
    (ps : List α) (c : α → ℝ) (F : α → (ι → ℝ) → ℝ)
    (hF : ∀ p ∈ ps, BddSmooth 0 (F p)) :
    BddSmooth 0 (fun x => (ps.map (fun p => c p * F p x)).sum) := by
  induction ps with
  | nil => exact BddSmooth.const 0 0
  | cons p ps ih =>
    exact ((hF p List.mem_cons_self).const_mul (c p)).add
      (ih (fun r hr => hF r (List.mem_cons_of_mem p hr)))

private theorem native_second_low_list_sum_shiftedMean {α : Type*}
    (ps : List α) (c : α → ℝ) (F : α → (ι → ℝ) → ℝ)
    (hF : ∀ p ∈ ps, BddSmooth 0 (F p))
    {ν : Measure (ι → ℝ)} [IsProbabilityMeasure ν] (m : ℝ)
    (H : (ι → ℝ) → ℝ) (x : ι → ℝ)
    (hi : Integrable (fun z => Real.exp (m * H (x+z))) ν) :
    shiftedMean ν m H (fun y => (ps.map (fun p => c p * F p y)).sum) x =
      (ps.map (fun p => c p * shiftedMean ν m H (F p) x)).sum := by
  induction ps with
  | nil => simp [shiftedMean,tiltedMean]
  | cons p ps ih =>
    change shiftedMean ν m H
      (fun y => c p * F p y + (ps.map (fun p => c p * F p y)).sum) x = _
    rw [shiftedMean_add ((hF p List.mem_cons_self).const_mul (c p))
      (native_second_low_list_sum_smooth ps c F (fun r hr => hF r (List.mem_cons_of_mem p hr))) hi,
      shiftedMean_const_mul,ih (fun r hr => hF r (List.mem_cons_of_mem p hr))]
    rfl

def nativeSecondLowHighFieldPair (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (s : T.Slot) (star : ℕ) (a : ℝ)
    (q : ℕ → ι → ℝ≥0) (P : T.Assignment → ℝ) (u v x : ι → ℝ) : ℝ :=
  ((nativeHighMarkedRows T s star a).map fun p => p.coeff *
    ((nativeHighMarkedRows p.tree (p.embed s) star a).map fun r => r.coeff *
      r.tree.expect w φ q (fun σ => P (p.restrict (r.restrict σ)) *
        (φ (p.spin (r.restrict σ)) u * φ (r.spin σ) v)) x).sum).sum

private theorem native_second_low_two_field_rows_step
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (b : PositiveMass)
    (ho : MassOrdered b.val as) (q : ℕ → ι → ℝ≥0) (P : T.Assignment → ℝ)
    (ps : List (MarkedPlacement T)) (rs : ∀ p : MarkedPlacement T, List (MarkedPlacement p.tree))
    (u v x : ι → ℝ) :
    (ps.map fun p => p.coeff *
      ((rs p).map fun r => r.coeff *
        (r.tree.step b).expect w φ q (fun σ => P (p.restrict (r.restrict σ)) *
          (φ (p.spin (r.restrict σ)) u * φ (r.spin σ) v)) x).sum).sum =
    shiftedMean (Measure.pi fun i => gaussianReal 0 (q 0 i)) b.val
      (gaussianHierarchy w φ (clockSteps as (fun j => q (j+1))))
      (fun y => (ps.map fun p => p.coeff *
        ((rs p).map fun r => r.coeff *
          r.tree.expect w φ (fun j => q (j+1)) (fun σ => P (p.restrict (r.restrict σ)) *
            (φ (p.spin (r.restrict σ)) u * φ (r.spin σ) v)) y).sum).sum) x := by
  let F := fun (p : MarkedPlacement T) (r : MarkedPlacement p.tree) =>
    r.tree.expect w φ (fun j => q (j+1)) (fun σ => P (p.restrict (r.restrict σ)) *
      (φ (p.spin (r.restrict σ)) u * φ (r.spin σ) v))
  have hF (p : MarkedPlacement T) (r : MarkedPlacement p.tree) : BddSmooth 0 (F p r) :=
    native_second_low_clock_expect_smooth hw φ r.tree ho _ _
  have hi := gaussianHierarchy_integrable hw φ (clockSteps as (fun j => q (j+1)))
    (clockSteps_ordered ho _) b.val (q 0) x
  rw [native_second_low_list_sum_shiftedMean ps (fun p => p.coeff)
    (fun p y => ((rs p).map fun r => r.coeff * F p r y).sum)
    (fun p _ => native_second_low_list_sum_smooth (rs p) (fun r => r.coeff) (F p) (fun r _ => hF p r))
    b.val _ x hi]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  rw [native_second_low_list_sum_shiftedMean (rs p) (fun r => r.coeff) (F p)
    (fun r _ => hF p r) b.val _ x hi]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro r _
  rw [expect_step hw φ b r.tree ho]

theorem native_second_low_high_field_pair_step_succ
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (b : PositiveMass)
    (s : T.Slot) (star : ℕ) (a : ℝ) (ho : MassOrdered b.val as)
    (q : ℕ → ι → ℝ≥0) (P : T.Assignment → ℝ) (u v x : ι → ℝ) :
    nativeSecondLowHighFieldPair w φ (T.step b) s (star+1) a q P u v x =
      shiftedMean (Measure.pi fun i => gaussianReal 0 (q 0 i)) b.val
        (gaussianHierarchy w φ (clockSteps as (fun j => q (j+1))))
        (nativeSecondLowHighFieldPair w φ T s star b.val (fun j => q (j+1)) P u v) x := by
  unfold nativeSecondLowHighFieldPair
  simp only [nativeHighMarkedRows,List.map_map,Function.comp_def,MarkedPlacement.step]
  exact native_second_low_two_field_rows_step hw φ T b ho q P
    (nativeHighMarkedRows T s star b.val) (fun p => nativeHighMarkedRows p.tree (p.embed s) star b.val) u v x

theorem native_second_low_high_field_pair_step_zero
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (b : PositiveMass)
    (s : T.Slot) (a : ℝ) (ho : MassOrdered b.val as)
    (q : ℕ → ι → ℝ≥0) (P : T.Assignment → ℝ) (u v x : ι → ℝ) :
    nativeSecondLowHighFieldPair w φ (T.step b) s 0 a q P u v x =
      shiftedMean (Measure.pi fun i => gaussianReal 0 (q 0 i)) b.val
        (gaussianHierarchy w φ (clockSteps as (fun j => q (j+1))))
        (fun y => T.profilePair w φ b.val (fun j => q (j+1)) P (fun _ σ τ => φ σ u * φ τ v) y) x := by
  unfold nativeSecondLowHighFieldPair profilePair profilePairTest
  simp only [nativeHighMarkedRows,List.map_map,Function.comp_def,MarkedPlacement.step]
  exact native_second_low_two_field_rows_step hw φ T b ho q P
    (T.markedAttach b.val) (fun p => p.tree.markedAttach b.val) u v x

omit [Nonempty S] in
theorem native_second_low_high_field_pair_fork_left
    (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T V : ClockTree S as) (s : T.Slot) (star : ℕ) (a : ℝ)
    (q : ℕ → ι → ℝ≥0) (P : (T.fork V).Assignment → ℝ) (u v x : ι → ℝ) :
    nativeSecondLowHighFieldPair w φ (T.fork V) (Sum.inl s) star a q P u v x =
      ∑ τ : V.Assignment, V.weight w φ q τ x *
        nativeSecondLowHighFieldPair w φ T s star a q (fun σ => P (σ,τ)) u v x := by
  have HF (p : MarkedPlacement T) (r : MarkedPlacement p.tree) :
      (r.tree.fork V).expect w φ q (fun σ => P (p.restrict (r.restrict σ.1),σ.2) *
        (φ (p.spin (r.restrict σ.1)) u * φ (r.spin σ.1) v)) x =
      ∑ τ : V.Assignment, V.weight w φ q τ x *
        r.tree.expect w φ q (fun σ => P (p.restrict (r.restrict σ),τ) *
          (φ (p.spin (r.restrict σ)) u * φ (r.spin σ) v)) x := by
    simp only [expect,weight_fork,Fintype.sum_prod_type,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro τ _
    apply Finset.sum_congr rfl
    intro σ _
    ring
  unfold nativeSecondLowHighFieldPair
  simp only [nativeHighMarkedRows,List.map_map,Function.comp_def]
  simp_rw [nativeHighRows_marked_left,List.map_map,Function.comp_def]
  dsimp only [MarkedPlacement.left]
  simp_rw [HF,Finset.mul_sum,ReplicaTree.list_sum_finset_sum,Finset.mul_sum,ReplicaTree.list_sum_finset_sum]
  apply Finset.sum_congr rfl
  intro τ _
  rw [←List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  have HC : ((nativeHighMarkedRows p.tree (p.embed s) star a).map fun r =>
      r.coeff * (V.weight w φ q τ x * r.tree.expect w φ q (fun σ => P (p.restrict (r.restrict σ),τ) *
            (φ (p.spin (r.restrict σ)) u * φ (r.spin σ) v)) x)).sum =
      V.weight w φ q τ x * ((nativeHighMarkedRows p.tree (p.embed s) star a).map fun r =>
        r.coeff * r.tree.expect w φ q (fun σ => P (p.restrict (r.restrict σ),τ) *
            (φ (p.spin (r.restrict σ)) u * φ (r.spin σ) v)) x).sum := by
    rw [←List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro r _
    ring
  rw [HC]
  ring

omit [Nonempty S] in
theorem native_second_low_high_field_pair_fork_right
    (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T V : ClockTree S as) (s : V.Slot) (star : ℕ) (a : ℝ)
    (q : ℕ → ι → ℝ≥0) (P : (T.fork V).Assignment → ℝ) (u v x : ι → ℝ) :
    nativeSecondLowHighFieldPair w φ (T.fork V) (Sum.inr s) star a q P u v x =
      ∑ τ : T.Assignment, T.weight w φ q τ x *
        nativeSecondLowHighFieldPair w φ V s star a q (fun σ => P (τ,σ)) u v x := by
  have HF (p : MarkedPlacement V) (r : MarkedPlacement p.tree) :
      (T.fork r.tree).expect w φ q (fun σ => P (σ.1,p.restrict (r.restrict σ.2)) *
        (φ (p.spin (r.restrict σ.2)) u * φ (r.spin σ.2) v)) x =
      ∑ τ : T.Assignment, T.weight w φ q τ x *
        r.tree.expect w φ q (fun σ => P (τ,p.restrict (r.restrict σ)) *
          (φ (p.spin (r.restrict σ)) u * φ (r.spin σ) v)) x := by
    simp only [expect,weight_fork,Fintype.sum_prod_type,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro τ _
    apply Finset.sum_congr rfl
    intro σ _
    ring
  unfold nativeSecondLowHighFieldPair
  simp only [nativeHighMarkedRows,List.map_map,Function.comp_def]
  simp_rw [nativeHighRows_marked_right,List.map_map,Function.comp_def]
  dsimp only [MarkedPlacement.right]
  simp_rw [HF,Finset.mul_sum,ReplicaTree.list_sum_finset_sum,Finset.mul_sum,ReplicaTree.list_sum_finset_sum]
  apply Finset.sum_congr rfl
  intro τ _
  rw [←List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  have HC : ((nativeHighMarkedRows p.tree (p.embed s) star a).map fun r =>
      r.coeff * (T.weight w φ q τ x * r.tree.expect w φ q (fun σ => P (τ,p.restrict (r.restrict σ)) *
            (φ (p.spin (r.restrict σ)) u * φ (r.spin σ) v)) x)).sum =
      T.weight w φ q τ x * ((nativeHighMarkedRows p.tree (p.embed s) star a).map fun r =>
        r.coeff * r.tree.expect w φ q (fun σ => P (τ,p.restrict (r.restrict σ)) *
            (φ (p.spin (r.restrict σ)) u * φ (r.spin σ) v)) x).sum := by
    rw [←List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro r _
    ring
  rw [HC]
  ring

theorem native_second_low_high_field_pair_symm
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (s : T.Slot) (star : ℕ)
    (a : ℝ) (ho : MassOrdered a as) (q : ℕ → ι → ℝ≥0)
    (P : T.Assignment → ℝ) (u v x : ι → ℝ) :
    nativeSecondLowHighFieldPair w φ T s star a q P u v x =
      nativeSecondLowHighFieldPair w φ T s star a q P v u x := by
  induction T generalizing star a q x with
  | leaf => rfl
  | step b T ih =>
    cases star with
    | zero =>
      rw [native_second_low_high_field_pair_step_zero hw φ T b s a ho.2.2,
        native_second_low_high_field_pair_step_zero hw φ T b s a ho.2.2]
      congr 1
      funext y
      exact native_second_low_full_clock_field_pair_symm hw φ T ho.2.2 (fun j => q (j+1)) P u v y
    | succ star =>
      rw [native_second_low_high_field_pair_step_succ hw φ T b s star a ho.2.2,
        native_second_low_high_field_pair_step_succ hw φ T b s star a ho.2.2]
      congr 1
      funext y
      exact ih s star b.val ho.2.2 (fun j => q (j+1)) P y
  | fork T V ihT ihV =>
    cases s with
    | inl s =>
      rw [native_second_low_high_field_pair_fork_left,native_second_low_high_field_pair_fork_left]
      apply Finset.sum_congr rfl
      intro τ _
      rw [ihT s star a ho q (fun σ => P (σ,τ)) x]
    | inr s =>
      rw [native_second_low_high_field_pair_fork_right,native_second_low_high_field_pair_fork_right]
      apply Finset.sum_congr rfl
      intro τ _
      rw [ihV s star a ho q (fun σ => P (τ,σ)) x]

end OAI.SKFluctuations.Hierarchy.ClockTree
