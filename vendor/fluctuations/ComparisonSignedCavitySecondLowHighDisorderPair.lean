module

public import ComparisonSignedCavitySecondLowHighOldDependentPair

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal Topology
variable {ι : Type*} {S : Type} [Fintype ι] [Fintype S] [Nonempty S]
set_option maxHeartbeats 30000000

omit [Fintype ι] in
private theorem native_second_low_pair_list_integrable {α : Type*}
    (L : List α) (c : α → ℝ) (F : α → (ι → ℝ) → ℝ) (ν : Measure (ι → ℝ))
    (hF : ∀ z ∈ L, Integrable (F z) ν) :
    Integrable (fun y => (L.map (fun z => c z * F z y)).sum) ν := by
  induction L with
  | nil => simp
  | cons z L ih =>
    exact ((hF z List.mem_cons_self).const_mul (c z)).add
      (ih (fun z hz => hF z (List.mem_cons_of_mem _ hz)))

omit [Fintype ι] in
private theorem native_second_low_pair_list_integral {α : Type*}
    (L : List α) (c : α → ℝ) (F : α → (ι → ℝ) → ℝ) (ν : Measure (ι → ℝ))
    (hF : ∀ z ∈ L, Integrable (F z) ν) :
    (L.map (fun z => c z * ∫ y, F z y ∂ν)).sum =
      ∫ y, (L.map (fun z => c z * F z y)).sum ∂ν := by
  induction L with
  | nil => simp
  | cons z L ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [integral_add ((hF z List.mem_cons_self).const_mul (c z))
      (native_second_low_pair_list_integrable L c F ν (fun z hz => hF z (List.mem_cons_of_mem _ hz))),
      integral_const_mul,← ih (fun z hz => hF z (List.mem_cons_of_mem _ hz))]

def nativeSecondLowHighOldDependentDisorderPair
    (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (s : T.Slot) (star : ℕ) (a : ℝ)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (P : T.Assignment → ℝ)
    (u z : T.Assignment → ι → ℝ) (x : ι → ℝ) : ℝ :=
  ((nativeHighMarkedRows T s star a).map fun p => p.coeff *
    ((nativeHighMarkedRows p.tree (p.embed s) star a).map fun r => r.coeff *
      r.tree.disorderExpect w φ v q (fun σ =>
        let old := p.restrict (r.restrict σ)
        P old * (φ (p.spin (r.restrict σ)) (u old) * φ (r.spin σ) (z old))) x).sum).sum

theorem native_second_low_high_old_dependent_disorder_pair_eq_integral
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (s : T.Slot) (star : ℕ)
    (a : ℝ) (ho : MassOrdered a as) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (P : T.Assignment → ℝ) (u z : T.Assignment → ι → ℝ) (x : ι → ℝ) :
    nativeSecondLowHighOldDependentDisorderPair w φ T s star a v q P u z x =
      ∫ y, nativeSecondLowHighOldDependentPair w φ T s star a
        (cumulativeIncrements (q 0) (fun j => q (j+1))) P u z (x+y)
        ∂(Measure.pi fun i => gaussianReal 0 (Real.toNNReal (q 0 i-v i))) := by
  let qs := cumulativeIncrements (q 0) (fun j => q (j+1))
  let ν := Measure.pi fun i => gaussianReal 0 (Real.toNNReal (q 0 i-v i))
  let F := fun (p : MarkedPlacement T) (r : MarkedPlacement p.tree) y =>
    r.tree.expect w φ qs (fun σ =>
      let old := p.restrict (r.restrict σ)
      P old * (φ (p.spin (r.restrict σ)) (u old) * φ (r.spin σ) (z old))) (x+y)
  have hF (p : MarkedPlacement T) (r : MarkedPlacement p.tree) : Integrable (F p r) ν := by
    have HE : (fun y => r.tree.expect w φ qs (fun σ =>
        let old := p.restrict (r.restrict σ)
        P old * (φ (p.spin (r.restrict σ)) (u old) * φ (r.spin σ) (z old))) y) =
      (r.tree.realize qs).expect w φ (fun σ =>
        let τ := (r.tree.assignmentEquiv qs).symm σ
        let old := p.restrict (r.restrict τ)
        P old * (φ (p.spin (r.restrict τ)) (u old) * φ (r.spin τ) (z old))) := by
      funext y
      exact r.tree.expect_realize w φ qs _ y
    have HH := (r.tree.realize qs).expect_smooth hw φ (clockSteps_ordered ho qs)
      (fun σ =>
        let τ := (r.tree.assignmentEquiv qs).symm σ
        let old := p.restrict (r.restrict τ)
        P old * (φ (p.spin (r.restrict τ)) (u old) * φ (r.spin τ) (z old))) 0
    rw [← HE] at HH
    exact HH.integrable_zero_shift x
  unfold nativeSecondLowHighOldDependentDisorderPair nativeSecondLowHighOldDependentPair
  simp_rw [disorderExpect_integral hw φ _ ho,zeroContinuation]
  change ((nativeHighMarkedRows T s star a).map fun p => p.coeff *
    ((nativeHighMarkedRows p.tree (p.embed s) star a).map fun r => r.coeff * ∫ y, F p r y ∂ν).sum).sum = _
  simp_rw [native_second_low_pair_list_integral _ (fun r : MarkedPlacement _ => r.coeff) _ ν
    (fun r _ => hF _ r)]
  exact native_second_low_pair_list_integral (nativeHighMarkedRows T s star a) (fun p => p.coeff)
    (fun p y => ((nativeHighMarkedRows p.tree (p.embed s) star a).map fun r => r.coeff * F p r y).sum) ν
    (fun p _ => native_second_low_pair_list_integrable _ (fun r => r.coeff) (F p) ν (fun r _ => hF p r))

theorem native_second_low_high_old_dependent_disorder_pair_symm
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (s : T.Slot) (star : ℕ)
    (a : ℝ) (ho : MassOrdered a as) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (P : T.Assignment → ℝ) (u z : T.Assignment → ι → ℝ) (x : ι → ℝ) :
    nativeSecondLowHighOldDependentDisorderPair w φ T s star a v q P u z x =
      nativeSecondLowHighOldDependentDisorderPair w φ T s star a v q P z u x := by
  rw [native_second_low_high_old_dependent_disorder_pair_eq_integral hw φ T s star a ho,
    native_second_low_high_old_dependent_disorder_pair_eq_integral hw φ T s star a ho]
  apply integral_congr_ae
  filter_upwards with y
  exact native_second_low_high_old_dependent_pair_symm hw φ T s star a ho _ P u z (x+y)

end OAI.SKFluctuations.Hierarchy.ClockTree
