module

public import ComparisonSignedCavityStarInnovation

@[expose] public section

noncomputable section
set_option maxHeartbeats 4500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations
open Hierarchy

theorem physical_projection_schedule_with_short_layer (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {c : ℝ} (hs : OrderedSteps c steps)
    {fork t u : ℕ} (htu : t ≤ u) (hu : u ≤ steps.length+1)
    (cs : List (ℝ×ℕ)) (hlast : lastLayerCut cs u=steps.length+1)
    (a D : Fin cs.length→ℝ) {a₀ Dshort D₀ B H xs : ℝ}
    (ha₀ : 0<a₀) (hDshort : D₀ ≤ Dshort) (hDB : Dshort ≤ B)
    (hshort : PhysicalProjectionClock n steps fork t u a₀ Dshort)
    (hanchor : xs+physicalCutMass c steps u ≤ H*a₀^2)
    (hends : ∀ j,cutPredecessor cs u j ≤ (cs.get j).2 ∧ (cs.get j).2 ≤ steps.length+1)
    (hclock : ∀ j,0<a j ∧ D₀ ≤ D j ∧ D j ≤ B ∧
      PhysicalProjectionClock n steps fork (cutPredecessor cs u j) (cs.get j).2 (a j) (D j))
    (hscale : ∀ i j,i ≤ j.succ → xs+physicalCutMass c steps (overlapComponentEnd cs u i) ≤ H*(a j)^2) :
    ∃ a' D' : Fin (((1:ℝ),u)::cs).length→ℝ,
      lastLayerCut (((1:ℝ),u)::cs) t=steps.length+1 ∧
      (∀ j,cutPredecessor (((1:ℝ),u)::cs) t j ≤ ((((1:ℝ),u)::cs).get j).2 ∧
        ((((1:ℝ),u)::cs).get j).2 ≤ steps.length+1) ∧
      (∀ j,0<a' j ∧ D₀ ≤ D' j ∧ D' j ≤ B ∧
        PhysicalProjectionClock n steps fork (cutPredecessor (((1:ℝ),u)::cs) t j)
          ((((1:ℝ),u)::cs).get j).2 (a' j) (D' j)) ∧
      (∀ i j,i ≤ j.succ → xs+physicalCutMass c steps
        (overlapComponentEnd (((1:ℝ),u)::cs) t i) ≤ H*(a' j)^2) := by
  let a' : Fin (((1:ℝ),u)::cs).length→ℝ := Fin.cases a₀ a
  let D' : Fin (((1:ℝ),u)::cs).length→ℝ := Fin.cases Dshort D
  refine ⟨a',D',hlast,?_,?_,?_⟩
  · intro j
    refine Fin.cases ?_ (fun j=>?_) j
    · exact ⟨htu,hu⟩
    · exact hends j
  · intro j
    refine Fin.cases ?_ (fun j=>?_) j
    · exact ⟨ha₀,hDshort,hDB,hshort⟩
    · exact hclock j
  · intro i j
    refine Fin.cases ?_ (fun j=>?_) j
    · refine Fin.cases ?_ (fun i=>?_) i
      · intro _
        exact (add_le_add (le_refl xs) (physicalCutMass_monotone steps hs htu)).trans hanchor
      · intro hij
        have hiv : i.val+1 ≤ 1 := by simpa only [Fin.le_def,Fin.val_succ,Fin.val_zero] using hij
        have hi0 : i=0 := Fin.ext (by simp only [Fin.val_zero]; omega)
        subst i
        exact hanchor
    · refine Fin.cases ?_ (fun i=>?_) i
      · intro _
        exact (add_le_add (le_refl xs) (physicalCutMass_monotone steps hs htu)).trans
          (hscale 0 j (Fin.zero_le _))
      · intro hij
        have hiv : i.val+1 ≤ j.val+1+1 := by simpa only [Fin.le_def,Fin.val_succ] using hij
        have hij' : i ≤ j.succ := by change i.val ≤ j.val+1; omega
        have he : overlapComponentEnd (((1:ℝ),u)::cs) t i.succ=overlapComponentEnd cs u i := by
          refine Fin.cases ?_ (fun i=>?_) i <;> rfl
        change xs+physicalCutMass c steps (overlapComponentEnd (((1:ℝ),u)::cs) t i.succ) ≤ H*(a j)^2
        rw [he]
        exact hscale i j hij'

theorem eventually_physical_projection_error_short_and_later
    (k d : ℕ) (B C : ℝ) {kappa delta : ℝ} (hgap : 2*delta<kappa) :
    ∀ᶠ n : ℕ in atTop,∀ (P : Type) [MeasurableSpace P]
      (steps : List (GaussianStep (FeatureIndex n))) (c D₀ xs H v : ℝ),
      0<D₀ → 0<xs → 0 ≤ H → OrderedSteps c steps →
    ∀ (μ : Measure P) [IsProbabilityMeasure μ] (x : P→FeatureIndex n→ℝ) (hx : Measurable x)
      (fork t u : ℕ) (cs : List (ℝ×ℕ)) (a D : Fin cs.length→ℝ) (a₀ Dshort : ℝ),
      t ≤ u → u ≤ steps.length+1 → lastLayerCut cs u=steps.length+1 →
      0<a₀ → D₀ ≤ Dshort → Dshort ≤ B →
      PhysicalProjectionClock n steps fork t u a₀ Dshort →
      xs+physicalCutMass c steps u ≤ H*a₀^2 →
      (∀ j,cutPredecessor cs u j ≤ (cs.get j).2 ∧ (cs.get j).2 ≤ steps.length+1) →
      (∀ j,0<a j ∧ D₀ ≤ D j ∧ D j ≤ B ∧
        PhysicalProjectionClock n steps fork (cutPredecessor cs u j) (cs.get j).2 (a j) (D j)) →
      (∀ i j,i ≤ j.succ → xs+physicalCutMass c steps (overlapComponentEnd cs u i) ≤ H*(a j)^2) →
      ((cs.length+2:ℕ):ℝ)^4*
        (4*(projectionLpConstant k)^2*(Real.log (n:ℝ))^4*
          (physicalRawRatio n (k+1) steps c xs μ x hx)^2*H/((n:ℝ)*D₀)) ≤
        C*(Real.log (n:ℝ))^d*(n:ℝ)^(-kappa)*v^2 →
      physicalOverlapProjectionErrorMoment n (k+1) steps μ x hx fork t ≤
        ((n:ℝ)^(-delta)*v)^(2*(k+1)) := by
  filter_upwards [eventually_physical_projection_error_polynomial k d B C hgap] with n hn
  intro P _ steps c D₀ xs H v hD₀ hxs hH hs μ _ x hx fork t u cs a D a₀ Dshort
    htu hu hlast ha₀ hDshort hDB hshort hanchor hends hclock hscale hbase
  obtain ⟨a',D',hlast',hends',hclock',hscale'⟩ := physical_projection_schedule_with_short_layer
    n steps hs htu hu cs hlast a D ha₀ hDshort hDB hshort hanchor hends hclock hscale
  apply hn P steps c D₀ xs H v hD₀ hxs hH hs μ x hx (((1:ℝ),u)::cs) fork t a' D'
    (htu.trans hu) hlast' hends' hclock' hscale'
  have hcard : (((physicalOverlapResidualPairs (((1:ℝ),u)::cs)).card:ℝ))^2 ≤
      ((cs.length+2:ℕ):ℝ)^4 := by
    have H := pow_le_pow_left₀ (Nat.cast_nonneg ((physicalOverlapResidualPairs (((1:ℝ),u)::cs)).card))
      (show (((physicalOverlapResidualPairs (((1:ℝ),u)::cs)).card:ℝ)) ≤ ((cs.length+2:ℕ):ℝ)^2 by
        exact_mod_cast physicalOverlapResidualPairs_card_le (((1:ℝ),u)::cs)) 2
    simpa only [←pow_mul] using H
  exact (mul_le_mul_of_nonneg_right hcard (by positivity)).trans hbase

end OAI.SKFluctuations
