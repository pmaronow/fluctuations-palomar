module

public import ComparisonSignedCavityActualRetainedGammaPairedSource
public import ComparisonSignedCavityHighFreshRowInterchange
public import ComparisonSignedCavityHighRowsSupportReduction
public import ComparisonSignedCavityObservedFreshDisplacementFold
public import CavityScalarGammaTopology

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
set_option maxHeartbeats 14000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {S B ι : Type} [Fintype ι] [Fintype S] [Nonempty S] [Fintype B] [Nonempty B]

omit [Fintype B] [Nonempty B] in
theorem NativeHighFreshRowRelation.rest_disorder_eq {as : List PositiveMass}
    {w : S→ℝ} {φ : S→(ι→ℝ)→L[ℝ]ℝ} {T : ClockTree (S×B) as}
    {s : T.Slot} {star : ℕ} {aFresh : ℝ}
    {p : MarkedPlacement (nativeFreshAtSlot T aFresh s star).tree} {r : MarkedPlacement T}
    (H : NativeHighFreshRowRelation w φ T s star aFresh p r)
    (hw : ∀σ,0<w σ) {a₀ : ℝ} (ho : MassOrdered a₀ as)
    (v : ι→ℝ) (q : ℕ→ι→ℝ) (Q : T.cavityLeft.Assignment→S→S→ℝ) (x : ι→ℝ) :
    p.tree.cavityLeft.disorderExpect w φ v q (fun σ=>Q
      ((nativeFreshAtSlot T aFresh s star).restRestrict (p.restRestrict σ))
      (p.restSpin σ) ((nativeFreshAtSlot T aFresh s star).restSpin (p.restRestrict σ))) x=
    let g:=nativeFreshAtSlot r.tree aFresh (r.embed s) star
    g.tree.cavityLeft.disorderExpect w φ v q (fun σ=>Q (r.restRestrict (g.restRestrict σ))
      (r.restSpin (g.restRestrict σ)) (g.restSpin σ)) x := by
  dsimp only
  rw [←native_star_field_disorder_field_independent _ _ star hw φ ho v q,
    ←native_star_field_disorder_field_independent _ _ star hw φ ho v q]
  unfold nativeStarFieldDisorderMean
  apply integral_congr_ae
  exact Eventually.of_forall fun y=>H.2.2 _ (fun _ σ u z=>Q σ u z) (x+y)

end OAI.SKFluctuations.Hierarchy.ClockTree
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

private theorem retained_fold_gamma_topology
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (U : ℕ) (K : ℕ→ℝ) (s : T.Slot) (p : MarkedPlacement T) :
    scalarGammaFromTopology as U K (p.tree.splitIndex (p.embed s) p.mark)
      (if decide (p.mark=p.embed s) then 1 else 0)=
      fullScalarCutGamma p.tree U K (p.embed s) p.mark := by
  rw [fullScalarCutGamma_marked_eq_topology T ho]
  simp only [MarkedPlacement.hit,decide_eq_true_eq]

theorem native_high_fresh_rest_gamma_expectation_row
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (s : T.Slot) (star U : ℕ) (hstar : star≤as.length) (ho : MassOrdered 0 as)
    (q : ℕ→RestCoordinate n→ℝ) (K : ℕ→ℝ)
    (Q : T.cavityLeft.Assignment→Spin n→Spin n→ℝ) :
    let g:=nativeFreshAtSlot T 0 s star
    ((nativeHighMarkedRows g.tree (g.embed s) star 0).map (fun p=>p.coeff*
      fullScalarCutGamma p.tree U K (p.embed (g.embed s)) p.mark*
      p.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
        (fun σ=>Q (g.restRestrict (p.restRestrict σ)) (p.restSpin σ) (g.restSpin (p.restRestrict σ))) 0)).sum=
    ((nativeHighMarkedRows T s star 0).map (fun r=>r.coeff*
      fullScalarCutGamma r.tree U K (r.embed s) r.mark*
      (let g:=nativeFreshAtSlot r.tree 0 (r.embed s) star
      g.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
        (fun σ=>Q (r.restRestrict (g.restRestrict σ)) (r.restSpin (g.restRestrict σ)) (g.restSpin σ)) 0))).sum := by
  dsimp only
  have H:=native_high_fresh_row_interchange T s star hstar 0 0 (restWeight_pos n) (restFeature n) ho
  apply congrArg List.sum
  apply (show ∀{l₁ l₂ : List ℝ},List.Forall₂ Eq l₁ l₂ → l₁=l₂ from
    fun h=>by simpa only [List.forall₂_eq_eq_eq] using h)
  apply List.rel_map (fun p r h=>?_) H
  have Hlaw:=h.rest_disorder_eq (restWeight_pos n) ho 0 q Q 0
  have Hsplit:=(h.2.1 s).1
  have Hdiag:=congrArg (fun P:Prop=>@decide P (Classical.propDecidable P)) (propext (h.2.1 s).2)
  rw [←retained_fold_gamma_topology _ ho,←retained_fold_gamma_topology _ ho,
    Hsplit,Hdiag,h.1,Hlaw]

theorem native_retained_gamma_paired_row_fresh_fold
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (s : T.Slot) (star U : ℕ) (hs : star<U) (hU : U≤as.length) (ho : MassOrdered 0 as)
    (q : ℕ→RestCoordinate n→ℝ) (K : ℕ→ℝ)
    (A : Spin n→Spin n→ℝ) (P : T.cavityLeft.Assignment→ℝ) :
    let g:=nativeFreshAtSlot T 0 s star
    ((g.tree.markedAttach 0).map (fun p=>p.coeff*
      fullScalarCutGamma p.tree U K (p.embed (g.embed s)) p.mark*
      p.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
        (nativeRestProjectedPairedTest T s star A P p) 0)).sum=
    ((T.markedAttach 0).map (fun r=>r.coeff*
      fullScalarCutGamma r.tree U K (r.embed s) r.mark*
      nativeStarFieldDisorderMean (restWeight n) (restFeature n) r.tree.cavityLeft
        (r.tree.cavityLeftSlot (r.embed s)) star 0 q
        (fun y σ=>(P (r.restRestrict σ)-P (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot s)
          (r.restRestrict σ) (r.restSpin σ)))*
          (nativeStarPairFactor (restWeight n) (restFeature n) as star
            (cumulativeIncrements (q 0) (fun j=>q (j+1))) A y (r.restSpin σ)-
          nativeStarPairFactor (restWeight n) (restFeature n) as star
            (cumulativeIncrements (q 0) (fun j=>q (j+1))) A y
            (T.cavityLeft.atSlot (r.restRestrict σ) (T.cavityLeftSlot s)))) 0)).sum := by
  dsimp only
  let Q:=fun (σ : T.cavityLeft.Assignment) u z=>
    (A u z-A (T.cavityLeft.atSlot σ (T.cavityLeftSlot s)) z)*
      (P σ-P (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot s) σ u))
  have H:=native_high_fresh_rest_gamma_expectation_row T s star U (hs.le.trans hU) ho q K Q
  dsimp only at H
  have Hleft:=native_high_row_sum_eq_full_of_support
    (nativeFreshAtSlot T 0 s star).tree ((nativeFreshAtSlot T 0 s star).embed s) star 0
    (fun p=>p.coeff*fullScalarCutGamma p.tree U K
      (p.embed ((nativeFreshAtSlot T 0 s star).embed s)) p.mark*
      p.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
        (nativeRestProjectedPairedTest T s star A P p) 0) (by
      intro p hp hh
      rw [fullScalarCutGamma_cross_zero p.tree ho U K _ _ hU (by omega),mul_zero,zero_mul])
  rw [←Hleft]
  change _=_ at H
  rw [show ((nativeHighMarkedRows (nativeFreshAtSlot T 0 s star).tree
      ((nativeFreshAtSlot T 0 s star).embed s) star 0).map (fun p=>p.coeff*
      fullScalarCutGamma p.tree U K (p.embed ((nativeFreshAtSlot T 0 s star).embed s)) p.mark*
      p.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
        (nativeRestProjectedPairedTest T s star A P p) 0)).sum=_ from H]
  have Hright:=native_high_row_sum_eq_full_of_support T s star 0
    (fun r=>r.coeff*fullScalarCutGamma r.tree U K (r.embed s) r.mark*
      (let g:=nativeFreshAtSlot r.tree 0 (r.embed s) star
      g.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
        (fun σ=>Q (r.restRestrict (g.restRestrict σ)) (r.restSpin (g.restRestrict σ)) (g.restSpin σ)) 0)) (by
      intro r hr hh
      rw [fullScalarCutGamma_cross_zero r.tree ho U K _ _ hU (by omega),mul_zero,zero_mul])
  rw [Hright]
  apply congrArg List.sum
  apply List.map_congr_left
  intro r hr
  congr 1
  let g:=nativeFreshAtSlot r.tree 0 (r.embed s) star
  rw [←native_star_field_disorder_field_independent g.tree.cavityLeft
    (g.tree.cavityLeftSlot (g.embed (r.embed s))) star (restWeight_pos n) (restFeature n) ho 0 q]
  have HF:=native_star_field_disorder_fresh_displacement_fold r.tree (r.embed s) star (hs.le.trans hU) 0
    (restWeight_pos n) (restFeature n) ho 0 q A
    (fun _ σ=>P (r.restRestrict σ)-P (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot s)
      (r.restRestrict σ) (r.restSpin σ)))
    (fun _ σ=>r.restSpin σ)
    (fun _ σ=>T.cavityLeft.atSlot (r.restRestrict σ) (T.cavityLeftSlot s)) 0
  dsimp only at HF
  rw [←HF]
  apply congrArg (fun J=>nativeStarFieldDisorderMean (restWeight n) (restFeature n) g.tree.cavityLeft
    (g.tree.cavityLeftSlot (g.embed (r.embed s))) star 0 q J 0)
  funext y σ
  dsimp only [Q]
  ring

end OAI.SKFluctuations.Cavity
