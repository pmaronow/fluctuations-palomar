module

public import ComparisonSignedCavityObservedSecondLowJoin
public import CavityActualScalarRowHessian

@[expose] public section

noncomputable section
set_option maxHeartbeats 3500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem native_observed_rest_marked_preserves (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho0 : MassOrdered 0 as) (a : ℝ) (hoa : MassOrdered a as)
    (P : T.cavityLeft.Assignment→ℝ)
    (p : ClockTree.MarkedPlacement T) (hp : p∈T.markedAttach a) :
    p.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (fun τ=>P (p.restRestrict τ)) 0=
      T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q P 0 := by
  have H:=T.markedAttach_disorderPreserves_actual (fullWeight_pos n) (fullFeature n)
    hoa p hp 0 (cutFullVariance n q U 0 0 b h K)
    (fun σ=>P (T.cavityAssignment σ).1) 0
  simp only [p.restRestrict_actual] at H
  rw [native_decoupled_rest_expect n q U b h K p.tree ho0 (fun τ=>P (p.restRestrict τ)),
    native_decoupled_rest_expect n q U b h K T ho0 P] at H
  exact H

theorem native_observed_gamma_full_test_collapse (n : ℕ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho0 : MassOrdered 0 as) (a : ℝ) (hoa : MassOrdered a as)
    (U : ℕ) (hU0 : 0<U) (K : ℕ→ℝ) (c : T.Slot)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (P : T.Assignment→ℝ) (x : FullCoordinate n→ℝ) :
    ((T.markedAttach a).map (fun p=>p.coeff*
      fullScalarCutGamma p.tree U K (p.embed c) p.mark*
      p.tree.disorderExpect (fullWeight n) (fullFeature n) v q
        (fun σ=>P (p.restrict σ)) x)).sum=
    (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*
      T.disorderExpect (fullWeight n) (fullFeature n) v q P x := by
  have he : ((T.markedAttach a).map (fun p=>p.coeff*
      fullScalarCutGamma p.tree U K (p.embed c) p.mark*
      p.tree.disorderExpect (fullWeight n) (fullFeature n) v q
        (fun σ=>P (p.restrict σ)) x)).sum=
      ((T.markedAttach a).map (fun p=>p.coeff*
        fullScalarCutGamma p.tree U K (p.embed c) p.mark*
        T.disorderExpect (fullWeight n) (fullFeature n) v q P x)).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    rw [T.markedAttach_disorderPreserves_actual (fullWeight_pos n) (fullFeature n)
      hoa p hp v q P x]
  rw [he,List.sum_map_mul_right,native_full_gamma_row_hessian n T ho0 a hoa U hU0 K c]

theorem native_observed_gamma_rest_test_collapse (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho0 : MassOrdered 0 as) (a : ℝ) (hoa : MassOrdered a as)
    (hU0 : 0<U) (c : T.Slot) (P : T.cavityLeft.Assignment→ℝ) :
    ((T.markedAttach a).map (fun p=>p.coeff*
      fullScalarCutGamma p.tree U K (p.embed c) p.mark*
      p.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
        (fun σ=>P (p.restRestrict σ)) 0)).sum=
    (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*
      T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q P 0 := by
  have he : ((T.markedAttach a).map (fun p=>p.coeff*
      fullScalarCutGamma p.tree U K (p.embed c) p.mark*
      p.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
        (fun σ=>P (p.restRestrict σ)) 0)).sum=
      ((T.markedAttach a).map (fun p=>p.coeff*
        fullScalarCutGamma p.tree U K (p.embed c) p.mark*
        T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q P 0)).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    rw [native_observed_rest_marked_preserves n q U b h K T ho0 a hoa P p hp]
  rw [he,List.sum_map_mul_right,native_full_gamma_row_hessian n T ho0 a hoa U hU0 K c]

def nativeObservedGammaRow (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (a : ℝ) (c : T.Slot) (R : T.cavityLeft.Assignment→Spin n→ℝ) : ℝ :=
  ((T.markedAttach a).map (fun p=>p.coeff*
    fullScalarCutGamma p.tree U K (p.embed c) p.mark*
    p.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (fun σ=>R (p.restRestrict σ) (p.restSpin σ)) 0)).sum

def nativeObservedGammaReplacementResidual (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (a : ℝ) (c : T.Slot) (R : T.cavityLeft.Assignment→Spin n→ℝ) : ℝ :=
  ((T.markedAttach a).map (fun p=>p.coeff*
    fullScalarCutGamma p.tree U K (p.embed c) p.mark*
    p.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (fun σ=>R (p.restRestrict σ) (p.restSpin σ)-
        R (p.restRestrict σ)
          (T.cavityLeft.atSlot (p.restRestrict σ) (T.cavityLeftSlot c))) 0)).sum

theorem native_observed_gamma_replacement_coincidence_zero (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (c : T.Slot)
    (R : T.cavityLeft.Assignment→Spin n→ℝ)
    (p : ClockTree.MarkedPlacement T) (hdiag : p.embed c=p.mark) :
    p.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (fun σ=>R (p.restRestrict σ) (p.restSpin σ)-
        R (p.restRestrict σ)
          (T.cavityLeft.atSlot (p.restRestrict σ) (T.cavityLeftSlot c))) 0=0 := by
  have he : (fun σ=>R (p.restRestrict σ) (p.restSpin σ)-
      R (p.restRestrict σ)
        (T.cavityLeft.atSlot (p.restRestrict σ) (T.cavityLeftSlot c)))=fun _=>0 := by
    funext σ
    rw [p.restRestrict_at σ c,hdiag]
    simp only [ClockTree.MarkedPlacement.restSpin,sub_self]
  rw [he]
  simp [ClockTree.disorderExpect]

theorem native_observed_gamma_row_eq_collapsed_add_residual (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho0 : MassOrdered 0 as) (a : ℝ) (hoa : MassOrdered a as)
    (hU0 : 0<U) (c : T.Slot) (R : T.cavityLeft.Assignment→Spin n→ℝ) :
    nativeObservedGammaRow n q U K T a c R=
      (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*
        T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (fun σ=>R σ (T.cavityLeft.atSlot σ (T.cavityLeftSlot c))) 0+
      nativeObservedGammaReplacementResidual n q U K T a c R := by
  let P:=fun σ=>R σ (T.cavityLeft.atSlot σ (T.cavityLeftSlot c))
  have hc := native_observed_gamma_rest_test_collapse n q U b h K T ho0 a hoa hU0 c P
  rw [←hc]
  unfold nativeObservedGammaRow nativeObservedGammaReplacementResidual
  rw [←List.sum_map_add]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  have he : p.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (fun σ=>R (p.restRestrict σ) (p.restSpin σ)-P (p.restRestrict σ)) 0=
      p.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
        (fun σ=>R (p.restRestrict σ) (p.restSpin σ)) 0-
      p.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
        (fun σ=>P (p.restRestrict σ)) 0 := by
    unfold ClockTree.disorderExpect
    simp only [mul_sub,Finset.sum_sub_distrib]
  change _=_+p.coeff*fullScalarCutGamma p.tree U K (p.embed c) p.mark*
    p.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (fun σ=>R (p.restRestrict σ) (p.restSpin σ)-P (p.restRestrict σ)) 0
  rw [he]
  ring

theorem native_observed_gamma_product_difference_exact (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho0 : MassOrdered 0 as) (a : ℝ) (hoa : MassOrdered a as)
    (hU0 : 0<U) (c : T.Slot)
    (P F G : T.cavityLeft.Assignment→ℝ)
    (L : T.cavityLeft.Assignment→Spin n→ℝ) :
    nativeObservedGammaRow n q U K T a c (fun σ e=>P σ*(F σ*L σ e-G σ))=
      (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*
        T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (fun σ=>P σ*(F σ*L σ (T.cavityLeft.atSlot σ (T.cavityLeftSlot c))-G σ)) 0+
      ((T.markedAttach a).map (fun p=>p.coeff*
        fullScalarCutGamma p.tree U K (p.embed c) p.mark*
        p.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (fun σ=>P (p.restRestrict σ)*F (p.restRestrict σ)*
            (L (p.restRestrict σ) (p.restSpin σ)-
              L (p.restRestrict σ)
                (T.cavityLeft.atSlot (p.restRestrict σ) (T.cavityLeftSlot c)))) 0)).sum := by
  rw [native_observed_gamma_row_eq_collapsed_add_residual n q U b h K T ho0 a hoa hU0]
  congr 1
  unfold nativeObservedGammaReplacementResidual
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  congr 1
  congr 1
  funext σ
  ring

end OAI.SKFluctuations.Cavity
