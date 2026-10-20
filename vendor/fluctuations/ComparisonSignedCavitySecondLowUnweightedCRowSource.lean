module

public import ComparisonSignedCavitySecondLowUnweightedCForestSource

@[expose] public section

noncomputable section
set_option maxHeartbeats 30000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal ENNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

 def nativeSecondLowUnweightedCRow (n : ℕ) (q : ℕ→RestCoordinate n→ℝ)
    (U : ℕ) (b h K : ℕ→ℝ) {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (f c z : T.Slot) (P : T.cavityLeft.Assignment→ℝ) : ℝ :=
  ((nativeHighMarkedRows T c (U-1) 0).map fun p=>p.coeff*
    p.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (nativeSecondLowUnweightedCPayload n U b h K T f c z P p) 0).sum

 def nativeSecondLowUnweightedCReplacementRow (n : ℕ) (q : ℕ→RestCoordinate n→ℝ)
    (U : ℕ) (b h K : ℕ→ℝ) {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (f c z : T.Slot) (P : T.cavityLeft.Assignment→ℝ) : ℝ :=
  ((nativeHighMarkedRows T c (U-1) 0).map fun p=>p.coeff*
    p.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (fun τ=>nativeSecondLowUnweightedCPayload n U b h K T f c z P p τ-
        nativeSecondLowUnweightedCOldPayload n U b h K T f c z P (p.restRestrict τ)) 0).sum

 private theorem second_low_unweighted_list_add {α : Type} (L : List α) (F G : α→ℝ) :
    (L.map (fun a=>F a+G a)).sum=(L.map F).sum+(L.map G).sum := by
  induction L with
  | nil=>simp
  | cons a L ih=>simp only [List.map_cons,List.sum_cons,ih];ring

 theorem native_second_low_unweighted_c_eq_old_baseline_add_forest_replacement
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (hU0 : 0<U) (hU : U≤as.length) (f c z : T.Slot) (P : T.cavityLeft.Assignment→ℝ) :
    nativeSecondLowUnweightedCRow n q U b h K T f c z P=
      partitionPoint 0 as U*T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
        (nativeSecondLowUnweightedCOldPayload n U b h K T f c z P) 0+
      nativeSecondLowUnweightedCReplacementRow n q U b h K T f c z P := by
  let B:=T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
    (nativeSecondLowUnweightedCOldPayload n U b h K T f c z P) 0
  have Hpoint (p : MarkedPlacement T) (hp : p∈nativeHighMarkedRows T c (U-1) 0) :
      p.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
        (nativeSecondLowUnweightedCPayload n U b h K T f c z P p) 0=
      B+p.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
        (fun τ=>nativeSecondLowUnweightedCPayload n U b h K T f c z P p τ-
          nativeSecondLowUnweightedCOldPayload n U b h K T f c z P (p.restRestrict τ)) 0 := by
    have hp0:=((mem_nativeHighMarkedRows T c (U-1) 0 p).mp hp).1
    have HM:=native_rest_marked_restrict_preserves n q U b h K T ho
      (nativeSecondLowUnweightedCOldPayload n U b h K T f c z P) p hp0
    change _=B at HM
    rw [←HM]
    unfold ClockTree.disorderExpect
    simp only [mul_sub,Finset.sum_sub_distrib]
    ring
  unfold nativeSecondLowUnweightedCRow nativeSecondLowUnweightedCReplacementRow
  calc
    _=((nativeHighMarkedRows T c (U-1) 0).map fun p=>p.coeff*B+
      p.coeff*p.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
        (fun τ=>nativeSecondLowUnweightedCPayload n U b h K T f c z P p τ-
          nativeSecondLowUnweightedCOldPayload n U b h K T f c z P (p.restRestrict τ)) 0).sum:=by
      apply congrArg List.sum
      apply List.map_congr_left
      intro p hp
      rw [Hpoint p hp,mul_add]
    _= _:=by
      rw [second_low_unweighted_list_add,List.sum_map_mul_right,
        native_high_marked_clock_row_mass T c (U-1) 0 (by omega),show U-1+1=U by omega]

 theorem native_second_low_unweighted_c_payload_grouped_boundary_layers
    (n U : ℕ) (b h K : ℕ→ℝ) {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (f c z : T.Slot) (P : T.cavityLeft.Assignment→ℝ) (p : MarkedPlacement T)
    (τ : p.tree.cavityLeft.Assignment) :
    nativeSecondLowUnweightedCPayload n U b h K T f c z P p τ-
      nativeSecondLowUnweightedCOldPayload n U b h K T f c z P (p.restRestrict τ)=
    let old:=p.restRestrict τ
    let Qf:=fun s=>restLowKernel n U b h (T.splitIndex f c)
      (T.cavityLeft.atSlot old (T.cavityLeftSlot f)) s
    let Qz:=fun s=>restLowKernel n U b h (T.splitIndex c z) s
      (T.cavityLeft.atSlot old (T.cavityLeftSlot z))
    let cold:=T.cavityLeft.atSlot old (T.cavityLeftSlot c)
    P old*((Qf (p.restSpin τ)-Qf cold)*Qz (p.restSpin τ)+
      Qf cold*(Qz (p.restSpin τ)-Qz cold)) := by
  dsimp only
  unfold nativeSecondLowUnweightedCPayload nativeSecondLowUnweightedCOldPayload
  ring

end OAI.SKFluctuations.Cavity
