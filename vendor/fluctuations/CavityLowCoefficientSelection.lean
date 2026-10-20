module

public import CavityCutBlocks
public import CavityGraphSelection

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal

namespace OAI.SKFluctuations.Cavity
open Hierarchy

section
variable (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (U : ℕ) (hU0 : 0 < U)
  (t : ℝ) (b h K : ℕ → ℝ) {as : List PositiveMass}
  (T : ClockTree (Spin n × Bool) as) (hU : U ≤ as.length)
  (P : T.cavityLeft.Assignment → ℝ) (x : FullCoordinate n → ℝ)
  (hs : ∀ i, x (.inl (.inr i)) = 0) (hr : ∀ i, x (.inr i) = 0)
include hU0 hs hr

theorem cutDisorderExpect_graph_nonzero_even (es : List T.Slot)
    (hne : T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cutFullVariance n q U 0 t b h K)
      (fun σ => P (T.cavityAssignment σ).1*siteMonomial T σ es) x ≠ 0) :
    letI : DecidableEq (T.CutBlock U hU) := Classical.decEq _
    ∀ z : T.CutBlock U hU, Even ((es.map (T.cutBlock U hU)).count z) := by
  classical
  letI : DecidableEq (T.CutBlock U hU) := Classical.decEq _
  intro z
  obtain ⟨s,rfl⟩ := Quotient.exists_rep z
  change Even ((es.map (T.cutBlock U hU)).count (T.cutBlock U hU s))
  rw [← blockDegree_eq_count_cutBlock T U hU s es]
  by_contra heven
  exact hne (cutDisorderExpect_graph_odd n q U hU0 t b h K T hU s es
    (Nat.not_even_iff_odd.mp heven) P x hs hr)

theorem cutDisorderExpect_one_low_edge_zero (a z c d : T.Slot)
    (haz : ¬ U ≤ T.splitIndex a z) (hcd : ¬ U ≤ T.splitIndex c d)
    (hjoin : ¬ joins (T.cutBlock U hU a) (T.cutBlock U hU z)
      (T.cutBlock U hU c) (T.cutBlock U hU d)) :
    T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 0 t b h K)
      (fun σ => P (T.cavityAssignment σ).1*siteMonomial T σ [a,z,c,d]) x = 0 := by
  classical
  letI : DecidableEq (T.CutBlock U hU) := Classical.decEq _
  by_contra hne
  have heven := cutDisorderExpect_graph_nonzero_even n q U hU0 t b h K T hU P x hs hr
    [a,z,c,d] hne
  have hab' : T.cutBlock U hU a ≠ T.cutBlock U hU z := by
    exact fun h => haz ((T.cutBlock_eq_iff U hU a z).mp h)
  have hcd' : T.cutBlock U hU c ≠ T.cutBlock U hU d := by
    exact fun h => hcd ((T.cutBlock_eq_iff U hU c d).mp h)
  apply hjoin
  apply one_low_edge_selection _ _ _ _ hab' hcd'
  simpa only [List.map_cons, List.map_nil] using heven

theorem cutDisorderExpect_two_low_edges_zero (a z c d e f : T.Slot)
    (haz : ¬ U ≤ T.splitIndex a z) (hcd : ¬ U ≤ T.splitIndex c d)
    (hef : ¬ U ≤ T.splitIndex e f)
    (hpath : ¬ ∃ w : T.CutBlock U hU,
      w ≠ T.cutBlock U hU a ∧ w ≠ T.cutBlock U hU z ∧
      ((joins (T.cutBlock U hU a) w (T.cutBlock U hU c) (T.cutBlock U hU d) ∧
        joins w (T.cutBlock U hU z) (T.cutBlock U hU e) (T.cutBlock U hU f)) ∨
       (joins (T.cutBlock U hU a) w (T.cutBlock U hU e) (T.cutBlock U hU f) ∧
        joins w (T.cutBlock U hU z) (T.cutBlock U hU c) (T.cutBlock U hU d)))) :
    T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 0 t b h K)
      (fun σ => P (T.cavityAssignment σ).1*siteMonomial T σ [a,z,c,d,e,f]) x = 0 := by
  classical
  letI : DecidableEq (T.CutBlock U hU) := Classical.decEq _
  by_contra hne
  have heven := cutDisorderExpect_graph_nonzero_even n q U hU0 t b h K T hU P x hs hr
    [a,z,c,d,e,f] hne
  apply hpath
  apply two_low_edges_selection
    (T.cutBlock U hU a) (T.cutBlock U hU z) (T.cutBlock U hU c)
    (T.cutBlock U hU d) (T.cutBlock U hU e) (T.cutBlock U hU f)
    (fun h => haz ((T.cutBlock_eq_iff U hU a z).mp h))
    (fun h => hcd ((T.cutBlock_eq_iff U hU c d).mp h))
    (fun h => hef ((T.cutBlock_eq_iff U hU e f).mp h))
  simpa only [List.map_cons, List.map_nil] using heven

end
end OAI.SKFluctuations.Cavity
