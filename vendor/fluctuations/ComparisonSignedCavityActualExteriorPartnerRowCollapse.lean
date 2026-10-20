module

public import ComparisonSignedCavityActualOriginalFreshPartnerCollapse
public import ComparisonSignedCavityScalarFirstCalibration

@[expose] public section

noncomputable section
set_option maxHeartbeats 22000000
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type}

theorem NativeTargetStarSingleton.retain_outside_mark {as : List PositiveMass}
    {T : ClockTree S as} {s : T.Slot} {star : ℕ}
    (h : NativeTargetStarSingleton T s star) (p : MarkedPlacement T)
    (hp : p∈T.markedAttach 0)
    (hh : p.tree.splitIndex (p.embed s) p.mark ≤ star) :
    NativeTargetStarSingleton p.tree (p.embed s) star := by
  intro c hc
  rcases markedAttach_slot_coverage T 0 p hp c with rfl | ⟨d,rfl⟩
  · omega
  · rw [(T.markedAttach_embed_preserves 0 p hp).2] at hc
    exact congrArg p.embed (h d hc)

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem native_original_singleton_exterior_gamma_row_collapse {n : ℕ}
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (s : T.Slot) (star U : ℕ) (hs : star < U) (hU : U ≤ as.length)
    (h : NativeTargetStarSingleton T s star) (K : ℕ→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (Q : T.Assignment→(Spin n×Bool)→ℝ)
    (hQ : ∀σ u z,Q (nativeReplaceAtSlot T s σ u) z=Q σ z) :
    ((T.markedAttach 0).map (fun p=>p.coeff*
      fullScalarCutGamma p.tree U K (p.embed s) p.mark*
      p.tree.disorderExpect (fullWeight n) (fullFeature n) v q
        (fun σ=>Q (p.restrict σ) (p.spin σ)) x)).sum=
      (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*
        T.disorderExpect (fullWeight n) (fullFeature n) v q
          (fun σ=>Q σ (T.atSlot σ s)) x := by
  have HE : ((T.markedAttach 0).map (fun p=>p.coeff*
      fullScalarCutGamma p.tree U K (p.embed s) p.mark*
      p.tree.disorderExpect (fullWeight n) (fullFeature n) v q
        (fun σ=>Q (p.restrict σ) (p.spin σ)) x)).sum=
      ((T.markedAttach 0).map (fun p=>p.coeff*
        fullScalarCutGamma p.tree U K (p.embed s) p.mark*
        p.tree.disorderExpect (fullWeight n) (fullFeature n) v q
          (fun σ=>Q (p.restrict σ) (T.atSlot (p.restrict σ) s)) x)).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    by_cases hh : U ≤ p.tree.splitIndex (p.embed s) p.mark
    · have Hs : ∀c : T.Slot,star+1 ≤ T.splitIndex s c → c=s := by
        intro c hc
        exact h c (by omega)
      have H:=native_target_singleton_whole_disorder_exchange T s (star+1) Hs
        (fullWeight_pos n) (fullFeature n) ho p hp (by omega) v q Q x
      simp_rw [hQ] at H
      rw [H]
    · rw [fullScalarCutGamma_cross_zero p.tree ho U K (p.embed s) p.mark hU (lt_of_not_ge hh)]
      ring
  rw [HE]
  exact native_observed_gamma_full_test_collapse n T ho 0 ho U (by omega) K s v q
    (fun σ=>Q σ (T.atSlot σ s)) x

theorem native_actual_fresh_high_partner_gamma_row_collapse {n : ℕ}
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (s : T.Slot) (star U : ℕ) (hs : star < U) (hU : U ≤ as.length) (K : ℕ→ℝ)
    (p : MarkedPlacement (nativeFreshAtSlot T 0 s star).tree)
    (hp : p∈(nativeFreshAtSlot T 0 s star).tree.markedAttach 0)
    (hh : U ≤ p.tree.splitIndex (p.embed ((nativeFreshAtSlot T 0 s star).embed s)) p.mark)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (Q : T.Assignment→(Spin n×Bool)→(Spin n×Bool)→ℝ) :
    let g:=nativeFreshAtSlot T 0 s star
    ((p.tree.markedAttach 0).map (fun r=>r.coeff*
      fullScalarCutGamma r.tree U K (r.embed (p.embed g.mark)) r.mark*
      r.tree.disorderExpect (fullWeight n) (fullFeature n) v q
        (fun σ=>Q (g.restrict (p.restrict (r.restrict σ)))
          (p.spin (r.restrict σ)) (r.spin σ)) x)).sum=
      (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*
        p.tree.disorderExpect (fullWeight n) (fullFeature n) v q
          (fun σ=>Q (g.restrict (p.restrict σ)) (p.spin σ) (g.spin (p.restrict σ))) x := by
  dsimp only
  let g:=nativeFreshAtSlot T 0 s star
  have hab : g.tree.splitIndex (g.embed s) g.mark=star := by
    rw [g.tree.splitIndex_symm,nativeFreshAtSlot_split,T.splitIndex_self,
      Nat.min_eq_left (hs.le.trans hU)]
  have Hsplit : p.tree.splitIndex (p.embed g.mark) p.mark=star := by
    have HE : p.tree.splitIndex (p.embed (g.embed s)) (p.embed g.mark)=star := by
      rw [(g.tree.markedAttach_embed_preserves 0 p hp).2,hab]
    have HE' : p.tree.splitIndex (p.embed (g.embed s)) (p.embed g.mark) < U := by omega
    have HB : U ≤ p.tree.splitIndex (p.embed g.mark) (p.embed g.mark) := by
      rw [p.tree.splitIndex_self]
      exact hU
    have HX:=native_cross_split_of_same_cut_blocks p.tree U (p.embed (g.embed s)) (p.embed g.mark)
      p.mark (p.embed g.mark) HE' hh HB
    exact (p.tree.splitIndex_symm _ _).trans (HX.trans HE)
  have Hsingle : NativeTargetStarSingleton p.tree (p.embed g.mark) star :=
    (native_fresh_target_star_singleton T 0 s star).retain_outside_mark p hp Hsplit.le
  have Hmark : p.mark≠p.embed g.mark := by
    intro HE
    rw [HE,p.tree.splitIndex_self] at Hsplit
    omega
  have Hold (σ : p.tree.Assignment) (u : Spin n×Bool) :
      g.restrict (p.restrict (nativeReplaceAtSlot p.tree (p.embed g.mark) σ u))=
        g.restrict (p.restrict σ) := by
    apply T.assignment_ext
    intro c
    rw [g.restrict_at,g.restrict_at,p.restrict_at,p.restrict_at,nativeReplaceAtSlot_at,
      ite_eq_right]
    exact fun HE=>nativeFreshAtSlot_distinct T 0 s star c
      ((g.tree.markedAttach_embed_preserves 0 p hp).1 (HE.symm))
  have Hspin (σ : p.tree.Assignment) (u : Spin n×Bool) :
      p.spin (nativeReplaceAtSlot p.tree (p.embed g.mark) σ u)=p.spin σ := by
    rw [p.spin_at,p.spin_at,nativeReplaceAtSlot_at,ite_eq_right Hmark]
  have H:=native_original_singleton_exterior_gamma_row_collapse p.tree ho (p.embed g.mark)
    star U hs hU Hsingle K v q x (fun σ d=>Q (g.restrict (p.restrict σ)) (p.spin σ) d)
    (by intro σ u d;rw [Hold,Hspin])
  have HE : (fun σ : p.tree.Assignment=>Q (g.restrict (p.restrict σ)) (p.spin σ)
      (p.tree.atSlot σ (p.embed g.mark)))=
    (fun σ=>Q (g.restrict (p.restrict σ)) (p.spin σ) (g.spin (p.restrict σ))) := by
    funext σ
    rw [←p.restrict_at,←g.spin_at]
  rw [HE] at H
  exact H

end OAI.SKFluctuations.Cavity
