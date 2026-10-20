module

public import ComparisonSignedCavityActualFullMarkedExchange
public import ComparisonSignedCavityObservedGammaCollapse

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

omit [Fintype S] [Nonempty S] in
theorem native_fresh_replace_restrict {as : List PositiveMass}
    (T : ClockTree S as) (s : T.Slot) (star : ℕ)
    (σ : (nativeFreshAtSlot T 0 s star).tree.Assignment) (u : S) :
    let g:=nativeFreshAtSlot T 0 s star
    g.restrict (nativeReplaceAtSlot g.tree g.mark σ u)=g.restrict σ := by
  dsimp only
  apply T.assignment_ext
  intro c
  rw [(nativeFreshAtSlot T 0 s star).restrict_at,(nativeFreshAtSlot T 0 s star).restrict_at,
    nativeReplaceAtSlot_at,ite_eq_right (Ne.symm (nativeFreshAtSlot_distinct T 0 s star c))]

theorem native_fresh_partner_whole_disorder_exchange {as : List PositiveMass}
    (T : ClockTree S as) (s : T.Slot) (star : ℕ)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (ho : MassOrdered 0 as)
    (p : MarkedPlacement (nativeFreshAtSlot T 0 s star).tree)
    (hp : p∈(nativeFreshAtSlot T 0 s star).tree.markedAttach 0)
    (hh : star < p.tree.splitIndex (p.embed (nativeFreshAtSlot T 0 s star).mark) p.mark)
    (v : ι→ℝ) (q : ℕ→ι→ℝ) (Q : T.Assignment→S→ℝ) (x : ι→ℝ) :
    let g:=nativeFreshAtSlot T 0 s star
    p.tree.disorderExpect w φ v q (fun σ=>Q (g.restrict (p.restrict σ)) (p.spin σ)) x=
      p.tree.disorderExpect w φ v q
        (fun σ=>Q (g.restrict (p.restrict σ)) (g.spin (p.restrict σ))) x := by
  dsimp only
  have HS : ∀c : (nativeFreshAtSlot T 0 s star).tree.Slot,
      star+1 ≤ (nativeFreshAtSlot T 0 s star).tree.splitIndex (nativeFreshAtSlot T 0 s star).mark c →
      c=(nativeFreshAtSlot T 0 s star).mark := by
    intro c hc
    exact native_fresh_target_star_singleton T 0 s star c (by omega)
  have HE:=native_target_singleton_whole_disorder_exchange
    (nativeFreshAtSlot T 0 s star).tree (nativeFreshAtSlot T 0 s star).mark (star+1) HS hw φ ho
    p hp (by omega) v q (fun τ u=>Q ((nativeFreshAtSlot T 0 s star).restrict τ) u) x
  simp_rw [native_fresh_replace_restrict T s star,←(nativeFreshAtSlot T 0 s star).spin_at] at HE
  exact HE

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem native_original_fresh_partner_gamma_row_collapse {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as) (s : T.Slot) (star U : ℕ)
    (hs : star < U) (hU : U ≤ as.length) (K : ℕ→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (Q : T.Assignment→(Spin n×Bool)→ℝ) :
    let g:=nativeFreshAtSlot T 0 s star
    ((g.tree.markedAttach 0).map (fun p=>p.coeff*
      fullScalarCutGamma p.tree U K (p.embed g.mark) p.mark*
      p.tree.disorderExpect (fullWeight n) (fullFeature n) v q
        (fun σ=>Q (g.restrict (p.restrict σ)) (p.spin σ)) x)).sum=
      (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*
        g.tree.disorderExpect (fullWeight n) (fullFeature n) v q
          (fun σ=>Q (g.restrict σ) (g.spin σ)) x := by
  dsimp only
  let g:=nativeFreshAtSlot T 0 s star
  have HE : ((g.tree.markedAttach 0).map (fun p=>p.coeff*
      fullScalarCutGamma p.tree U K (p.embed g.mark) p.mark*
      p.tree.disorderExpect (fullWeight n) (fullFeature n) v q
        (fun σ=>Q (g.restrict (p.restrict σ)) (p.spin σ)) x)).sum=
      ((g.tree.markedAttach 0).map (fun p=>p.coeff*
        fullScalarCutGamma p.tree U K (p.embed g.mark) p.mark*
        p.tree.disorderExpect (fullWeight n) (fullFeature n) v q
          (fun σ=>Q (g.restrict (p.restrict σ)) (g.spin (p.restrict σ))) x)).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    by_cases hh : U ≤ p.tree.splitIndex (p.embed g.mark) p.mark
    · rw [native_fresh_partner_whole_disorder_exchange T s star (fullWeight_pos n) (fullFeature n)
        ho p hp (hs.trans_le hh) v q Q x]
    · rw [fullScalarCutGamma_cross_zero p.tree ho U K (p.embed g.mark) p.mark hU (lt_of_not_ge hh)]
      ring
  rw [HE]
  exact native_observed_gamma_full_test_collapse n g.tree ho 0 ho U (by omega) K g.mark v q
    (fun σ=>Q (g.restrict σ) (g.spin σ)) x

end OAI.SKFluctuations.Cavity
