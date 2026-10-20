module

public import ComparisonSignedCavityActualOriginalGProjectedPolarization
public import ComparisonSignedCavityActualTargetSingleton

@[expose] public section

noncomputable section
set_option maxHeartbeats 24000000
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type}

theorem native_fresh_restrict_replace_old {as : List PositiveMass}
    (T : ClockTree S as) (s a : T.Slot) (star : ℕ)
    (σ : (nativeFreshAtSlot T 0 s star).tree.Assignment) (u : S) :
    let g:=nativeFreshAtSlot T 0 s star
    g.restrict (nativeReplaceAtSlot g.tree (g.embed a) σ u)=
      nativeReplaceAtSlot T a (g.restrict σ) u := by
  dsimp only
  apply T.assignment_ext
  intro c
  rw [(nativeFreshAtSlot T 0 s star).restrict_at,nativeReplaceAtSlot_at,nativeReplaceAtSlot_at,
    (nativeFreshAtSlot_old_splits T 0 s star).1.eq_iff,
    (nativeFreshAtSlot T 0 s star).restrict_at]

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators Topology NNReal

theorem native_actual_generated_original_G_fresh_displacement_polarization
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k : ℕ} {seed : List NativeResourceMark} {P₀ : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P₀) (hi : i ≤ star) (hs : star < U)
    (ho : MassOrdered 0 as)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (K b C : ℕ→ℝ)
    (p : MarkedPlacement (nativeFreshAtSlot T 0 P₀.live.test.target star).tree)
    (hp : p∈(nativeFreshAtSlot T 0 P₀.live.test.target star).tree.markedAttach 0)
    (hh : U ≤ p.tree.splitIndex
      (p.embed ((nativeFreshAtSlot T 0 P₀.live.test.target star).embed P₀.live.test.target)) p.mark)
    (hq : ∀j,Monotone (fun u=>q u j)) (hq0 : ∀j,v j ≤ q 0 j)
    (hK : ∀j,0 ≤ K j) (hKm : Monotone K)
    (A : (Spin n×Bool)→(Spin n×Bool)→ℝ) (P : T.Assignment→ℝ) :
    let g:=nativeFreshAtSlot T 0 P₀.live.test.target star
    nativeOriginalConnectedHighResponse n v q x U K b C p.tree
      (fun σ=>(A (p.spin σ) (g.spin (p.restrict σ))-
        A (T.atSlot (g.restrict (p.restrict σ)) P₀.live.test.target) (g.spin (p.restrict σ)))*
        P (g.restrict (p.restrict σ))) (p.embed (g.embed P₀.live.test.target)) p.mark=
      (1/2:ℝ)*nativeOriginalConnectedHighResponse n v q x U K b C p.tree
        (fun σ=>(A (p.spin σ) (g.spin (p.restrict σ))-
          A (T.atSlot (g.restrict (p.restrict σ)) P₀.live.test.target) (g.spin (p.restrict σ)))*
          (P (g.restrict (p.restrict σ))-
            P (nativeReplaceAtSlot T P₀.live.test.target (g.restrict (p.restrict σ)) (p.spin σ))))
        (p.embed (g.embed P₀.live.test.target)) p.mark := by
  dsimp only
  let g:=nativeFreshAtSlot T 0 P₀.live.test.target star
  have HT : ∀c : g.tree.Slot,star+1 ≤ g.tree.splitIndex (g.embed P₀.live.test.target) c →
      c=g.embed P₀.live.test.target := by
    intro c hc
    have HS : NativeTargetStarSingleton g.tree (g.embed P₀.live.test.target) star :=
      (hP.targetStarSingleton hi).retain_fresh 0 (le_refl star)
    exact HS c (Nat.lt_of_succ_le hc)
  have HH : star+1 ≤ p.tree.splitIndex (p.embed (g.embed P₀.live.test.target)) p.mark :=
    Nat.succ_le_of_lt (hs.trans_le hh)
  have H:=native_original_singleton_G_displacement_polarization n v q x U K b C g.tree ho
    (g.embed P₀.live.test.target) g.mark (star+1)
    (nativeFreshAtSlot_distinct T 0 P₀.live.test.target star P₀.live.test.target) HT p hp
    HH hq hq0 hK hKm hP.highCut_le_length A (fun σ=>P (g.restrict σ))
  have HR (σ : g.tree.Assignment) (u : Spin n×Bool) :
      g.restrict (nativeReplaceAtSlot g.tree (g.embed P₀.live.test.target) σ u)=
        nativeReplaceAtSlot T P₀.live.test.target (g.restrict σ) u :=
    native_fresh_restrict_replace_old T P₀.live.test.target P₀.live.test.target star σ u
  simp only [←g.spin_at,←g.restrict_at] at H
  simp_rw [HR] at H
  exact H

end OAI.SKFluctuations.Cavity
