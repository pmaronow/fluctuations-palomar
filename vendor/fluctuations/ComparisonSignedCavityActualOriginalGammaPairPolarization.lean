module

public import ComparisonSignedCavityActualOriginalGeneratedGPolarization
public import ComparisonSignedCavityActualFullMarkedExchange

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree
open scoped BigOperators NNReal
set_option maxHeartbeats 22000000
set_option backward.isDefEq.respectTransparency false

theorem native_original_singleton_pair_displacement_polarization (n : ℕ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (s t : T.Slot) (k : ℕ) (ht : t≠s)
    (h : ∀c : T.Slot,k ≤ T.splitIndex s c→c=s)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (hh : k ≤ p.tree.splitIndex (p.embed s) p.mark)
    (A : (Spin n×Bool)→(Spin n×Bool)→ℝ) (P : T.Assignment→ℝ) :
    p.tree.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>(A (p.spin σ) (T.atSlot (p.restrict σ) t)-
        A (T.atSlot (p.restrict σ) s) (T.atSlot (p.restrict σ) t))*P (p.restrict σ)) x=
      (1/2:ℝ)*p.tree.disorderExpect (fullWeight n) (fullFeature n) v q
        (fun σ=>(A (p.spin σ) (T.atSlot (p.restrict σ) t)-
          A (T.atSlot (p.restrict σ) s) (T.atSlot (p.restrict σ) t))*
          (P (p.restrict σ)-P (nativeReplaceAtSlot T s (p.restrict σ) (p.spin σ)))) x := by
  let D:=fun σ : p.tree.Assignment=>A (p.spin σ) (T.atSlot (p.restrict σ) t)-
    A (T.atSlot (p.restrict σ) s) (T.atSlot (p.restrict σ) t)
  let F:=fun σ : p.tree.Assignment=>D σ*P (p.restrict σ)
  let G:=fun σ : p.tree.Assignment=>D σ*P (nativeReplaceAtSlot T s (p.restrict σ) (p.spin σ))
  have HE:=native_target_singleton_whole_disorder_exchange T s k h (fullWeight_pos n)
    (fullFeature n) ho p hp hh v q
    (fun σ u=>(A u (T.atSlot σ t)-A (T.atSlot σ s) (T.atSlot σ t))*P σ) x
  have HR : (fun σ : p.tree.Assignment=>
      (A (T.atSlot (p.restrict σ) s)
          (T.atSlot (nativeReplaceAtSlot T s (p.restrict σ) (p.spin σ)) t)-
        A (T.atSlot (nativeReplaceAtSlot T s (p.restrict σ) (p.spin σ)) s)
          (T.atSlot (nativeReplaceAtSlot T s (p.restrict σ) (p.spin σ)) t))*
          P (nativeReplaceAtSlot T s (p.restrict σ) (p.spin σ)))=fun σ=>-G σ := by
    funext σ
    rw [nativeReplaceAtSlot_at,nativeReplaceAtSlot_at]
    simp only [ht,ite_false,ite_true]
    dsimp only [G,D]
    ring
  rw [HR] at HE
  have HQ : (fun σ : p.tree.Assignment=>D σ*(P (p.restrict σ)-
      P (nativeReplaceAtSlot T s (p.restrict σ) (p.spin σ))))=fun σ=>F σ-G σ := by
    funext σ
    dsimp only [F,G]
    ring
  change p.tree.disorderExpect (fullWeight n) (fullFeature n) v q F x=
    (1/2:ℝ)*p.tree.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>D σ*(P (p.restrict σ)-P (nativeReplaceAtSlot T s (p.restrict σ) (p.spin σ)))) x
  rw [HQ]
  change p.tree.disorderExpect (fullWeight n) (fullFeature n) v q F x=
    p.tree.disorderExpect (fullWeight n) (fullFeature n) v q (fun σ=>-G σ) x at HE
  unfold ClockTree.disorderExpect at HE ⊢
  simp only [mul_sub,Finset.sum_sub_distrib,mul_neg,Finset.sum_neg_distrib] at HE ⊢
  linear_combination (1/2:ℝ)*HE

theorem native_actual_generated_original_pair_fresh_displacement_polarization
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k : ℕ} {seed : List NativeResourceMark} {P₀ : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P₀) (hi : i ≤ star) (hs : star < U)
    (ho : MassOrdered 0 as)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (p : MarkedPlacement (nativeFreshAtSlot T 0 P₀.live.test.target star).tree)
    (hp : p∈(nativeFreshAtSlot T 0 P₀.live.test.target star).tree.markedAttach 0)
    (hh : U ≤ p.tree.splitIndex
      (p.embed ((nativeFreshAtSlot T 0 P₀.live.test.target star).embed P₀.live.test.target)) p.mark)
    (A : (Spin n×Bool)→(Spin n×Bool)→ℝ) (P : T.Assignment→ℝ) :
    let g:=nativeFreshAtSlot T 0 P₀.live.test.target star
    p.tree.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>(A (p.spin σ) (g.spin (p.restrict σ))-
        A (T.atSlot (g.restrict (p.restrict σ)) P₀.live.test.target) (g.spin (p.restrict σ)))*
        P (g.restrict (p.restrict σ))) x=
      (1/2:ℝ)*p.tree.disorderExpect (fullWeight n) (fullFeature n) v q
        (fun σ=>(A (p.spin σ) (g.spin (p.restrict σ))-
          A (T.atSlot (g.restrict (p.restrict σ)) P₀.live.test.target) (g.spin (p.restrict σ)))*
          (P (g.restrict (p.restrict σ))-
            P (nativeReplaceAtSlot T P₀.live.test.target (g.restrict (p.restrict σ)) (p.spin σ)))) x := by
  dsimp only
  let g:=nativeFreshAtSlot T 0 P₀.live.test.target star
  have HT : ∀c : g.tree.Slot,star+1 ≤ g.tree.splitIndex (g.embed P₀.live.test.target) c→
      c=g.embed P₀.live.test.target := by
    intro c hc
    have HS : NativeTargetStarSingleton g.tree (g.embed P₀.live.test.target) star:=
      (hP.targetStarSingleton hi).retain_fresh 0 (le_refl star)
    exact HS c (Nat.lt_of_succ_le hc)
  have H:=native_original_singleton_pair_displacement_polarization n v q x g.tree ho
    (g.embed P₀.live.test.target) g.mark (star+1)
    (nativeFreshAtSlot_distinct T 0 P₀.live.test.target star P₀.live.test.target) HT p hp
    (Nat.succ_le_of_lt (hs.trans_le hh)) A (fun σ=>P (g.restrict σ))
  have HR (σ : g.tree.Assignment) (u : Spin n×Bool) :
      g.restrict (nativeReplaceAtSlot g.tree (g.embed P₀.live.test.target) σ u)=
        nativeReplaceAtSlot T P₀.live.test.target (g.restrict σ) u:=
    native_fresh_restrict_replace_old T P₀.live.test.target P₀.live.test.target star σ u
  simp only [←g.spin_at,←g.restrict_at] at H
  simp_rw [HR] at H
  exact H

end OAI.SKFluctuations.Cavity
