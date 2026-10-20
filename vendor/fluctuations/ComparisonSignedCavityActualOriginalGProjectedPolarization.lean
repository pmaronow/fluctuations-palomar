module

public import ComparisonSignedCavityActualOriginalHighExchange
public import ComparisonSignedCavityActualProjectedRowOriginalLaw

@[expose] public section

noncomputable section
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators Topology NNReal

theorem native_original_connected_high_test_linear (n : ℕ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (U : ℕ) (K b C : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P Q : T.Assignment→ℝ) (a c : T.Slot) (hU : U ≤ as.length) (α β : ℝ) :
    nativeOriginalConnectedHighResponse n v q x U K b C T (fun σ=>α*P σ+β*Q σ) a c=
      α*nativeOriginalConnectedHighResponse n v q x U K b C T P a c+
      β*nativeOriginalConnectedHighResponse n v q x U K b C T Q a c := by
  rw [←native_original_G_rows_eq_connected_response n v q x U K b C T ho _ a c hU,
    ←native_original_G_rows_eq_connected_response n v q x U K b C T ho P a c hU,
    ←native_original_G_rows_eq_connected_response n v q x U K b C T ho Q a c hU]
  have HI (p : MarkedPlacement T) (r : MarkedPlacement p.tree) :
      r.tree.disorderExpect (fullWeight n) (fullFeature n) v q
        (fun σ=>(α*P (p.restrict (r.restrict σ))+β*Q (p.restrict (r.restrict σ)))*
          nativeOriginalHighGAtom r.tree U K b C (r.embed (p.embed a)) (r.embed (p.embed c))
            (r.embed p.mark) r.mark σ) x=
      α*r.tree.disorderExpect (fullWeight n) (fullFeature n) v q
        (fun σ=>P (p.restrict (r.restrict σ))*nativeOriginalHighGAtom r.tree U K b C
          (r.embed (p.embed a)) (r.embed (p.embed c)) (r.embed p.mark) r.mark σ) x+
      β*r.tree.disorderExpect (fullWeight n) (fullFeature n) v q
        (fun σ=>Q (p.restrict (r.restrict σ))*nativeOriginalHighGAtom r.tree U K b C
          (r.embed (p.embed a)) (r.embed (p.embed c)) (r.embed p.mark) r.mark σ) x := by
    unfold ClockTree.disorderExpect
    simp only [mul_add,add_mul,Finset.sum_add_distrib,Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro σ _ <;> ring
  simp_rw [HI]
  simp only [mul_add,List.sum_map_add,mul_left_comm,List.sum_map_mul_left]

theorem native_original_singleton_G_displacement_polarization (n : ℕ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (U : ℕ) (K b C : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (s t : T.Slot) (k : ℕ) (ht : t≠s)
    (h : ∀c : T.Slot,k ≤ T.splitIndex s c→c=s)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (hh : k ≤ p.tree.splitIndex (p.embed s) p.mark)
    (hq : ∀i,Monotone (fun j=>q j i)) (hq0 : ∀i,v i ≤ q 0 i)
    (hK : ∀j,0 ≤ K j) (hKm : Monotone K) (hU : U ≤ as.length)
    (A : (Spin n×Bool)→(Spin n×Bool)→ℝ) (P : T.Assignment→ℝ) :
    nativeOriginalConnectedHighResponse n v q x U K b C p.tree
      (fun σ=>(A (p.spin σ) (T.atSlot (p.restrict σ) t)-
        A (T.atSlot (p.restrict σ) s) (T.atSlot (p.restrict σ) t))*P (p.restrict σ))
      (p.embed s) p.mark=
    (1/2:ℝ)*nativeOriginalConnectedHighResponse n v q x U K b C p.tree
      (fun σ=>(A (p.spin σ) (T.atSlot (p.restrict σ) t)-
        A (T.atSlot (p.restrict σ) s) (T.atSlot (p.restrict σ) t))*
        (P (p.restrict σ)-P (nativeReplaceAtSlot T s (p.restrict σ) (p.spin σ))))
      (p.embed s) p.mark := by
  classical
  let D:=fun σ : p.tree.Assignment=>A (p.spin σ) (T.atSlot (p.restrict σ) t)-
    A (T.atSlot (p.restrict σ) s) (T.atSlot (p.restrict σ) t)
  let F:=fun σ : p.tree.Assignment=>D σ*P (p.restrict σ)
  let G:=fun σ : p.tree.Assignment=>D σ*P (nativeReplaceAtSlot T s (p.restrict σ) (p.spin σ))
  have HE:=native_original_connected_high_whole_exchange n v q x U K b C T ho s k h p hp hh
    hq hq0 hK hKm
    (fun σ u=>(A u (T.atSlot σ t)-A (T.atSlot σ s) (T.atSlot σ t))*P σ)
  have HP : (fun σ : p.tree.Assignment=>
      (A (T.atSlot (p.restrict σ) s)
          (T.atSlot (nativeReplaceAtSlot T s (p.restrict σ) (p.spin σ)) t)-
        A (T.atSlot (nativeReplaceAtSlot T s (p.restrict σ) (p.spin σ)) s)
          (T.atSlot (nativeReplaceAtSlot T s (p.restrict σ) (p.spin σ)) t))*
          P (nativeReplaceAtSlot T s (p.restrict σ) (p.spin σ)))=
      fun σ=>(-1:ℝ)*G σ+0*F σ := by
    funext σ
    rw [nativeReplaceAtSlot_at,nativeReplaceAtSlot_at]
    simp only [ht,ite_false,ite_true]
    dsimp only [G,F,D]
    ring
  rw [HP] at HE
  have HL:=native_original_connected_high_test_linear n v q x U K b C p.tree ho G F
    (p.embed s) p.mark hU (-1) 0
  rw [HL] at HE
  have HR : (fun σ : p.tree.Assignment=>D σ*(P (p.restrict σ)-
      P (nativeReplaceAtSlot T s (p.restrict σ) (p.spin σ))))=
      fun σ=>(1:ℝ)*F σ+(-1)*G σ := by
    funext σ
    dsimp only [F,G]
    ring
  change nativeOriginalConnectedHighResponse n v q x U K b C p.tree F (p.embed s) p.mark=
    (1/2:ℝ)*nativeOriginalConnectedHighResponse n v q x U K b C p.tree
      (fun σ=>D σ*(P (p.restrict σ)-P (nativeReplaceAtSlot T s (p.restrict σ) (p.spin σ))))
      (p.embed s) p.mark
  rw [HR,native_original_connected_high_test_linear n v q x U K b C p.tree ho F G
    (p.embed s) p.mark hU 1 (-1)]
  change nativeOriginalConnectedHighResponse n v q x U K b C p.tree F (p.embed s) p.mark=
    (-1)*nativeOriginalConnectedHighResponse n v q x U K b C p.tree G (p.embed s) p.mark+
      0*nativeOriginalConnectedHighResponse n v q x U K b C p.tree F (p.embed s) p.mark at HE
  linear_combination (1/2:ℝ)*HE

end OAI.SKFluctuations.Cavity
