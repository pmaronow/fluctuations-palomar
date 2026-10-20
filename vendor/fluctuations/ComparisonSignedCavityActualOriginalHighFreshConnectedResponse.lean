module

public import ComparisonSignedCavityActualOriginalHighFreshPairResponse
public import CavityScalarGammaTopology

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

private theorem connected_gamma_bool_topology
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (U : ℕ) (K : ℕ→ℝ) (s : T.Slot) (p : MarkedPlacement T) :
    scalarGammaFromTopology as U K (p.tree.splitIndex (p.embed s) p.mark)
      (if decide (p.mark=p.embed s) then 1 else 0)=
      fullScalarCutGamma p.tree U K (p.embed s) p.mark := by
  rw [fullScalarCutGamma_marked_eq_topology T ho]
  simp only [MarkedPlacement.hit,decide_eq_true_eq]

private theorem connected_gamma_fresh_preserves
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (U : ℕ) (K : ℕ→ℝ) (s a c : T.Slot) (star : ℕ) :
    let g:=nativeFreshAtSlot T 0 s star
    fullScalarCutGamma g.tree U K (g.embed a) (g.embed c)=fullScalarCutGamma T U K a c :=
  fullScalarCutGamma_marked_preserves T ho U K a c (nativeFreshAtSlot T 0 s star)
    (nativeFreshAtSlot_mem T 0 s star)

theorem native_original_high_fresh_connected_response_row
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (s : T.Slot) (star : ℕ) (hstar : star ≤ as.length)
    (hq : ∀i,Monotone (fun j=>q j i)) (hq0 : ∀i,v i ≤ q 0 i)
    (hK : ∀j,0 ≤ K j) (hKm : Monotone K)
    (Q : T.Assignment→(Spin n×Bool)→(Spin n×Bool)→ℝ) :
    let g:=nativeFreshAtSlot T 0 s star
    ((nativeHighMarkedRows g.tree (g.embed s) star 0).map (fun p=>p.coeff*
      nativeOriginalConnectedHighResponse n v q x U K b C p.tree
        (fun σ=>Q (g.restrict (p.restrict σ)) (p.spin σ) (g.spin (p.restrict σ)))
        (p.embed (g.embed s)) p.mark)).sum=
    ((nativeHighMarkedRows T s star 0).map (fun r=>r.coeff*
      (let g:=nativeFreshAtSlot r.tree 0 (r.embed s) star
      nativeOriginalConnectedHighResponse n v q x U K b C g.tree
        (fun σ=>Q (r.restrict (g.restrict σ)) (r.spin (g.restrict σ)) (g.spin σ))
        (g.embed (r.embed s)) (g.embed r.mark)))).sum := by
  have HP:=native_original_high_fresh_pair_response_row n v q x U K b C T ho s star hstar
    0 0 hq hq0 hK hKm (fun _ _=>1) Q
  simp only [mul_one] at HP
  have HN:=native_original_high_fresh_response_row n v q x U K b C T ho s star hstar
    0 0 hq hq0 hK hKm (fun j hit=>scalarGammaFromTopology as U K j (if hit then 1 else 0)) Q
  dsimp only at HP HN ⊢
  simp only [connected_gamma_bool_topology _ ho] at HN
  unfold nativeOriginalConnectedHighResponse
  simp_rw [connected_gamma_fresh_preserves _ ho]
  simp only [mul_sub,sum_map_sub_explicit,←mul_assoc]
  rw [HP,HN]

end OAI.SKFluctuations.Cavity
