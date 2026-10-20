module

public import ComparisonSignedCavityActualOriginalExteriorGammaCollapse
public import ComparisonSignedCavityActualOriginalHighFreshConnectedResponse
public import ComparisonSignedCavityActualOriginalLowOrientation

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 26000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

def nativeOriginalFreshExteriorGSource
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (star : ℕ)
    (Q : T.Assignment→(Spin n×Bool)→(Spin n×Bool)→ℝ) : ℝ :=
  let g:=nativeFreshAtSlot T 0 s star
  ((g.tree.markedAttach 0).map (fun p=>p.coeff*
    ((p.tree.markedAttach 0).map (fun r=>r.coeff*
      fullScalarCutGamma r.tree U K (r.embed (p.embed g.mark)) r.mark*
      nativeOriginalConnectedHighResponse n v q x U K b C r.tree
        (fun σ=>Q (g.restrict (p.restrict (r.restrict σ)))
          (p.spin (r.restrict σ)) (r.spin σ)) (r.embed (p.embed (g.embed s))) (r.embed p.mark))).sum)).sum

def nativeOriginalFreshExteriorGResponse
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (star : ℕ)
    (Q : T.Assignment→(Spin n×Bool)→(Spin n×Bool)→ℝ) : ℝ :=
  ((T.markedAttach 0).map (fun r=>r.coeff*
    (let g:=nativeFreshAtSlot r.tree 0 (r.embed s) star
    nativeOriginalConnectedHighResponse n v q x U K b C g.tree
      (fun σ=>Q (r.restrict (g.restrict σ)) (r.spin (g.restrict σ)) (g.spin σ))
      (g.embed (r.embed s)) (g.embed r.mark)))).sum

private theorem exterior_response_row_mul {A : Type*} (L : List A)
    (w F : A→ℝ) (c : ℝ) :
    (L.map (fun a=>w a*(c*F a))).sum=c*(L.map (fun a=>w a*F a)).sum := by
  induction L with
  | nil=>simp
  | cons a L ih=>simp only [List.map_cons,List.sum_cons,ih];ring

theorem native_original_fresh_forward_Gamma_G_source_eq_chi_response
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (s : T.Slot) (star : ℕ) (hs : star < U) (hU : U ≤ as.length)
    (hq : ∀i,Monotone (fun j=>q j i)) (hq0 : ∀i,v i ≤ q 0 i)
    (hK : ∀j,0 ≤ K j) (hKm : Monotone K)
    (Q : T.Assignment→(Spin n×Bool)→(Spin n×Bool)→ℝ) :
    nativeOriginalFreshExteriorGSource n v q x U K b C T s star Q=
      (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*
        nativeOriginalFreshExteriorGResponse n v q x U K b C T s star Q := by
  let g:=nativeFreshAtSlot T 0 s star
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  let FP (p : MarkedPlacement g.tree) := p.coeff*
    ((p.tree.markedAttach 0).map (fun r=>r.coeff*
      fullScalarCutGamma r.tree U K (r.embed (p.embed g.mark)) r.mark*
      nativeOriginalConnectedHighResponse n v q x U K b C r.tree
        (fun σ=>Q (g.restrict (p.restrict (r.restrict σ)))
          (p.spin (r.restrict σ)) (r.spin σ)) (r.embed (p.embed (g.embed s))) (r.embed p.mark))).sum
  let FL (p : MarkedPlacement g.tree) := p.coeff*
    nativeOriginalConnectedHighResponse n v q x U K b C p.tree
      (fun σ=>Q (g.restrict (p.restrict σ)) (p.spin σ) (g.spin (p.restrict σ)))
      (p.embed (g.embed s)) p.mark
  let FR (r : MarkedPlacement T) := r.coeff*
    (let g:=nativeFreshAtSlot r.tree 0 (r.embed s) star
    nativeOriginalConnectedHighResponse n v q x U K b C g.tree
      (fun σ=>Q (r.restrict (g.restrict σ)) (r.spin (g.restrict σ)) (g.spin σ))
      (g.embed (r.embed s)) (g.embed r.mark))
  have HFPzero (p : MarkedPlacement g.tree)
      (hh : p.tree.splitIndex (p.embed (g.embed s)) p.mark < U) : FP p=0 := by
    dsimp only [FP]
    apply mul_eq_zero_of_right
    apply List.sum_eq_zero
    intro z hz
    obtain ⟨r,hr,rfl⟩:=List.mem_map.mp hz
    have hs : r.tree.splitIndex (r.embed (p.embed (g.embed s))) (r.embed p.mark)<U := by
      rwa [(p.tree.markedAttach_embed_preserves 0 r hr).2]
    rw [native_original_connected_high_cross_zero n v q x U K b C r.tree ho _ _ _ hU hs,mul_zero]
  have HP:=native_high_row_sum_eq_full_of_support g.tree (g.embed s) star 0 FP (by
    intro p hp hh
    exact HFPzero p (by omega))
  have HR:=native_high_row_sum_eq_full_of_support T s star 0 FR (by
    intro r hr hh
    dsimp only [FR]
    rw [native_original_connected_high_cross_zero n v q x U K b C _ ho _ _ _ hU]
    · exact mul_zero _
    · rw [(r.tree.markedAttach_embed_preserves 0 (nativeFreshAtSlot r.tree 0 (r.embed s) star)
          (nativeFreshAtSlot_mem r.tree 0 (r.embed s) star)).2]
      omega)
  have HE : ((nativeHighMarkedRows g.tree (g.embed s) star 0).map FP).sum=
      chi*((nativeHighMarkedRows g.tree (g.embed s) star 0).map FL).sum := by
    rw [←exterior_response_row_mul]
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    have hp0:=((mem_nativeHighMarkedRows g.tree (g.embed s) star 0 p).mp hp).1
    by_cases hh : U ≤ p.tree.splitIndex (p.embed (g.embed s)) p.mark
    · dsimp only [FP]
      rw [native_actual_fresh_high_Gamma_partner_G_row_collapse n v q x U K b C T ho s star
        hs hU p hp0 hh hq hq0 hK hKm Q]
    · rw [HFPzero p (lt_of_not_ge hh),
        native_original_connected_high_cross_zero n v q x U K b C p.tree ho _ _ _ hU
          (lt_of_not_ge hh)]
      ring
  have HF:=native_original_high_fresh_connected_response_row n v q x U K b C T ho s star
    (hs.le.trans hU) hq hq0 hK hKm Q
  change ((g.tree.markedAttach 0).map FP).sum=chi*((T.markedAttach 0).map FR).sum
  exact HP.symm.trans (HE.trans (congrArg (fun z=>chi*z) (HF.trans HR)))

theorem native_original_fresh_forward_exterior_G_eq_chi_response
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (s : T.Slot) (star : ℕ) (hs : star < U) (hU : U ≤ as.length)
    (hq : ∀i,Monotone (fun j=>q j i)) (hq0 : ∀i,v i ≤ q 0 i)
    (hK : ∀j,0 ≤ K j) (hKm : Monotone K)
    (P : T.Assignment→ℝ) (A : (Spin n×Bool)→(Spin n×Bool)→ℝ) :
    let g:=nativeFreshAtSlot T 0 s star
    nativeOriginalConnectedLowForward n v q x U K b C g.tree (fun σ=>P (g.restrict σ))
      (g.embed s) g.mark A=
      (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*
        nativeOriginalFreshExteriorGResponse n v q x U K b C T s star (fun σ c d=>P σ*A c d) := by
  dsimp only
  have H : nativeOriginalConnectedLowForward n v q x U K b C
      (nativeFreshAtSlot T 0 s star).tree (fun σ=>P ((nativeFreshAtSlot T 0 s star).restrict σ))
      ((nativeFreshAtSlot T 0 s star).embed s) (nativeFreshAtSlot T 0 s star).mark A=
      nativeOriginalFreshExteriorGSource n v q x U K b C T s star (fun σ c d=>P σ*A c d) := by
    unfold nativeOriginalConnectedLowForward nativeOriginalFreshExteriorGSource
    simp only [mul_assoc]
  rw [H]
  exact native_original_fresh_forward_Gamma_G_source_eq_chi_response n v q x U K b C T ho s star
    hs hU hq hq0 hK hKm _

end OAI.SKFluctuations.Cavity
