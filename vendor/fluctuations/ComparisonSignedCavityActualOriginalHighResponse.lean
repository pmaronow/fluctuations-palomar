module

public import ComparisonSignedCavityActualDummyHighDirection

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
set_option maxHeartbeats 12000000

def nativeOriginalSignedJets (n : ℕ) (v : FullCoordinate n→ℝ)
    (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ) (U : ℕ) (K : ℕ→ℝ) :
    (As : List (ℕ→(Spin n×Bool)→(Spin n×Bool)→ℝ)) → {as : List PositiveMass} →
      (T : ClockTree (Spin n×Bool) as) → (T.Assignment→ℝ) → List T.Slot → ℝ
  | [], _, T, P, es =>
    T.disorderExpect (fullWeight n) (fullFeature n) v q P x*fullScalarCutMoment T U K es
  | A::As, _, T, P, es =>
    ((T.markedAttach 0).map (fun p=>p.coeff*
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*
        nativeOriginalSignedJets n v q x U K As r.tree (ClockTree.profilePairTest P A p r)
          (insertedSiteSlots es p r))).sum)).sum/2

def nativeOriginalConnectedHighResponse (n : ℕ) (v : FullCoordinate n→ℝ)
    (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.Assignment→ℝ) (a c : T.Slot) : ℝ :=
  nativeOriginalSignedJets n v q x U K [nativeOriginalHighKernel n U b C] T P [a,c]-
    fullScalarCutGamma T U K a c*
      nativeOriginalSignedJets n v q x U K [nativeOriginalHighKernel n U b C] T P []

theorem native_original_high_G_expect_eq_kernel {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (U : ℕ) (K b C : ℕ→ℝ) (P : T.Assignment→ℝ) (a c : T.Slot)
    (hU : U ≤ as.length) (p : ClockTree.MarkedPlacement T)
    (r : ClockTree.MarkedPlacement p.tree) :
    r.tree.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>P (p.restrict (r.restrict σ))*nativeOriginalHighGAtom r.tree U K b C
        (r.embed (p.embed a)) (r.embed (p.embed c)) (r.embed p.mark) r.mark σ) x=
      r.tree.disorderExpect (fullWeight n) (fullFeature n) v q
        (ClockTree.profilePairTest P (nativeOriginalHighKernel n U b C) p r) x*
        fullScalarCutConnected4 r.tree U K (r.embed (p.embed a)) (r.embed (p.embed c))
          (r.embed p.mark) r.mark/2 := by
  let A := (1/2:ℝ)*fullScalarCutConnected4 r.tree U K (r.embed (p.embed a))
    (r.embed (p.embed c)) (r.embed p.mark) r.mark
  have He : (fun σ=>P (p.restrict (r.restrict σ))*nativeOriginalHighGAtom r.tree U K b C
        (r.embed (p.embed a)) (r.embed (p.embed c)) (r.embed p.mark) r.mark σ)=
      (fun σ=>A*ClockTree.profilePairTest P (nativeOriginalHighKernel n U b C) p r σ) := by
    funext σ
    rw [native_original_high_G_atom_eq_kernel r.tree ho U K b C _ _ _ _ hU]
    dsimp only [A,ClockTree.profilePairTest]
    rw [r.spin_at,p.spin_at,r.restrict_at]
    ring
  rw [He,r.tree.disorderExpect_const_mul (fullWeight_pos n) (fullFeature n) ho]
  dsimp only [A]
  ring

theorem native_original_G_rows_eq_connected_response
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.Assignment→ℝ) (a c : T.Slot) (hU : U ≤ as.length) :
    ((T.markedAttach 0).map (fun p=>p.coeff*
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*
        r.tree.disorderExpect (fullWeight n) (fullFeature n) v q
          (fun σ=>P (p.restrict (r.restrict σ))*nativeOriginalHighGAtom r.tree U K b C
            (r.embed (p.embed a)) (r.embed (p.embed c)) (r.embed p.mark) r.mark σ) x)).sum)).sum=
      nativeOriginalConnectedHighResponse n v q x U K b C T P a c := by
  simp_rw [native_original_high_G_expect_eq_kernel T ho v q x U K b C P a c hU]
  simp only [div_eq_mul_inv,←mul_assoc,List.sum_map_mul_right]
  let F := fun (p : ClockTree.MarkedPlacement T) (r : ClockTree.MarkedPlacement p.tree)=>
    r.tree.disorderExpect (fullWeight n) (fullFeature n) v q
      (ClockTree.profilePairTest P (nativeOriginalHighKernel n U b C) p r) x*
      fullScalarCutMoment r.tree U K (insertedSiteSlots [a,c] p r)
  let G := fun (p : ClockTree.MarkedPlacement T) (r : ClockTree.MarkedPlacement p.tree)=>
    r.tree.disorderExpect (fullWeight n) (fullFeature n) v q
      (ClockTree.profilePairTest P (nativeOriginalHighKernel n U b C) p r) x*
      fullScalarCutMoment r.tree U K (insertedSiteSlots [] p r)
  have HE : (T.markedAttach 0).map (fun p=>p.coeff*
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*
        r.tree.disorderExpect (fullWeight n) (fullFeature n) v q
          (ClockTree.profilePairTest P (nativeOriginalHighKernel n U b C) p r) x*
        fullScalarCutConnected4 r.tree U K (r.embed (p.embed a)) (r.embed (p.embed c))
          (r.embed p.mark) r.mark)).sum)=
    (T.markedAttach 0).map (fun p=>p.coeff*
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*(F p r-fullScalarCutGamma T U K a c*G p r))).sum) := by
    apply List.map_congr_left
    intro p hp
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro r hr
    unfold fullScalarCutConnected4
    rw [fullScalarCutGamma_double_preserves T ho U K a c p hp r hr]
    simp only [F,G,insertedSiteSlots,List.map_cons,List.map_nil,List.cons_append,List.nil_append,
      fullScalarCutGamma]
    ring
  rw [HE,native_signed_double_sum_sub]
  simp only [nativeOriginalConnectedHighResponse,nativeOriginalSignedJets,F,G]
  ring

theorem native_original_longitudinal_eq_connected_rows
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.Assignment→ℝ) (a : T.Slot) (hU : U ≤ as.length) :
    nativeOriginalLongitudinalPairing n v q x U K b C T P a=
      ((T.markedAttach 0).map (fun p=>p.coeff*
        nativeOriginalConnectedHighResponse n v q x U K b C p.tree
          (fun σ=>P (p.restrict σ)) (p.embed a) p.mark)).sum := by
  unfold nativeOriginalLongitudinalPairing
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  rw [native_original_G_rows_eq_connected_response n v q x U K b C p.tree ho
    (fun σ=>P (p.restrict σ)) (p.embed a) p.mark hU]

end OAI.SKFluctuations.Cavity
