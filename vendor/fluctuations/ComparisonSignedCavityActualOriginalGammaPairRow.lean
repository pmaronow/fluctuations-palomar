module

public import ComparisonSignedCavityActualOriginalGammaPairPolarization
public import ComparisonSignedCavityActualOriginalForwardSourceAdapters

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

def nativeActualOriginalGammaPairDisplacement {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (star U : ℕ) (K : ℕ→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (A : (Spin n×Bool)→(Spin n×Bool)→ℝ) (P : T.Assignment→ℝ) : ℝ :=
  let g:=nativeFreshAtSlot T 0 s star
  ((g.tree.markedAttach 0).map (fun p=>p.coeff*
    fullScalarCutGamma p.tree U K (p.embed (g.embed s)) p.mark*
    p.tree.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>(A (p.spin σ) (g.spin (p.restrict σ))-
        A (T.atSlot (g.restrict (p.restrict σ)) s) (g.spin (p.restrict σ)))*
        P (g.restrict (p.restrict σ))) x)).sum

def nativeActualOriginalGammaPairResampling {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (star U : ℕ) (K : ℕ→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (A : (Spin n×Bool)→(Spin n×Bool)→ℝ) (P : T.Assignment→ℝ) : ℝ :=
  let g:=nativeFreshAtSlot T 0 s star
  ((g.tree.markedAttach 0).map (fun p=>p.coeff*
    fullScalarCutGamma p.tree U K (p.embed (g.embed s)) p.mark*
    p.tree.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>(A (p.spin σ) (g.spin (p.restrict σ))-
        A (T.atSlot (g.restrict (p.restrict σ)) s) (g.spin (p.restrict σ)))*
        (P (g.restrict (p.restrict σ))-
          P (nativeReplaceAtSlot T s (g.restrict (p.restrict σ)) (p.spin σ)))) x)).sum

theorem native_actual_generated_original_Gamma_pair_polarization
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k : ℕ} {seed : List NativeResourceMark} {P₀ : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P₀) (hi : i ≤ star) (hs : star < U)
    (ho : MassOrdered 0 as) (K : ℕ→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (A : (Spin n×Bool)→(Spin n×Bool)→ℝ) (P : T.Assignment→ℝ) :
    nativeActualOriginalGammaPairDisplacement T P₀.live.test.target star U K v q x A P=
      (1/2:ℝ)*nativeActualOriginalGammaPairResampling T P₀.live.test.target star U K v q x A P := by
  unfold nativeActualOriginalGammaPairDisplacement nativeActualOriginalGammaPairResampling
  dsimp only
  rw [←List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  by_cases hh : U ≤ p.tree.splitIndex
      (p.embed ((nativeFreshAtSlot T 0 P₀.live.test.target star).embed P₀.live.test.target)) p.mark
  · rw [native_actual_generated_original_pair_fresh_displacement_polarization
      hP hi hs ho v q x p hp hh A P]
    ring
  · rw [fullScalarCutGamma_cross_zero p.tree ho U K _ _ hP.highCut_le_length (lt_of_not_ge hh)]
    ring

theorem native_original_fresh_leading_response_eq_full_Gamma_pair_row
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (s : T.Slot) (star : ℕ) (hs : star < U) (hU : U ≤ as.length)
    (P : T.Assignment→ℝ) (A : (Spin n×Bool)→(Spin n×Bool)→ℝ) :
    let g:=nativeFreshAtSlot T 0 s star
    nativeOriginalFreshPartnerLeadingResponse n v q x U K T s star (fun σ c d=>P σ*A c d)=
      ((g.tree.markedAttach 0).map (fun p=>p.coeff*
        fullScalarCutGamma p.tree U K (p.embed (g.embed s)) p.mark*
        p.tree.disorderExpect (fullWeight n) (fullFeature n) v q
          (fun σ=>P (g.restrict (p.restrict σ))*A (p.spin σ) (g.spin (p.restrict σ))) x)).sum := by
  dsimp only
  let g:=nativeFreshAtSlot T 0 s star
  let FL (p : MarkedPlacement g.tree):=p.coeff*
    fullScalarCutGamma p.tree U K (p.embed (g.embed s)) p.mark*
    p.tree.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>P (g.restrict (p.restrict σ))*A (p.spin σ) (g.spin (p.restrict σ))) x
  let FR (r : MarkedPlacement T):=r.coeff*
    fullScalarCutGamma r.tree U K (r.embed s) r.mark*
    (let g:=nativeFreshAtSlot r.tree 0 (r.embed s) star
     g.tree.disorderExpect (fullWeight n) (fullFeature n) v q
       (fun σ=>P (r.restrict (g.restrict σ))*A (r.spin (g.restrict σ)) (g.spin σ)) x)
  have HL:=native_high_row_sum_eq_full_of_support g.tree (g.embed s) star 0 FL (by
    intro p hp hh
    dsimp only [FL]
    rw [fullScalarCutGamma_cross_zero p.tree ho U K _ _ hU (by omega)]
    ring)
  have HR:=native_high_row_sum_eq_full_of_support T s star 0 FR (by
    intro r hr hh
    dsimp only [FR]
    rw [fullScalarCutGamma_cross_zero r.tree ho U K _ _ hU (by omega)]
    ring)
  have HF:=native_original_high_fresh_gamma_expectation_row n v q x U K T ho s star
    (hs.le.trans hU) 0 0 (fun σ c d=>P σ*A c d)
  change ((T.markedAttach 0).map FR).sum=((g.tree.markedAttach 0).map FL).sum
  exact HR.symm.trans (HF.symm.trans HL)

theorem native_actual_generated_original_leading_response_eq_baseline_add_resampling
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k : ℕ} {seed : List NativeResourceMark} {P₀ : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P₀) (hi : i ≤ star) (hs : star < U)
    (ho : MassOrdered 0 as) (K : ℕ→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (A : (Spin n×Bool)→(Spin n×Bool)→ℝ) (P : T.Assignment→ℝ) :
    let s:=P₀.live.test.target
    let g:=nativeFreshAtSlot T 0 s star
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    nativeOriginalFreshPartnerLeadingResponse n v q x U K T s star (fun σ c d=>P σ*A c d)=
      chi*g.tree.disorderExpect (fullWeight n) (fullFeature n) v q
        (fun σ=>P (g.restrict σ)*A (T.atSlot (g.restrict σ) s) (g.spin σ)) x+
      (1/2:ℝ)*nativeActualOriginalGammaPairResampling T s star U K v q x A P := by
  dsimp only
  let s:=P₀.live.test.target
  let g:=nativeFreshAtSlot T 0 s star
  let F:=fun σ : g.tree.Assignment=>P (g.restrict σ)*A (T.atSlot (g.restrict σ) s) (g.spin σ)
  have HB:=native_observed_gamma_full_test_collapse n g.tree ho 0 ho U (by omega) K
    (g.embed s) v q F x
  have HD : nativeOriginalFreshPartnerLeadingResponse n v q x U K T s star (fun σ c d=>P σ*A c d)=
      ((g.tree.markedAttach 0).map (fun p=>p.coeff*
        fullScalarCutGamma p.tree U K (p.embed (g.embed s)) p.mark*
        p.tree.disorderExpect (fullWeight n) (fullFeature n) v q (fun σ=>F (p.restrict σ)) x)).sum+
      nativeActualOriginalGammaPairDisplacement T s star U K v q x A P := by
    rw [native_original_fresh_leading_response_eq_full_Gamma_pair_row n v q x U K T ho
      s star hs hP.highCut_le_length P A]
    unfold nativeActualOriginalGammaPairDisplacement
    dsimp only
    rw [←List.sum_map_add]
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    dsimp only [F]
    unfold ClockTree.disorderExpect
    simp only [Finset.mul_sum]
    rw [←Finset.sum_add_distrib]
    congr 1
    funext σ
    ring
  rw [HB,native_actual_generated_original_Gamma_pair_polarization hP hi hs ho K v q x A P] at HD
  exact HD

end OAI.SKFluctuations.Cavity
