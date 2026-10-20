module

public import ComparisonSignedCavityActualGammaFirstHighPairedSource

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 22000000

theorem native_actual_generated_retained_gamma_row_polarization
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k : ℕ} {seed : List NativeResourceMark} {P₀ : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P₀) (hi : i ≤ star) (hs : star < U)
    (ho : MassOrdered 0 as) (q : ℕ→RestCoordinate n→ℝ) (K : ℕ→ℝ)
    (p : MarkedPlacement (nativeFreshAtSlot T 0 P₀.live.test.target star).tree)
    (hp : p∈(nativeFreshAtSlot T 0 P₀.live.test.target star).tree.markedAttach 0)
    (hpH : U ≤ p.tree.splitIndex
      (p.embed ((nativeFreshAtSlot T 0 P₀.live.test.target star).embed P₀.live.test.target)) p.mark)
    (A : Spin n→Spin n→ℝ) (P : T.cavityLeft.Assignment→ℝ) :
    p.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (nativeRestProjectedDisplacementTest T P₀.live.test.target star A P p) 0=
      (1/2:ℝ)*p.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
        (nativeRestProjectedPairedTest T P₀.live.test.target star A P p) 0 := by
  have H:=native_actual_generated_original_pair_fresh_displacement_polarization hP hi hs ho
    0 (cutFullVariance n q U 0 0 (fun _=>0) (fun _=>0) K) 0 p hp hpH
    (fun σ τ=>A σ.1 τ.1) (fun σ=>P (T.cavityAssignment σ).1)
  have H' : p.tree.disorderExpect (fullWeight n) (fullFeature n) 0
      (cutFullVariance n q U 0 0 (fun _=>0) (fun _=>0) K)
      (fun σ=>nativeRestProjectedDisplacementTest T P₀.live.test.target star A P p
        (p.tree.cavityAssignment σ).1) 0=
      (1/2:ℝ)*p.tree.disorderExpect (fullWeight n) (fullFeature n) 0
        (cutFullVariance n q U 0 0 (fun _=>0) (fun _=>0) K)
        (fun σ=>nativeRestProjectedPairedTest T P₀.live.test.target star A P p
          (p.tree.cavityAssignment σ).1) 0:=by
    simpa only [←native_rest_projected_displacement_test_actual,
      ←native_rest_projected_paired_test_actual] using H
  rw [native_decoupled_rest_expect n q U (fun _=>0) (fun _=>0) K p.tree ho,
    native_decoupled_rest_expect n q U (fun _=>0) (fun _=>0) K p.tree ho] at H'
  exact H'

theorem native_actual_generated_retained_gamma_eq_paired_source
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k : ℕ} {seed : List NativeResourceMark} {P₀ : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P₀) (hi : i ≤ star) (hs : star < U)
    (ho : MassOrdered 0 as) (q : ℕ→RestCoordinate n→ℝ) (K : ℕ→ℝ)
    (A : Spin n→Spin n→ℝ) (P : T.cavityLeft.Assignment→ℝ) :
    let g:=nativeFreshAtSlot T 0 P₀.live.test.target star
    nativeRetainedGammaProjectedDisplacement T P₀.live.test.target star U q K A P=
      (1/2:ℝ)*((g.tree.markedAttach 0).map (fun p=>p.coeff*
        fullScalarCutGamma p.tree U K (p.embed (g.embed P₀.live.test.target)) p.mark*
        p.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (nativeRestProjectedPairedTest T P₀.live.test.target star A P p) 0)).sum := by
  dsimp only
  unfold nativeRetainedGammaProjectedDisplacement
  dsimp only
  rw [←List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  by_cases hpH : U ≤ p.tree.splitIndex
      (p.embed ((nativeFreshAtSlot T 0 P₀.live.test.target star).embed P₀.live.test.target)) p.mark
  · rw [native_actual_generated_retained_gamma_row_polarization hP hi hs ho q K p hp hpH A P]
    ring
  · rw [fullScalarCutGamma_cross_zero p.tree ho U K _ _ hP.highCut_le_length (lt_of_not_ge hpH)]
    ring

theorem native_rest_projected_paired_test_center_independent
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (s : T.Slot) (star : ℕ) (A : Spin n→Spin n→ℝ)
    (P : T.cavityLeft.Assignment→ℝ) (c : ℝ)
    (p : MarkedPlacement (nativeFreshAtSlot T 0 s star).tree) :
    nativeRestProjectedPairedTest T s star A (fun σ=>P σ-c) p=
      nativeRestProjectedPairedTest T s star A P p := by
  funext σ
  dsimp only [nativeRestProjectedPairedTest]
  ring

end OAI.SKFluctuations.Cavity
