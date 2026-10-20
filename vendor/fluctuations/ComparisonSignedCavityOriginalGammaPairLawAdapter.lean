module

public import ComparisonSignedCavityOriginalGammaProjectedSourceAdapter
public import ComparisonSignedCavityActualOriginalGammaPairRow

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 16000000

theorem native_original_gamma_projected_displacement_eq_actual_pair {n : ℕ}
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (s : T.Slot) (star U : ℕ) (K : ℕ→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (A : (Spin n×Bool)→(Spin n×Bool)→ℝ) (P : T.Assignment→ℝ) :
    nativeOriginalGammaProjectedDisplacement T s star U K v q x A P=
      nativeActualOriginalGammaPairDisplacement T s star U K v q x A P := by
  unfold nativeOriginalGammaProjectedDisplacement nativeOriginalGammaWeightedExpectation
    nativeActualOriginalGammaPairDisplacement
  dsimp only
  simp only [mul_assoc]

theorem native_actual_original_Gamma_pair_half_eq_rest_first_high_and_remainders
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k : ℕ} {seed : List NativeResourceMark} {P₀ : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P₀) (hi : i ≤ star) (hs : star < U)
    (ho : MassOrdered 0 as)
    (q : ℕ→RestCoordinate n→ℝ) (b h K : ℕ→ℝ)
    (A : Spin n→Spin n→ℝ) (P : T.cavityLeft.Assignment→ℝ)
    (hq0 : ∀j i,0 ≤ q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    (1/2:ℝ)*nativeActualOriginalGammaPairResampling T P₀.live.test.target star U K 0
      (cutFullVariance n q U 1 1 b h K) 0 (fun σ τ=>A σ.1 τ.1)
      (fun σ=>P (T.cavityAssignment σ).1)=
      nativeRetainedGammaProjectedDisplacement T P₀.live.test.target star U q K A P+
      nativeGammaProjectedFirstHighDisplacement T P₀.live.test.target star U q b h K A P+
      nativeGammaProjectedHighSecondRestoration T P₀.live.test.target star U q b h K A P+
      nativeGammaProjectedLowSecondRestoration T P₀.live.test.target star U q b h K A P := by
  rw [←native_actual_generated_original_Gamma_pair_polarization hP hi hs ho K 0
    (cutFullVariance n q U 1 1 b h K) 0 (fun σ τ=>A σ.1 τ.1)
    (fun σ=>P (T.cavityAssignment σ).1),
    ←native_original_gamma_projected_displacement_eq_actual_pair T P₀.live.test.target star U K 0
      (cutFullVariance n q U 1 1 b h K) 0 (fun σ τ=>A σ.1 τ.1)
      (fun σ=>P (T.cavityAssignment σ).1)]
  exact native_original_gamma_projected_displacement_eq_retained_first_high_and_remainders n T ho
    P₀.live.test.target star U q b h K hP.highCut_le_length A P hq0 hq hb hh hK hbm hhm hKm

end OAI.SKFluctuations.Cavity
