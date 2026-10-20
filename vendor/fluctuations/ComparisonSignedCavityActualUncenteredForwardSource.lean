module

public import ComparisonSignedCavityActualFreshForwardSource

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 24000000

theorem actual_original_uncentered_site_pair_gap_eq_forward_sources (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K S : ℕ→ℝ)
    (hKS : ∀j,K j=h j+b j*S j) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (hq0 : ∀j i,0 ≤ q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    (hU0 : 0 < U) (hU : U ≤ as.length) (haz : T.splitIndex a z < U) :
    nativeOriginalSitePairExpectation n q U b h K T P a z-
      nativePureScalarEndpointPair n q U b h K T a z*
        nativeOriginalRestTestExpectation n q U b h K T P=
      (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*
        K (T.splitIndex a z)*
          (nativeOriginalLongitudinalPairing n 0 (cutFullVariance n q U 1 1 b h K) 0 U K b S T
              (fun σ=>P (T.cavityAssignment σ).1) a+
            nativeOriginalLongitudinalPairing n 0 (cutFullVariance n q U 1 1 b h K) 0 U K b S T
              (fun σ=>P (T.cavityAssignment σ).1) z)+
      nativeOriginalGammaLowForward n 0 (cutFullVariance n q U 1 1 b h K) 0 U K T
        (fun σ=>P (T.cavityAssignment σ).1) a z
        (fun σ τ=>restCenteredFixedForkKernel n b S (T.splitIndex a z) 0 σ.1 τ.1)+
      nativeOriginalConnectedLowForward n 0 (cutFullVariance n q U 1 1 b h K) 0 U K b S T
        (fun σ=>P (T.cavityAssignment σ).1) a z
        (fun σ τ=>restCenteredFixedForkKernel n b S (T.splitIndex a z) 0 σ.1 τ.1)+
      nativeOriginalConnectedLowForward n 0 (cutFullVariance n q U 1 1 b h K) 0 U K b S T
        (fun σ=>P (T.cavityAssignment σ).1) z a
        (fun σ τ=>restCenteredFixedForkKernel n b S (T.splitIndex a z) 0 σ.1 τ.1)+
      nativeActualHigherAllocatedRemainder n q U b h K T P a z-
      nativeCenteredLowGammaHighSecondRemainder n q U b h K S T P a z-
      nativeCenteredLowGammaLowRestoration n q U b h K S T P a z-
      (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*
        K (T.splitIndex a z)*
          (nativeOriginalLongitudinalRestoration n q U b h K S T
              (fun σ=>P (T.cavityAssignment σ).1) a+
            nativeOriginalLongitudinalRestoration n q U b h K S T
              (fun σ=>P (T.cavityAssignment σ).1) z)-
      nativeOriginalGKernelLowRestoration n q U b h K S T P a z (restCenteredLowKernel n U b S) := by
  have HE:=actual_original_site_pair_eq_original_longitudinal_endpoint n q U b h K S hKS T ho P a z
    hq0 hq hb hh hK hbm hhm hKm hU0 hU haz
  have HL:=native_centered_low_gamma_original_leading_eq_path_add_low_restoration n q U b h K S T ho
    P a z hq0 hq hb hh hK hbm hhm hKm hU
  have HG:=native_original_G_low_allocation_eq_retained_add_restoration n q U b h K S hKS T ho
    P a z (restCenteredLowKernel n U b S) hU hq0 hq hb hh hK hbm hhm hKm
  have HC:=native_original_gamma_leading_eq_forward_row n q U b h K S T ho P a z hU haz
  have HF:=native_original_four_G_low_eq_two_forward_rows n q U b h K S T ho P a z hU haz
  dsimp only at HC HF
  rw [HC] at HL
  rw [HF] at HG
  linear_combination HE-HL-HG

end OAI.SKFluctuations.Cavity
