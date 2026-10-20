module

public import ComparisonSignedCavityActualOriginalTwoForwardEndpoint
public import ComparisonSignedCavityActualOriginalGammaLeadingCollapse

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 22000000

theorem actual_original_centered_site_pair_eq_forward_sources (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K S : ℕ→ℝ)
    (hKS : ∀j,K j=h j+b j*S j) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (hq0 : ∀j i,0 ≤ q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    (hU0 : 0 < U) (hU : U ≤ as.length) (haz : T.splitIndex a z < U) :
    let Pc:=nativeOriginalCenteredRestTest n q U b h K T P
    nativeOriginalSitePairExpectation n q U b h K T Pc a z=
      (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*
        K (T.splitIndex a z)*
          (nativeOriginalLongitudinalPairing n 0 (cutFullVariance n q U 1 1 b h K) 0 U K b S T
              (fun σ=>Pc (T.cavityAssignment σ).1) a+
            nativeOriginalLongitudinalPairing n 0 (cutFullVariance n q U 1 1 b h K) 0 U K b S T
              (fun σ=>Pc (T.cavityAssignment σ).1) z)+
      nativeOriginalGammaLowForward n 0 (cutFullVariance n q U 1 1 b h K) 0 U K T
        (fun σ=>Pc (T.cavityAssignment σ).1) a z
        (fun σ τ=>restCenteredFixedForkKernel n b S (T.splitIndex a z) 0 σ.1 τ.1)+
      nativeOriginalConnectedLowForward n 0 (cutFullVariance n q U 1 1 b h K) 0 U K b S T
        (fun σ=>Pc (T.cavityAssignment σ).1) a z
        (fun σ τ=>restCenteredFixedForkKernel n b S (T.splitIndex a z) 0 σ.1 τ.1)+
      nativeOriginalConnectedLowForward n 0 (cutFullVariance n q U 1 1 b h K) 0 U K b S T
        (fun σ=>Pc (T.cavityAssignment σ).1) z a
        (fun σ τ=>restCenteredFixedForkKernel n b S (T.splitIndex a z) 0 σ.1 τ.1)+
      nativeActualHigherAllocatedRemainder n q U b h K T Pc a z-
      nativeCenteredLowGammaHighSecondRemainder n q U b h K S T Pc a z-
      nativeCenteredLowGammaLowRestoration n q U b h K S T Pc a z-
      (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*
        K (T.splitIndex a z)*
          (nativeOriginalLongitudinalRestoration n q U b h K S T
              (fun σ=>Pc (T.cavityAssignment σ).1) a+
            nativeOriginalLongitudinalRestoration n q U b h K S T
              (fun σ=>Pc (T.cavityAssignment σ).1) z)-
      nativeOriginalGKernelLowRestoration n q U b h K S T Pc a z (restCenteredLowKernel n U b S) := by
  dsimp only
  have HE:=actual_original_centered_site_pair_eq_two_forward_G_sources n q U b h K S hKS T ho P a z
    hq0 hq hb hh hK hbm hhm hKm hU0 hU haz
  have HC:=native_original_gamma_leading_eq_forward_row n q U b h K S T ho
    (nativeOriginalCenteredRestTest n q U b h K T P) a z hU haz
  dsimp only at HE HC
  rw [HC] at HE
  exact HE

end OAI.SKFluctuations.Cavity
