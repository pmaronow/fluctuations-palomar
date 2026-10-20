module

public import ComparisonSignedCavityActualLongitudinalAllocation
public import ComparisonSignedCavityActualAllocatedEndpoint
public import ComparisonSignedCavityActualGLawRestoration
public import ComparisonSignedCavityLowGammaHighTaylor

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 18000000

theorem actual_original_site_pair_eq_retained_longitudinal_endpoint (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K S : ℕ→ℝ)
    (hKS : ∀j,K j=h j+b j*S j) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (hq0 : ∀j i,0 ≤ q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    (hU0 : 0 < U) (hU : U ≤ as.length) (haz : T.splitIndex a z < U) :
    nativeOriginalSitePairExpectation n q U b h K T P a z=
      nativePureScalarEndpointPair n q U b h K T a z*
        nativeOriginalRestTestExpectation n q U b h K T P+
      (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*
        K (T.splitIndex a z)*
          (nativeRetainedLongitudinalPairing n q U b h K T P a+
            nativeRetainedLongitudinalPairing n q U b h K T P z)+
      nativeCenteredLowGammaHighPath n q U b h K S T P a z 1+
      nativeGKernelLowAllocation n q U b h K T P a z (restCenteredLowKernel n U b S)+
      nativeActualHigherAllocatedRemainder n q U b h K T P a z-
      nativeCenteredLowGammaHighSecondRemainder n q U b h K S T P a z := by
  rw [actual_original_site_pair_eq_allocated_G_row n q U b h K S hKS T ho P a z
    hq0 hq hb hh hK hbm hhm hKm hU haz,
    native_G_low_allocation_eq_longitudinal_add_centered n q U b h K S hKS T ho P a z
      hq0 hq hb hh hK hbm hhm hKm hU0 hU haz]
  have HT:=native_first_low_and_gamma_high_eq_restored_path n q U b h K S T ho P a z
    hq0 hq hb hh hK hbm hhm hKm hU haz
  linear_combination HT

theorem actual_original_site_pair_eq_original_longitudinal_endpoint (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K S : ℕ→ℝ)
    (hKS : ∀j,K j=h j+b j*S j) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (hq0 : ∀j i,0 ≤ q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    (hU0 : 0 < U) (hU : U ≤ as.length) (haz : T.splitIndex a z < U) :
    nativeOriginalSitePairExpectation n q U b h K T P a z=
      nativePureScalarEndpointPair n q U b h K T a z*
        nativeOriginalRestTestExpectation n q U b h K T P+
      (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*
        K (T.splitIndex a z)*
          (nativeOriginalLongitudinalPairing n 0 (cutFullVariance n q U 1 1 b h K) 0 U K b S T
              (fun σ=>P (T.cavityAssignment σ).1) a+
            nativeOriginalLongitudinalPairing n 0 (cutFullVariance n q U 1 1 b h K) 0 U K b S T
              (fun σ=>P (T.cavityAssignment σ).1) z)+
      nativeCenteredLowGammaHighPath n q U b h K S T P a z 1+
      nativeGKernelLowAllocation n q U b h K T P a z (restCenteredLowKernel n U b S)+
      nativeActualHigherAllocatedRemainder n q U b h K T P a z-
      nativeCenteredLowGammaHighSecondRemainder n q U b h K S T P a z-
      (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*
        K (T.splitIndex a z)*
          (nativeOriginalLongitudinalRestoration n q U b h K S T
              (fun σ=>P (T.cavityAssignment σ).1) a+
            nativeOriginalLongitudinalRestoration n q U b h K S T
              (fun σ=>P (T.cavityAssignment σ).1) z) := by
  have HE:=actual_original_site_pair_eq_retained_longitudinal_endpoint n q U b h K S hKS T ho P a z
    hq0 hq hb hh hK hbm hhm hKm hU0 hU haz
  have HA:=native_original_longitudinal_eq_retained_add_restoration n q U b h K S hKS T ho P a hU
    hq0 hq hb hh hK hbm hhm hKm
  have HZ:=native_original_longitudinal_eq_retained_add_restoration n q U b h K S hKS T ho P z hU
    hq0 hq hb hh hK hbm hhm hKm
  rw [HA,HZ]
  linear_combination HE

end OAI.SKFluctuations.Cavity
