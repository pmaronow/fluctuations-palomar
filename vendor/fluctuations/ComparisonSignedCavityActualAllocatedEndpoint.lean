module

public import ComparisonSignedCavityActualMixedLowDefect

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 9000000

def nativeActualHigherAllocatedRemainder (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) : ℝ :=
  (1/2:ℝ)*nativeRetainedCenteredCoefficient n q U b h K T P [a,z] 2 0+
    nativeActualTaylorRemainder n q U b h K T P a z

theorem actual_centered_pair_eq_allocated_G_ledger (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K S : ℕ→ℝ)
    (hKS : ∀ j,K j=h j+b j*S j) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (hq0 : ∀ j i,0 ≤ q j i) (hq : ∀ i,Monotone (fun j=>q j i))
    (hb : ∀ j,0 ≤ b j) (hh : ∀ j,0 ≤ h j) (hK : ∀ j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    (hU : U ≤ as.length) (haz : T.splitIndex a z < U) :
    cutCenteredJet n q U b h K T P (sitePair T a z) 0 0 1 1=
      retainedSignedJets n q U b h K [restCenteredLowKernel n U b S] T P [a,z]+
      nativeGPairLowAllocation n q U b h K T P a z+
      nativeCenteredLowGammaHighLedger n q U b h K S T P a z+
      nativeActualHigherAllocatedRemainder n q U b h K T P a z := by
  have H (k : Fin 4) (r : ℕ) :
      nativeRetainedCenteredCoefficient n q U b h K T P [a,z] k r=
        cutFrozenCenteredJet n q U b h K T P (sitePair T a z) 0 k r 0 := by
    rw [←nativeScalarTest_pair]
    exact (actual_frozen_centered_coefficient_eq_native_retained n q U b h K T ho P [a,z]
      hq0 hq hb hh hK hbm hhm hKm k r).symm
  rw [actual_centered_pair_eq_full_retained_ledger n q U b h K T ho P a z
    hq0 hq hb hh hK hbm hhm hKm hU haz,H 1 0,H 1 1,
    actual_first_low_centered_eq_defect_insertion n q U b h K S hKS T ho P a z
      hq0 hq hb hh hK hbm hhm hKm hU haz,
    actual_first_low_high_centered_eq_G_and_centered_low n q U b h K S hKS T ho P a z
      hq0 hq hb hh hK hbm hhm hKm hU haz]
  unfold nativeActualHigherAllocatedRemainder
  ring

def nativeOriginalSitePairExpectation (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) : ℝ :=
  T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 1 1 b h K)
    (fun σ=>P (T.cavityAssignment σ).1*sitePair T a z (T.cavityAssignment σ).2) 0

def nativeOriginalRestTestExpectation (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) : ℝ :=
  T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 1 1 b h K)
    (fun σ=>P (T.cavityAssignment σ).1) 0

def nativePureScalarEndpointPair (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (a z : T.Slot) : ℝ :=
  T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 1 0 b h K)
    (fun σ=>sitePair T a z (T.cavityAssignment σ).2) 0

theorem native_original_site_pair_eq_centered_add_scalar (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) :
    nativeOriginalSitePairExpectation n q U b h K T P a z=
      cutCenteredJet n q U b h K T P (sitePair T a z) 0 0 1 1+
      nativePureScalarEndpointPair n q U b h K T a z*
        nativeOriginalRestTestExpectation n q U b h K T P := by
  unfold cutCenteredJet
  simp only [productJet3,Fin.val_zero]
  simp only [cutLowJet_zero n q U b h K T ho,map_zero]
  unfold nativeOriginalSitePairExpectation nativePureScalarEndpointPair nativeOriginalRestTestExpectation
  ring

theorem actual_original_site_pair_eq_allocated_G_row (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K S : ℕ→ℝ)
    (hKS : ∀ j,K j=h j+b j*S j) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (hq0 : ∀ j i,0 ≤ q j i) (hq : ∀ i,Monotone (fun j=>q j i))
    (hb : ∀ j,0 ≤ b j) (hh : ∀ j,0 ≤ h j) (hK : ∀ j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    (hU : U ≤ as.length) (haz : T.splitIndex a z < U) :
    nativeOriginalSitePairExpectation n q U b h K T P a z=
      nativePureScalarEndpointPair n q U b h K T a z*
        nativeOriginalRestTestExpectation n q U b h K T P+
      retainedSignedJets n q U b h K [restCenteredLowKernel n U b S] T P [a,z]+
      nativeGPairLowAllocation n q U b h K T P a z+
      nativeCenteredLowGammaHighLedger n q U b h K S T P a z+
      nativeActualHigherAllocatedRemainder n q U b h K T P a z := by
  rw [native_original_site_pair_eq_centered_add_scalar n q U b h K T ho P a z,
    actual_centered_pair_eq_allocated_G_ledger n q U b h K S hKS T ho P a z
      hq0 hq hb hh hK hbm hhm hKm hU haz]
  ring

end OAI.SKFluctuations.Cavity
