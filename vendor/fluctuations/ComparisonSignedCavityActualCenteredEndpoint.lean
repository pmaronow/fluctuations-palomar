module

public import ComparisonSignedCavityActualLongitudinalEndpoint
public import ComparisonSignedCavityActualMinimumSiteRestoration

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 18000000

def nativeOriginalCenteredRestTest (n : ℕ) (q : ℕ→RestCoordinate n→ℝ)
    (U : ℕ) (b h K : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (P : T.cavityLeft.Assignment→ℝ) :
    T.cavityLeft.Assignment→ℝ :=
  fun σ=>P σ-nativeOriginalRestTestExpectation n q U b h K T P

theorem native_original_centered_rest_test_mean_zero (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) :
    nativeOriginalRestTestExpectation n q U b h K T
      (nativeOriginalCenteredRestTest n q U b h K T P)=0 := by
  have hw:=T.disorderWeight_probability (fullWeight_pos n) (fullFeature n) ho 0
    (cutFullVariance n q U 1 1 b h K) 0
  unfold nativeOriginalCenteredRestTest
  unfold nativeOriginalRestTestExpectation ClockTree.disorderExpect
  simp only [mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul,hw.2,one_mul,sub_self]

theorem actual_original_centered_site_pair_eq_longitudinal_endpoint (n : ℕ)
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
      nativeCenteredLowGammaHighPath n q U b h K S T Pc a z 1+
      nativeGKernelLowAllocation n q U b h K T Pc a z (restCenteredLowKernel n U b S)+
      nativeActualHigherAllocatedRemainder n q U b h K T Pc a z-
      nativeCenteredLowGammaHighSecondRemainder n q U b h K S T Pc a z-
      (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*
        K (T.splitIndex a z)*
          (nativeOriginalLongitudinalRestoration n q U b h K S T
              (fun σ=>Pc (T.cavityAssignment σ).1) a+
            nativeOriginalLongitudinalRestoration n q U b h K S T
              (fun σ=>Pc (T.cavityAssignment σ).1) z) := by
  dsimp only
  rw [actual_original_site_pair_eq_original_longitudinal_endpoint n q U b h K S hKS T ho
    (nativeOriginalCenteredRestTest n q U b h K T P) a z hq0 hq hb hh hK hbm hhm hKm hU0 hU haz,
    native_original_centered_rest_test_mean_zero n q U b h K T ho P,mul_zero,zero_add]

theorem native_original_site_overlap_error_center_independent
    (n a U : ℕ) {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (b h K : ℕ→ℝ) (G : ActualNaturalBoundaryShape n a T)
    (s t : T.Slot) (c : ℝ) :
    let q:=cavityPath n U 1 1 (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) b h K
    T.disorderExpect (fullWeight n) (fullFeature n) 0 q
        (fun σ=>spinValue (T.atSlot σ s).2*spinValue (T.atSlot σ t).2*(G.product σ-c)) 0-
      T.disorderExpect (fullWeight n) (fullFeature n) 0 q
        (fun σ=>orderedOverlap (n+1) (joinSpin (T.atSlot σ s)) (joinSpin (T.atSlot σ t))*(G.product σ-c)) 0=
    T.disorderExpect (fullWeight n) (fullFeature n) 0 q
        (fun σ=>spinValue (T.atSlot σ s).2*spinValue (T.atSlot σ t).2*G.product σ) 0-
      T.disorderExpect (fullWeight n) (fullFeature n) 0 q
        (fun σ=>orderedOverlap (n+1) (joinSpin (T.atSlot σ s)) (joinSpin (T.atSlot σ t))*G.product σ) 0 := by
  have H:=native_actual_full_site_pair_eq_overlap T ho U b h K (fun _=>1) (by intros;rfl) s t (Fin.last n)
  simp only [joinSpin_last,mul_one,ClockTree.disorderExpect] at H
  dsimp only [ClockTree.disorderExpect]
  simp only [mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul,←mul_assoc] at H ⊢
  linear_combination -c*H

end OAI.SKFluctuations.Cavity
