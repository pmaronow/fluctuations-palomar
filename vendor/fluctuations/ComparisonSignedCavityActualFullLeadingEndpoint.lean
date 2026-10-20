module

public import ComparisonSignedCavityActualCenteredEndpoint
public import ComparisonSignedCavityActualConnectedLowSplitSupport
public import ComparisonSignedCavityLowGammaFullRestoration

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 18000000

theorem actual_original_centered_site_pair_eq_full_leading_longitudinal (n : ℕ)
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
      nativeCenteredLowGammaOriginalLeading n q U b h K S T Pc a z+
      nativeGKernelLowAllocation n q U b h K T Pc a z (restCenteredLowKernel n U b S)+
      nativeActualHigherAllocatedRemainder n q U b h K T Pc a z-
      nativeCenteredLowGammaHighSecondRemainder n q U b h K S T Pc a z-
      nativeCenteredLowGammaLowRestoration n q U b h K S T Pc a z-
      (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*
        K (T.splitIndex a z)*
          (nativeOriginalLongitudinalRestoration n q U b h K S T
              (fun σ=>Pc (T.cavityAssignment σ).1) a+
            nativeOriginalLongitudinalRestoration n q U b h K S T
              (fun σ=>Pc (T.cavityAssignment σ).1) z) := by
  dsimp only
  have HE:=actual_original_centered_site_pair_eq_longitudinal_endpoint n q U b h K S hKS T ho P a z
    hq0 hq hb hh hK hbm hhm hKm hU0 hU haz
  have HL:=native_centered_low_gamma_original_leading_eq_path_add_low_restoration n q U b h K S T ho
    (nativeOriginalCenteredRestTest n q U b h K T P) a z hq0 hq hb hh hK hbm hhm hKm hU
  dsimp only at HE
  rw [HL]
  linear_combination HE

def nativeCenteredLowGammaFixedForkOriginalLeading (n : ℕ) (q : ℕ→RestCoordinate n→ℝ)
    (U : ℕ) (b h K S : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (P : T.cavityLeft.Assignment→ℝ)
    (a z : T.Slot) : ℝ :=
  ((T.markedAttach 0).map (fun p=>p.coeff*
    ((p.tree.markedAttach 0).map (fun r=>r.coeff*
      (nativeLowScalarPairing r.tree U K (r.embed (p.embed a)) (r.embed (p.embed z))
        (r.embed p.mark) r.mark*
       r.tree.disorderExpect (fullWeight n) (fullFeature n) 0
         (cutFullVariance n q U 1 1 b h K)
         (fun σ=>insertedRestTest P (restCenteredFixedForkKernel n b S (T.splitIndex a z)) p r
           (r.tree.cavityAssignment σ).1) 0))).sum)).sum/2

theorem native_original_leading_eq_fixed_target_fork (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K S : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (hU : U ≤ as.length) (haz : T.splitIndex a z < U) :
    nativeCenteredLowGammaOriginalLeading n q U b h K S T P a z=
      nativeCenteredLowGammaFixedForkOriginalLeading n q U b h K S T P a z := by
  unfold nativeCenteredLowGammaOriginalLeading nativeCenteredLowGammaFixedForkOriginalLeading
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro r hr
  let A:=nativeLowScalarPairing r.tree U K (r.embed (p.embed a)) (r.embed (p.embed z))
    (r.embed p.mark) r.mark
  have HS : r.tree.splitIndex (r.embed (p.embed a)) (r.embed (p.embed z))=T.splitIndex a z := by
    rw [(p.tree.markedAttach_embed_preserves 0 r hr).2,(T.markedAttach_embed_preserves 0 p hp).2]
  have HE : (fun σ : r.tree.Assignment=>A*insertedRestTest P (restCenteredLowKernel n U b S) p r
      (r.tree.cavityAssignment σ).1)=
      fun σ=>A*insertedRestTest P (restCenteredFixedForkKernel n b S (T.splitIndex a z)) p r
        (r.tree.cavityAssignment σ).1 := by
    funext σ
    have H:=native_low_scalar_pairing_centered_kernel_eq_target_split r.tree ho U b K S
      (r.embed (p.embed a)) (r.embed (p.embed z)) (r.embed p.mark) r.mark hU (by rwa [HS])
      (p.restSpin (r.restRestrict (r.tree.cavityAssignment σ).1)) (r.restSpin (r.tree.cavityAssignment σ).1)
    rw [HS] at H
    dsimp only [A,insertedRestTest,restCenteredFixedForkKernel]
    linear_combination P (p.restRestrict (r.restRestrict (r.tree.cavityAssignment σ).1))*H
  have H:=congrArg (fun F=>r.tree.disorderExpect (fullWeight n) (fullFeature n) 0
    (cutFullVariance n q U 1 1 b h K) F 0) HE
  rw [r.tree.disorderExpect_const_mul (fullWeight_pos n) (fullFeature n) ho,
    r.tree.disorderExpect_const_mul (fullWeight_pos n) (fullFeature n) ho] at H
  exact congrArg (r.coeff*·) H

end OAI.SKFluctuations.Cavity
