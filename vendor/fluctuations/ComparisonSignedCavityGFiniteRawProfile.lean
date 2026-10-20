module

public import ComparisonSignedCavityGRestorationRawLow
public import CavityFiniteProfilePermutation

@[expose] public section

noncomputable section
set_option maxHeartbeats 14000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators

theorem native_original_G_finite_raw_profile_restoration_bound (n U : ℕ)
    (b h K S : ℕ→ℝ) (hKS : ∀j,K j=h j+b j*S j)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (hU : U≤as.length) {rBound : ℕ} (hT : T.leaves≤rBound)
    (law : ℕ→FullCoordinate n→ℝ) (P : T.Assignment→ℝ) (a c e f : T.Slot) (hef : e≠f)
    (B : ℕ→FullCoordinate n→ℝ) {C rho : ℝ} (hC : 0≤C) (hrho : 0<rho)
    (hP : T.disorderExpect (fullWeight n) (fullFeature n) 0 law (fun σ=>|P σ|^4) 0≤C^4)
    (hNew : ∀j,j≤as.length→(ClockTree.pairClock as j).disorderExpect
      (fullWeight n) (fullFeature n) 0 law
      (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n) B j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^4) 0≤rho^4) :
    |ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0 law 0
      [ReplicaTree.coordinateProfile (fullFeature n) B] T
      (fun σ=>P σ*nativeOriginalHighGAtom T U K b S a c e f σ)|≤
      |(1/2:ℝ)*fullScalarCutConnected4 T U K a c e f| *
        (ClockTree.absJetVariation rBound 1*C*
          nativeWholeLawErrorRadius n as law (cutTSlope n U 0 b h K) (T.splitIndex e f)*rho) := by
  have Hmoment j : (ClockTree.pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0 law
      (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n) (ClockTree.clipDirection as.length B) j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^4) 0≤rho^4 := by
    by_cases hj : j≤as.length
    · simpa only [ClockTree.coordinateProfile_clip_below (fullFeature n) as.length B hj] using hNew j hj
    · simp only [ClockTree.coordinateProfile_clip_above (fullFeature n) as.length B hj,Pi.zero_apply,
        abs_zero,zero_pow (by norm_num : (4:ℕ)≠0),ClockTree.disorderExpect,mul_zero,Finset.sum_const_zero]
      exact pow_nonneg hrho.le _
  have H:=native_original_G_raw_profile_restoration_bound n U b h K S hKS T ho hU hT law P a c e f hef
    (ClockTree.clipDirection as.length B) hC hrho hP Hmoment
  have HE:=ClockTree.disorderProfileJets_eq_clipDirections (fullWeight n) (fullFeature n) 0 law 0 [B] T
    (fun σ=>P σ*nativeOriginalHighGAtom T U K b S a c e f σ)
  simp only [List.map_cons,List.map_nil] at HE
  rw [HE]
  exact H

end OAI.SKFluctuations.Cavity
