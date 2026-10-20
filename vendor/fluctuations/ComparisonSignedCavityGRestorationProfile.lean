module

public import ComparisonSignedCavityActualGLawRestoration
public import ComparisonSignedCavityMixedErrorFixedProfile
public import ComparisonSignedCavityWholeLawErrorProfiles

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy

theorem native_rest_high_kernel_abs_eq_profile (n U : ℕ) (b h K : ℕ→ℝ)
    (j : ℕ) (σ τ : Spin n×Bool) :
    |restHighKernel n U b h K j σ.1 τ.1|=
      |ReplicaTree.coordinateProfile (fullFeature n) (cutTSlope n U 0 b h K) j σ τ| := by
  rw [←siteRestKernel_eq_cut_high]
  simp only [siteRestKernel,abs_mul,abs_spinValue,one_mul]

theorem native_rest_high_kernel_square_eq_profile (n U : ℕ) (b h K : ℕ→ℝ)
    (j : ℕ) (σ τ : Spin n×Bool) :
    (restHighKernel n U b h K j σ.1 τ.1)^2=
      (ReplicaTree.coordinateProfile (fullFeature n) (cutTSlope n U 0 b h K) j σ τ)^2 := by
  rw [←sq_abs (restHighKernel n U b h K j σ.1 τ.1),
    native_rest_high_kernel_abs_eq_profile,sq_abs]

theorem native_original_G_profile_restoration_bound (n U : ℕ)
    (b h K S : ℕ→ℝ) (hKS : ∀j,K j=h j+b j*S j)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (hU : U ≤ as.length) {r : ℕ} (hT : T.leaves ≤ r)
    (law : ℕ→FullCoordinate n→ℝ) (P : T.Assignment→ℝ) (a c e f : T.Slot) (hef : e≠f)
    (B : ℕ→FullCoordinate n→ℝ)
    {C p Mhigh Mnew : ℝ} (hC : 0 ≤ C) (hp : 2 < p) (hMhigh : 0 ≤ Mhigh) (hMnew : 0 ≤ Mnew)
    (hP : T.disorderExpect (fullWeight n) (fullFeature n) 0 law
      (fun σ=>|P σ|^(2*(p/(p-2)))) 0 ≤ C^(2*(p/(p-2))))
    (hHigh : ∀(j : ℕ) (σ τ : Spin n×Bool),
      |ReplicaTree.coordinateProfile (fullFeature n) (cutTSlope n U 0 b h K) j σ τ| ≤ Mhigh)
    (hNew : ∀(j : ℕ) (σ τ : Spin n×Bool),
      |ReplicaTree.coordinateProfile (fullFeature n) B j σ τ| ≤ Mnew) :
    |ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0 law 0
      [ReplicaTree.coordinateProfile (fullFeature n) B] T
      (fun σ=>P σ*nativeOriginalHighGAtom T U K b S a c e f σ)| ≤
      |(1/2:ℝ)*fullScalarCutConnected4 T U K a c e f| *
        (ClockTree.pairForkVariation r*C*Mhigh^((p-2)/p)*Mnew^((p-2)/p)*
          (nativeWholeLawErrorRadius n as law (cutTSlope n U 0 b h K) (T.splitIndex e f))^(2/p)*
          nativeWholeLawProfileCost n law B T (2/p)) := by
  let A:=fun σ τ : Spin n×Bool=>restHighKernel n U b h K (T.splitIndex e f) σ.1 τ.1
  let d:=nativeWholeLawErrorRadius n as law (cutTSlope n U 0 b h K) (T.splitIndex e f)
  let κ:=(1/2:ℝ)*fullScalarCutConnected4 T U K a c e f
  have Hsecond : (ClockTree.pairClock as (T.splitIndex e f)).disorderExpect
      (fullWeight n) (fullFeature n) 0 law
      (fun σ=>(A (ClockTree.pairSpin as (T.splitIndex e f) σ).1
        (ClockTree.pairSpin as (T.splitIndex e f) σ).2)^2) 0 ≤ d^2 := by
    dsimp only [A]
    simp_rw [native_rest_high_kernel_square_eq_profile]
    exact le_of_eq (nativeWholeLawErrorSecond_eq_radius_sq n ho law
      (cutTSlope n U 0 b h K) (T.splitIndex e f))
  have H:=T.disorderProfileJets_fixedLow_highError_wholeLaw_product_bound
    (fullWeight_pos n) (fullFeature n) ho 0 law 0 hT P hC hp hMhigh hMnew
    (nativeWholeLawErrorRadius_nonneg n as law (cutTSlope n U 0 b h K) (T.splitIndex e f)) hP
    A e f hef (by
      intro σ τ
      dsimp only [A]
      rw [native_rest_high_kernel_abs_eq_profile]
      exact hHigh _ _ _) Hsecond (ReplicaTree.coordinateProfile (fullFeature n) B)
    (fun σ=>fullFeature_coordinateProfile_self n B as.length σ) hNew
    (nativeWholeLawErrorRadius n as law B) (nativeWholeLawErrorRadius_nonneg n as law B)
    (fun j=>le_of_eq (nativeWholeLawErrorSecond_eq_radius_sq n ho law B j))
  have Htest : (fun σ=>P σ*nativeOriginalHighGAtom T U K b S a c e f σ)=
      fun σ=>κ*(P σ*A (T.atSlot σ e) (T.atSlot σ f)) := by
    funext σ
    rw [native_original_high_G_atom_eq_unmasked_rest_kernel T ho U b h K S hKS a c e f hU]
    dsimp only [κ,A]
    ring
  rw [Htest,ClockTree.disorderProfileJets_const_mul,abs_mul]
  exact mul_le_mul_of_nonneg_left H (abs_nonneg κ)

end OAI.SKFluctuations.Cavity
