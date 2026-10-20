module

public import ComparisonSignedCavityGRestorationProfile
public import ComparisonSignedCavityWholeLawOneErrorJets

@[expose] public section

noncomputable section
set_option maxHeartbeats 14000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy

theorem native_original_G_raw_profile_restoration_bound (n U : ℕ)
    (b h K S : ℕ→ℝ) (hKS : ∀j,K j=h j+b j*S j)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (hU : U ≤ as.length) {r : ℕ} (hT : T.leaves ≤ r)
    (law : ℕ→FullCoordinate n→ℝ) (P : T.Assignment→ℝ) (a c e f : T.Slot) (hef : e≠f)
    (B : ℕ→FullCoordinate n→ℝ) {C rho : ℝ} (hC : 0 ≤ C) (hrho : 0 < rho)
    (hP : T.disorderExpect (fullWeight n) (fullFeature n) 0 law (fun σ=>|P σ|^4) 0 ≤ C^4)
    (hNew : ∀j,(ClockTree.pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0 law
      (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n) B j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^4) 0 ≤ rho^4) :
    |ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0 law 0
      [ReplicaTree.coordinateProfile (fullFeature n) B] T
      (fun σ=>P σ*nativeOriginalHighGAtom T U K b S a c e f σ)| ≤
      |(1/2:ℝ)*fullScalarCutConnected4 T U K a c e f| *
        (ClockTree.absJetVariation r 1*C*
          nativeWholeLawErrorRadius n as law (cutTSlope n U 0 b h K) (T.splitIndex e f)*rho) := by
  let A:=fun j (σ τ : Spin n×Bool)=>restHighKernel n U b h K j σ.1 τ.1
  let κ:=(1/2:ℝ)*fullScalarCutConnected4 T U K a c e f
  let J:=fun σ=>P σ*A (T.splitIndex e f) (T.atSlot σ e) (T.atSlot σ f)
  have Hsecond (j : ℕ) : (ClockTree.pairClock as j).disorderExpect
      (fullWeight n) (fullFeature n) 0 law
      (fun σ=>(A j (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2)^2) 0 ≤
        (nativeWholeLawErrorRadius n as law (cutTSlope n U 0 b h K) j)^2 := by
    dsimp only [A]
    simp_rw [native_rest_high_kernel_square_eq_profile]
    exact le_of_eq (nativeWholeLawErrorSecond_eq_radius_sq n ho law (cutTSlope n U 0 b h K) j)
  have H:=ClockTree.disorderOffDiagonalJets_oneError_wholeLaw_scaled_pair_bound
    (fullWeight_pos n) (fullFeature n) ho 0 law 0
    [(ReplicaTree.coordinateProfile (fullFeature n) B,rho)] (k:=1) (by norm_num) hC T hT 0
    P hP A e f hef (nativeWholeLawErrorRadius_nonneg n as law (cutTSlope n U 0 b h K)) Hsecond
    Fin.elim0 Fin.elim0 Fin.elim0 (fun i=>Fin.elim0 i) Fin.elim0 (fun i=>Fin.elim0 i)
    (by simp) (fun i=>Fin.elim0 i) (by
      intro L hL j
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hL
      subst L
      simpa only [Nat.mul_one] using hNew j) (by
      intro L hL
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hL
      subst L
      exact hrho)
  simp only [List.map_cons,List.map_nil,Fin.prod_univ_zero,mul_one,List.length_cons,
    List.length_nil,List.prod_cons,List.prod_nil] at H
  have HE:=T.disorderProfileJets_one_eq_offDiagonal (fullWeight_pos n) (fullFeature n)
    ho 0 law J (fun σ=>fullFeature_coordinateProfile_self n B as.length σ) 0
  have Htest : (fun σ=>P σ*nativeOriginalHighGAtom T U K b S a c e f σ)=fun σ=>κ*J σ := by
    funext σ
    rw [native_original_high_G_atom_eq_unmasked_rest_kernel T ho U b h K S hKS a c e f hU]
    dsimp only [κ,J,A]
    ring
  rw [Htest,ClockTree.disorderProfileJets_const_mul,abs_mul,HE]
  exact mul_le_mul_of_nonneg_left H (abs_nonneg κ)

end OAI.SKFluctuations.Cavity
