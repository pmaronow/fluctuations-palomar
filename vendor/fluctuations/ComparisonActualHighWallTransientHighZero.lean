module

public import ComparisonActualHighWallHighAllDegreeContinuumMoments
public import ComparisonSignedCavityCanonicalTransientHighBudget
public import ComparisonSignedCavityWholeLawZeroLowError

@[expose] public section

noncomputable section
set_option maxHeartbeats 16000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open Hierarchy.ClockTree
open scoped Topology NNReal ENNReal BigOperators

theorem eventually_actual_high_wall_canonical_transient_high_zero_budget
    (aDegree rBound : ℕ)
    (Bclock Cmass : ℝ) (hCmass : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0< delta) (hroom : delta < 3*m)
    (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az) (hC0 : 0< C0) (hCt : 0≤ Ct) :
    ∃Cp : ℝ,0< Cp ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=2*max Bclock 0
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),
          l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → T.leaves≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm),
          (∀e,G.sourceLowMass e ≤ Cmass*M.data.d) →
        ∀es : List T.Slot,
          |nativeTransientHighJet n q U b h K T
            (fun σ=>(G.canonicalHighWallSource M forms).product σ*siteMonomial T σ es) 0 0 l t|≤
            pairForkVariation rBound*
              (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*M.data.d^aDegree)*
              nativeWholeLawProfileCost n (cutFullVariance n q U l t b h K) (cutTSlope n U 0 b h K) T 1 := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_high_wall_all_degree_continuum_square_even_moment
    (D:=D) aDegree 1 rBound (by norm_num) Bclock Cmass hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,hCp,?_⟩
  filter_upwards [HP] with n hnP
  intro M hwork L us hus hret hmesh
  filter_upwards [hnP M hwork L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U T l t hl ht hT G forms hmass es
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let law:=cutFullVariance n q U l t b h K
  let A:=cutTSlope n U 0 b h K
  let C:=Real.exp (wholeLawRowComparisonConstant rBound*
    (2*max Bclock 0))*Cp^aDegree*M.data.d^aDegree
  let P:=fun σ=>(G.canonicalHighWallSource M forms).product σ*siteMonomial T σ es
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hd := M.data.hd
  have hC : 0≤ C:=by dsimp [C];positivity
  have HPmoment : T.disorderExpect (fullWeight n) (fullFeature n) 0 law (fun σ=>P σ^2) 0≤ C^2:=by
    have HH:=hgrid U T l t hl ht hT G forms hmass
    have HE : (fun σ=>P σ^2)=(fun σ=>|(G.canonicalHighWallSource M forms).product σ|^2):=by
      funext σ
      rw [←sq_abs]
      simp only [P,abs_mul,native_site_monomial_abs_one,mul_one]
    rw [HE]
    simpa only [Nat.mul_one,law,q,b,h,S,K,C,as] using HH
  have HB:=T.disorderProfileJets_oneError_offDiagonal_wholeLaw_L2 (fullWeight_pos n) (fullFeature n)
    ho 0 law 0 hT P hC HPmoment (ReplicaTree.coordinateProfile (fullFeature n) A)
    (fun σ=>fullFeature_coordinateProfile_self n A as.length σ)
    (nativeWholeLawErrorRadius_nonneg n as law A)
    (fun j=>le_of_eq (nativeWholeLawErrorSecond_eq_radius_sq n ho law A j))
  simpa only [nativeTransientHighJet,List.replicate_zero,List.nil_append,List.map_cons,List.map_nil,
    nativeWholeLawProfileCost,Real.rpow_one,P,C,law,A,q,b,h,K,S,as] using HB

end OAI.SKFluctuations.Cavity
