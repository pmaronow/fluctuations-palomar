module

public import ComparisonSignedCavityTransientLowPartProfileBudget
public import ComparisonSignedCavityActualSmallCutCanonicalOldMoment
public import ComparisonSignedCavityWholeLawZeroLowError
public import ComparisonSignedCavityCanonicalTransientHighBudget

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 18000000

theorem native_transient_low_part_zero_wholeLaw_bound (n U i star : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    {rBound : ℕ} (hT : T.leaves≤rBound) (P : T.Assignment→ℝ)
    (part : NativeTransientLowErrorPart) {l t C : ℝ} (hC : 0≤C)
    (hP : T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cutFullVariance n q U l t b h K) (fun σ=>P σ^2) 0≤C^2) :
    |nativeTransientLowErrorPartJet n q i star U b h K T P 0 part 0 l t|≤
      let law:=cutFullVariance n q U l t b h K
      let R:=nativeWholeLawErrorRadius n as law (nativeTransientLowErrorPartDirection n U i star b h K part)
      ClockTree.pairForkVariation rBound*C*(T.forkCost R+ClockTree.edgeBudget 0 as R) := by
  let law:=cutFullVariance n q U l t b h K
  let A:=nativeTransientLowErrorPartDirection n U i star b h K part
  unfold nativeTransientLowErrorPartJet
  simp only [List.replicate_zero,List.nil_append]
  rw [←native_transient_low_part_direction_profile]
  have H:=T.disorderProfileJets_oneError_offDiagonal_wholeLaw_L2
    (fullWeight_pos n) (fullFeature n) ho 0 law 0 hT P hC hP
    (ReplicaTree.coordinateProfile (fullFeature n) A)
    (fun σ=>fullFeature_coordinateProfile_self n A as.length σ)
    (nativeWholeLawErrorRadius_nonneg n as law A)
    (fun j=>le_of_eq (nativeWholeLawErrorSecond_eq_radius_sq n ho law A j))
  simpa only [ClockTree.edgeDensity_integral ho,law,A] using H

theorem eventually_actual_minimum_bare_canonical_transient_low_part_zero_budget
    (aDegree rBound : ℕ) (Bclock Temp Cmass : ℝ) (hTemp : 0≤Temp) (hCmass : 0≤Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct) :
    ∃Cp : ℝ,0<Cp ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        (∀u,M.b u=Temp) → (∀u,M.h u=0) → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*NativeOverlapMinimum.bareSourceClockConstant cl Az D+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),
          l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (W : ℝ),M.xs≤W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale M.xs W initial e) →
        ∀(i star : ℕ) (part : NativeTransientLowErrorPart) (es : List T.Slot),
          |nativeTransientLowErrorPartJet n q i star U b h K T
            (fun σ=>(G.canonicalMinimumSource M forms).product σ*siteMonomial T σ es) 0 part 0 l t|≤
            ClockTree.pairForkVariation rBound*
              (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*
                sourceMonomialScale M.xs W initial)*
              (T.forkCost (nativeWholeLawErrorRadius n as (cutFullVariance n q U l t b h K)
                (nativeTransientLowErrorPartDirection n U i star b h K part))+
              ClockTree.edgeBudget 0 as (nativeWholeLawErrorRadius n as (cutFullVariance n q U l t b h K)
                (nativeTransientLowErrorPartDirection n U i star b h K part))) := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_bare_canonical_continuum_even_all_degree
    (D:=D) aDegree 1 rBound (by norm_num) Bclock Temp Cmass hTemp hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,hCp,?_⟩
  filter_upwards [HP] with n hnP
  intro M hb hh hxs L us hus hret hmesh
  filter_upwards [hnP M hb hh hxs L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U T l t hl ht hT G forms initial W hxW hmass i star part es
  let as:=finiteCutMasses us jGrid
  let Mclock:=4*NativeOverlapMinimum.bareSourceClockConstant cl Az D+2*Temp
  let C:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*
    sourceMonomialScale M.xs W initial
  have HC : 0≤C:=by
    dsimp only [C]
    rw [←source_factor_scale_product]
    exact mul_nonneg (by positivity) (Finset.prod_nonneg fun e _=>
      (source_factor_scale_pos M.hxs (M.hxs.trans_le hxW) initial e).le)
  apply native_transient_low_part_zero_wholeLaw_bound n U i star _ _ _ _ T
    (finiteCutMasses_ordered us hus jGrid) hT _ part HC
  have HE : (fun σ=>((G.canonicalMinimumSource M forms).product σ*siteMonomial T σ es)^2)=
      (fun σ=>|(G.canonicalMinimumSource M forms).product σ|^2) := by
    funext σ
    rw [←sq_abs]
    simp only [abs_mul,native_site_monomial_abs_one,mul_one]
  rw [HE]
  simpa only [Nat.mul_one,C,Mclock,as] using hgrid U T l t hl ht hT G forms initial W hxW hmass

end OAI.SKFluctuations.Cavity
