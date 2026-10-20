module

public import ComparisonActualHighWallLowProfileMoments
public import ComparisonActualHighWallAllDegreeContinuumMoments
public import ComparisonSignedCavityInheritedTransientLowPartBudget

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators

theorem eventually_actual_high_wall_canonical_transient_low_part_budget
    (aDegree k rBound : ℕ) (hk : 0<k)
    (Bclock Cmass Ccut : ℝ) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct) :
    ∃Cp Cq : ℝ,0<Cp ∧ 0<Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=2*max Bclock 0
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),
          U≤as.length → l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm),
          partitionPoint 0 as U ≤ Ccut*M.data.d →
          (∀e,G.sourceLowMass e ≤ Cmass*M.data.d) →
        ∀(i star : ℕ) (part : NativeTransientLowErrorPart) (es : List T.Slot),
          |nativeTransientLowErrorPartJet n q i star U b h K T
            (fun σ=>(G.canonicalHighWallSource M forms).product σ*siteMonomial T σ es) 0 part k l t|≤
            ClockTree.pairForkVariation rBound*ClockTree.absJetVariation (rBound+2) k*
              (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*
                M.data.d^aDegree)*(Cq*M.data.d)^k*
              (T.forkCost (nativeWholeLawErrorRadius n as (cutFullVariance n q U l t b h K)
                (nativeTransientLowErrorPartDirection n U i star b h K part))+
              ClockTree.edgeBudget 0 as (nativeWholeLawErrorRadius n as (cutFullVariance n q U l t b h K)
                (nativeTransientLowErrorPartDirection n U i star b h K part))) := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_high_wall_canonical_continuum_all_degree_even_moment
    (D:=D) aDegree 2 rBound (by norm_num) Bclock Cmass hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cq,hCq,HQ⟩:=eventually_actual_high_wall_continuum_low_profile_moment
    (D:=D) (2*k) (by omega) Bclock Ccut hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,Cq,hCp,hCq,?_⟩
  filter_upwards [HP,HQ] with n hnP hnQ
  intro M hwork L us hus hret hmesh
  filter_upwards [hnP M hwork L us hus hret hmesh,
    hnQ M hwork L us hus hret hmesh] with jGrid hgrid hgridQ
  dsimp only at hgrid hgridQ ⊢
  intro U T l t hU hl ht hT G forms hcut hmass i star part es
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let Mclock:=2*max Bclock 0
  let C:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*
    M.data.d^aDegree
  let rho:=Cq*M.data.d
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.bf M.hf
    (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) (partitionPoint_mem as ho j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.bf u:ℝ)≤M.bf v from M.data.bf_monotone M.alpha hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.hf u:ℝ)≤M.hf v from M.data.hf_monotone M.alpha hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.bf M.hf (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha)) as ho
  have hK0 j : 0≤K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HS j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HS i).1 (NNReal.coe_nonneg _))
  have HC : 0 ≤ C:=by
    dsimp only [C]
    exact mul_nonneg (by positivity) (pow_nonneg M.data.hd.le _)
  have Hrho : 0 < rho:=by dsimp only [rho];exact mul_pos hCq M.data.hd
  have HPmoment : T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l t b h K)
      (fun σ=>|(G.canonicalHighWallSource M forms).product σ*siteMonomial T σ es|^4) 0≤C^4 := by
    simp only [abs_mul,native_site_monomial_abs_one,mul_one]
    exact hgrid U T l t hl ht hT G forms hmass
  have HQmoment j (hj : j≤as.length) : (ClockTree.pairClock as j).disorderExpect
      (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l t b h K)
      (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U t b h K) j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^(4*k)) 0≤rho^(4*k) := by
    have Hraw:=hgridQ U l t t hl ht ht hcut j hj
    rw [show 2*(2*k)=4*k by omega] at Hraw
    exact Hraw
  exact native_transient_low_part_wholeLaw_first_bound n U i star k hk q b h K T ho hT _ part hl ht HC Hrho
    (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
    (fun i=>by cases i <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm HPmoment HQmoment

end OAI.SKFluctuations.Cavity
