module

public import ComparisonActualHighWallAllDegreeContinuumMoments
public import ComparisonSignedCavityInheritedTransientLowZeroBudget

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 18000000

theorem eventually_actual_high_wall_canonical_transient_low_part_zero_budget
    (aDegree rBound : ℕ) (Bclock Cmass : ℝ) (hCmass : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct) :
    ∃Cp : ℝ,0<Cp ∧ ∀ᶠn : ℕ in atTop,
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
          l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm),
          (∀e,G.sourceLowMass e ≤ Cmass*M.data.d) →
        ∀(i star : ℕ) (part : NativeTransientLowErrorPart) (es : List T.Slot),
          |nativeTransientLowErrorPartJet n q i star U b h K T
            (fun σ=>(G.canonicalHighWallSource M forms).product σ*siteMonomial T σ es) 0 part 0 l t|≤
            ClockTree.pairForkVariation rBound*
              (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*
                M.data.d^aDegree)*
              (T.forkCost (nativeWholeLawErrorRadius n as (cutFullVariance n q U l t b h K)
                (nativeTransientLowErrorPartDirection n U i star b h K part))+
              ClockTree.edgeBudget 0 as (nativeWholeLawErrorRadius n as (cutFullVariance n q U l t b h K)
                (nativeTransientLowErrorPartDirection n U i star b h K part))) := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_high_wall_canonical_continuum_all_degree_even_moment
    (D:=D) aDegree 1 rBound (by norm_num) Bclock Cmass hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,hCp,?_⟩
  filter_upwards [HP] with n hnP
  intro M hwork L us hus hret hmesh
  filter_upwards [hnP M hwork L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U T l t hl ht hT G forms hmass i star part es
  let as:=finiteCutMasses us jGrid
  let Mclock:=2*max Bclock 0
  let C:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*
    M.data.d^aDegree
  have HC : 0 ≤ C:=by
    dsimp only [C]
    exact mul_nonneg (by positivity) (pow_nonneg M.data.hd.le _)
  apply native_transient_low_part_zero_wholeLaw_bound n U i star _ _ _ _ T
    (finiteCutMasses_ordered us hus jGrid) hT _ part HC
  have HE : (fun σ=>((G.canonicalHighWallSource M forms).product σ*siteMonomial T σ es)^2)=
      (fun σ=>|(G.canonicalHighWallSource M forms).product σ|^2) := by
    funext σ
    rw [←sq_abs]
    simp only [abs_mul,native_site_monomial_abs_one,mul_one]
  rw [HE]
  simpa only [Nat.mul_one,C,Mclock,as] using hgrid U T l t hl ht hT G forms hmass

end OAI.SKFluctuations.Cavity
