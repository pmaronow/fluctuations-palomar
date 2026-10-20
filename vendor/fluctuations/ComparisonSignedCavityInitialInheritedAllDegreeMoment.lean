module

public import ComparisonSignedCavityInheritedContinuumMoments
public import ComparisonSignedCavityActualSmallCutCanonicalOldMoment

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 18000000

theorem eventually_actual_minimum_inherited_canonical_continuum_even_all_degree
    (aDegree dOrder rBound : ℕ) (hd : 0<dOrder)
    (Bclock Temp Cf Cmass : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0≤Cf) (hCmass : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cp : ℝ,0<Cp ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),
          l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs≤x → x≤W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e) →
          T.disorderExpect (fullWeight n) (fullFeature n) 0
            (cutFullVariance n (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) U l t b h K)
            (fun σ=>|(G.canonicalMinimumSource M forms).product σ|^(2*dOrder)) 0≤
            (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*
              sourceMonomialScale x W initial)^(2*dOrder) := by
  by_cases ha : 0<aDegree
  · exact eventually_actual_minimum_inherited_canonical_continuum_square_even_moment
      (D:=D) aDegree dOrder rBound ha hd Bclock Temp Cf Cmass hTemp hCf hCmass
      hm hdelta hroom hcl hcu hAz hC0 hCt
  · have hz : aDegree=0:=by omega
    subst aDegree
    refine ⟨1,by norm_num,Filter.Eventually.of_forall (fun n=>?_)⟩
    intro M hsource hxs L us hus hret hmesh
    refine Filter.Eventually.of_forall (fun jGrid=>?_)
    dsimp only
    intro U T l t hl ht hT G forms initial x W hxsx hxW hmass
    have ho : MassOrdered 0 (finiteCutMasses us jGrid):=finiteCutMasses_ordered us hus jGrid
    have Hp0 : sourceMonomialScale x W initial=1 := by
      rw [←source_factor_scale_product]
      exact Fin.prod_univ_zero _
    simp_rw [native_canonical_source_zero_degree_product]
    simp only [abs_one,one_pow,pow_zero,mul_one,Hp0]
    rw [T.disorderExpect_one (fullWeight_pos n) (fullFeature n) ho]
    apply one_le_pow₀
    apply Real.one_le_exp
    exact mul_nonneg (wholeLawRowComparisonConstant_nonneg _)
      (by positivity)

end OAI.SKFluctuations.Cavity
