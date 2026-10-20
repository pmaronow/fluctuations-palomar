module

public import ComparisonSignedCavityInheritedContinuumMoments
public import ComparisonSignedCavityCanonicalLowFactor

public import ComparisonSignedCavityCanonicalUnbondedLowFactor
public import ComparisonSignedCavityInheritedErrorTransport

@[expose] public section

noncomputable section
set_option maxHeartbeats 24000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal ENNReal
open Classical
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_minimum_inherited_canonical_unbonded_low_factor_even_moment
    (aDegree dOrder rBound : ℕ) (hd : 0<dOrder)
    (Bclock Temp Cf Cmass : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃ Cp : ℝ,0 < Cp ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),
          l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (f : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs ≤ x → x ≤ W →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
        ∀c d : T.Slot,c≠d → partitionPoint 0 as (T.splitIndex c d) ≤ Cmass*W →
          T.disorderExpect (fullWeight n) (fullFeature n) 0
            (cutFullVariance n (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) U l t b h K)
            (fun σ=>|(G.canonicalMinimumSource M f).product σ*
              (deletedOverlap n (joinSpin (T.atSlot σ c))
                (joinSpin (T.atSlot σ d))-S (T.splitIndex c d))|^(2*dOrder)) 0 ≤
            (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^(aDegree+1)*
              (W*sourceMonomialScale x W initial))^(2*dOrder) := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_inherited_canonical_continuum_square_even_moment
    (D:=D) (aDegree+1) dOrder rBound (by omega) hd Bclock Temp Cf Cmass hTemp hCf hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,hCp,?_⟩
  filter_upwards [HP] with n hnP
  intro M hsource hxs1 L us hus hret hmesh
  filter_upwards [hnP M hsource hxs1 L us hus hret hmesh] with jGrid hgridP
  dsimp only at hgridP ⊢
  intro U T l t hl ht hT G f initial x W hxsx hxW hmass c d hcd hmassNew
  let as:=finiteCutMasses us jGrid
  have ho:=finiteCutMasses_ordered us hus jGrid
  have had:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have Hcenter:=native_ordered_source_center_eq_completed n M.bf M.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1)
    (partitionPoint_mem as ho (T.splitIndex c d))
  have Hgeo : ∀e,(G.prependSourceEdge c d hcd).sourceLowMass e ≤
      Cmass*sourceFactorScale x W (sourceInitialAfterStar initial) e := by
    intro e
    refine Fin.cases ?_ (fun e=>?_) e
    · simpa only [ActualNaturalBoundaryShape.sourceLowMass,ActualNaturalBoundaryShape.prependSourceEdge,
        Fin.cases_zero,source_factor_scale_after_star_zero] using hmassNew
    · simpa only [ActualNaturalBoundaryShape.sourceLowMass,ActualNaturalBoundaryShape.prependSourceEdge,
        Fin.cases_succ,source_factor_scale_after_star_succ] using hmass e
  have H:=hgridP U T l t hl ht hT (G.prependSourceEdge c d hcd)
    (Fin.cases .centered f) (sourceInitialAfterStar initial) x W hxsx hxW Hgeo
  simp_rw [canonical_source_prepend_centered_product] at H
  rw [←Hcenter] at H
  rw [source_monomial_scale_after_star] at H
  simpa only [mul_assoc,mul_left_comm,mul_comm] using H

end OAI.SKFluctuations.Cavity
