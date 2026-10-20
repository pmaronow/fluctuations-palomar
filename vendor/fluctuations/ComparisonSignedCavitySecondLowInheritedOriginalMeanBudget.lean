module

public import ComparisonSignedCavityInheritedContinuumMoments
public import ComparisonSignedCavityCenteredLowRestorationStarRate
public import ComparisonSignedCavityOriginalConstantEndpoints

@[expose] public section

noncomputable section
set_option maxHeartbeats 25000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_minimum_inherited_second_low_original_mean_budget
    (degree rBound : ℕ) (Bclock Temp Cf Cmass : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cp : ℝ,0 < Cp ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=fun j=>h j+b j*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n degree T) (forms : Fin degree→NativeSourceFactorForm)
          (initial : Finset (Fin degree)) (x W : ℝ),M.xs ≤ x → x ≤ W →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
          |nativeOriginalRestTestExpectation n q U b h K T
            (G.canonicalMinimumSource M forms).restProduct| ≤
            Real.exp (wholeLawRowComparisonConstant rBound*(4*Cf+2*Temp))*
              Cp^degree*sourceMonomialScale x W initial := by
  by_cases ha : 0 < degree
  · obtain ⟨Cp,hCp,H⟩:=eventually_actual_minimum_inherited_canonical_continuum_square_even_moment
      (D:=D) degree 1 rBound ha (by norm_num) Bclock Temp Cf Cmass hTemp hCf hCm
      hm hdelta hroom hcl hcu hAz hC0 hCt
    refine ⟨Cp,hCp,?_⟩
    filter_upwards [H] with n hn
    intro M HS hxs L us hus hret hmesh
    filter_upwards [hn M HS hxs L us hus hret hmesh] with k hk
    dsimp only at hk ⊢
    intro U T hT G forms initial x W hxsx hxW hmass
    have hscale : 0 ≤ Real.exp (wholeLawRowComparisonConstant rBound*(4*Cf+2*Temp))*
        Cp^degree*sourceMonomialScale x W initial:=by
      have hx : 0 < x:=M.hxs.trans_le hxsx
      have hW : 0 < W:=hx.trans_le hxW
      unfold sourceMonomialScale
      positivity
    apply native_original_rest_mean_abs_le_square n _ U _ _ _ T (finiteCutMasses_ordered us hus k)
      _ hscale
    simpa only [ActualNaturalBoundaryShape.product_eq_restProduct,mul_one] using
      hk U T 1 1 (by norm_num) (by norm_num) hT G forms initial x W hxsx hxW hmass
  · have hz : degree=0:=by omega
    subst degree
    refine ⟨1,by norm_num,Eventually.of_forall fun n=>?_⟩
    intro M HS hxs L us hus hret hmesh
    refine Eventually.of_forall fun k=>?_
    dsimp only
    intro U T hT G forms initial x W hxsx hxW hmass
    have HP:(G.canonicalMinimumSource M forms).restProduct=(fun _=>1):=by
      funext σ
      simp only [ActualNaturalBoundaryShape.restProduct,Finset.univ_eq_empty,Finset.prod_empty]
    have Hp0:sourceMonomialScale x W initial=1:=by
      rw [←source_factor_scale_product]
      exact Fin.prod_univ_zero _
    rw [HP,native_original_rest_test_one n _ U _ _ _ T (finiteCutMasses_ordered us hus k)]
    simp only [abs_one,pow_zero,mul_one,Hp0]
    apply Real.one_le_exp
    exact mul_nonneg (wholeLawRowComparisonConstant_nonneg _) (by positivity)

end OAI.SKFluctuations.Cavity
