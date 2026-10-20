module

public import ComparisonSignedCavityInheritedGammaLowRestorationPrice

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_minimum_inherited_bounded_degree_gamma_LOW_restoration_price
    (degree rBound : ℕ)
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf→M.xs ≤ 1→
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1)→(∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹ ≤ M.xs→
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀aDegree : ℕ,aDegree ≤ degree →
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U ≤ as.length→T.leaves ≤ rBound→
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs ≤ x→x ≤ W→
          partitionPoint 0 as U ≤ Ccut*W→
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e)→
        ∀(a : T.Slot) (star : ℕ),star<U →
          |nativeGammaProjectedLowSecondRestoration T a star U q b h K
            (restCenteredFixedForkKernel n b S star 0) (G.canonicalMinimumSource M forms).restProduct| ≤
            C*sourceMonomialScale x W initial*
              (actualLowErrorComparisonConstant Mclock Temp*
                (nativeOriginalCutLowErrorRadius n M.bf M.hf as star+1/(n+1:ℕ)))*W^2 := by
  classical
  have HP (a : Fin (degree+1)):=eventually_actual_minimum_inherited_canonical_gamma_LOW_restoration_price
    (D:=D) a.val rBound Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  choose C hC HC using HP
  let Cmax:=1+∑a : Fin (degree+1),C a
  have hsum : 0 ≤ ∑a : Fin (degree+1),C a:=Finset.sum_nonneg (fun a _=>(hC a).le)
  have hCmax : 0 < Cmax:=by dsimp only [Cmax];linarith
  have hdom a : C a ≤ Cmax:=by
    have H:=Finset.single_le_sum (fun a _=>(hC a).le) (Finset.mem_univ a)
    dsimp only [Cmax]
    linarith
  refine ⟨Cmax,hCmax,?_⟩
  filter_upwards [Filter.eventually_all.mpr HC] with n hn
  intro M hsource hxs L us hus hret hmesh
  have Hgrids a:=hn a M hsource hxs L us hus hret hmesh
  filter_upwards [Filter.eventually_all.mpr Hgrids] with jGrid hj
  dsimp only at hj ⊢
  intro aDegree hdegree U T hU hT G forms initial x W hxsx hxW hcut hmass slot star hs
  let a : Fin (degree+1):=⟨aDegree,by omega⟩
  have Hraw:=hj a U T hU hT G forms initial x W hxsx hxW hcut hmass slot star hs
  let as:=finiteCutMasses us jGrid
  have hZ : 0 ≤ sourceMonomialScale x W initial:=by
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos (M.hxs.trans_le hxsx)
      ((M.hxs.trans_le hxsx).trans_le hxW) initial e).le
  have hd : 0 ≤ actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
      (nativeOriginalCutLowErrorRadius n M.bf M.hf as star+1/(n+1:ℕ)):=
    mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp)
      (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  exact Hraw.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hdom a) hZ) hd) (sq_nonneg W))

end OAI.SKFluctuations.Cavity
