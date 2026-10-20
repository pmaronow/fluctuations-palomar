module

public import ComparisonSignedCavityMixedErrorCanonicalMoment
public import ComparisonSignedCavityCanonicalRestMoments

@[expose] public section

noncomputable section
set_option maxHeartbeats 15000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators

theorem native_fixed_centered_rest_kernel_abs_le (n : ℕ) (b S : ℕ→ℝ) (j : ℕ)
    {B : ℝ} (hb0 : 0 ≤ b j) (hb : b j ≤ B) (hS : S j∈Icc (0:ℝ) 1)
    (σ τ : Spin n) : |restCenteredFixedForkKernel n b S j 0 σ τ| ≤ 2*B := by
  have HD : |deletedOverlap n (joinSpin (σ,false)) (joinSpin (τ,false))-S j| ≤ 2 := by
    apply (abs_sub _ _).trans
    rw [abs_of_nonneg hS.1]
    linarith [abs_deletedOverlap_le_one n (joinSpin (σ,false)) (joinSpin (τ,false)),hS.2]
  have HM:=mul_le_mul hb HD (abs_nonneg _) (hb0.trans hb)
  rw [←abs_of_nonneg hb0,←abs_mul] at HM
  simpa only [restCenteredFixedForkKernel,deletedOverlap,joinSpin_old,mul_comm] using HM

theorem native_centered_high_kernel_abs_le (n U : ℕ) (b h S : ℕ→ℝ)
    {B : ℝ} (hb0 : ∀j,0 ≤ b j) (hb : ∀j,b j ≤ B) (hS : ∀j,S j∈Icc (0:ℝ) 1)
    (j : ℕ) (σ τ : Spin n×Bool) :
    |ReplicaTree.coordinateProfile (fullFeature n)
      (cutTSlope n U 0 b h (fun j=>h j+b j*S j)) j σ τ| ≤ 2*B := by
  rw [cutTSlope_zero_covariance]
  by_cases hj : j<U
  · simp only [hj,ite_true,abs_zero]
    have HB:= (hb0 j).trans (hb j)
    positivity
  · simp only [hj,ite_false]
    rw [show h j+b j*deletedOverlap n (joinSpin σ) (joinSpin τ)-(h j+b j*S j)=
      b j*(deletedOverlap n (joinSpin σ) (joinSpin τ)-S j) by ring]
    rw [abs_mul,abs_mul,abs_spinValue,abs_spinValue,one_mul,one_mul,
      abs_mul,abs_of_nonneg (hb0 j)]
    have HD : |deletedOverlap n (joinSpin σ) (joinSpin τ)-S j| ≤ 2 := by
      apply (abs_sub _ _).trans
      rw [abs_of_nonneg (hS j).1]
      linarith [abs_deletedOverlap_le_one n (joinSpin σ) (joinSpin τ),(hS j).2]
    simpa only [mul_comm] using mul_le_mul (hb j) HD (abs_nonneg _) ((hb0 j).trans (hb j))

theorem eventually_actual_minimum_bare_canonical_mixed_gamma_ledger
    (aDegree rBound : ℕ) (ha : 0<aDegree)
    (Bclock Temp Cmass : ℝ) (hTemp : 0 ≤ Temp) (hCmass : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃ Cp : ℝ,0 < Cp ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        (∀u,M.b u=Temp) → (∀u,M.h u=0) → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*NativeOverlapMinimum.bareSourceClockConstant cl Az D+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (f : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (W : ℝ),M.xs ≤ W →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale M.xs W initial e) →
        ∀a z : T.Slot,U ≤ as.length → T.splitIndex a z<U →
          |nativeCenteredLowGammaHighLedger n q U b h K S T (G.canonicalMinimumSource M f).restProduct a z| ≤
            ClockTree.pairForkVariation (rBound+2)*
              (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*
                sourceMonomialScale M.xs W initial)*(2*Temp)^((1:ℝ)/2)*(2*Temp)^((1:ℝ)/2)*
              (nativeWholeLawErrorRadius n as (cutFullVariance n q U 0 0 b h K)
                (cutLowError n U b h K) (T.splitIndex a z))^((1:ℝ)/2)*
              nativeMixedGammaWeightedHighBudget n q U b h K ((1:ℝ)/2) T a z/2 := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_bare_canonical_mixed_old_fourth
    (D:=D) aDegree rBound ha Bclock Temp Cmass hTemp hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,hCp,?_⟩
  filter_upwards [HP] with n hnP
  intro M hbareb hbareh hxs1 L us hus hret hmesh
  filter_upwards [hnP M hbareb hbareh hxs1 L us hus hret hmesh] with jGrid hgridP
  dsimp only at hgridP ⊢
  intro U T hT G f initial W hxW hmass a z hU haz
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let C:=Real.exp (wholeLawRowComparisonConstant rBound*
    (4*NativeOverlapMinimum.bareSourceClockConstant cl Az D+2*Temp))*Cp^aDegree*
    sourceMonomialScale M.xs W initial
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have had:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.bf M.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) (partitionPoint_mem as ho j)
  have Hb j : b j ≤ Temp:=
    (M.bare_source_clock_bounds hcl hAz Temp hbareb hbareh (partitionPoint_mem as ho j)).2.1
  have HC : 0 ≤ C := by
    dsimp only [C]
    rw [←source_factor_scale_product]
    apply mul_nonneg (by positivity)
    exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos M.hxs (M.hxs.trans_le hxW) initial e).le
  have Hmom:=hgridP U T hT G f initial W hxW hmass
  simp_rw [(G.canonicalMinimumSource M f).product_eq_restProduct] at Hmom
  have Hbound:=native_centered_low_gamma_high_ledger_wholeLaw_bound n U
    (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) b h S T ho hT
    (G.canonicalMinimumSource M f).restProduct a z hU haz
    (C:=C) (p:=4) (Mlow:=2*Temp) (Mhigh:=2*Temp) HC (by norm_num)
    (by positivity) (by positivity)
    (by
      norm_num only [show (2*(4/(4-2)):ℝ)=4 by norm_num,Real.rpow_ofNat]
      exact Hmom)
    (native_fixed_centered_rest_kernel_abs_le n b S (T.splitIndex a z)
      (NNReal.coe_nonneg _) (Hb _) (HS _))
    (native_centered_high_kernel_abs_le n U b h S (fun _=>NNReal.coe_nonneg _) Hb HS)
  simpa only [C,show ((4-2)/4:ℝ)=(1:ℝ)/2 by norm_num,
    show (2/4:ℝ)=(1:ℝ)/2 by norm_num] using Hbound

end OAI.SKFluctuations.Cavity
