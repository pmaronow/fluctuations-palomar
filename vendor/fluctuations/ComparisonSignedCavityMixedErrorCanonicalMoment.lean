module

public import ComparisonSignedCavityMixedErrorGammaLedger
public import ComparisonSignedCavityActualLowErrorDensity
public import ComparisonSignedCavityCanonicalSourceMoments
public import ComparisonSignedCavityWholeLawScalarClock

@[expose] public section

noncomputable section
set_option maxHeartbeats 15000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators

theorem eventually_actual_minimum_bare_canonical_mixed_old_fourth
    (aDegree rBound : ℕ) (ha : 0 < aDegree)
    (Bclock Temp Cmass : ℝ) (hTemp : 0  ≤  Temp) (hCmass : 0  ≤  Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0  ≤  Az) (hC0 : 0 < C0) (hCt : 0  ≤  Ct) :
    ∃ Cp : ℝ,0 < Cp ∧ ∀ᶠ n : ℕ in atTop,
      ∀ M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        (∀u,M.b u=Temp) → (∀u,M.h u=0) → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠ jGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let Mclock:=4*NativeOverlapMinimum.bareSourceClockConstant cl Az D+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (f : Fin aDegree → NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (W : ℝ),M.xs ≤ W →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale M.xs W initial e) →
          T.disorderExpect (fullWeight n) (fullFeature n) 0
            (cutFullVariance n (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) U 0 0 b h K)
            (fun σ=>|(G.canonicalMinimumSource M f).product σ|^4) 0  ≤
            (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*
              sourceMonomialScale M.xs W initial)^4 := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_bare_canonical_square_even_moment
    (D:=D) aDegree 2 ha (by norm_num) Bclock Temp Cmass hTemp hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,hCp,?_⟩
  filter_upwards [HP] with n hnP
  intro M hbareb hbareh hxs1 L us hus hret hmesh
  filter_upwards [hnP M hbareb hbareh hxs1 L us hus hret hmesh] with jGrid hgridP
  dsimp only at hgridP ⊢
  intro U T hT G f initial W hxW hmassOld
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let Kfinite:=finitePhysicalMixedClock (n+1) as b h
  let Mclock:=4*NativeOverlapMinimum.bareSourceClockConstant cl Az D+2*Temp
  let E:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)
  let P:=(G.canonicalMinimumSource M f).product
  let q:=cutFullVariance n (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) U 0 0 b h K
  let A:=cutLowError n U b h K
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have had:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.bf u:ℝ)  ≤  M.bf v from toNNReal_monotoneOn had.1 hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.hf u:ℝ)  ≤  M.hf v from toNNReal_monotoneOn had.2.1 hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.bf M.hf (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1)) as ho
  have hS0 j : 0  ≤  S j:=(physicalOrderedPathS_mem_unit n M.bf M.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) (partitionPoint_mem as ho j)).1
  have hK0 j : 0  ≤  K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (hS0 j))
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (hS0 i) (NNReal.coe_nonneg _))
  have hKfinite0:=finitePhysicalMixedClock_nonneg (n+1) as b h
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _)
  have hKfinitem:=finitePhysicalMixedClock_monotone (n+1) ho b h hbm hhm (fun _=>NNReal.coe_nonneg _)
  have hCf:=NativeOverlapMinimum.bare_source_clock_constant_nonneg (D:=D) hcl hAz
  have Hsource:=M.bare_source_clock_bounds hcl hAz Temp hbareb hbareh (partitionPoint_mem as ho as.length)
  have hfield : h as.length  ≤  2*NativeOverlapMinimum.bareSourceClockConstant cl Az D := by
    have HH:=mul_le_mul_of_nonneg_left
      (show M.xs+partitionPoint 0 as as.length  ≤  2 by linarith [(partitionPoint_mem as ho as.length).2]) hCf
    exact Hsource.2.2.2.trans (by linarith only [HH])
  have HS:=(physicalOrderedPathS_mem_unit n M.bf M.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) (partitionPoint_mem as ho as.length)).2
  have Hcur:=mul_le_mul_of_nonneg_left HS (NNReal.coe_nonneg (M.bf (partitionPoint 0 as as.length)))
  have Hfin:=mul_le_mul_of_nonneg_left (finitePhysicalMean_le_one (n+1) ho b h as.length)
    (NNReal.coe_nonneg (M.bf (partitionPoint 0 as as.length)))
  have hclock : K as.length+Kfinite as.length  ≤  Mclock := by
    dsimp only [K,Kfinite,finitePhysicalMixedClock,Mclock,b,h,S] at *
    linarith [Hsource.2.1]
  have hscale : 0  ≤  Cp^aDegree*sourceMonomialScale M.xs W initial := by
    rw [←source_factor_scale_product]
    exact mul_nonneg (pow_nonneg hCp.le _) (Finset.prod_nonneg fun e _=>
      (source_factor_scale_pos M.hxs (M.hxs.trans_le hxW) initial e).le)
  have Hraw:=hgridP U T 0 0 (by norm_num) (by norm_num) G f initial M.xs W le_rfl hxW hmassOld
  have HPcur:=native_wholeLaw_scalar_clock_nat_moment_le n U rBound 4 (by norm_num) T ho
    (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) b h K Kfinite
    (fun i=>by cases i <;> first | exact hbm | exact hhm)
    (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
    hbm hhm hKm hKfinitem (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _)
    hK0 hKfinite0 (by norm_num : (0:ℝ)∈Icc 0 1) (by norm_num : (0:ℝ)∈Icc 0 1)
    P (Cp^aDegree*sourceMonomialScale M.xs W initial) Mclock hscale
    (by dsimp [Mclock];positivity) hT hclock
    (by
      change T.disorderExpect (fullWeight n) (fullFeature n) 0
        (finitePhysicalCavitySquareVariance n U as b h 0 0) (fun σ=>|P σ|^4) 0  ≤  _
      simpa only [show 2*2=4 by norm_num,P,b,h,as] using Hraw)
  simpa only [P,E,q,mul_assoc] using HPcur

end OAI.SKFluctuations.Cavity
