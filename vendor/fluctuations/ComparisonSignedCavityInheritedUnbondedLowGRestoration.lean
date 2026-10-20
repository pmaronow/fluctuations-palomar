module

public import ComparisonSignedCavityInheritedUnbondedLowGHighProfile
public import ComparisonSignedCavityInheritedUnbondedLowGLowProfile
public import ComparisonSignedCavityInheritedGRestorationOriginalBudget

public import ComparisonSignedCavityCanonicalUnbondedLowGRestoration
public import ComparisonSignedCavityInheritedErrorTransport

@[expose] public section

noncomputable section
set_option maxHeartbeats 24000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal ENNReal
open Classical
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_minimum_inherited_unbonded_low_G_restoration
    (aDegree dOrder rBound : ℕ) (hd : 0<dOrder)
    (p : ℝ) (hp : 2<p) (hOrder : p/(p-2)≤(dOrder:ℝ))
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0<delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct) :
    ∃Ch Cl Cq : ℝ,0<Ch ∧ 0<Cl ∧ 0<Cq ∧ ∀ᶠn : ℕ in atTop,
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
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U≤as.length → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs≤x →x≤W →
          partitionPoint 0 as U≤Ccut*W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e) →
        ∀u z a c e f : T.Slot,u≠z → T.splitIndex u z<U → e≠f →
          let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as Mclock Temp
          let CH:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Ch^(aDegree+1)*
            (W*sourceMonomialScale x W initial)
          let CL:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cl^(aDegree+1)*
            (W*sourceMonomialScale x W initial)
          let J:=fun σ=>(G.canonicalMinimumSource M forms).product σ*
            (deletedOverlap n (joinSpin (T.atSlot σ u))
              (joinSpin (T.atSlot σ z))-S (T.splitIndex u z))
          |nativeActualLawRestorationRemainder n q U b h K T
            (fun σ=>J σ*nativeOriginalHighGAtom T U K b S a c e f σ)|≤
            |(1/2:ℝ)*fullScalarCutConnected4 T U K a c e f| *
              (ClockTree.pairForkVariation rBound*CH*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*
                (R (T.splitIndex e f))^(2/p)*
                (T.forkCost (fun j=>(R j)^(2/p))+ClockTree.edgeBudget 0 as (fun j=>(R j)^(2/p)))+
                ClockTree.absJetVariation rBound 1*CL*R (T.splitIndex e f)*(Cq*(1+Ccut)*W)) := by
  obtain ⟨Ch,hCh,HH⟩:=eventually_actual_minimum_inherited_unbonded_low_G_high_profile
    (D:=D) aDegree dOrder rBound hd p hp hOrder Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cl,Cq,hCl,hCq,HL⟩:=eventually_actual_minimum_inherited_unbonded_low_G_low_profile
    (D:=D) aDegree rBound Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Ch,Cl,Cq,hCh,hCl,hCq,?_⟩
  filter_upwards [HH,HL] with n hnH hnL
  intro M hsource hxs L us hus hret hmesh
  filter_upwards [hnH M hsource hxs L us hus hret hmesh,
    hnL M hsource hxs L us hus hret hmesh] with jGrid hgridH hgridL
  dsimp only at hgridH hgridL ⊢
  intro U T hU hT G forms initial x W hxsx hxW hcut hmass u z a c e f huz huzcut hef
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let Mclock:=4*Cf+2*Temp
  let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as Mclock Temp
  let CH:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Ch^(aDegree+1)*
    (W*sourceMonomialScale x W initial)
  let CL:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cl^(aDegree+1)*
    (W*sourceMonomialScale x W initial)
  let J:=fun σ=>(G.canonicalMinimumSource M forms).product σ*
    (deletedOverlap n (joinSpin (T.atSlot σ u))
      (joinSpin (T.atSlot σ z))-S (T.splitIndex u z))
  let κ:=|(1/2:ℝ)*fullScalarCutConnected4 T U K a c e f|
  let BH:=κ*(ClockTree.pairForkVariation rBound*CH*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*
    (R (T.splitIndex e f))^(2/p)*
    (T.forkCost (fun j=>(R j)^(2/p))+ClockTree.edgeBudget 0 as (fun j=>(R j)^(2/p))))
  let BL:=κ*(ClockTree.absJetVariation rBound 1*CL*R (T.splitIndex e f)*(Cq*(1+Ccut)*W))
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have had:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.bf M.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) (partitionPoint_mem as ho j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.bf u:ℝ)≤M.bf v from toNNReal_monotoneOn had.1 hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.hf u:ℝ)≤M.hf v from toNNReal_monotoneOn had.2.1 hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.bf M.hf
      (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1)) as ho
  have hK0 j : 0≤K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HS j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HS i).1 (NNReal.coe_nonneg _))
  have hW : 0≤W:=(M.hxs.le.trans hxsx).trans hxW
  have hscale : 0 ≤ sourceMonomialScale x W initial:=by
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun i _=>(source_factor_scale_pos (M.hxs.trans_le hxsx) ((M.hxs.trans_le hxsx).trans_le hxW) initial i).le
  have hCH : 0≤CH:=by dsimp [CH];positivity
  have hCL : 0≤CL:=by dsimp [CL];positivity
  have hR j : 0≤R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg Mclock hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hH (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
      |cutMixedJet n q U b h K T (fun σ=>J σ*nativeOriginalHighGAtom T U K b S a c e f σ) 0 0 0 t|≤BH:=by
    rw [native_cutMixedJet_zero_eq_profile n q U b h K T ho _ 0
      (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
      (fun i=>by cases i <;> first | exact hbm | exact hhm)
      (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm (by norm_num) ht]
    have H:=hgridH U T 0 t hU (by norm_num) ht hT G forms initial x W hxsx hxW hcut hmass u z a c e f huz huzcut hef
    apply H.trans
    have HR:=Real.rpow_le_rpow (nativeWholeLawErrorRadius_nonneg n as _ _ (T.splitIndex e f))
      (actual_minimum_inherited_current_high_error_radius_le_original (l:=0) (t:=t) M Temp Cf hTemp hCf hsource hxs ho U
        (by norm_num) ht (T.splitIndex e f) (T.splitIndex_le_clockLength e f)) (show 0≤2/p by positivity)
    have HC:=actual_minimum_inherited_current_high_profile_le_original (l:=0) (t:=t) M Temp Cf hTemp hCf hsource hxs T ho U
      (by norm_num) ht (show 0≤2/p by positivity)
    have Hprof:=native_whole_law_profile_cost_nonneg n ho
      (cutFullVariance n q U 0 t b h K) (cutTSlope n U 0 b h K) T (2/p)
    have Hpv:=ClockTree.pairForkVariation_nonneg rBound
    have HRj:=hR (T.splitIndex e f)
    dsimp only [BH,κ]
    gcongr
  have hL (l : ℝ) (hl : l∈Icc (0:ℝ) 1) :
      |cutLowJet n q U b h K T (fun σ=>J σ*nativeOriginalHighGAtom T U K b S a c e f σ) 0 1 l 1|≤BL:=by
    rw [cutLowJet_eq_profileJets n q U b h K T ho _ 0
      (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
      (fun i=>by cases i <;> first | exact hbm | exact hhm)
      (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm 1 hl (by norm_num)]
    simp only [List.replicate_one]
    have H:=hgridL U T l 1 hU hl (by norm_num) hT G forms initial x W hxsx hxW hcut hmass u z a c e f huz huzcut hef
    apply H.trans
    have HR:=actual_minimum_inherited_current_high_error_radius_le_original (l:=l) (t:=1) M Temp Cf hTemp hCf hsource hxs ho U
      hl (by norm_num) (T.splitIndex e f) (T.splitIndex_le_clockLength e f)
    have Hav:=ClockTree.absJetVariation_nonneg rBound 1
    have HRj:=hR (T.splitIndex e f)
    dsimp only [BL,κ]
    gcongr
  have H:=native_actual_law_restoration_abs_le n q U b h K T
    (fun σ=>J σ*nativeOriginalHighGAtom T U K b S a c e f σ) BH BL hH hL
  convert H using 1
  dsimp only [BH,BL,κ,CH,CL,R,J,Mclock,K,b,h,S,q,as]
  ring

end OAI.SKFluctuations.Cavity
