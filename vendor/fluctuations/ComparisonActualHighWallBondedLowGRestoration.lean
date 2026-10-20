module

public import ComparisonActualHighWallBondedLowGHighProfile
public import ComparisonActualHighWallBondedLowGLowProfile
public import ComparisonSignedCavityGRestorationOriginalBudget
public import ComparisonActualHighWallHighProfile

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators

theorem eventually_actual_high_wall_low_factor_G_restoration
    (aDegree dOrder rBound : ℕ) (hd : 0< dOrder)
    (p : ℝ) (hp : 2< p) (hOrder : p/(p-2)≤(dOrder:ℝ))
    (Bclock Cmass Ccut : ℝ) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0< delta) (hroom : delta < 3*m)
    (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az) (hC0 : 0< C0) (hCt : 0≤ Ct) :
    ∃Ch Cl Cq : ℝ,0< Ch ∧ 0< Cl ∧ 0< Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let _Mclock:=2*M.data.T
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U≤ as.length → T.leaves≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm),
          partitionPoint 0 as U ≤ Ccut*M.data.d →
          (∀e,G.sourceLowMass e ≤ Cmass*M.data.d) →
        ∀u z a c e f : T.Slot,u≠z → T.splitIndex u z< U → e≠f →
          let R:=M.data.highErrorEnvelope M.alpha as U
          let CH:=Real.exp (wholeLawRowComparisonConstant rBound*(2*max Bclock 0))*Ch^(aDegree+1)*
            (M.data.d*M.data.d^aDegree)
          let CL:=Real.exp (wholeLawRowComparisonConstant rBound*(2*max Bclock 0))*Cl^(aDegree+1)*
            (M.data.d*M.data.d^aDegree)
          let J:=fun σ=>(G.canonicalHighWallSource M forms).product σ*
            (b (T.splitIndex u z)*(deletedOverlap n (joinSpin (T.atSlot σ u))
              (joinSpin (T.atSlot σ z))-S (T.splitIndex u z)))
          |nativeActualLawRestorationRemainder n q U b h K T
            (fun σ=>J σ*nativeOriginalHighGAtom T U K b S a c e f σ)|≤
            |(1/2:ℝ)*fullScalarCutConnected4 T U K a c e f| *
              (ClockTree.pairForkVariation rBound*CH*(2*M.data.T)^((p-2)/p)*(2*M.data.T)^((p-2)/p)*
                (R (T.splitIndex e f))^(2/p)*
                (T.forkCost (fun j=>(R j)^(2/p))+ClockTree.edgeBudget 0 as (fun j=>(R j)^(2/p)))+
                ClockTree.absJetVariation rBound 1*CL*R (T.splitIndex e f)*(Cq*M.data.d)) := by
  let Cgeom:=max Cmass Ccut
  have hCg : 0 ≤ Cgeom:=hCmass.trans (le_max_left _ _)
  obtain ⟨Ch,hCh,HH⟩:=eventually_actual_high_wall_bonded_low_G_high_profile
    (D:=D) aDegree dOrder rBound hd p hp hOrder Bclock Cgeom hCg
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cl,hCl,Cq,hCq,HL⟩:=eventually_actual_high_wall_bonded_low_G_low_profile
    (D:=D) aDegree rBound Bclock Cgeom Ccut hCg hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Ch,Cl,Cq,hCh,hCl,hCq,?_⟩
  filter_upwards [HH,HL] with n hnH hnL
  intro M hwork L us hus hret hmesh
  filter_upwards [hnH M hwork L us hus hret hmesh,
    hnL M hwork L us hus hret hmesh] with jGrid hgridH hgridL
  dsimp only at hgridH hgridL ⊢
  intro U T hU hT G forms hcut hmass u z a c e f huz huzcut hef
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let Mclock:=2*M.data.T
  let R:=M.data.highErrorEnvelope M.alpha as U
  let CH:=Real.exp (wholeLawRowComparisonConstant rBound*(2*max Bclock 0))*Ch^(aDegree+1)*
    (M.data.d*M.data.d^aDegree)
  let CL:=Real.exp (wholeLawRowComparisonConstant rBound*(2*max Bclock 0))*Cl^(aDegree+1)*
    (M.data.d*M.data.d^aDegree)
  let J:=fun σ=>(G.canonicalHighWallSource M forms).product σ*
    (b (T.splitIndex u z)*(deletedOverlap n (joinSpin (T.atSlot σ u))
      (joinSpin (T.atSlot σ z))-S (T.splitIndex u z)))
  let κ:=|(1/2:ℝ)*fullScalarCutConnected4 T U K a c e f|
  let BH:=κ*(ClockTree.pairForkVariation rBound*CH*(2*M.data.T)^((p-2)/p)*(2*M.data.T)^((p-2)/p)*
    (R (T.splitIndex e f))^(2/p)*
    (T.forkCost (fun j=>(R j)^(2/p))+ClockTree.edgeBudget 0 as (fun j=>(R j)^(2/p))))
  let BL:=κ*(ClockTree.absJetVariation rBound 1*CL*R (T.splitIndex e f)*(Cq*M.data.d))
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.bf M.hf
    (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) (partitionPoint_mem as ho j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.bf u:ℝ)≤ M.bf v from M.data.bf_monotone M.alpha hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.hf u:ℝ)≤ M.hf v from M.data.hf_monotone M.alpha hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.bf M.hf
      (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha)) as ho
  have hK0 j : 0≤ K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HS j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HS i).1 (NNReal.coe_nonneg _))
  have hW : 0 ≤ M.data.d:=M.data.hd.le
  have hscale : 0 ≤ M.data.d^aDegree:=pow_nonneg M.data.hd.le _
  have hmass' e : G.sourceLowMass e ≤ Cgeom*M.data.d:=(hmass e).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) M.data.hd.le)
  have hnew : partitionPoint 0 as (T.splitIndex u z) ≤ Cgeom*M.data.d:=by
    exact ((partitionPoint_mono as ho huzcut.le).trans hcut).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) M.data.hd.le)
  have hTemp := M.data.hTpos.le
  have hCH : 0≤ CH:=by dsimp [CH];positivity
  have hCL : 0≤ CL:=by dsimp [CL];positivity
  have hR j : 0≤ R j:=by
    dsimp only [R,ActualHighWallData.highErrorEnvelope,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg Mclock hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hH (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
      |cutMixedJet n q U b h K T (fun σ=>J σ*nativeOriginalHighGAtom T U K b S a c e f σ) 0 0 0 t|≤ BH:=by
    have H:=hgridH U T t hU ht hT G forms hmass' u z a c e f huz hnew hef
    apply H.trans
    have HR:=M.data.current_high_error_radius_le_original (l:=0) (t:=t) M.alpha ho U
      (by norm_num) ht (T.splitIndex e f) (T.splitIndex_le_clockLength e f)
    change nativeWholeLawErrorRadius n as (cutFullVariance n q U 0 t b h K)
      (cutTSlope n U 0 b h K) (T.splitIndex e f) ≤ R (T.splitIndex e f) at HR
    have HC:=M.data.current_high_profile_le_original (l:=0) (t:=t) M.alpha T ho U
      (by norm_num) ht (show 0≤2/p by positivity)
    change nativeWholeLawProfileCost n (cutFullVariance n q U 0 t b h K)
      (cutTSlope n U 0 b h K) T (2/p) ≤
      T.forkCost (fun j=>(R j)^(2/p))+edgeBudget 0 as (fun j=>(R j)^(2/p)) at HC
    have Hprof:=native_whole_law_profile_cost_nonneg n ho
      (cutFullVariance n q U 0 t b h K) (cutTSlope n U 0 b h K) T (2/p)
    have Hpv:=ClockTree.pairForkVariation_nonneg rBound
    have HRj:=hR (T.splitIndex e f)
    dsimp only [BH,κ]
    gcongr
    all_goals first | exact HR | exact HC | positivity | exact nativeWholeLawErrorRadius_nonneg _ _ _ _ _
  have hL (l : ℝ) (hl : l∈Icc (0:ℝ) 1) :
      |cutLowJet n q U b h K T (fun σ=>J σ*nativeOriginalHighGAtom T U K b S a c e f σ) 0 1 l 1|≤ BL:=by
    have H:=hgridL U T l hU hl hT G forms hcut hmass' u z a c e f huz hnew hef
    apply H.trans
    have HR:=M.data.current_high_error_radius_le_original (l:=l) (t:=1) M.alpha ho U
      hl (by norm_num) (T.splitIndex e f) (T.splitIndex_le_clockLength e f)
    change nativeWholeLawErrorRadius n as (cutFullVariance n q U l 1 b h K)
      (cutTSlope n U 0 b h K) (T.splitIndex e f) ≤ R (T.splitIndex e f) at HR
    have Hav:=ClockTree.absJetVariation_nonneg rBound 1
    have HRj:=hR (T.splitIndex e f)
    dsimp only [BL,κ]
    gcongr
  have H:=native_actual_law_restoration_abs_le n q U b h K T
    (fun σ=>J σ*nativeOriginalHighGAtom T U K b S a c e f σ) BH BL hH hL
  convert H using 1
  dsimp only [BH,BL,κ,CH,CL,R,J,Mclock,K,b,h,S,q,as]
  ring_nf

end OAI.SKFluctuations.Cavity
