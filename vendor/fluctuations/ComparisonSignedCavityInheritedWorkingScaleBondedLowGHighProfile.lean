module

public import ComparisonSignedCavityInheritedWorkingScaleBondedLowFactor
public import ComparisonSignedCavityGRestorationProfile
public import ComparisonSignedCavityMixedErrorCanonicalLedger

@[expose] public section

noncomputable section
set_option maxHeartbeats 30000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators

theorem eventually_actual_minimum_inherited_working_scale_low_factor_G_high_profile
    (aDegree dOrder rBound : ℕ) (hd : 0<dOrder)
    (p : ℝ) (hp : 2<p) (hOrder : p/(p-2)≤(dOrder:ℝ))
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct) :
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
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),
          U≤as.length → l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (xScale W : ℝ),M.xs ≤ xScale → xScale ≤ W →
          partitionPoint 0 as U≤Ccut*W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale xScale W initial e) →
        ∀u z a c e f : T.Slot,u≠z → T.splitIndex u z<U → e≠f →
          let law:=cutFullVariance n q U l t b h K
          let A:=cutTSlope n U 0 b h K
          let J:=fun σ=>(G.canonicalMinimumSource M forms).product σ*
            (b (T.splitIndex u z)*(deletedOverlap n (joinSpin (T.atSlot σ u))
              (joinSpin (T.atSlot σ z))-S (T.splitIndex u z)))
          |ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0 law 0
            [ReplicaTree.coordinateProfile (fullFeature n) A] T
            (fun σ=>J σ*nativeOriginalHighGAtom T U K b S a c e f σ)|≤
            |(1/2:ℝ)*fullScalarCutConnected4 T U K a c e f| *
              (ClockTree.pairForkVariation rBound*
                (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^(aDegree+1)*
                  (W*sourceMonomialScale xScale W initial))*
                (2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*
                (nativeWholeLawErrorRadius n as law A (T.splitIndex e f))^(2/p)*
                nativeWholeLawProfileCost n law A T (2/p)) := by
  let Cjoint:=Cmass+Ccut+1
  have hCjoint : 0≤Cjoint:=by dsimp [Cjoint];positivity
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_inherited_canonical_working_scale_low_factor_even_moment
    (D:=D) aDegree dOrder rBound hd Bclock Temp Cf Cjoint hTemp hCf hCjoint
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,hCp,?_⟩
  filter_upwards [HP] with n hnP
  intro M hsource hxs L us hus hret hmesh
  filter_upwards [hnP M hsource hxs L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U T l t hU hl ht hT G forms initial xScale W hxsScale hxW hcut hmass u z a c e f huz huzcut hef
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let law:=cutFullVariance n q U l t b h K
  let A:=cutTSlope n U 0 b h K
  let Mclock:=4*Cf+2*Temp
  let C:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^(aDegree+1)*
    (W*sourceMonomialScale xScale W initial)
  let J:=fun σ=>(G.canonicalMinimumSource M forms).product σ*
    (b (T.splitIndex u z)*(deletedOverlap n (joinSpin (T.atSlot σ u))
      (joinSpin (T.atSlot σ z))-S (T.splitIndex u z)))
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have HW : 0<W:=M.hxs.trans_le (hxsScale.trans hxW)
  have HC : 0≤C:=by
    dsimp only [C]
    rw [←source_factor_scale_product]
    exact mul_nonneg (by positivity) (mul_nonneg HW.le (Finset.prod_nonneg fun e _=>
      (source_factor_scale_pos (M.hxs.trans_le hxsScale) HW initial e).le))
  have Hmass' e : G.sourceLowMass e≤Cjoint*sourceFactorScale xScale W initial e := by
    apply (hmass e).trans
    apply mul_le_mul_of_nonneg_right (by dsimp [Cjoint];linarith)
      (source_factor_scale_pos (M.hxs.trans_le hxsScale) HW initial e).le
  have Hnew : partitionPoint 0 as (T.splitIndex u z)≤Cjoint*W := by
    apply (partitionPoint_mono as ho huzcut.le).trans
    exact hcut.trans (mul_le_mul_of_nonneg_right (by dsimp [Cjoint];linarith) HW.le)
  have Hraw:=hgrid U T l t hl ht hT G forms initial xScale W hxsScale hxW Hmass' u z huz Hnew
  have Hmoment : T.disorderExpect (fullWeight n) (fullFeature n) 0 law
      (fun σ=>|J σ|^(2*(p/(p-2)))) 0≤C^(2*(p/(p-2))) := by
    apply T.disorderExpect_rpow_moment_le (fullWeight_pos n) (fullFeature n) ho 0 law 0 J
      (by have Hq : 0<p/(p-2):=div_pos (by linarith) (by linarith);positivity)
      (show 2*(p/(p-2))≤((2*dOrder:ℕ):ℝ) by push_cast;linarith) HC
    simpa only [Real.rpow_natCast,C,J,law,q,b,h,S,K,Mclock,as] using Hraw
  have had:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.bf M.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) (partitionPoint_mem as ho j)
  have Hb j : b j≤Temp:=(hsource _ (partitionPoint_mem as ho j)).1
  exact native_original_G_profile_restoration_bound n U b h K S (fun _=>rfl) T ho hU hT law J a c e f hef A
    HC hp (show 0≤2*Temp by positivity) (show 0≤2*Temp by positivity) Hmoment
    (native_centered_high_kernel_abs_le n U b h S (fun _=>NNReal.coe_nonneg _) Hb HS)
    (native_centered_high_kernel_abs_le n U b h S (fun _=>NNReal.coe_nonneg _) Hb HS)

end OAI.SKFluctuations.Cavity
