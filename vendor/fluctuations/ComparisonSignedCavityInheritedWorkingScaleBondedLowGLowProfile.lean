module

public import ComparisonSignedCavityGFiniteRawProfile
public import ComparisonSignedCavityInheritedWorkingScaleBondedLowGHighProfile
public import ComparisonSignedCavityInheritedContinuumLowProfile

@[expose] public section

noncomputable section
set_option maxHeartbeats 30000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators

theorem eventually_actual_minimum_inherited_working_scale_low_factor_G_low_profile
    (aDegree rBound : ℕ)
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct) :
    ∃Cp Cq : ℝ,0<Cp ∧ 0<Cq ∧ ∀ᶠn : ℕ in atTop,
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
          let J:=fun σ=>(G.canonicalMinimumSource M forms).product σ*
            (b (T.splitIndex u z)*(deletedOverlap n (joinSpin (T.atSlot σ u))
              (joinSpin (T.atSlot σ z))-S (T.splitIndex u z)))
          |ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0 law 0
            [ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U 1 b h K)] T
            (fun σ=>J σ*nativeOriginalHighGAtom T U K b S a c e f σ)|≤
            |(1/2:ℝ)*fullScalarCutConnected4 T U K a c e f| *
              (ClockTree.absJetVariation rBound 1*
                (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^(aDegree+1)*
                  (W*sourceMonomialScale xScale W initial))*
                nativeWholeLawErrorRadius n as law (cutTSlope n U 0 b h K) (T.splitIndex e f)*
                (Cq*(1+Ccut)*W)) := by
  let Cjoint:=Cmass+Ccut+1
  have hCjoint : 0≤Cjoint:=by dsimp [Cjoint];positivity
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_inherited_canonical_working_scale_low_factor_even_moment
    (D:=D) aDegree 2 rBound (by norm_num) Bclock Temp Cf Cjoint hTemp hCf hCjoint
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cq,hCq,HQ⟩:=eventually_actual_minimum_inherited_continuum_low_profile_moment
    (D:=D) 2 (by norm_num) Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,Cq,hCp,hCq,?_⟩
  filter_upwards [HP,HQ] with n hnP hnQ
  intro M hsource hxs L us hus hret hmesh
  filter_upwards [hnP M hsource hxs L us hus hret hmesh,
    hnQ M hsource hxs L us hus hret hmesh] with jGrid hgrid hgridQ
  dsimp only at hgrid hgridQ ⊢
  intro U T l t hU hl ht hT G forms initial xScale W hxsScale hxW hcut hmass u z a c e f huz huzcut hef
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let law:=cutFullVariance n q U l t b h K
  let Mclock:=4*Cf+2*Temp
  let C:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^(aDegree+1)*
    (W*sourceMonomialScale xScale W initial)
  let rho:=Cq*(1+Ccut)*W
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
  have Hrho : 0<rho:=by dsimp [rho];positivity
  have Hmass' e : G.sourceLowMass e≤Cjoint*sourceFactorScale xScale W initial e := by
    apply (hmass e).trans
    exact mul_le_mul_of_nonneg_right (by dsimp [Cjoint];linarith)
      (source_factor_scale_pos (M.hxs.trans_le hxsScale) HW initial e).le
  have Hnew : partitionPoint 0 as (T.splitIndex u z)≤Cjoint*W := by
    apply (partitionPoint_mono as ho huzcut.le).trans
    exact hcut.trans (mul_le_mul_of_nonneg_right (by dsimp [Cjoint];linarith) HW.le)
  have HPmoment : T.disorderExpect (fullWeight n) (fullFeature n) 0 law
      (fun σ=>|J σ|^4) 0≤C^4 := hgrid U T l t hl ht hT G forms initial xScale W hxsScale hxW Hmass' u z huz Hnew
  have HQmoment j (hj : j≤as.length) : (ClockTree.pairClock as j).disorderExpect
      (fullWeight n) (fullFeature n) 0 law
      (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U 1 b h K) j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^4) 0≤rho^4 := by
    by_cases hju : j<U
    · have Hraw:=hgridQ U l t 1 hl ht (by norm_num) j hj
      apply Hraw.trans
      apply pow_le_pow_left₀ (mul_nonneg hCq.le (add_nonneg M.hxs.le (partitionPoint_mem as ho j).1))
      dsimp only [rho]
      have Hmass:=partitionPoint_mono as ho hju.le
      have Hscale : M.xs+partitionPoint 0 as j≤(1+Ccut)*W := by nlinarith only [hxsScale,hxW,hcut,Hmass]
      exact (mul_le_mul_of_nonneg_left Hscale hCq.le).trans_eq (by ring)
    · have HE : (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U 1 b h K) j
          (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^4)=fun _=>0 := by
        funext σ
        simp only [ReplicaTree.coordinateProfile,cutLSlope,hju,ite_false,Pi.zero_apply,
          zero_mul,Finset.sum_const_zero,abs_zero,zero_pow (by norm_num : (4:ℕ)≠0)]
      rw [HE]
      simp only [ClockTree.disorderExpect,mul_zero,Finset.sum_const_zero]
      exact pow_nonneg Hrho.le _
  exact native_original_G_finite_raw_profile_restoration_bound n U b h K S (fun _=>rfl) T ho hU hT law J
    a c e f hef (cutLSlope n U 1 b h K) HC Hrho HPmoment HQmoment

end OAI.SKFluctuations.Cavity
