module

public import ComparisonSignedCavityFixedLowRestorationBudget

@[expose] public section

noncomputable section
set_option maxHeartbeats 15000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators

theorem eventually_actual_minimum_bare_canonical_second_low_restoration
    (aDegree rBound : ℕ) (ha : 0<aDegree)
    (Bclock Temp Cmass Ccut : ℝ) (hTemp : 0≤Temp) (hCmass : 0≤Cmass) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct) :
    ∃Cp : ℝ,0<Cp ∧ ∃Cq : ℝ,0<Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        (∀u,M.b u=Temp) → (∀u,M.h u=0) → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*NativeOverlapMinimum.bareSourceClockConstant cl Az D+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l : ℝ),
          U≤as.length → l∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (W : ℝ),M.xs≤W →
          partitionPoint 0 as U≤Ccut*W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale M.xs W initial e) →
        ∀u z : T.Slot,u≠z → T.splitIndex u z<U →
          |cutLowJet n q U b h K T
            (fun σ=>(G.canonicalMinimumSource M forms).product σ*
              restCenteredFixedForkKernel n b S (T.splitIndex u z) 0
                (T.atSlot σ u).1 (T.atSlot σ z).1) 0 2 l 1|≤
            ClockTree.absJetVariation rBound 2*
              (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*
                sourceMonomialScale M.xs W initial)*
              nativeWholeLawErrorRadius n as (cutFullVariance n q U l 1 b h K)
                (cutLowError n U b h K) (T.splitIndex u z)*(Cq*(1+Ccut)*W)^2 := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_bare_canonical_continuum_square_even_moment
    (D:=D) aDegree 2 rBound ha (by norm_num) Bclock Temp Cmass hTemp hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cq,hCq,HQ⟩:=eventually_actual_minimum_bare_continuum_low_profile_moment
    (D:=D) 4 (by norm_num) Bclock Temp hTemp hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,hCp,Cq,hCq,?_⟩
  filter_upwards [HP,HQ] with n hnP hnQ
  intro M hb hh hxs L us hus hret hmesh
  filter_upwards [hnP M hb hh hxs L us hus hret hmesh,
    hnQ M hb hh hxs L us hus hret hmesh] with jGrid hgrid hgridQ
  dsimp only at hgrid hgridQ ⊢
  intro U T l hU hl hT G forms initial W hxW hcut hmass u z huz huzcut
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let Mclock:=4*NativeOverlapMinimum.bareSourceClockConstant cl Az D+2*Temp
  let C:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*
    sourceMonomialScale M.xs W initial
  let rho:=Cq*(1+Ccut)*W
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
    (physicalOrderedPathS_monotone_unit n M.bf M.hf (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1)) as ho
  have hK0 j : 0≤K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HS j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HS i).1 (NNReal.coe_nonneg _))
  have hCf:=NativeOverlapMinimum.bare_source_clock_constant_nonneg (D:=D) hcl hAz
  have HM : 0≤Mclock:=by dsimp [Mclock];positivity
  have HC : 0≤C:=by
    dsimp only [C]
    rw [←source_factor_scale_product]
    exact mul_nonneg (by positivity) (Finset.prod_nonneg fun i _=>
      (source_factor_scale_pos M.hxs (M.hxs.trans_le hxW) initial i).le)
  have HW : 0<W:=M.hxs.trans_le hxW
  have Hrho : 0<rho:=by dsimp [rho];positivity
  have Hclock j (_hj : j≤as.length) : |b j|≤Mclock∧|h j|≤Mclock∧|K j|≤Mclock := by
    have Hfield:=M.bare_source_clock_bounds hcl hAz Temp hb hh (partitionPoint_mem as ho j)
    have Hh : h j≤2*NativeOverlapMinimum.bareSourceClockConstant cl Az D := by
      have H:=mul_le_mul_of_nonneg_left
        (show M.xs+partitionPoint 0 as j≤2 by linarith [(partitionPoint_mem as ho j).2]) hCf
      exact Hfield.2.2.2.trans (by linarith only [H])
    have HK : K j≤2*NativeOverlapMinimum.bareSourceClockConstant cl Az D+Temp := by
      have H:=mul_le_mul_of_nonneg_left (HS j).2 (NNReal.coe_nonneg (M.bf (partitionPoint 0 as j)))
      dsimp only [K]
      linarith [Hfield.2.1]
    rw [abs_of_nonneg (NNReal.coe_nonneg _),abs_of_nonneg (NNReal.coe_nonneg _),abs_of_nonneg (hK0 j)]
    dsimp only [Mclock]
    exact ⟨by linarith [Hfield.2.1],by linarith,by linarith⟩
  have HQmoment j (hj : j≤as.length) : (ClockTree.pairClock as j).disorderExpect
      (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l 1 b h K)
      (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U 1 b h K) j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^8) 0≤rho^8 := by
    by_cases hju : j<U
    · have Hraw:=hgridQ U l 1 1 hl (by norm_num) (by norm_num) j hj
      apply Hraw.trans
      apply pow_le_pow_left₀ (mul_nonneg hCq.le
        (add_nonneg M.hxs.le (partitionPoint_mem as ho j).1))
      dsimp only [rho]
      have Hmass:=partitionPoint_mono as ho hju.le
      have Hscale : M.xs+partitionPoint 0 as j≤(1+Ccut)*W := by
        nlinarith only [hxW,hcut,Hmass]
      exact (mul_le_mul_of_nonneg_left Hscale hCq.le).trans_eq (by ring)
    · have HE : (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U 1 b h K) j
          (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^8)=fun _=>0 := by
        funext σ
        simp only [ReplicaTree.coordinateProfile,cutLSlope,hju,ite_false,Pi.zero_apply,
          zero_mul,Finset.sum_const_zero,abs_zero,zero_pow (by norm_num : (8:ℕ)≠0)]
      rw [HE]
      simp only [ClockTree.disorderExpect,mul_zero,Finset.sum_const_zero]
      exact pow_nonneg Hrho.le _
  exact native_fixed_low_second_restoration_wholeLaw_bound n U q b h S T ho hT
    (G.canonicalMinimumSource M forms).product u z huz huzcut hl HC Hrho HM
    (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
    (fun i=>by cases i <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm
    (hgrid U T l 1 hl (by norm_num) hT G forms initial W hxW hmass) Hclock HQmoment

end OAI.SKFluctuations.Cavity
