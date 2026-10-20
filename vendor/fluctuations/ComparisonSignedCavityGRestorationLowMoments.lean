module

public import ComparisonSignedCavityWholeLawScalarLowProfile
public import ComparisonNativeActualMeanRawUpper
public import ComparisonSignedCavityMixedErrorCanonicalLedger

@[expose] public section

noncomputable section
set_option maxHeartbeats 15000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem eventually_actual_minimum_bare_original_low_profile_fourth
    (Bclock Temp Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cq : ℝ,0 < Cq ∧ ∀ᶠn : ℕ in atTop,
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
        ∀(U : ℕ) (l t s W : ℝ),U ≤ as.length →
          l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → s∈Icc (0:ℝ) 1 → M.xs ≤ W →
          partitionPoint 0 as U ≤ Ccut*W →
        ∀j,(ClockTree.pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0
          (cutFullVariance n q U l t b h K)
          (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U s b h K) j
            (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^4) 0 ≤ (Cq*W)^4 := by
  obtain ⟨Cs,hCs,HS⟩:=eventually_actual_minimum_mass_mean_upper
    (D:=D) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cf:=NativeOverlapMinimum.bareSourceClockConstant cl Az D
  have hCf : 0 ≤ Cf:=NativeOverlapMinimum.bare_source_clock_constant_nonneg hcl hAz
  let Bscalar:=4*Cf+2*Temp
  let Cscalar:=Cf+Temp*Cs
  have hBscalar : 0 ≤ Bscalar:=by dsimp [Bscalar];positivity
  have hCscalar : 0 ≤ Cscalar:=by dsimp [Cscalar];positivity
  obtain ⟨Cq,hCq,HQ⟩:=eventually_actual_minimum_bare_scalar_wholeLaw_low_profile_moment
    (D:=D) 2 (by norm_num) Bclock Temp Bscalar Cscalar hTemp hBscalar hCscalar
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cq*(1+Ccut),by positivity,?_⟩
  filter_upwards [HS,HQ] with n hnS hnQ
  intro M hb hh hxs L us hus hret hmesh
  filter_upwards [hnQ M hb hh hxs L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U l t s W hU hl ht hs hxW hcut j
  have hxs0:=M.hxs.le
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have had:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have HSunit j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.bf M.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) (partitionPoint_mem as ho j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.bf u:ℝ) ≤ M.bf v from toNNReal_monotoneOn had.1 hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.hf u:ℝ) ≤ M.hf v from toNNReal_monotoneOn had.2.1 hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.bf M.hf (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1)) as ho
  have hK0 j : 0 ≤ K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HSunit j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HSunit i).1 (NNReal.coe_nonneg _))
  have Hb j : b j ≤ Temp:=
    (M.bare_source_clock_bounds hcl hAz Temp hb hh (partitionPoint_mem as ho j)).2.1
  have Hfield j : h j ≤ Cf*(M.xs+partitionPoint 0 as j):=
    (M.bare_source_clock_bounds hcl hAz Temp hb hh (partitionPoint_mem as ho j)).2.2.2
  have Hmean j : S j ≤ Cs*(M.xs+partitionPoint 0 as j):=by
    by_cases hj : 0 < partitionPoint 0 as j
    · exact hnS M _ ⟨hj,(partitionPoint_mem as ho j).2⟩
    · have hz : partitionPoint 0 as j=0:=le_antisymm (le_of_not_gt hj) (partitionPoint_mem as ho j).1
      dsimp only [S]
      rw [hz,orderedPathS,orderedPathPair_zero]
      positivity
  have Hlocal j : |K j| ≤ Cscalar*(M.xs+partitionPoint 0 as j):=by
    rw [abs_of_nonneg (hK0 j)]
    have Hp:=mul_le_mul (Hb j) (Hmean j) (HSunit j).1 hTemp
    dsimp only [K,Cscalar]
    nlinarith only [Hp,Hfield j]
  have HKbound : K as.length ≤ Bscalar:=by
    have Hmass:= (partitionPoint_mem as ho as.length).2
    have Hh : h as.length ≤ 2*Cf:= (Hfield _).trans (by
      have H:=mul_le_mul_of_nonneg_left (show M.xs+partitionPoint 0 as as.length ≤ 2 by linarith) hCf
      linarith only [H])
    have Hp:=mul_le_mul (Hb as.length) (HSunit as.length).2 (HSunit as.length).1 hTemp
    dsimp only [K,Bscalar]
    linarith
  change (ClockTree.pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0
    (cutFullVariance n (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) U l t b h K)
    (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U s b h K) j
      (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^4) 0 ≤ _
  by_cases hj : j<U
  · have H:=hgrid U K l t s hl ht hs hKm hK0 HKbound j (by omega) (fun _=>Hlocal j)
    have Hmass : partitionPoint 0 as j ≤ partitionPoint 0 as U:=partitionPoint_mono as ho (by omega)
    have Hscale : Cq*(M.xs+partitionPoint 0 as j) ≤ (Cq*(1+Ccut))*W:=by
      have HH:=mul_le_mul_of_nonneg_left (show M.xs+partitionPoint 0 as j ≤ (1+Ccut)*W by nlinarith) hCq.le
      nlinarith only [HH]
    exact H.trans (pow_le_pow_left₀ (by positivity [(partitionPoint_mem as ho j).1]) Hscale 4)
  · have HE (σ τ : Spin n×Bool) : ReplicaTree.coordinateProfile (fullFeature n)
        (cutLSlope n U s b h K) j σ τ=0:=scalarPhysicalSquareLowKernel_at_high n U b h K s hj σ τ
    simp_rw [HE,abs_zero,zero_pow (by norm_num : (4:ℕ)≠0)]
    simp only [ClockTree.disorderExpect,mul_zero,Finset.sum_const_zero]
    positivity

end OAI.SKFluctuations.Cavity
