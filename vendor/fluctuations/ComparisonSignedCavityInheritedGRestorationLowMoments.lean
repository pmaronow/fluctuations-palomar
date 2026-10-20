module

public import ComparisonSignedCavityInheritedContinuumLowProfile
public import ComparisonSignedCavityGRestorationLowMoments

@[expose] public section

noncomputable section
set_option maxHeartbeats 16000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem eventually_actual_minimum_inherited_original_low_profile_fourth
    (Bclock Temp Cf Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cq : ℝ,0 < Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
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
  obtain ⟨Cq,hCq,HQ⟩:=eventually_actual_minimum_inherited_continuum_low_profile_moment
    (D:=D) 2 (by norm_num) Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cq*(1+Ccut),by positivity,?_⟩
  filter_upwards [HQ] with n hnQ
  intro M hsource hxs L us hus hret hmesh
  filter_upwards [hnQ M hsource hxs L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U l t s W hU hl ht hs hxW hcut j
  have hxs0:=M.hxs.le
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  change (ClockTree.pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0
    (cutFullVariance n (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) U l t b h K)
    (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U s b h K) j
      (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^4) 0 ≤ _
  by_cases hj : j<U
  · have H:=hgrid U l t s hl ht hs j (by omega)
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
