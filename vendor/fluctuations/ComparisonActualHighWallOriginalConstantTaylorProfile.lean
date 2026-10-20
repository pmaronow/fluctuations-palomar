module

public import ComparisonActualHighWallOriginalConstantThirdLow
public import ComparisonActualHighWallCanonicalHighTaylorProfile
public import ComparisonSignedCavityActualTaylorHighLowBudget

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000

theorem eventually_actual_high_wall_original_constant_HIGH_profile
    (rBound dOrder : ℕ) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ)) (Bclock Ccut : ℝ) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      M.xs=M.data.d → ∀(L : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠj : ℕ in atTop,
        let as:=finiteCutMasses us j
        let b:=fun k=>(M.bf (partitionPoint 0 as k):ℝ)
        let h:=fun k=>(M.hf (partitionPoint 0 as k):ℝ)
        let K:=nativeContinuumMixedClock n M.bf M.hf as
        let q : ℕ→RestCoordinate n→ℝ:=fun k=>Sum.elim (fun _=>b k) (fun _=>h k)
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U ≤ as.length → T.leaves ≤ rBound →
        partitionPoint 0 as U ≤ Ccut*M.data.d →
        ∀(a z : T.Slot) (l t : ℝ),l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → ∀part : Fin 3,
          let R:=M.data.highErrorEnvelope M.alpha as U
          |nativeActualHigherHighPart part n q U b h K T (fun _=>1) a z l t| ≤
            C*M.data.d*(T.forkCost (fun k=>(R k)^(4/p))+edgeBudget 0 as (fun k=>(R k)^(4/p))+
              M.data.d*(T.forkCost R+edgeBudget 0 as R)) := by
  obtain ⟨C,hC,HC⟩:=eventually_actual_high_wall_canonical_HIGH_parts_profile
    (D:=D) 0 rBound dOrder hd p hp hOrder Bclock 0 Ccut (by norm_num) hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [HC] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with j hj
  dsimp only at hj ⊢
  intro U T hU hT hcut a z l t hl ht part
  let G : ActualNaturalBoundaryShape n 0 T:=
    ⟨Fin.elim0,Fin.elim0,Fin.elim0,Fin.elim0,(fun e=>Fin.elim0 e),(fun e=>Fin.elim0 e)⟩
  let forms : Fin 0→NativeSourceFactorForm:=Fin.elim0
  have H:=hj U T hU hT G forms hcut (fun e=>Fin.elim0 e) a z l t hl ht part
  have Heq : (G.canonicalHighWallSource M forms).product=(fun _=>1):=by
    funext σ
    simp only [ActualNaturalBoundaryShape.product,fullBoundaryAffineProduct,Fin.prod_univ_zero]
  rw [Heq] at H
  simpa only [pow_zero,mul_one] using H

theorem eventually_actual_high_wall_original_constant_Taylor_remainder_profile
    (rBound dOrder : ℕ) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ)) (Bclock Ccut : ℝ) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      M.xs=M.data.d → ∀(L : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠj : ℕ in atTop,
        let as:=finiteCutMasses us j
        let b:=fun k=>(M.bf (partitionPoint 0 as k):ℝ)
        let h:=fun k=>(M.hf (partitionPoint 0 as k):ℝ)
        let K:=nativeContinuumMixedClock n M.bf M.hf as
        let q : ℕ→RestCoordinate n→ℝ:=fun k=>Sum.elim (fun _=>b k) (fun _=>h k)
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U ≤ as.length → T.leaves ≤ rBound →
        partitionPoint 0 as U ≤ Ccut*M.data.d →
        ∀a z : T.Slot,
          let R:=M.data.highErrorEnvelope M.alpha as U
          |nativeActualTaylorRemainder n q U b h K T (fun _=>1) a z| ≤
            C*(M.data.d*(T.forkCost (fun k=>(R k)^(4/p))+edgeBudget 0 as (fun k=>(R k)^(4/p))+
              M.data.d*(T.forkCost R+edgeBudget 0 as R))+M.data.d^3) := by
  obtain ⟨CH,hCH,HH⟩:=eventually_actual_high_wall_original_constant_HIGH_profile
    (D:=D) rBound dOrder hd p hp hOrder Bclock Ccut hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨CL,hCL,HL⟩:=eventually_actual_high_wall_original_constant_third_low_cubic
    (D:=D) rBound Bclock Ccut hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨2*CH+CL,by positivity,?_⟩
  filter_upwards [HH,HL] with n hnH hnL
  intro M hwork L us hus hret hmesh
  filter_upwards [hnH M hwork L us hus hret hmesh,
    hnL M hwork L us hus hret hmesh] with j hjH hjL
  dsimp only at hjH hjL ⊢
  intro U T hU hT hcut a z
  let as:=finiteCutMasses us j
  let b:=fun k=>(M.bf (partitionPoint 0 as k):ℝ)
  let h:=fun k=>(M.hf (partitionPoint 0 as k):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun k=>Sum.elim (fun _=>b k) (fun _=>h k)
  let R:=M.data.highErrorEnvelope M.alpha as U
  let profile:=T.forkCost (fun k=>(R k)^(4/p))+edgeBudget 0 as (fun k=>(R k)^(4/p))+
    M.data.d*(T.forkCost R+edgeBudget 0 as R)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus j
  have hbf:=M.data.bf_monotone M.alpha
  have hhf:=M.data.hf_monotone M.alpha
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.bf u:ℝ)≤M.bf v from hbf hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.hf u:ℝ)≤M.hf v from hhf hu hv huv) as ho
  have hR k : 0 ≤ R k:=M.data.highErrorEnvelope_nonneg M.alpha as U k
  have hprofile : 0 ≤ profile:=add_nonneg
    (add_nonneg (T.forkCost_nonneg (fun k=>Real.rpow_nonneg (hR k) _))
      (edgeBudget_nonneg ho (fun k=>Real.rpow_nonneg (hR k) _)))
    (mul_nonneg M.data.hd.le (add_nonneg (T.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)))
  have HHi (l t : ℝ) (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1) (part : Fin 3) :
      |nativeActualHigherHighPart part n q U b h K T (fun _=>1) a z l t| ≤ CH*M.data.d*profile:=by
    exact hjH U T hU hT hcut a z l t hl ht part
  have HLo (l t : ℝ) (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1) :
      |nativeActualCenteredThirdLowPart n q U b h K T (fun _=>1) a z l t| ≤ CL*M.data.d^3:=by
    exact hjL U T hU hT hcut a z l t hl ht
  have hdpos:=M.data.hd
  have HB:=native_actual_taylor_remainder_abs_le_HIGH_LOW n q U b h K T ho (fun _=>1) a z
    (fun k e=>by cases e <;> exact NNReal.coe_nonneg _)
    (fun e=>by cases e <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _)
    (native_continuum_mixed_clock_nonneg n M.bf M.hf hbf hhf as ho) hbm hhm
    (native_continuum_mixed_clock_monotone n M.bf M.hf hbf hhf as ho)
    (CH*M.data.d*profile) (CL*M.data.d^3) (by positivity) (by positivity) HHi HLo
  apply HB.trans
  change 2*(CH*M.data.d*profile)+(CL*M.data.d^3)/2 ≤
    (2*CH+CL)*(M.data.d*profile+M.data.d^3)
  nlinarith only [mul_nonneg hCL.le (mul_nonneg M.data.hd.le hprofile),
    mul_nonneg hCH.le (pow_nonneg M.data.hd.le 3),
    mul_nonneg hCL.le (pow_nonneg M.data.hd.le 3)]

end OAI.SKFluctuations.Cavity
