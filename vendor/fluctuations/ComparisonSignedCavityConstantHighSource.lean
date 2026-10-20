module

public import ComparisonSignedCavityCanonicalFixedLowOneHigh
public import ComparisonSignedCavityWholeLawZeroLowError

@[expose] public section

noncomputable section
set_option maxHeartbeats 20000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open Hierarchy.ClockTree
open scoped Topology NNReal ENNReal BigOperators

theorem native_site_monomial_rpow_moment_one (n : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (law : ℕ→FullCoordinate n→ℝ) (es : List T.Slot) (p : ℝ) :
    T.disorderExpect (fullWeight n) (fullFeature n) 0 law
      (fun σ=>|siteMonomial T σ es|^p) 0=1 := by
  simp only [native_site_monomial_abs_one,Real.one_rpow]
  exact T.disorderExpect_one (fullWeight_pos n) (fullFeature n) ho 0 law 0

theorem native_constant_fixed_zero_high_bound (n U rBound : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (b h K : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as) (hT : T.leaves≤rBound)
    (es : List T.Slot) (s l t : ℝ) :
    |nativeFixedLowHighProfile n q U b h K T (fun σ=>siteMonomial T σ es) 0 1 s l t|≤
      pairForkVariation rBound*nativeWholeLawProfileCost n (cutFullVariance n q U l t b h K)
        (cutTSlope n U 0 b h K) T 1 := by
  let law:=cutFullVariance n q U l t b h K
  let A:=cutTSlope n U 0 b h K
  have HP : T.disorderExpect (fullWeight n) (fullFeature n) 0 law (fun σ=>(siteMonomial T σ es)^2) 0≤(1:ℝ)^2:=by
    have HH:=native_site_monomial_rpow_moment_one n T ho law es 2
    simpa only [Real.rpow_two,sq_abs,one_pow] using HH.le
  have H:=T.disorderProfileJets_oneError_offDiagonal_wholeLaw_L2 (fullWeight_pos n) (fullFeature n)
    ho 0 law 0 hT (fun σ=>siteMonomial T σ es) (by norm_num : (0:ℝ)≤1) HP
    (ReplicaTree.coordinateProfile (fullFeature n) A) (fun σ=>fullFeature_coordinateProfile_self n A as.length σ)
    (nativeWholeLawErrorRadius_nonneg n as law A)
    (fun j=>le_of_eq (nativeWholeLawErrorSecond_eq_radius_sq n ho law A j))
  simpa only [nativeFixedLowHighProfile,List.replicate_zero,List.nil_append,List.replicate_one,List.map_cons,
    List.map_nil,mul_one,nativeWholeLawProfileCost,Real.rpow_one,law,A] using H

theorem eventually_actual_minimum_bare_constant_fixed_low_one_high_budget
    (k rBound : ℕ) (hk : 0<k)
    (Bclock Temp Ccut : ℝ) (hTemp : 0≤Temp) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct) :
    ∃Cq : ℝ,0<Cq ∧ ∀ᶠn : ℕ in atTop,
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
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l t s : ℝ),
          U≤as.length → l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → s∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀W : ℝ,M.xs≤W → partitionPoint 0 as U≤Ccut*W →
        ∀es : List T.Slot,
          |nativeFixedLowHighProfile n q U b h K T
            (fun σ=>siteMonomial T σ es) k 1 s l t|≤
            ClockTree.pairForkVariation rBound*ClockTree.absJetVariation (rBound+2) k*
              (Cq*(1+Ccut)*W)^k*
              nativeWholeLawProfileCost n (cutFullVariance n q U l t b h K)
                (cutTSlope n U 0 b h K) T 1 := by
  obtain ⟨Cq,hCq,HQ⟩:=eventually_actual_minimum_bare_continuum_low_profile_moment
    (D:=D) (2*k) (by omega) Bclock Temp hTemp hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cq,hCq,?_⟩
  filter_upwards [HQ] with n hnQ
  intro M hb hh hxs L us hus hret hmesh
  filter_upwards [hnQ M hb hh hxs L us hus hret hmesh] with jGrid hgridQ
  dsimp only at hgridQ ⊢
  intro U T l t s hU hl ht hs hT W hxW hcut es
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let C : ℝ:=1
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
  have HC : 0≤C:=by norm_num [C]
  have HW : 0<W:=M.hxs.trans_le hxW
  have Hrho : 0<rho:=by dsimp [rho];positivity
  have HPmoment : T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l t b h K)
      (fun σ=>|siteMonomial T σ es|^4) 0≤C^4:=by
    simp only [native_site_monomial_abs_one,C,one_pow]
    exact le_of_eq (T.disorderExpect_one (fullWeight_pos n) (fullFeature n) ho 0 (cutFullVariance n q U l t b h K) 0)
  have HQmoment j (hj : j≤as.length) : (ClockTree.pairClock as j).disorderExpect
      (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l t b h K)
      (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U s b h K) j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^(4*k)) 0≤rho^(4*k) := by
    by_cases hju : j<U
    · have Hraw:=hgridQ U l t s hl ht hs j hj
      rw [show 2*(2*k)=4*k by omega] at Hraw
      apply Hraw.trans
      apply pow_le_pow_left₀ (mul_nonneg hCq.le (add_nonneg M.hxs.le (partitionPoint_mem as ho j).1))
      dsimp only [rho]
      have Hmass:=partitionPoint_mono as ho hju.le
      have Hscale : M.xs+partitionPoint 0 as j≤(1+Ccut)*W := by nlinarith only [hxW,hcut,Hmass]
      exact (mul_le_mul_of_nonneg_left Hscale hCq.le).trans_eq (by ring)
    · have HE : (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U s b h K) j
          (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^(4*k))=fun _=>0 := by
        funext σ
        simp only [ReplicaTree.coordinateProfile,cutLSlope,hju,ite_false,Pi.zero_apply,
          zero_mul,Finset.sum_const_zero,abs_zero,zero_pow (by omega : 4*k≠0)]
      rw [HE]
      simp only [ClockTree.disorderExpect,mul_zero,Finset.sum_const_zero]
      exact pow_nonneg Hrho.le _
  simpa only [C,mul_one] using native_fixed_low_one_high_wholeLaw_first_bound n U k hk q b h K T ho hT (fun σ=>siteMonomial T σ es) hl ht HC Hrho
    (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
    (fun i=>by cases i <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm HPmoment HQmoment

end OAI.SKFluctuations.Cavity
