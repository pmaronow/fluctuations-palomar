module

public import ComparisonSignedCavityGRestorationProfile
public import ComparisonSignedCavityGRestorationRawLow
public import ComparisonSignedCavityInheritedGRestorationLowMoments
public import ComparisonSignedCavityMixedErrorCanonicalLedger
public import ComparisonNativeActualInheritedClocks

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 20000000

theorem actual_inherited_constant_G_high_restoration_bound
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp Cf : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hsource : NativeActualSmallSourceClocks M Temp Cf) (hTemp : 0 ≤ Temp)
    (p : ℝ) (hp : 2 < p) (rBound : ℕ)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (U : ℕ)
    (T : ClockTree (Spin n×Bool) as) (t : ℝ)
    (hU : U ≤ as.length) (ht : t∈Icc (0:ℝ) 1) (hT : T.leaves ≤ rBound)
    (a c e f : T.Slot) (hef : e≠f) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
    let K:=fun j=>h j+b j*S j
    let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    let law:=cutFullVariance n q U 0 t b h K
    let high:=cutTSlope n U 0 b h K
    |cutMixedJet n q U b h K T (nativeOriginalHighGAtom T U K b S a c e f) 0 0 0 t| ≤
      |(1/2:ℝ)*fullScalarCutConnected4 T U K a c e f| *
        (ClockTree.pairForkVariation rBound*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*
          (nativeWholeLawErrorRadius n as law high (T.splitIndex e f))^(2/p)*
          nativeWholeLawProfileCost n law high T (2/p)) := by
  dsimp only
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let law:=cutFullVariance n q U 0 t b h K
  let high:=cutTSlope n U 0 b h K
  have had:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.bf M.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) (partitionPoint_mem as ho j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.bf u:ℝ) ≤ M.bf v from toNNReal_monotoneOn had.1 hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.hf u:ℝ) ≤ M.hf v from toNNReal_monotoneOn had.2.1 hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.bf M.hf (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1)) as ho
  have hK0 j : 0 ≤ K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HS j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HS i).1 (NNReal.coe_nonneg _))
  have Hb j : b j ≤ Temp:=
    (hsource _ (partitionPoint_mem as ho j)).1
  have HPmoment : T.disorderExpect (fullWeight n) (fullFeature n) 0 law
      (fun _=>|(1:ℝ)|^(2*(p/(p-2)))) 0 ≤ (1:ℝ)^(2*(p/(p-2))) := by
    simp only [abs_one,Real.one_rpow]
    exact (T.disorderExpect_one (fullWeight_pos n) (fullFeature n) ho 0 law 0).le
  have Hcap:=native_centered_high_kernel_abs_le n U b h S (fun _=>NNReal.coe_nonneg _) Hb HS
  have H:=native_original_G_profile_restoration_bound n U b h K S (fun _=>rfl)
    T ho hU hT law (fun _=>1) a c e f hef high (by norm_num : (0:ℝ) ≤ 1) hp
    (by positivity) (by positivity) HPmoment Hcap Hcap
  rw [native_cutMixedJet_zero_eq_profile n q U b h K T ho _ 0
    (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
    (fun i=>by cases i <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm (by norm_num) ht]
  simpa only [one_mul,mul_one] using H

theorem eventually_actual_minimum_inherited_constant_G_low_restoration
    (rBound : ℕ)
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
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l : ℝ),
          U ≤ as.length → l∈Icc (0:ℝ) 1 → T.leaves ≤ rBound →
        ∀W : ℝ,M.xs ≤ W → partitionPoint 0 as U ≤ Ccut*W →
        ∀a c e f : T.Slot,e≠f →
          let law:=cutFullVariance n q U l 1 b h K
          let high:=cutTSlope n U 0 b h K
          |cutLowJet n q U b h K T (nativeOriginalHighGAtom T U K b S a c e f) 0 1 l 1| ≤
            |(1/2:ℝ)*fullScalarCutConnected4 T U K a c e f| *
              (ClockTree.absJetVariation rBound 1*
                1*
                nativeWholeLawErrorRadius n as law high (T.splitIndex e f)*(Cq*W)) := by
  obtain ⟨Cq,hCq,HQ⟩:=eventually_actual_minimum_inherited_original_low_profile_fourth
    (D:=D) Bclock Temp Cf Ccut hTemp hCf hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cq,hCq,?_⟩
  filter_upwards [HQ] with n hnQ
  intro M hsource hxs L us hus hret hmesh
  filter_upwards [hnQ M hsource hxs L us hus hret hmesh] with jGrid hgridQ
  dsimp only at hgridQ ⊢
  intro U T l hU hl hT W hxW hcut a c e f hef
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let law:=cutFullVariance n q U l 1 b h K
  let high:=cutTSlope n U 0 b h K
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have had:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.bf M.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) (partitionPoint_mem as ho j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.bf u:ℝ) ≤ M.bf v from toNNReal_monotoneOn had.1 hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.hf u:ℝ) ≤ M.hf v from toNNReal_monotoneOn had.2.1 hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.bf M.hf (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1)) as ho
  have hK0 j : 0 ≤ K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HS j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HS i).1 (NNReal.coe_nonneg _))
  have HPmoment : T.disorderExpect (fullWeight n) (fullFeature n) 0 law
      (fun _=>|(1:ℝ)|^4) 0 ≤ (1:ℝ)^4 := by
    simp only [abs_one,one_pow]
    exact (T.disorderExpect_one (fullWeight_pos n) (fullFeature n) ho 0 law 0).le
  have HQmoment:=hgridQ U l 1 1 W hU hl (by norm_num) (by norm_num) hxW hcut
  have H:=native_original_G_raw_profile_restoration_bound n U b h K S (fun _=>rfl)
    T ho hU hT law (fun _=>1) a c e f hef (cutLSlope n U 1 b h K) (by norm_num : (0:ℝ) ≤ 1)
    (mul_pos hCq (M.hxs.trans_le hxW)) HPmoment HQmoment
  rw [cutLowJet_eq_profileJets n q U b h K T ho _ 0
    (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
    (fun i=>by cases i <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm 1 hl (by norm_num)]
  simpa only [List.replicate_one,one_mul,mul_one] using H

end OAI.SKFluctuations.Cavity
