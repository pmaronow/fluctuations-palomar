module

public import ComparisonSignedCavityTransientScalarBudget
public import ComparisonNativeActualMeanRawUpper
public import ComparisonSignedCavityInheritedContinuumMoments

@[expose] public section

noncomputable section
set_option maxHeartbeats 16000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open Hierarchy.ClockTree
open scoped Topology NNReal ENNReal BigOperators

theorem eventually_actual_minimum_inherited_original_scalar_low_jets
    (rBound : ℕ) (Bclock Temp Cf Ccut : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0<delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct) :
    ∃Ck : ℝ,0<Ck ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf →
      ∀(us : List PositiveMass) (jGrid : ℕ), (∀u∈us,u.val≤1) →
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (W l : ℝ),M.xs≤W →
          partitionPoint 0 as U≤Ccut*W → l∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀(a z : T.Slot) (k : ℕ),
          |cutLowJet n q U b h K T (fun σ=>sitePair T a z (T.cavityAssignment σ).2)
            (cavityEmbed 0) k l 0|≤jetVariation rBound k*(Ck*W)^k := by
  obtain ⟨Cs,hCs,HS⟩:=eventually_actual_minimum_mass_mean_upper
    (D:=D) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cscalar:=Cf+Temp*Cs
  have hCscalar : 0≤Cscalar:=by dsimp [Cscalar];positivity
  let Ck:=Cscalar*(1+Ccut)+1
  have hCk : 0<Ck:=by dsimp [Ck];positivity
  refine ⟨Ck,hCk,?_⟩
  filter_upwards [HS] with n hnS
  intro M hsource us jGrid hus
  dsimp only
  intro U T W l hxW hcut hl hT a z k
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hW : 0≤W:=M.hxs.le.trans hxW
  have hxs0 :=M.hxs.le
  have had:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have HSunit j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.bf M.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) (partitionPoint_mem as ho j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.bf u:ℝ)≤M.bf v from toNNReal_monotoneOn had.1 hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.hf u:ℝ)≤M.hf v from toNNReal_monotoneOn had.2.1 hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.bf M.hf
      (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1)) as ho
  have hK0 j : 0≤K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HSunit j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HSunit i).1 (NNReal.coe_nonneg _))
  have Hb j : b j≤Temp:=(hsource _ (partitionPoint_mem as ho j)).1
  have Hfield j : h j≤Cf*(M.xs+partitionPoint 0 as j):=
    (hsource _ (partitionPoint_mem as ho j)).2
  have Hmean j : S j≤Cs*(M.xs+partitionPoint 0 as j):=by
    by_cases hj : 0<partitionPoint 0 as j
    · exact hnS M _ ⟨hj,(partitionPoint_mem as ho j).2⟩
    · have hz : partitionPoint 0 as j=0:=le_antisymm (le_of_not_gt hj) (partitionPoint_mem as ho j).1
      dsimp only [S]
      rw [hz,orderedPathS,orderedPathPair_zero]
      positivity
  have Hcap j (hj : j<U) : |K j|≤Ck*W:=by
    rw [abs_of_nonneg (hK0 j)]
    have Hprod:=mul_le_mul (Hb j) (Hmean j) (HSunit j).1 hTemp
    have Hlocal : K j≤Cscalar*(M.xs+partitionPoint 0 as j):=by
      dsimp only [K,Cscalar]
      nlinarith only [Hprod,Hfield j]
    have Hmass:=partitionPoint_mono as ho hj.le
    have Hscale : M.xs+partitionPoint 0 as j≤(1+Ccut)*W:=by nlinarith only [Hmass,hcut,hxW]
    have HH:=(Hlocal.trans (mul_le_mul_of_nonneg_left Hscale hCscalar))
    have HW:=hW
    dsimp only [Ck]
    nlinarith only [HH,HW]
  rw [cutLowJet_eq_profileJets n q U b h K T ho _ (cavityEmbed 0)
    (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
    (fun i=>by cases i <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm k hl (by norm_num)]
  have H:=T.disorderProfileJets_abs_le (fullWeight_pos n) (fullFeature n) ho
    (List.replicate k (ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U 0 b h K))) hT
    (fun σ=>sitePair T a z (T.cavityAssignment σ).2) (C:=1) (by norm_num)
    (mul_nonneg hCk.le hW) (fun σ=>by simp only [sitePair_apply,abs_mul,abs_spinValue,one_mul,le_refl])
    (fun A hA j σ τ=>by
      rw [(List.mem_replicate.mp hA).2]
      exact native_scalar_low_profile_abs_le n U b h K (mul_nonneg hCk.le hW) Hcap j σ τ)
    0 (cutFullVariance n q U l 0 b h K) (cavityEmbed 0)
  simpa only [List.length_replicate,mul_one] using H

end OAI.SKFluctuations.Cavity
