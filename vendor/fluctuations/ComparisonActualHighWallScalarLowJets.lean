module

public import ComparisonActualHighWallSourceMoments
public import ComparisonSignedCavityInheritedOriginalScalarLowJets

@[expose] public section

noncomputable section
set_option maxHeartbeats 16000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open Hierarchy.ClockTree
open scoped Topology NNReal ENNReal BigOperators

theorem eventually_actual_high_wall_original_scalar_low_jets
    (rBound : ℕ) (Bclock Ccut : ℝ) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0<delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct) :
    ∃Ck : ℝ,0<Ck ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
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
  let Temp:=max Bclock 0
  have hTemp : 0 ≤ Temp:=le_max_right _ _
  obtain ⟨Cs,hCs,HS⟩:=eventually_actual_high_wall_continuum_center_bound
    (D:=D) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cscalar:=1+Temp*Cs
  have hCscalar : 0≤Cscalar:=by dsimp [Cscalar];positivity
  let Ck:=Cscalar*(1+Ccut)+1
  have hCk : 0<Ck:=by dsimp [Ck];positivity
  refine ⟨Ck,hCk,?_⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually HS] with n hnS
  intro M hwork us jGrid hus
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
  have HSunit j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.bf M.hf
    (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) (partitionPoint_mem as ho j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.bf u:ℝ)≤M.bf v from M.data.bf_monotone M.alpha hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.hf u:ℝ)≤M.hf v from M.data.hf_monotone M.alpha hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.bf M.hf
      (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha)) as ho
  have hK0 j : 0≤K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HSunit j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HSunit i).1 (NNReal.coe_nonneg _))
  have Hsource j:=M.data.small_source_clock_budget M.alpha
    (by rw [hwork] : M.data.d ≤ M.xs) (partitionPoint_mem as ho j)
  have Hb j : b j≤Temp:=(Hsource j).1.trans (M.hT.trans (le_max_left _ _))
  have Hfield j : h j≤M.xs+partitionPoint 0 as j:=(Hsource j).2
  have Hmean j : S j≤Cs*(M.xs+partitionPoint 0 as j):=by
    have HC:=native_ordered_source_center_eq_completed n M.bf M.hf
      (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) (partitionPoint_mem as ho j)
    apply (le_abs_self (S j)).trans
    dsimp only [S]
    rw [HC]
    exact hnS M _ (partitionPoint_mem as ho j)
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
