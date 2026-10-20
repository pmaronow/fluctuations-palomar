module

public import ComparisonActualHighWallAllDegreeContinuumMoments
public import ComparisonActualHighWallHighAllDegreeContinuumMoments
public import ComparisonActualHighWallLowCost
public import ComparisonSignedCavityGammaLowRestorationBudget

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_high_wall_canonical_gamma_LOW_cubic_price
    (aDegree rBound : ℕ) (Bclock Cmass Ccut : ℝ) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U ≤ as.length → T.leaves ≤ rBound →
        partitionPoint 0 as U ≤ Ccut*M.data.d →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm),
        (∀e,G.sourceLowMass e ≤ Cmass*M.data.d) →
        ∀(a : T.Slot) (star : ℕ),star<U →
        |nativeGammaProjectedLowSecondRestoration T a star U q b h K
          (restCenteredFixedForkKernel n b S star 0) (G.canonicalHighWallSource M forms).restProduct| ≤
          C*M.data.d^aDegree*M.data.d^3 := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_high_wall_all_degree_continuum_square_even_moment
    (D:=D) aDegree 2 rBound (by norm_num) Bclock Cmass hCmass hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cq,hCq,HQ⟩:=eventually_actual_high_wall_continuum_low_profile_moment
    (D:=D) 4 (by norm_num) Bclock Ccut hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cr,hCr,HR⟩:=eventually_actual_high_wall_current_LOW_radius_bigO
    (D:=D) Bclock Ccut hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  let B:=2*max Bclock 0
  let Cp0:=Real.exp (wholeLawRowComparisonConstant rBound*B)*Cp^aDegree
  let Cbase:=4*((rBound:ℝ)+1)*absJetVariation (rBound+2) 2*Cp0*Cr*Cq^2
  have hbase : 0 ≤ Cbase:=by
    have hv:=absJetVariation_nonneg (rBound+2) 2
    dsimp only [Cbase,Cp0];positivity
  refine ⟨Cbase+1,by positivity,?_⟩
  filter_upwards [HP,HQ,HR] with n hnP hnQ hnR
  intro M hwork L us hus hret hmesh
  filter_upwards [hnP M hwork L us hus hret hmesh,hnQ M hwork L us hus hret hmesh,
    hnR M hwork L us hus hret hmesh] with jGrid hjP hjQ hjR
  dsimp only at hjP hjQ hjR ⊢
  intro U T hU hT hcut G forms hmass a star hs
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have ho:=finiteCutMasses_ordered us hus jGrid
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.bf M.hf
    (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) (partitionPoint_mem as ho j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.bf u:ℝ) ≤ M.bf v from M.data.bf_monotone M.alpha hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.hf u:ℝ) ≤ M.hf v from M.data.hf_monotone M.alpha hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.bf M.hf (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha)) as ho
  have hK0 j : 0 ≤ K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HS j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HS i).1 (NNReal.coe_nonneg _))
  have HB : 0 ≤ B:=by dsimp only [B];positivity
  have hclock j (_hj : j≤as.length) : |b j|≤B ∧ |h j|≤B ∧ |K j|≤B:=by
    have Htotal:=M.data.total_clock_le M.alpha _ (partitionPoint_mem as ho j)
    have HT : M.data.T≤B:=M.hT.trans ((le_max_left _ _).trans (by dsimp only [B];linarith [le_max_right Bclock 0]))
    have HK : K j≤M.data.T:=by
      have HP:=mul_le_mul_of_nonneg_left (HS j).2 (NNReal.coe_nonneg (M.bf (partitionPoint 0 as j)))
      dsimp only [K];linarith only [HP,Htotal]
    rw [abs_of_nonneg (NNReal.coe_nonneg _),abs_of_nonneg (NNReal.coe_nonneg _),abs_of_nonneg (hK0 j)]
    exact ⟨(le_add_of_nonneg_left (NNReal.coe_nonneg _)).trans (Htotal.trans HT),
      (le_add_of_nonneg_right (NNReal.coe_nonneg _)).trans (Htotal.trans HT),HK.trans HT⟩
  have Hprice:=native_gamma_projected_low_second_restoration_wholeLaw_bound n U star q b h S T ho hT
    (G.canonicalHighWallSource M forms).restProduct a hs hU
    (show 0≤Cp0*M.data.d^aDegree by
      exact mul_nonneg (by dsimp only [Cp0];positivity) (pow_nonneg M.data.hd.le _))
    (mul_pos hCq M.data.hd) HB (mul_nonneg hCr.le M.data.hd.le)
    (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
    (fun i=>by cases i <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm
    (by
      intro l hl
      simpa only [ActualNaturalBoundaryShape.product_eq_restProduct,Cp0,B,mul_assoc]
        using hjP U T l 1 hl (by norm_num) hT G forms hmass)
    hclock
    (fun l hl=>hjR U star l 1 hU (hs.le.trans hU) hcut hl (by norm_num))
    (by
      intro l hl j hj
      simpa only [show 2*4=8 from rfl] using hjQ U l 1 1 hl (by norm_num) (by norm_num) hcut j hj)
  apply Hprice.trans
  have Hmajor:=mul_le_mul_of_nonneg_right (show Cbase≤Cbase+1 by linarith)
    (mul_nonneg (pow_nonneg M.data.hd.le aDegree) (pow_nonneg M.data.hd.le 3))
  convert Hmajor using 1 <;> dsimp only [Cbase] <;> ring

end OAI.SKFluctuations.Cavity
