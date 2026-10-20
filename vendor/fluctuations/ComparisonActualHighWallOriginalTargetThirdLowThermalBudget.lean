module

public import ComparisonActualHighWallOriginalConstantThirdLowProfile
public import ComparisonActualHighWallLowDensity
public import ComparisonNativeActualUniformBandL1Density

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open ActualHighWallOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_high_wall_original_target_third_LOW_thermal_integral_budget
    (Bclock Ccut : ℝ) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0<C ∧ ∀ᶠn in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock n M.bf M.hf as
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(i U : ℕ),i<U → U≤as.length → Ccut*M.data.d≤1 →
          partitionPoint 0 as U≤Ccut*M.data.d →
        let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i
        let Cerr:=actualLowErrorComparisonConstant (2*M.data.T) M.data.T
        let di:=nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ)
        ∀(l t : ℝ),l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 →
          |nativeActualCenteredThirdLowPart n q U b h K g.tree (fun _=>1)
            (g.embed (singleSlot as)) g.mark l t|≤
              C*M.data.d^2*Cerr*di+C*M.data.d*Cerr*
                (∫u in 0..Ccut*M.data.d,Real.sqrt (orderedPathB (n+1) M.bf M.hf u-
                  (orderedPathS (n+1) M.bf M.hf u)^2)) := by
  obtain ⟨C,hC,HC⟩:=eventually_actual_high_wall_original_constant_third_low_profile
    (D:=D) 2 Bclock Ccut hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨4*C,by positivity,?_⟩
  filter_upwards [HC] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh,
    original_band_l1_density_on_all_final_nets n M.bf M.hf
      (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha)] with jGrid hj hband
  dsimp only at hj ⊢
  intro i U hi hU hcut1 hcut l t hl ht
  let as:=finiteCutMasses us jGrid
  let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let R:=nativeWholeLawErrorRadius n as (cutFullVariance n q U l t b h K) (cutLowError n U b h K)
  let Cerr:=actualLowErrorComparisonConstant (2*M.data.T) M.data.T
  let di:=nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ)
  let I:=(∫u in 0..Ccut*M.data.d,Real.sqrt (orderedPathB (n+1) M.bf M.hf u-
    (orderedPathS (n+1) M.bf M.hf u)^2))
  have hx : 0<M.data.d:=M.data.hd
  have hx1:=M.data.hd1
  have hCe : 0≤Cerr:=actualLowErrorComparisonConstant_nonneg _
    (M.data.hepsilon.1.le.trans M.data.hepsilon.2.le)
  have hdi : 0≤di:=add_nonneg (Real.sqrt_nonneg _) (by positivity)
  have hsite : (1/(n+1:ℕ):ℝ)≤di:=le_add_of_nonneg_left (Real.sqrt_nonneg _)
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hg : g.tree.leaves≤2:=by
    have H:=(single (S:=Spin n×Bool) as).markedAttach_leaves 0 g (nativeFreshAtSlot_mem _ _ _ _)
    simpa only [single_leaves_exact] using H
  have HR : R i≤Cerr*di:=by
    have H:=M.data.current_low_error_radius_le_original M.alpha as ho U hl ht i (hi.le.trans hU)
    change R i≤ if i<U then Cerr*di else 0 at H
    simpa only [hi,ite_true] using H
  have HF : g.tree.forkCost R=R i:=by
    rw [nativeFreshAtSlot_forkCost,single_forkCost,zero_add,Nat.min_eq_left (hi.le.trans hU)]
  have HD : edgeBudget 0 as R≤Cerr*(I+3/(n+1:ℕ)):=by
    have Hmono:=actual_low_edgeBudget_mono ho (fun j hj=>
      M.data.current_low_error_radius_le_original M.alpha as ho U hl ht j hj)
    have Heq : (fun j=>if j<U then Cerr*(nativeOriginalCutLowErrorRadius n M.bf M.hf as j+1/(n+1:ℕ)) else 0)=
        (fun j=>Cerr*(if j<U then nativeOriginalCutLowErrorRadius n M.bf M.hf as j+1/(n+1:ℕ) else 0)+0*(0:ℝ)):=by
      funext j
      split_ifs <;> simp
    change edgeBudget 0 as R≤edgeBudget 0 as _ at Hmono
    rw [Heq,actual_low_edgeBudget_linear] at Hmono
    simp only [zero_mul,add_zero] at Hmono
    have HB:=hband us hus 0 U (Nat.zero_le _) hU
    simp only [Nat.not_lt_zero,ite_false] at HB
    have hz : partitionPoint 0 (finiteCutMasses us jGrid) 0=0:=by cases finiteCutMasses us jGrid <;> rfl
    rw [hz] at HB
    change edgeBudget 0 as (fun j=>if j<U then nativeOriginalCutLowErrorRadius n M.bf M.hf as j+1/(n+1:ℕ) else 0)≤
      (∫u in 0..partitionPoint 0 as U,Real.sqrt
        (orderedPathB (n+1) M.bf M.hf u-(orderedPathS (n+1) M.bf M.hf u)^2))+3/(n+1:ℕ) at HB
    have HI:=native_intervalIntegrable_sqrt_of_intervalIntegrable
      ((physicalOrderedThermal_intervalIntegrable n M.bf M.hf (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha)).mono_set (by
        rw [uIcc_of_le (mul_nonneg hCcut hx.le),uIcc_of_le zero_le_one]
        exact Icc_subset_Icc le_rfl hcut1))
    have HImono : (∫u in 0..partitionPoint 0 as U,Real.sqrt
        (orderedPathB (n+1) M.bf M.hf u-(orderedPathS (n+1) M.bf M.hf u)^2))≤I:=
      intervalIntegral.integral_mono_interval le_rfl (partitionPoint_mem as ho U).1 hcut
        (ae_of_all _ (fun _=>Real.sqrt_nonneg _)) HI
    exact Hmono.trans (mul_le_mul_of_nonneg_left (HB.trans (add_le_add HImono le_rfl)) hCe)
  have H:=hj U g.tree hU hg hcut (g.embed (singleSlot as)) g.mark l t hl ht
  rw [HF] at H
  have HP:=mul_le_mul_of_nonneg_left (add_le_add HR HD) (mul_nonneg hC.le (sq_nonneg M.data.d))
  have hI : 0≤I:=intervalIntegral.integral_nonneg (mul_nonneg hCcut hx.le) (fun _ _=>Real.sqrt_nonneg _)
  have Hsite:=mul_le_mul_of_nonneg_left hsite (show 0≤3*C*M.data.d^2*Cerr by positivity)
  have HX : M.data.d^2≤M.data.d:=by nlinarith
  have Hmove:=mul_le_mul_of_nonneg_right HX (show 0≤C*Cerr*I by positivity)
  have Hextra : 0≤3*C*M.data.d*Cerr*I:=by positivity
  apply H.trans (HP.trans _)
  dsimp only [I,Cerr,di] at Hsite Hmove Hextra ⊢
  simp only [div_eq_mul_inv] at Hsite ⊢
  nlinarith

end OAI.SKFluctuations.Cavity
