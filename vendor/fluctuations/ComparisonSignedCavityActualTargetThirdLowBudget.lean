module

public import ComparisonSignedCavityActualConstantTransientLowProfile
public import ComparisonNativeActualUniformBandL1Density

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 20000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_minimum_inherited_target_third_LOW_integral_budget
    (Bclock Temp Cf Ccut : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0<C ∧ ∀ᶠn in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock n M.bf M.hf as
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(i U : ℕ) (x : ℝ),i<U → U≤as.length → M.xs≤x → x≤1 → Ccut*x≤1 →
          partitionPoint 0 as U≤Ccut*x →
        let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i
        let Cerr:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp
        let di:=nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ)
        ∀(l t : ℝ),l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 →
          |nativeActualCenteredThirdLowPart n q U b h K g.tree (fun _=>1)
            (g.embed (singleSlot as)) g.mark l t|≤
              C*x^2*Cerr*di+C*x*Cerr*
                (∫u in 0..Ccut*x,Real.sqrt (orderedPathB (n+1) M.bf M.hf u-
                  (orderedPathS (n+1) M.bf M.hf u)^2)) := by
  obtain ⟨C,hC,HC⟩:=eventually_actual_minimum_inherited_constant_centered_third_LOW_profile
    (D:=D) 2 Bclock Temp Cf Ccut hTemp hCf hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨4*C,by positivity,?_⟩
  filter_upwards [HC] with n hn
  intro M HS hxs1 L us hus hret hmesh
  filter_upwards [hn M HS hxs1 L us hus hret hmesh,
    M.actual_original_band_l1_density_on_all_final_nets] with jGrid hj hband
  dsimp only at hj ⊢
  intro i U x hi hU hxsx hx1 hcut1 hcut l t hl ht
  let as:=finiteCutMasses us jGrid
  let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let R:=nativeWholeLawErrorRadius n as (cutFullVariance n q U l t b h K) (cutLowError n U b h K)
  let Cerr:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp
  let di:=nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ)
  let I:=(∫u in 0..Ccut*x,Real.sqrt (orderedPathB (n+1) M.bf M.hf u-
    (orderedPathS (n+1) M.bf M.hf u)^2))
  have hx : 0<x:=M.hxs.trans_le hxsx
  have hCe : 0≤Cerr:=actualLowErrorComparisonConstant_nonneg _ hTemp
  have hdi : 0≤di:=add_nonneg (Real.sqrt_nonneg _) (by positivity)
  have hsite : (1/(n+1:ℕ):ℝ)≤di:=le_add_of_nonneg_left (Real.sqrt_nonneg _)
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hg : g.tree.leaves≤2:=by
    have H:=(single (S:=Spin n×Bool) as).markedAttach_leaves 0 g (nativeFreshAtSlot_mem _ _ _ _)
    simpa only [single_leaves_exact] using H
  have HR : R i≤Cerr*di:=by
    have H:=actual_minimum_inherited_current_low_error_radius_le_original M Temp Cf hTemp hCf
      HS hxs1 ho U hl ht i (hi.le.trans hU)
    change R i≤ if i<U then Cerr*di else 0 at H
    simpa only [hi,ite_true] using H
  have HF : g.tree.forkCost R=R i:=by
    rw [nativeFreshAtSlot_forkCost,single_forkCost,zero_add,Nat.min_eq_left (hi.le.trans hU)]
  have HD : edgeBudget 0 as R≤Cerr*(I+3/(n+1:ℕ)):=by
    have Hmono:=actual_low_edgeBudget_mono ho (fun j hj=>
      actual_minimum_inherited_current_low_error_radius_le_original M Temp Cf hTemp hCf HS hxs1
        ho U hl ht j hj)
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
      ((native_comparison_thermal_intervalIntegrable M).mono_set (by
        rw [uIcc_of_le (mul_nonneg hCcut hx.le),uIcc_of_le zero_le_one]
        exact Icc_subset_Icc le_rfl hcut1))
    have HImono : (∫u in 0..partitionPoint 0 as U,Real.sqrt
        (orderedPathB (n+1) M.bf M.hf u-(orderedPathS (n+1) M.bf M.hf u)^2))≤I:=
      intervalIntegral.integral_mono_interval le_rfl (partitionPoint_mem as ho U).1 hcut
        (ae_of_all _ (fun _=>Real.sqrt_nonneg _)) HI
    exact Hmono.trans (mul_le_mul_of_nonneg_left (HB.trans (add_le_add HImono le_rfl)) hCe)
  have H:=hj U g.tree x l t hU hg hxsx hx1 hcut hl ht (g.embed (singleSlot as)) g.mark
  rw [HF] at H
  have HP:=mul_le_mul_of_nonneg_left (add_le_add HR HD) (mul_nonneg hC.le (sq_nonneg x))
  have hI : 0≤I:=intervalIntegral.integral_nonneg (mul_nonneg hCcut hx.le) (fun _ _=>Real.sqrt_nonneg _)
  have Hsite:=mul_le_mul_of_nonneg_left hsite (show 0≤3*C*x^2*Cerr by positivity)
  have HX : x^2≤x:=by nlinarith
  have Hmove:=mul_le_mul_of_nonneg_right HX (show 0≤C*Cerr*I by positivity)
  have Hextra : 0≤3*C*x*Cerr*I:=by positivity
  apply H.trans (HP.trans _)
  dsimp only [I,Cerr,di] at Hsite Hmove Hextra ⊢
  simp only [div_eq_mul_inv] at Hsite ⊢
  nlinarith

end OAI.SKFluctuations.Cavity
