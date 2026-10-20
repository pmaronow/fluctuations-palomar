module

public import ComparisonSignedCavityActualTargetMeanCorrections
public import ComparisonSignedCavityActualConstantSourceClosedRatesAlong
public import ComparisonSignedCavityUniformCenterRefinement

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_inherited_target_mean_correction_rate
    (Bclock Temp Cf Ccut : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0<C ∧∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf →
        (∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤Temp) → M.h 0=0 → M.xs≤1 →
      ∀us : List PositiveMass,(∀u∈us,u.val≤1) →∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀i U : ℕ,i<U → U≤as.length →∀x : ℝ,M.xs≤x →
          partitionPoint 0 as i≤Ccut*x →
          |nativeActualTargetOriginalMeanCorrection M as i U|≤
            C*((n+1:ℕ):ℝ)^(-(1:ℝ)/6)*x^3 := by
  obtain ⟨CK,hCK,HK⟩:=eventually_actual_inherited_continuum_clock_mass_upper
    (D:=D) Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  have HL:=eventually_actual_inherited_original_clock_longitudinal_mean_saving
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D)
    2 Bclock Temp hTemp hm hC0
  have HO:=eventually_actual_omitted_product_cubic_cost_saved
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock)
    hm hC0 (2*Temp+1) (by positivity)
  let C:=2*CK*(1+Ccut)+1
  have hC : 0<C:=by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [HK,HL,HO] with n hnK hnL hnO
  intro M hs ht hroot hxs1 us hus
  have HM:=eventually_native_finite_physical_mean_uniform_center n M.bf M.hf
    M.inherited_bf_monotone M.inherited_hf_monotone (M.inherited_zero_root_field hroot)
    us hus (1/(n+1:ℕ)) (by positivity)
  filter_upwards [hnL M ht hroot us hus,HM] with jGrid hL hmesh
  dsimp only at hL hmesh ⊢
  intro i U hi hU x hxs hmass
  let as:=finiteCutMasses us jGrid
  let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  have hx:=M.hxs.trans_le hxs
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hK : K i≤CK*(1+Ccut)*x := by
    have H:=hnK M hs (partitionPoint 0 as i) (partitionPoint_mem as ho i)
    change K i≤CK*(M.xs+partitionPoint 0 as i) at H
    nlinarith only [H,hCK,hxs,hmass]
  have hleaves : g.tree.leaves≤2 := by
    have H:=(single (S:=Spin n×Bool) as).markedAttach_leaves 0 g
      (nativeFreshAtSlot_mem _ 0 (singleSlot as) i)
    simpa only [single_leaves_exact] using H
  have Hpart:=actual_target_original_constant_part_abs_le M as ho i U hi hU
    (E:=((n+1:ℕ):ℝ)^(-(1:ℝ)/3)*M.xs^2) hK
    (fun a=>hL K g.tree U a hleaves)
  have Hcorr:=actual_target_original_mean_correction_abs_le M ht as ho i U hi hU Hpart
    (hmesh i (hi.le.trans hU))
  have hN : (1:ℝ)≤(n+1:ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have Hexp : ((n+1:ℕ):ℝ)^(-(1:ℝ)/3)≤((n+1:ℕ):ℝ)^(-(1:ℝ)/6) :=
    Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
  have Hsq : M.xs^2≤x^2:=pow_le_pow_left₀ M.hxs.le hxs 2
  have Hscale : x*M.xs^2≤x^3 := by nlinarith only [mul_le_mul_of_nonneg_left Hsq hx.le]
  have HA : (2*Temp+1)/(n+1:ℕ)≤((n+1:ℕ):ℝ)^(-(1:ℝ)/6)*x^3 := by
    have Hden : (n+1:ℕ)*M.xs≤(n+1:ℕ)*(1:ℝ):=mul_le_mul_of_nonneg_left hxs1 (by positivity)
    have Hdiv:=div_le_div_of_nonneg_left (show (0:ℝ)≤2*Temp+1 by positivity)
      (show (0:ℝ)<(n+1:ℕ)*M.xs by have :=M.hxs;positivity) Hden
    simp only [mul_one] at Hdiv
    exact Hdiv.trans ((hnO M x hxs).trans
      (mul_le_mul_of_nonneg_left Hscale (Real.rpow_nonneg (by positivity) _)))
  have HB : 2*(CK*(1+Ccut)*x)*(((n+1:ℕ):ℝ)^(-(1:ℝ)/3)*M.xs^2)≤
      (2*CK*(1+Ccut))*(((n+1:ℕ):ℝ)^(-(1:ℝ)/6)*x^3) := by
    have HP:=mul_le_mul Hexp Hscale (by positivity : (0:ℝ)≤x*M.xs^2)
      (Real.rpow_nonneg (by positivity) (-(1:ℝ)/6))
    have Hmul:=mul_le_mul_of_nonneg_left HP (show (0:ℝ)≤2*CK*(1+Ccut) by positivity)
    convert Hmul using 1
    ring
  apply Hcorr.trans
  dsimp only [C]
  have H:=add_le_add HB HA
  convert H using 1
  ring

end OAI.SKFluctuations.Cavity
