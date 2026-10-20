module

public import ComparisonActualGeneralTargetMeanReadout
public import ComparisonSignedCavityActualClockFrozenMeanCorrection
public import ComparisonSignedCavityUniformCenterRefinement

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false

theorem eventually_actual_general_original_longitudinal_mean_budget
    (n r : ℕ) (bf hf : ℝ → ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    (hroot : hf 0 = 0) (Temp : ℝ) (hTemp : 0 ≤ Temp)
    (htotal : ∀u∈Icc (0:ℝ) 1,(hf u:ℝ)+(bf u:ℝ) ≤ Temp)
    (us : List PositiveMass) (hus : ∀u∈us,u.val ≤ 1) :
    ∀ᶠk in atTop,
      let as:=finiteCutMasses us k
      let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
      let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
      ∀(K : ℕ → ℝ) (T : ClockTree (Spin n×Bool) as) (U : ℕ) (a : T.Slot),
        T.leaves ≤ r →
        |nativeOriginalLongitudinalMean T U K b h
          (nativePhysicalResourceCenter n bf hf as) a| ≤
          (16*(r:ℝ)*(r+1)*(r+2)*Temp)/(n+1:ℕ) := by
  have H:=eventually_native_finite_physical_mean_uniform_center n bf hf hbf hhf hroot
    us hus (1/(n+1:ℕ)) (by positivity)
  filter_upwards [H] with k hk
  dsimp only at hk ⊢
  intro K T U a hT
  let as:=finiteCutMasses us k
  have ho:=finiteCutMasses_ordered us hus k
  have Hb (j : ℕ) (_hj : j ≤ as.length) : |(bf (partitionPoint 0 as j):ℝ)| ≤ Temp := by
    rw [abs_of_nonneg (NNReal.coe_nonneg _)]
    have HT:=htotal _ (partitionPoint_mem as ho j)
    linarith [(hf (partitionPoint 0 as j)).coe_nonneg]
  have HM:=native_original_longitudinal_mean_abs_le T ho U K _ _ _ a
    hTemp (show (0:ℝ) ≤ 1/(n+1:ℕ) by positivity) Hb hk
  have hle : (T.leaves:ℝ) ≤ r:=by exact_mod_cast hT
  have HP : 8*(T.leaves:ℝ)*(T.leaves+1)*(T.leaves+2)*Temp ≤
      8*(r:ℝ)*(r+1)*(r+2)*Temp := by gcongr
  have HH:=mul_le_mul_of_nonneg_right HP
    (show (0:ℝ) ≤ 1/(n+1:ℕ)+1/(n+1:ℕ) by positivity)
  apply HM.trans
  convert HH using 1 <;> ring

theorem actual_general_target_original_constant_part_abs_le
    {n : ℕ} (bf hf : ℝ → ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) (i U : ℕ)
    (hi : i < U) (hU : U ≤ as.length) {R E : ℝ}
    (hK : nativeContinuumMixedClock n bf hf as i ≤ R)
    (hL : let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i
      ∀a:g.tree.Slot,|nativeOriginalLongitudinalMean g.tree U
        (nativeContinuumMixedClock n bf hf as)
        (fun j=>(bf (partitionPoint 0 as j):ℝ))
        (fun j=>(hf (partitionPoint 0 as j):ℝ))
        (nativePhysicalResourceCenter n bf hf as) a| ≤ E) :
    |actualGeneralTargetOriginalConstantPart (n:=n) bf hf as i U| ≤ 2*R*E := by
  have Hchi:=actual_general_continuum_chi_mem_unit_on_any_grid (n:=n) bf hf hbf hhf as ho U (by omega) hU
  have HK:=native_continuum_mixed_clock_nonneg n bf hf hbf hhf as ho i
  have hR : 0 ≤ R:=HK.trans hK
  unfold actualGeneralTargetOriginalConstantPart
  dsimp only at hL ⊢
  simp only [native_original_clock_constant_pairing_eq_mean]
  rw [abs_mul,abs_mul,abs_of_nonneg Hchi.1,abs_of_nonneg HK]
  let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i
  have HL:=(abs_add_le _ _).trans (add_le_add (hL (g.embed (singleSlot as))) (hL g.mark))
  have HC:=mul_le_mul Hchi.2 hK HK (by norm_num : (0:ℝ) ≤ 1)
  simp only [one_mul] at HC
  have HH:=mul_le_mul HC HL (abs_nonneg _) hR
  nlinarith only [HH]

theorem actual_general_target_original_mean_correction_abs_le
    {n : ℕ} (bf hf : ℝ → ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    {Temp A : ℝ} (hTemp : 0 ≤ Temp)
    (htotal : ∀u∈Icc (0:ℝ) 1,(hf u:ℝ)+(bf u:ℝ) ≤ Temp)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (i U : ℕ)
    (hi : i < U) (hU : U ≤ as.length)
    (hpart : |actualGeneralTargetOriginalConstantPart (n:=n) bf hf as i U| ≤ A)
    (hmesh : |finitePhysicalMean (n+1) as
      (fun j=>(bf (partitionPoint 0 as j):ℝ)) (fun j=>(hf (partitionPoint 0 as j):ℝ)) i-
      nativePhysicalResourceCenter n bf hf as i| ≤ 1/(n+1:ℕ)) :
    |actualGeneralTargetOriginalMeanCorrection (n:=n) bf hf as i U| ≤ A+(2*Temp+1)/(n+1:ℕ) := by
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let C:=nativePhysicalResourceCenter n bf hf as
  let mean:=finitePhysicalMean (n+1) as b h i
  let K:=nativeContinuumMixedClock n bf hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  have Hchi:=actual_general_continuum_chi_mem_unit_on_any_grid (n:=n) bf hf hbf hhf as ho U (by omega) hU
  have Hmean0 : 0 ≤ mean:=finitePhysicalMean_nonneg (n+1) as b h i
  have Hmean1 : mean ≤ 1:=finitePhysicalMean_le_one (n+1) ho b h i
  have Hb : b i ≤ Temp:=by
    have HT:=htotal _ (partitionPoint_mem as ho i)
    linarith [(hf (partitionPoint 0 as i)).coe_nonneg]
  have Hb0 : 0 ≤ b i:=NNReal.coe_nonneg _
  have Hchi2 : chi^2 ≤ 1:=by change chi∈Icc (0:ℝ) 1 at Hchi;nlinarith [Hchi.1,Hchi.2]
  have Hcoef : chi^2*b i ≤ Temp:=by nlinarith
  have HE : |mean-mean/(n+1:ℕ)-C i| ≤ 2/(n+1:ℕ):=by
    have HH:=abs_add_le (mean-C i) (-(mean/(n+1:ℕ)))
    simp only [abs_neg,←sub_eq_add_neg] at HH
    rw [abs_of_nonneg (div_nonneg Hmean0 (by positivity))] at HH
    have Hdiv:=div_le_div_of_nonneg_right Hmean1 (show (0:ℝ) ≤ (n+1:ℕ) by positivity)
    change |mean-C i| ≤ 1/(n+1:ℕ) at hmesh
    rw [show mean-mean/(n+1:ℕ)-C i=mean-C i-mean/(n+1:ℕ) by ring,
      show (2:ℝ)/(n+1:ℕ)=1/(n+1:ℕ)+1/(n+1:ℕ) by ring]
    exact HH.trans (add_le_add hmesh Hdiv)
  have HM : |chi^2*b i*(mean-mean/(n+1:ℕ)-C i)| ≤ 2*Temp/(n+1:ℕ):=by
    rw [abs_mul,abs_of_nonneg (mul_nonneg (sq_nonneg _) Hb0)]
    have HH:=mul_le_mul Hcoef HE (abs_nonneg _) hTemp
    exact HH.trans_eq (by ring)
  change |actualGeneralTargetOriginalConstantPart (n:=n) bf hf as i U+
    chi^2*b i*(mean-mean/(n+1:ℕ)-C i)-(mean-C i)| ≤ _
  have HH:=(abs_add_le
    (actualGeneralTargetOriginalConstantPart (n:=n) bf hf as i U+chi^2*b i*(mean-mean/(n+1:ℕ)-C i))
    (-(mean-C i))).trans (add_le_add (abs_add_le _ _) le_rfl)
  simp only [abs_neg,←sub_eq_add_neg] at HH
  apply HH.trans
  have HH':=add_le_add (add_le_add hpart HM) hmesh
  convert HH' using 1 <;> ring

theorem eventually_actual_general_target_original_mean_correction_budget
    (n : ℕ) (bf hf : ℝ → ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    (hroot : hf 0 = 0) (Temp : ℝ) (hTemp : 0 ≤ Temp)
    (htotal : ∀u∈Icc (0:ℝ) 1,(hf u:ℝ)+(bf u:ℝ) ≤ Temp)
    (us : List PositiveMass) (hus : ∀u∈us,u.val ≤ 1) :
    ∀ᶠk in atTop,
      let as:=finiteCutMasses us k
      ∀i U : ℕ,i < U → U ≤ as.length →
        |actualGeneralTargetOriginalMeanCorrection (n:=n) bf hf as i U| ≤
          (768*Temp^2+2*Temp+1)/(n+1:ℕ) := by
  have HL:=eventually_actual_general_original_longitudinal_mean_budget n 2 bf hf hbf hhf hroot Temp hTemp htotal us hus
  have HC:=eventually_native_finite_physical_mean_uniform_center n bf hf hbf hhf hroot us hus
    (1/(n+1:ℕ)) (by positivity)
  filter_upwards [HL,HC] with k hk hc
  dsimp only at hk hc ⊢
  intro i U hi hU
  let as:=finiteCutMasses us k
  let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i
  have ho:=finiteCutMasses_ordered us hus k
  have hKm:=native_continuum_mixed_clock_monotone n bf hf hbf hhf as ho
  have hK : nativeContinuumMixedClock n bf hf as i ≤ Temp:=
    (hKm (hi.le.trans hU)).trans ((native_continuum_mixed_clock_terminal_le n bf hf hbf hhf as ho).trans
      (htotal 1 (by norm_num)))
  have hleaves : g.tree.leaves ≤ 2:=by
    have HH:=(single (S:=Spin n×Bool) as).markedAttach_leaves 0 g (nativeFreshAtSlot_mem _ 0 (singleSlot as) i)
    simpa only [single_leaves_exact] using HH
  have HP:=actual_general_target_original_constant_part_abs_le bf hf hbf hhf as ho i U hi hU hK
    (fun a=>hk _ g.tree U a hleaves)
  have HM:=actual_general_target_original_mean_correction_abs_le bf hf hbf hhf hTemp htotal as ho i U hi hU HP
    (hc i (hi.le.trans hU))
  apply HM.trans_eq
  norm_num only [Nat.cast_ofNat] at *
  ring

end OAI.SKFluctuations.Cavity
