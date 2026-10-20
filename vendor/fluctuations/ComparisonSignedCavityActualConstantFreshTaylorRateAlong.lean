module

public import ComparisonSignedCavityActualConstantFreshLowTaylorRateAlong
public import ComparisonSignedCavityActualConstantFreshHighTaylorRate
public import ComparisonSignedCavityActualTaylorHighLowBudget
public import ComparisonSignedCavityActualInheritedLowErrorDensity
public import ComparisonSignedCavitySharpOriginalLowRadius
public import ComparisonSignedCavityTransientForkCost

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 22000000

theorem actual_inherited_constant_fresh_full_Taylor_rate_along
    (Bclock Temp Cf Ccut : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCcut : 0 < Ccut)
    {m delta cl cu Az C0 Ct D Tstar Lwin Cs Cwindow c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) (hCs : 0≤Cs)
    (hc : 0 < c) (hcouter : 2*cu*(Az+1)≤c)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠ n : ℕ in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (hsmall : ∀ᶠ n : ℕ in atTop,(M n).xs^2≤Cs*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (Hshell : ∀ᶠn in atTop,∃(Tbase epsilon shell : ℝ) (ts : List ComparisonHistoryTerm),
      (∀u,(M n).b u=historyMatrixClock Tbase epsilon shell ts u) ∧
      (∀u,(M n).h u=historyFieldClock ts u))
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠ n : ℕ in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cwindow (w n)) :
    ∃err : ℕ→ℝ,Tendsto err atTop (𝓝 0) ∧ ∀ᶠ n : ℕ in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤(M n).xs → (w n).star ∈ us →
      ∀ᶠ jGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
        let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀U : ℕ,star < U → U≤as.length → 2*c*W n≤partitionPoint 0 as U → partitionPoint 0 as U≤ min (Ccut*W n) 1 →
        ∀seedMass : ℝ,
          let g:=nativeFreshAtSlot (single (S:=Spin (dim n)×Bool) as) seedMass (singleSlot as) star
          ∀a z : g.tree.Slot,
            |nativeActualTaylorRemainder (dim n) q U b h K g.tree (fun _=>1) a z|≤
              err n*(W n*(M n).xs^2) := by
  obtain ⟨CH,hCH,HH⟩:=eventually_actual_shell_history_constant_fresh_HIGH_parts_rate
    (D:=D) (Cs:=Cs) Bclock Temp Cf Ccut hTemp hCf hCcut.le
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  have Hclock : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1:=by
    filter_upwards [Hshell] with n hn
    rcases hn with ⟨Tbase,epsilon,shell,ts,hb,hh⟩
    exact NativePullbackClockRegularity.of_shell_history
      (M n).context.hc (M n).context.hk (M n).context.hkc (M n).context.hm (M n).context.hM
      (M n).alpha Tbase epsilon shell ts (M n).b (M n).h hb hh le_rfl zero_le_one le_rfl
  obtain ⟨eLow,heLow,HLow⟩:=actual_inherited_constant_fresh_third_LOW_rate_along
    Bclock Temp Cf Ccut hTemp hCf hCcut hm hdelta hroom hcl hcu hAz hC0 hCt hCs
    dim hdim M W hcanonical hWlim Hsource hsmall Hclock w hw
  let eta:=actualMassSavingExponent m delta
  let err:=fun n=>2*CH*((dim n+1:ℕ):ℝ)^(-eta/256)+|eLow n|/2
  have Hpow:=(tendsto_rpow_neg_atTop (show 0 < eta/256 from div_pos
    (actualMassSavingExponent_pos hm hdelta) (by norm_num))).comp
    (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
  have Herr : Tendsto err atTop (𝓝 0):=by
    have H:=(Hpow.const_mul (2*CH)).add (heLow.abs.div_const 2)
    simpa only [err,Function.comp_def,abs_zero,zero_mul,mul_zero,zero_div,add_zero,neg_div] using H
  refine ⟨err,Herr,?_⟩
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hdim.eventually HH,HLow,Hsource,hsmall,HW1,Hshell] with n hnH hnL hsource hnSmall hnW hnShell
  rcases hnShell with ⟨Tbase,epsilon,shell,ts,hb,hh⟩
  have hxW : (M n).xs≤W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hxs1:=hxW.trans hnW
  intro L us hus hret hmesh hstar
  filter_upwards [hnH (M n) Tbase epsilon shell ts hsource hb hh
      hnSmall (by simpa only [←hcanonical] using hnW) L us hus hret hmesh,
    hnL L us hus hret hmesh hstar] with jGrid hgridH hgridL
  dsimp only at hgridH hgridL ⊢
  intro U hs hU hcutlo hcut seedMass a z
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let g:=nativeFreshAtSlot (single (S:=Spin (dim n)×Bool) as) seedMass (singleSlot as) star
  let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have had:=comparisonVariableEndpoint_clocks_admissible (M n).context.hc (M n).context.hk
    (M n).context.hkc (M n).context.hm (M n).context.hM (M n).b (M n).h
    (M n).context.hd.ne' (M n).hlam.le (M n).hlb (M n).hb (M n).hh (M n).hh0 (M n).alpha
  have hbf:=toNNReal_monotoneOn had.1
  have hhf:=toNNReal_monotoneOn had.2.1
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show ((M n).bf u:ℝ)≤(M n).bf v from hbf hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show ((M n).hf u:ℝ)≤(M n).hf v from hhf hu hv huv) as ho
  let H:=CH*((dim n+1:ℕ):ℝ)^(-eta/256)*W n*(M n).xs^2
  let LL:=|eLow n| *(W n*(M n).xs^2)
  have hW : 0<W n:=(M n).hxs.trans_le hxW
  have hH : 0≤H:=by dsimp only [H];positivity
  have hLL : 0≤LL:=by dsimp only [LL];positivity
  have HHi (l t : ℝ) (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1) (part : Fin 3) :
      |nativeActualHigherHighPart part (dim n) q U b h K g.tree (fun _=>1) a z l t|≤H:=by
    have HH:=hgridH star U hs hU (by simpa only [←hcanonical] using hcutlo)
      (by simpa only [←hcanonical] using hcut.trans (min_le_left _ _)) seedMass a z l t hl ht part
    simpa only [H,eta,NativeOverlapContext.N,←hcanonical,neg_div] using HH
  have HLo (l t : ℝ) (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1) :
      |nativeActualCenteredThirdLowPart (dim n) q U b h K g.tree (fun _=>1) a z l t|≤LL:=by
    apply (hgridL U hs hU hcut seedMass a z l t hl ht).trans
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  have HB:=native_actual_taylor_remainder_abs_le_HIGH_LOW (dim n) q U b h K g.tree ho (fun _=>1) a z
    (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
    (fun i=>by cases i <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _)
    (native_continuum_mixed_clock_nonneg (dim n) (M n).bf (M n).hf hbf hhf as ho) hbm hhm
    (native_continuum_mixed_clock_monotone (dim n) (M n).bf (M n).hf hbf hhf as ho)
    H LL hH hLL HHi HLo
  apply HB.trans_eq
  dsimp only [H,LL,err]
  ring

end OAI.SKFluctuations.Cavity
