module

public import ComparisonSignedCavityActualOriginalClockGCarrier
public import ComparisonSignedCavityContinuumMixedClock

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 10000000

theorem nativeOriginalClockGBranchBeta_bound
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ Temp)
    {as : List PositiveMass} {i star U : ℕ} (ho : MassOrdered 0 as)
    (hs : star < U) (hU : U ≤ as.length) (K : ℕ→ℝ)
    (hK : ∀j,0 ≤ K j) (hKm : Monotone K)
    (st : NativeActualResourceState (Spin n×Bool) as i star) (tag : ℕ) :
    |nativeOriginalClockGBranchBeta U K (fun j=>(M.bf (partitionPoint 0 as j):ℝ)) st tag| ≤ Temp := by
  let chi:=((st.tree.markedAttach 0).map (fun p=>p.coeff*
    fullScalarCutGamma p.tree U K (p.embed st.term.live.test.target) p.mark)).sum
  obtain ⟨hlo,hhi⟩:=native_full_gamma_row_uniform_bounds n st.tree ho 0 ho U (by omega)
    hU K hKm hK (B:=K as.length) le_rfl st.term.live.test.target
  have hchi : 0 ≤ chi:=(Real.exp_pos _).le.trans hlo
  have hb : (M.bf (partitionPoint 0 as star):ℝ) ≤ Temp := by
    have H:=M.inherited_total_clock_le htotal _ (partitionPoint_mem as ho star)
    linarith [(M.hf (partitionPoint 0 as star)).coe_nonneg]
  unfold nativeOriginalClockGBranchBeta
  change |(if tag=0 then chi else 1)*(M.bf (partitionPoint 0 as star):ℝ)| ≤ Temp
  split_ifs with ht
  · rw [abs_of_nonneg (mul_nonneg hchi (NNReal.coe_nonneg _))]
    exact (mul_le_mul_of_nonneg_right hhi (NNReal.coe_nonneg _)).trans (by simpa using hb)
  · simpa only [one_mul,abs_of_nonneg (NNReal.coe_nonneg _)] using hb

theorem actual_calibrated_continuum_G_weight_bound
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp L Cs W : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcu : 0 < cu) (hAz : 0 ≤ Az) (hTemp : 0 < Temp) (hW : 0 < W)
    (hb : ∀u,M.b u=Temp) (hh : ∀u,M.h u=0)
    (w : ActualSlowWindowChoice) (Hw : IsActualCalibratedSlowWindow M W Temp L Cs w)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (hstar : w.star∈as)
    (i U : ℕ) (hs : retainedMassPrefixIndex w.star.val as < U) (hU : U ≤ as.length)
    (st : NativeActualResourceState (Spin n×Bool) as i (retainedMassPrefixIndex w.star.val as))
    (tag : ℕ) :
    let c:=starMassBandConstant cu Az/cu
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    |nativeOriginalClockParentWeight W U K st (nativeOriginalClockGBranchBeta U K b st tag)| ≤
      Temp/(Real.exp (-4*Temp)*(3*Temp*c/8)) := by
  let c:=starMassBandConstant cu Az/cu
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  have hc : 0 < c:=div_pos (star_mass_band_constant_pos hcu hAz) hcu
  have hK:=native_continuum_mixed_clock_nonneg n M.bf M.hf M.inherited_bf_monotone
    M.inherited_hf_monotone as ho
  have hKm:=native_continuum_mixed_clock_monotone n M.bf M.hf M.inherited_bf_monotone
    M.inherited_hf_monotone as ho
  have htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ Temp := by
    intro u hu
    rw [hh u,hb u,zero_add]
  have hterminal : K as.length ≤ Temp :=
    (native_continuum_mixed_clock_terminal_le n M.bf M.hf M.inherited_bf_monotone
      M.inherited_hf_monotone as ho).trans (M.inherited_total_clock_le htotal 1 (by norm_num))
  obtain ⟨p,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hlo,_,_⟩:=Hw
  have hstarK : (3*Temp*c/8)*W ≤ K (retainedMassPrefixIndex w.star.val as) := by
    dsimp only [K]
    rw [native_continuum_mixed_clock_retained_eq n M.bf M.hf as ho w.star hstar]
    exact hlo
  have hbeta:=nativeOriginalClockGBranchBeta_bound M htotal ho hs hU K hK hKm st tag
  have H:=native_full_gamma_recursion_coefficient_bound n st.tree ho 0 ho U (by omega)
    hU K hKm hK hterminal st.term.live.test.target hW
    (show 0 < 3*Temp*c/8 by positivity) hstarK hbeta
  dsimp only at H ⊢
  unfold nativeOriginalClockParentWeight
  dsimp only
  rw [abs_mul,abs_of_pos hW]
  apply (mul_le_mul_of_nonneg_left H hW.le).trans
  apply le_of_eq
  change W*(Temp/(Real.exp (-4*Temp)*(3*Temp*c/8)*W))=
    Temp/(Real.exp (-4*Temp)*(3*Temp*c/8))
  field_simp

end OAI.SKFluctuations.Cavity
