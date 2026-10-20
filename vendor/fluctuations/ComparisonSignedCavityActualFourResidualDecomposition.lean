module

public import ComparisonSignedCavityActualFourResourceIteration
public import ComparisonSignedCavityActualFourGContinuumWeights

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    {as : List PositiveMass} {i star U : ℕ}

def nativeActualOriginalFourPairContrast
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (U : ℕ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) : ℝ :=
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let qr : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let P:=nativeActualResourceRestValue st.term 0 qfull 0 C
  let Pc:=nativeOriginalCenteredRestTest n qr U b h K st.tree P
  let s:=st.term.live.test.target
  let g:=nativeFreshAtSlot st.tree 0 s star
  nativeActualOriginalFreshPairMoment n qr U b h K C st.tree Pc s star-
    (1/2:ℝ)*nativeActualOriginalFreshPairMoment n qr U b h K C g.tree
      (fun σ=>Pc (g.restRestrict σ)) g.mark star

def nativeActualOriginalFourSourceErrorContrast
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (U : ℕ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) : ℝ :=
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let qr : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let P:=nativeActualResourceRestValue st.term 0 qfull 0 C
  let Pc:=nativeOriginalCenteredRestTest n qr U b h K st.tree P
  let s:=st.term.live.test.target
  let g:=nativeFreshAtSlot st.tree 0 s star
  nativeActualOriginalOneStepError n qr U b h K C st.tree Pc s star-
    (1/2:ℝ)*nativeActualOriginalOneStepError n qr U b h K C g.tree
      (fun σ=>Pc (g.restRestrict σ)) g.mark star

def nativeActualOriginalFourFrozenChildCorrection
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : star<U) (hU : U≤as.length) (W : ℝ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) : ℝ :=
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let children:=nativeActualWeightedBranchStep (nativeOriginalHighRowGamma U K) hs (hs.le.trans hU)
    nativeActualOriginalFourGBranches
    (fun parent tag=>nativeOriginalClockParentWeight W U K parent
      (nativeOriginalClockFourGBranchBeta U K b parent tag)) st
  (children.map (fun Q=>nativeActualMinimumFourStateResponse M U W Q.freeze)).sum

theorem native_actual_original_four_resource_defect_decomposition
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (U : ℕ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    nativeActualOriginalFourResourceDefect M U st=
      (1-(M.bf (partitionPoint 0 as star):ℝ)*chi^2)*nativeActualOriginalFourPairContrast M U st-
        nativeActualOriginalFourSourceErrorContrast M U st := by
  unfold nativeActualOriginalFourResourceDefect nativeOriginalPairRecursionDefect
    nativeActualOriginalFourPairContrast nativeActualOriginalFourSourceErrorContrast
  dsimp only
  ring

theorem native_actual_original_four_recursion_error_decomposition
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : star<U) (hU : U≤as.length) (W : ℝ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    nativeActualOriginalFourRecursionError M hs hU W st=
      (1-(M.bf (partitionPoint 0 as star):ℝ)*chi^2)/(chi*K star)*
        ((W⁻¹)^st.generation*nativeActualOriginalFourPairContrast M U st)-
      (1/(chi*K star))*((W⁻¹)^st.generation*nativeActualOriginalFourSourceErrorContrast M U st)-
      nativeActualOriginalFourFrozenChildCorrection M hs hU W st := by
  unfold nativeActualOriginalFourRecursionError
  rw [native_actual_original_four_resource_defect_decomposition]
  dsimp only
  unfold nativeActualOriginalFourFrozenChildCorrection nativeActualMinimumFourStateResponse
  dsimp only
  ring

theorem actual_minimum_four_denominator_bounds
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {Temp W cK : ℝ} (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤Temp)
    (hW : 0<W) (hcK : 0<cK) (ho : MassOrdered 0 as)
    (hs : star<U) (hU : U≤as.length)
    (hstarK : cK*W≤nativeContinuumMixedClock n M.bf M.hf as star) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    0<chi*K star ∧ chi≤1 ∧ Real.exp (-4*Temp)*cK*W≤chi*K star := by
  dsimp only
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  have hKm:=native_continuum_mixed_clock_monotone n M.bf M.hf M.inherited_bf_monotone
    M.inherited_hf_monotone as ho
  have hK0:=native_continuum_mixed_clock_nonneg n M.bf M.hf M.inherited_bf_monotone
    M.inherited_hf_monotone as ho
  have hterm : K as.length≤Temp:=
    (native_continuum_mixed_clock_terminal_le n M.bf M.hf M.inherited_bf_monotone
      M.inherited_hf_monotone as ho).trans (M.inherited_total_clock_le htotal 1 (by norm_num))
  have HH:=scalar_boundary_hessian_uniform_bounds ho (relocatedClock U 0 K)
    (relocatedClock_monotone U (by norm_num : (0:ℝ)∈Icc 0 1) hKm hK0)
    (by simp [relocatedClock,show 0<U by omega])
    (B:=Temp) (by simpa [relocatedClock,not_lt.mpr hU] using hterm)
  have hchi:=(Real.exp_pos (-4*Temp)).trans_le HH.1
  have hp : 0<K star:=(mul_pos hcK hW).trans_le hstarK
  refine ⟨mul_pos hchi hp,HH.2,?_⟩
  simpa only [mul_assoc] using mul_le_mul HH.1 hstarK (mul_pos hcK hW).le hchi.le

theorem actual_minimum_four_recursion_error_abs_le
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {Temp W cK Bpair Bsource Bfrozen : ℝ}
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤Temp)
    (hW : 0<W) (hcK : 0<cK) (ho : MassOrdered 0 as)
    (hs : star<U) (hU : U≤as.length)
    (hstarK : cK*W≤nativeContinuumMixedClock n M.bf M.hf as star)
    (st : NativeActualResourceState (Spin n×Bool) as i star)
    (Hpair : |(W⁻¹)^st.generation*nativeActualOriginalFourPairContrast M U st|≤Bpair)
    (Hsource : |(W⁻¹)^st.generation*nativeActualOriginalFourSourceErrorContrast M U st|≤Bsource)
    (Hfrozen : |nativeActualOriginalFourFrozenChildCorrection M hs hU W st|≤Bfrozen) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    |nativeActualOriginalFourRecursionError M hs hU W st|≤
      (|1-(M.bf (partitionPoint 0 as star):ℝ)*chi^2| *Bpair+Bsource)/
        (Real.exp (-4*Temp)*cK*W)+Bfrozen := by
  dsimp only
  rw [native_actual_original_four_recursion_error_decomposition]
  obtain ⟨hd,_,hden⟩:=actual_minimum_four_denominator_bounds M htotal hW hcK ho hs hU hstarK
  have hp:= (abs_nonneg _).trans Hpair
  have hs0:= (abs_nonneg _).trans Hsource
  have Hsub (a b : ℝ) : |a-b|≤|a|+|b| := by
    simpa only [sub_eq_add_neg,abs_neg] using abs_add_le a (-b)
  apply (Hsub _ _).trans
  apply (add_le_add (Hsub _ _) Hfrozen).trans
  simp only [abs_mul,abs_div,abs_of_pos hd,abs_one] at Hpair Hsource ⊢
  let defect:=1-(M.bf (partitionPoint 0 as star):ℝ)*
    (scalarTerminal.schedule (scalarBoundaryClocks as
      (relocatedClock U 0 (nativeContinuumMixedClock n M.bf M.hf as)))).H 0 0^2
  have H1:=mul_le_mul_of_nonneg_left Hpair (div_nonneg (abs_nonneg defect) hd.le)
  have H2:=mul_le_mul_of_nonneg_left Hsource (div_nonneg zero_le_one hd.le)
  apply (add_le_add (add_le_add H1 H2) le_rfl).trans
  apply add_le_add _ le_rfl
  dsimp only [defect]
  calc
    _=(|1-(M.bf (partitionPoint 0 as star):ℝ)*
      (scalarTerminal.schedule (scalarBoundaryClocks as
        (relocatedClock U 0 (nativeContinuumMixedClock n M.bf M.hf as)))).H 0 0^2| *Bpair+Bsource)/
      ((scalarTerminal.schedule (scalarBoundaryClocks as
        (relocatedClock U 0 (nativeContinuumMixedClock n M.bf M.hf as)))).H 0 0*
          nativeContinuumMixedClock n M.bf M.hf as star) := by ring
    _≤_:=div_le_div_of_nonneg_left (by positivity) (by positivity) hden

end OAI.SKFluctuations.Cavity
