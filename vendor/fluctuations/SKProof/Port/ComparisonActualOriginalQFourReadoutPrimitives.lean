module

public import ComparisonSignedCavityActualFourResourceIteration
public import ComparisonSignedCavityCurrentGOriginalLawRestoration
public import ComparisonSignedCavityActualResourceGaReadout
public import ComparisonSignedCavityActualFourOtherSourceCategories
public import ComparisonSignedCavityActualFreshResourceHighTaylorReadout
public import ComparisonSignedCavityActualFreshResourceLowTaylorReadout
public import ComparisonSignedCavityActualFreshResourceTaylorBudget
public import ComparisonSignedCavityActualFourHigherTaylorReadout
public import ComparisonSignedCavityActualSmallSourceFourWeights
public import ComparisonSignedCavityActualSmallSourceTaylorDenominator
public import ComparisonSignedCavityActualFourHigherTaylorProfile
public import ComparisonSignedCavityActualFreshResourceJointHighRestorationReadout
public import ComparisonSignedCavityActualFourJointHighRestorationReadout
public import ComparisonSignedCavityActualFourJointHighRestorationProfile
public import ComparisonSignedCavityActualCenteredResourceLongitudinalRestoration
public import ComparisonSignedCavityActualFourLongitudinalRestorationReadout
public import ComparisonSignedCavityActualFourGaCurrent
public import ComparisonSignedCavityActualFourGaRestorationProfile
public import ComparisonSignedCavityActualFourLongitudinalRestorationProfile
public import ComparisonSignedCavityActualResourceGammaRestorationReadout
public import ComparisonSignedCavityActualFourGammaRestorationReadout
public import SKProof.Port.ComparisonActualOriginalQPhysicalSourceProfiles
public import SKProof.Port.ComparisonActualOriginalQPhysicalTaylorProfiles
public import SKProof.Port.ComparisonActualOriginalQOriginalTaylorProfiles
public import SKProof.Port.ComparisonActualOriginalQOriginalTargetReadout
public import SKProof.Port.ComparisonActualOriginalQOriginalTargetB0
public import SKProof.Port.ComparisonActualOriginalQAnalyticBasics

@[expose] public section

noncomputable section
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 26000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    {as : List PositiveMass} {i star U : ℕ}

def nativeActualMinimumFourCenteredForest_original_q
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : star < U) (hU : U ≤ as.length) (W : ℝ) (depth : ℕ)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star)) :
    List (NativeActualResourceState (Spin n×Bool) as i star) :=
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  nativeActualFourCenteredForest (nativeOriginalHighRowGamma U K) hs (hs.le.trans hU)
    (fun parent tag=>nativeOriginalClockParentWeight W U K parent
      (nativeOriginalClockFourGBranchBeta U K b parent tag)) depth xs

end OAI.SKFluctuations.Cavity

set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators

def nativeActualGProjectedRestoration_original_q
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : NativeGeneratedTest T) (star U : ℕ)
    {m delta cl cu Az C0 Ct D₀ Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D₀ Bclock)
    (q : ℕ→RestCoordinate n→ℝ) : ℝ :=
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let C:=fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
    (completedPathClock (n+1) M.sweepBf M.sweepHf) (orderedOverlap (n+1)) (partitionPoint 0 as j)
  let R:=fun u v=>deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false))
  nativeOriginalGProjectedDisplacementRestoration T P.target star U q b h K C R
    (nativeRestGeneratedTestValue T P R C)

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 24000000

def nativeActualResourceOriginalScalar_original_q {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) : ℝ :=
  P.scalar (fullWeight n) (fullFeature n) 0
    (finitePhysicalCavitySquareVariance n U as
      (fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)) (fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)) 1 1)
    (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
    (nativePhysicalResourceCenter n M.sweepBf M.sweepHf as) 0

def nativeActualResourceGaRestoration_original_q {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) : ℝ :=
  nativeActualResourceOriginalScalar_original_q M U P*
    nativeActualGProjectedRestoration_original_q T P.live.test star U M
      (fun j=>Sum.elim (fun _=>(M.sweepBf (partitionPoint 0 as j):ℝ))
        (fun _=>(M.sweepHf (partitionPoint 0 as j):ℝ)))

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 20000000

def nativeActualOriginalFourOtherCategoryContrast_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ)
    (st : NativeActualResourceState (Spin n×Bool) as i star)
    (cat : NativeActualOtherSourceCategory) : ℝ :=
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let Pc:=nativeOriginalCenteredRestTest n q U b h K st.tree
    (nativeActualResourceRestValue st.term 0 qfull 0 C)
  let s:=st.term.live.test.target
  let g:=nativeFreshAtSlot st.tree 0 s star
  nativeActualOriginalOtherSourceCategory cat n q U b h K C st.tree Pc s star-
    (1/2:ℝ)*nativeActualOriginalOtherSourceCategory cat n q U b h K C g.tree
      (fun σ=>Pc (g.restRestrict σ)) g.mark star

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 16000000

def nativeActualOriginalFreshResourceHigherHighPart_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) (part : Fin 3) (l t : ℝ) : ℝ :=
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let Pc:=nativeOriginalCenteredRestTest n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C)
  let g:=nativeFreshAtSlot T 0 P.live.test.target star
  nativeActualHigherHighPart part n q U b h K g.tree
    (fun σ=>Pc (g.restRestrict (g.tree.cavityAssignment σ).1)) (g.embed P.live.test.target) g.mark l t

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000

def nativeActualOriginalFreshResourceThirdLowPart_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) (l t : ℝ) : ℝ :=
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let Pc:=nativeOriginalCenteredRestTest n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C)
  let g:=nativeFreshAtSlot T 0 P.live.test.target star
  nativeActualCenteredThirdLowPart n q U b h K g.tree
    (fun σ=>Pc (g.restRestrict σ)) (g.embed P.live.test.target) g.mark l t

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000

def nativeActualOriginalFreshResourceTaylorRemainder_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) : ℝ :=
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let Pc:=nativeOriginalCenteredRestTest n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C)
  let g:=nativeFreshAtSlot T 0 P.live.test.target star
  nativeActualTaylorRemainder n q U b h K g.tree
    (fun σ=>Pc (g.restRestrict σ)) (g.embed P.live.test.target) g.mark

theorem actual_minimum_normalized_fresh_resource_Taylor_abs_le_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U k : ℕ) (P : NativeResourceTerm i star T) (ho : MassOrdered 0 as)
    {W H L : ℝ} (hW : 0 < W) (hH : 0 ≤ H) (hL : 0 ≤ L)
    (hHigh : ∀l t : ℝ,l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → ∀part : Fin 3,
      |(W⁻¹)^k*nativeActualOriginalFreshResourceHigherHighPart_original_q M U P part l t| ≤ H)
    (hLow : ∀l t : ℝ,l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 →
      |(W⁻¹)^k*nativeActualOriginalFreshResourceThirdLowPart_original_q M U P l t| ≤ L) :
    |(W⁻¹)^k*nativeActualOriginalFreshResourceTaylorRemainder_original_q M U P| ≤ 2*H+L/2 := by
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let Pc:=nativeOriginalCenteredRestTest n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C)
  let g:=nativeFreshAtSlot T 0 P.live.test.target star
  let norm:=(W⁻¹)^k
  have hnorm : 0 < norm:=by dsimp only [norm];positivity
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepBf u:ℝ) ≤ M.sweepBf v from M.inherited_bf_monotone hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepHf u:ℝ) ≤ M.sweepHf v from M.inherited_hf_monotone hu hv huv) as ho
  have HK:=native_continuum_mixed_clock_nonneg n M.sweepBf M.sweepHf M.inherited_bf_monotone M.inherited_hf_monotone as ho
  have HKm:=native_continuum_mixed_clock_monotone n M.sweepBf M.sweepHf M.inherited_bf_monotone M.inherited_hf_monotone as ho
  have H:=native_actual_taylor_remainder_abs_le_HIGH_LOW n q U b h K g.tree ho
    (fun σ=>Pc (g.restRestrict σ)) (g.embed P.live.test.target) g.mark
    (by intro j x;cases x <;> exact NNReal.coe_nonneg _)
    (by intro x;cases x <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) HK hbm hhm HKm
    (H/norm) (L/norm) (div_nonneg hH hnorm.le) (div_nonneg hL hnorm.le)
    (by
      intro l t hl ht part
      have HH:=hHigh l t hl ht part
      rw [abs_mul,abs_of_pos hnorm] at HH
      apply (le_div_iff₀ hnorm).2
      simpa only [nativeActualOriginalFreshResourceHigherHighPart_original_q,mul_comm] using HH)
    (by
      intro l t hl ht
      have HH:=hLow l t hl ht
      rw [abs_mul,abs_of_pos hnorm] at HH
      apply (le_div_iff₀ hnorm).2
      simpa only [nativeActualOriginalFreshResourceThirdLowPart_original_q,mul_comm] using HH)
  unfold nativeActualOriginalFreshResourceTaylorRemainder_original_q
  dsimp only
  change |norm*nativeActualTaylorRemainder n q U b h K g.tree
    (fun σ=>Pc (g.restRestrict σ)) (g.embed P.live.test.target) g.mark| ≤ _
  rw [abs_mul,abs_of_pos hnorm]
  apply (mul_le_mul_of_nonneg_left H hnorm.le).trans_eq
  field_simp

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 20000000

theorem native_actual_four_higher_Taylor_contrast_eq_resources_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) (ho : MassOrdered 0 as) :
    nativeActualOriginalFourOtherCategoryContrast_original_q M U st .higherTaylor=
      nativeActualOriginalFreshResourceTaylorRemainder_original_q M U st.term-
        (1/2:ℝ)*nativeActualOriginalFreshResourceTaylorRemainder_original_q M U (st.term.retarget 0) := by
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have HQ : cutFullVariance n q U 1 1 b h K=finitePhysicalCavitySquareVariance n U as b h 1 1:=
    native_full_endpoint_clock_mixed_independent n q U 1 b h K (finitePhysicalMixedClock (n+1) as b h)
  have Hread:=native_actual_centered_resource_fresh_rest_readout (U:=U) q b h K C st.tree st.term ho
  dsimp only at Hread
  rw [HQ] at Hread
  unfold nativeActualOriginalFourOtherCategoryContrast_original_q nativeActualOriginalOtherSourceCategory
    nativeActualOriginalFreshResourceTaylorRemainder_original_q
  dsimp only
  rw [Hread]
  rfl

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 10000000

theorem actual_continuum_four_G_weight_bound_of_small_source_clocks_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp Cf W cK : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hCf : 0 ≤ Cf) (hsource : ActualOriginalQSmallSourceClocks M Temp Cf) (hxs : M.xs ≤ 1)
    (hW : 0<W) (hcK : 0<cK) (as : List PositiveMass) (ho : MassOrdered 0 as)
    {i star U : ℕ} (hs : star<U) (hU : U ≤ as.length)
    (hstarK : cK*W ≤ nativeContinuumMixedClock n M.sweepBf M.sweepHf as star)
    (st : NativeActualResourceState (Spin n×Bool) as i star) (tag : ℕ) :
    let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
    let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
    |nativeOriginalClockParentWeight W U K st (nativeOriginalClockFourGBranchBeta U K b st tag)| ≤
      (Temp+2*Cf)/(Real.exp (-4*(Temp+2*Cf))*cK) := by
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  have hK:=native_continuum_mixed_clock_nonneg n M.sweepBf M.sweepHf M.inherited_bf_monotone
    M.inherited_hf_monotone as ho
  have hKm:=native_continuum_mixed_clock_monotone n M.sweepBf M.sweepHf M.inherited_bf_monotone
    M.inherited_hf_monotone as ho
  have hterminal : K as.length ≤ Temp+2*Cf:=by
    apply (native_continuum_mixed_clock_terminal_le n M.sweepBf M.sweepHf M.inherited_bf_monotone
      M.inherited_hf_monotone as ho).trans
    have HH:=hsource 1 (by norm_num)
    have HF:=mul_le_mul_of_nonneg_left (show M.xs+1 ≤ 2 by linarith) hCf
    linarith
  apply nativeOriginalClockParentWeight_four_beta_abs_le
  intro t
  have hbeta : |nativeOriginalClockGBranchBeta U K b st t| ≤ Temp+2*Cf:=by
    let chi:=((st.tree.markedAttach 0).map (fun p=>p.coeff*
      fullScalarCutGamma p.tree U K (p.embed st.term.live.test.target) p.mark)).sum
    obtain ⟨hlo,hhi⟩:=native_full_gamma_row_uniform_bounds n st.tree ho 0 ho U (by omega)
      hU K hKm hK (B:=K as.length) le_rfl st.term.live.test.target
    have hchi : 0 ≤ chi:=(Real.exp_pos _).le.trans hlo
    have hb : b star ≤ Temp+2*Cf:=by
      have H:=(hsource _ (partitionPoint_mem as ho star)).1
      dsimp only [b] at H ⊢
      linarith
    have hb0 : 0 ≤ b star:=NNReal.coe_nonneg _
    unfold nativeOriginalClockGBranchBeta
    change |(if t=0 then chi else 1)*b star| ≤ Temp+2*Cf
    split_ifs
    · rw [abs_of_nonneg (mul_nonneg hchi hb0)]
      exact (mul_le_mul_of_nonneg_right hhi hb0).trans (by simpa only [one_mul] using hb)
    · simpa only [one_mul,abs_of_nonneg hb0] using hb
  have H:=native_full_gamma_recursion_coefficient_bound n st.tree ho 0 ho U (by omega)
    hU K hKm hK hterminal st.term.live.test.target hW hcK hstarK hbeta
  unfold nativeOriginalClockParentWeight
  rw [abs_mul,abs_of_pos hW]
  apply (mul_le_mul_of_nonneg_left H hW.le).trans
  apply le_of_eq
  field_simp

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 16000000

theorem actual_minimum_four_denominator_bounds_of_small_source_clocks_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp Cf W cK : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hCf : 0 ≤ Cf) (HS : ActualOriginalQSmallSourceClocks M Temp Cf) (hxs : M.xs ≤ 1)
    (hW : 0 < W) (hcK : 0 < cK) {as : List PositiveMass} (ho : MassOrdered 0 as)
    {star U : ℕ} (hs : star<U) (hU : U ≤ as.length)
    (hstarK : cK*W ≤ nativeContinuumMixedClock n M.sweepBf M.sweepHf as star) :
    let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    0<chi*K star ∧ chi ≤ 1 ∧ Real.exp (-4*(Temp+2*Cf))*cK*W ≤ chi*K star := by
  dsimp only
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  have hK:=native_continuum_mixed_clock_nonneg n M.sweepBf M.sweepHf M.inherited_bf_monotone M.inherited_hf_monotone as ho
  have hKm:=native_continuum_mixed_clock_monotone n M.sweepBf M.sweepHf M.inherited_bf_monotone M.inherited_hf_monotone as ho
  have hterminal : K as.length ≤ Temp+2*Cf:=by
    apply (native_continuum_mixed_clock_terminal_le n M.sweepBf M.sweepHf M.inherited_bf_monotone
      M.inherited_hf_monotone as ho).trans
    have HH:=HS 1 (by norm_num)
    have HF:=mul_le_mul_of_nonneg_left (show M.xs+1 ≤ 2 by linarith) hCf
    linarith
  have HH:=scalar_boundary_hessian_uniform_bounds ho (relocatedClock U 0 K)
    (relocatedClock_monotone U (by norm_num : (0:ℝ)∈Icc 0 1) hKm hK)
    (by simp [relocatedClock,show 0<U by omega])
    (B:=Temp+2*Cf) (by simpa [relocatedClock,not_lt.mpr hU] using hterminal)
  have hchi:=(Real.exp_pos (-4*(Temp+2*Cf))).trans_le HH.1
  have hp : 0 < K star:=(mul_pos hcK hW).trans_le hstarK
  refine ⟨mul_pos hchi hp,HH.2,?_⟩
  simpa only [mul_assoc] using mul_le_mul HH.1 hstarK (mul_pos hcK hW).le hchi.le

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 20000000

def nativeActualOriginalFourHigherTaylorError_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ) (W : ℝ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) : ℝ :=
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  (1/(chi*K star))*((W⁻¹)^st.generation*nativeActualOriginalFourOtherCategoryContrast_original_q M U st .higherTaylor)

theorem actual_minimum_four_higher_Taylor_error_abs_le_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp Cf : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hCf : 0 ≤ Cf) (HS : ActualOriginalQSmallSourceClocks M Temp Cf) (hxs : M.xs ≤ 1)
    {as : List PositiveMass} {i star U : ℕ}
    (st : NativeActualResourceState (Spin n×Bool) as i star)
    (ho : MassOrdered 0 as) (hs : star<U) (hU : U ≤ as.length)
    {W cK B : ℝ} (hW : 0 < W) (hcK : 0 < cK) (hB : 0 ≤ B)
    (hstarK : cK*W ≤ nativeContinuumMixedClock n M.sweepBf M.sweepHf as star)
    (H0 : |(W⁻¹)^st.generation*nativeActualOriginalFreshResourceTaylorRemainder_original_q M U st.term| ≤
      |st.term.coefficient| *W*B)
    (H1 : |(W⁻¹)^st.generation*nativeActualOriginalFreshResourceTaylorRemainder_original_q M U (st.term.retarget 0)| ≤
      |st.term.coefficient| *W*B) :
    |nativeActualOriginalFourHigherTaylorError_original_q M U W st| ≤
      |st.term.coefficient| *(2/(Real.exp (-4*(Temp+2*Cf))*cK))*B := by
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  let Cd:=Real.exp (-4*(Temp+2*Cf))*cK
  have hCd : 0 < Cd:=by dsimp only [Cd];positivity
  obtain ⟨hden,_,hdenlo⟩:=actual_minimum_four_denominator_bounds_of_small_source_clocks_original_q M
    hCf HS hxs hW hcK ho hs hU hstarK
  have hterm : 0 ≤ |st.term.coefficient| *W*B:=by positivity
  have Hdiff:=abs_sub_le
    ((W⁻¹)^st.generation*nativeActualOriginalFreshResourceTaylorRemainder_original_q M U st.term) 0
    ((1/2:ℝ)*((W⁻¹)^st.generation*nativeActualOriginalFreshResourceTaylorRemainder_original_q M U (st.term.retarget 0)))
  simp only [sub_zero,zero_sub,abs_neg] at Hdiff
  rw [abs_mul (1/2:ℝ),abs_of_pos (show (0:ℝ)<1/2 by norm_num)] at Hdiff
  have Hdiff' : |(W⁻¹)^st.generation*nativeActualOriginalFreshResourceTaylorRemainder_original_q M U st.term-
      (1/2:ℝ)*((W⁻¹)^st.generation*nativeActualOriginalFreshResourceTaylorRemainder_original_q M U (st.term.retarget 0))| ≤
      2*(|st.term.coefficient| *W*B):=by linarith
  unfold nativeActualOriginalFourHigherTaylorError_original_q
  rw [native_actual_four_higher_Taylor_contrast_eq_resources_original_q M U st ho,mul_sub]
  have Hring : (W⁻¹)^st.generation*((1/2:ℝ)*nativeActualOriginalFreshResourceTaylorRemainder_original_q M U (st.term.retarget 0))=
      (1/2:ℝ)*((W⁻¹)^st.generation*nativeActualOriginalFreshResourceTaylorRemainder_original_q M U (st.term.retarget 0)):=by ring
  rw [Hring,abs_mul,abs_of_pos (div_pos zero_lt_one hden)]
  apply (mul_le_mul_of_nonneg_left Hdiff' (div_nonneg zero_le_one hden.le)).trans
  have Hfrac : 1/(chi*K star) ≤ 1/(Cd*W):=div_le_div_of_nonneg_left zero_le_one (mul_pos hCd hW) hdenlo
  apply (mul_le_mul_of_nonneg_right Hfrac (by positivity)).trans_eq
  dsimp only [Cd]
  field_simp

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000

def nativeActualOriginalFreshResourceJointHighRestoration_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (kind : NativeJointHighRestorationKind) (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) : ℝ :=
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let Pc:=nativeOriginalCenteredRestTest n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C)
  let g:=nativeFreshAtSlot T 0 P.live.test.target star
  nativeJointHighRestorationSource kind n q U b h K C g.tree
    (fun σ=>Pc (g.restRestrict σ)) (g.embed P.live.test.target) g.mark

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 20000000

theorem native_actual_four_joint_HIGH_restoration_contrast_eq_resources_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (kind : NativeJointHighRestorationKind) (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) (ho : MassOrdered 0 as) :
    nativeActualOriginalFourOtherCategoryContrast_original_q M U st kind.category=
      -(nativeActualOriginalFreshResourceJointHighRestoration_original_q kind M U st.term-
        (1/2:ℝ)*nativeActualOriginalFreshResourceJointHighRestoration_original_q kind M U (st.term.retarget 0)) := by
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have HQ : cutFullVariance n q U 1 1 b h K=finitePhysicalCavitySquareVariance n U as b h 1 1:=
    native_full_endpoint_clock_mixed_independent n q U 1 b h K (finitePhysicalMixedClock (n+1) as b h)
  have Hread:=native_actual_centered_resource_fresh_rest_readout (U:=U) q b h K C st.tree st.term ho
  dsimp only at Hread
  rw [HQ] at Hread
  cases kind <;>
    unfold NativeJointHighRestorationKind.category nativeActualOriginalFourOtherCategoryContrast_original_q
      nativeActualOriginalOtherSourceCategory nativeActualOriginalFreshResourceJointHighRestoration_original_q
      nativeJointHighRestorationSource <;>
    dsimp only <;>
    rw [Hread] <;>
    dsimp only [b,h,K,C,q,NativeResourceTerm.retarget,NativeResourceMonomial.retarget,NativeGeneratedTest.retarget] <;>
    ring

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 20000000

def nativeActualOriginalFourJointHighRestorationError_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (kind : NativeJointHighRestorationKind) (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ) (W : ℝ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) : ℝ :=
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  (1/(chi*K star))*((W⁻¹)^st.generation*nativeActualOriginalFourOtherCategoryContrast_original_q M U st kind.category)

theorem actual_minimum_four_joint_HIGH_restoration_error_abs_le_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp Cf : ℝ}
    (kind : NativeJointHighRestorationKind) (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hCf : 0 ≤ Cf) (HS : ActualOriginalQSmallSourceClocks M Temp Cf) (hxs : M.xs ≤ 1)
    {as : List PositiveMass} {i star U : ℕ}
    (st : NativeActualResourceState (Spin n×Bool) as i star)
    (ho : MassOrdered 0 as) (hs : star<U) (hU : U ≤ as.length)
    {W cK B : ℝ} (hW : 0 < W) (hcK : 0 < cK) (hB : 0 ≤ B)
    (hstarK : cK*W ≤ nativeContinuumMixedClock n M.sweepBf M.sweepHf as star)
    (H0 : |(W⁻¹)^st.generation*nativeActualOriginalFreshResourceJointHighRestoration_original_q kind M U st.term| ≤
      |st.term.coefficient| *W*B)
    (H1 : |(W⁻¹)^st.generation*nativeActualOriginalFreshResourceJointHighRestoration_original_q kind M U (st.term.retarget 0)| ≤
      |st.term.coefficient| *W*B) :
    |nativeActualOriginalFourJointHighRestorationError_original_q kind M U W st| ≤
      |st.term.coefficient| *(2/(Real.exp (-4*(Temp+2*Cf))*cK))*B := by
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  let Cd:=Real.exp (-4*(Temp+2*Cf))*cK
  have hCd : 0 < Cd:=by dsimp only [Cd];positivity
  obtain ⟨hden,_,hdenlo⟩:=actual_minimum_four_denominator_bounds_of_small_source_clocks_original_q M
    hCf HS hxs hW hcK ho hs hU hstarK
  have hterm : 0 ≤ |st.term.coefficient| *W*B:=by positivity
  have Hdiff:=abs_sub_le
    ((W⁻¹)^st.generation*nativeActualOriginalFreshResourceJointHighRestoration_original_q kind M U st.term) 0
    ((1/2:ℝ)*((W⁻¹)^st.generation*nativeActualOriginalFreshResourceJointHighRestoration_original_q kind M U (st.term.retarget 0)))
  simp only [sub_zero,zero_sub,abs_neg] at Hdiff
  rw [abs_mul (1/2:ℝ),abs_of_pos (show (0:ℝ)<1/2 by norm_num)] at Hdiff
  have Hdiff' : |(W⁻¹)^st.generation*nativeActualOriginalFreshResourceJointHighRestoration_original_q kind M U st.term-
      (1/2:ℝ)*((W⁻¹)^st.generation*nativeActualOriginalFreshResourceJointHighRestoration_original_q kind M U (st.term.retarget 0))| ≤
      2*(|st.term.coefficient| *W*B):=by linarith
  unfold nativeActualOriginalFourJointHighRestorationError_original_q
  dsimp only
  rw [native_actual_four_joint_HIGH_restoration_contrast_eq_resources_original_q kind M U st ho,mul_neg,mul_neg,abs_neg,mul_sub]
  have Hring : (W⁻¹)^st.generation*((1/2:ℝ)*nativeActualOriginalFreshResourceJointHighRestoration_original_q kind M U (st.term.retarget 0))=
      (1/2:ℝ)*((W⁻¹)^st.generation*nativeActualOriginalFreshResourceJointHighRestoration_original_q kind M U (st.term.retarget 0)):=by ring
  rw [Hring,abs_mul,abs_of_pos (div_pos zero_lt_one hden)]
  apply (mul_le_mul_of_nonneg_left Hdiff' (div_nonneg zero_le_one hden.le)).trans
  have Hfrac : 1/(chi*K star) ≤ 1/(Cd*W):=div_le_div_of_nonneg_left zero_le_one (mul_pos hCd hW) hdenlo
  apply (mul_le_mul_of_nonneg_right Hfrac (by positivity)).trans_eq
  dsimp only [Cd]
  field_simp

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 22000000

def nativeActualOriginalFreshResourceLongitudinalRestoration_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) (right : Bool) : ℝ :=
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let Pc:=nativeOriginalCenteredRestTest n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C)
  let g:=nativeFreshAtSlot T 0 P.live.test.target star
  nativeOriginalLongitudinalRestoration n q U b h K C g.tree
    (fun σ=>Pc (g.restRestrict (g.tree.cavityAssignment σ).1))
    (if right then g.mark else g.embed P.live.test.target)

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000

def nativeActualOriginalFourLongitudinalError_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ) (W : ℝ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) (right : Bool) : ℝ :=
  (W⁻¹)^st.generation*(nativeActualOriginalFreshResourceLongitudinalRestoration_original_q M U st.term right-
    (1/2:ℝ)*nativeActualOriginalFreshResourceLongitudinalRestoration_original_q M U (st.term.retarget 0) right)

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 18000000

def nativeActualOriginalFourGaRestorationError_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ) (W : ℝ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) : ℝ :=
  -((M.sweepBf (partitionPoint 0 as star):ℝ)/nativeContinuumMixedClock n M.sweepBf M.sweepHf as star)*
    ((W⁻¹)^st.generation*nativeActualResourceGaRestoration_original_q M U st.term-
      (1/2:ℝ)*((W⁻¹)^st.generation*nativeActualResourceGaRestoration_original_q M U (st.term.retarget 0)))

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000

theorem actual_minimum_four_Ga_restoration_error_abs_le_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star U : ℕ}
    (st : NativeActualResourceState (Spin n×Bool) as i star)
    {W cK B Temp : ℝ} (hW : 0 < W) (hcK : 0 < cK) (hB : 0 ≤ B) (hTemp : 0 ≤ Temp)
    (hb : (M.sweepBf (partitionPoint 0 as star):ℝ) ≤ Temp)
    (hK : cK*W ≤ nativeContinuumMixedClock n M.sweepBf M.sweepHf as star)
    (H0 : |(W⁻¹)^st.generation*nativeActualResourceGaRestoration_original_q M U st.term| ≤
      |st.term.coefficient| *W*B)
    (H1 : |(W⁻¹)^st.generation*nativeActualResourceGaRestoration_original_q M U (st.term.retarget 0)| ≤
      |st.term.coefficient| *W*B) :
    |nativeActualOriginalFourGaRestorationError_original_q M U W st| ≤
      |st.term.coefficient| *(2*Temp/cK)*B := by
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as star
  have hK0 : 0 < K:=(mul_pos hcK hW).trans_le hK
  have hterm : 0 ≤ |st.term.coefficient| *W*B:=by positivity
  have Hdiff:=abs_sub_le
    ((W⁻¹)^st.generation*nativeActualResourceGaRestoration_original_q M U st.term) 0
    ((1/2:ℝ)*((W⁻¹)^st.generation*nativeActualResourceGaRestoration_original_q M U (st.term.retarget 0)))
  simp only [sub_zero,zero_sub,abs_neg] at Hdiff
  have Hdiff' : |(W⁻¹)^st.generation*nativeActualResourceGaRestoration_original_q M U st.term-
      (1/2:ℝ)*((W⁻¹)^st.generation*nativeActualResourceGaRestoration_original_q M U (st.term.retarget 0))| ≤
      2*(|st.term.coefficient| *W*B):=by
    rw [abs_mul (1/2:ℝ),abs_of_pos (show (0:ℝ) < 1/2 by norm_num)] at Hdiff
    linarith
  unfold nativeActualOriginalFourGaRestorationError_original_q
  rw [abs_mul,abs_neg,abs_of_nonneg (show 0 ≤ (M.sweepBf (partitionPoint 0 as star):ℝ)/K by positivity)]
  apply (mul_le_mul_of_nonneg_left Hdiff' (by positivity)).trans
  have Hfrac : (M.sweepBf (partitionPoint 0 as star):ℝ)/K ≤ Temp/(cK*W):=
    div_le_div₀ hTemp hb (mul_pos hcK hW) hK
  apply (mul_le_mul_of_nonneg_right Hfrac (by positivity)).trans_eq
  field_simp

theorem actual_minimum_four_Ga_restoration_forest_profile_le_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star U : ℕ} (ho : MassOrdered 0 as)
    (hs : star < U) (hU : U ≤ as.length)
    {Temp Cf W cK B : ℝ} (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    (HS : ActualOriginalQSmallSourceClocks M Temp Cf) (hxs : M.xs ≤ 1)
    (hW : 0 < W) (hcK : 0 < cK) (hB : 0 ≤ B)
    (hK : cK*W ≤ nativeContinuumMixedClock n M.sweepBf M.sweepHf as star)
    (depth : ℕ) (st : NativeActualResourceState (Spin n×Bool) as i star)
    {r : ℕ} (hr : st.tree.leaves ≤ r)
    (f2 R : ℕ→ℝ) (hf2 : ∀j,0 ≤ f2 j) (hR : ∀j,0 ≤ R j)
    (hf2lo : ∀j,j < U → f2 j=0) (hRlo : ∀j,j < U → R j=0)
    (Hrows : ∀Q∈nativeActualMinimumFourCenteredForest_original_q M hs hU W depth [st],
      |nativeActualOriginalFourGaRestorationError_original_q M U W Q| ≤
        |Q.term.coefficient| *B*(Q.tree.forkCost f2+edgeBudget 0 as f2+
          W*(Q.tree.forkCost R+edgeBudget 0 as R))) :
    ((nativeActualMinimumFourCenteredForest_original_q M hs hU W depth [st]).map
      (fun Q=>|nativeActualOriginalFourGaRestorationError_original_q M U W Q|)).sum ≤
      2*|st.term.coefficient| *B*
        nativeActualWeightedProfileFrontierCost nativeActualOriginalFourGCenteredBranches
          ((Temp+2*Cf)/(Real.exp (-4*(Temp+2*Cf))*cK)) 3 r depth*
        (st.tree.forkCost f2+edgeBudget 0 as f2+W*(st.tree.forkCost R+edgeBudget 0 as R)) := by
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let Γ:=nativeOriginalHighRowGamma (n:=n) (as:=as) U K
  let weight:=fun (Q : NativeActualResourceState (Spin n×Bool) as i star) tag=>
    nativeOriginalClockParentWeight W U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag)
  let rows:=nativeActualMinimumFourCenteredForest_original_q M hs hU W depth [st]
  let Cw:=(Temp+2*Cf)/(Real.exp (-4*(Temp+2*Cf))*cK)
  have hCw : 0 ≤ Cw:=by dsimp only [Cw];positivity
  have HW Q tag : |weight Q tag| ≤ Cw:=
    actual_continuum_four_G_weight_bound_of_small_source_clocks_original_q M hCf HS hxs hW hcK as ho hs hU hK Q tag
  have Hf:=nativeActualFourCenteredForest_wholeProfile_le ho Γ
    (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one ho U K Q p) hs (hs.le.trans hU) weight
    hCw HW depth [st] r (by intro Q hQ;obtain rfl:=List.mem_singleton.mp hQ;exact hr)
    f2 hf2 hf2lo
  have HR:=nativeActualFourCenteredForest_wholeProfile_le ho Γ
    (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one ho U K Q p) hs (hs.le.trans hU) weight
    hCw HW depth [st] r (by intro Q hQ;obtain rfl:=List.mem_singleton.mp hQ;exact hr)
    R hR hRlo
  have Hsum : (rows.map (fun Q=>|nativeActualOriginalFourGaRestorationError_original_q M U W Q|)).sum ≤
      B*((rows.map (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost f2+edgeBudget 0 as f2))).sum+
        W*(rows.map (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost R+edgeBudget 0 as R))).sum) := by
    apply (List.sum_le_sum Hrows).trans_eq
    simp only [←List.sum_map_mul_left,←List.sum_map_add]
    congr 1
    apply List.map_congr_left
    intro Q hQ
    ring
  have H:=mul_le_mul_of_nonneg_left (add_le_add Hf (mul_le_mul_of_nonneg_left HR hW.le)) hB
  apply Hsum.trans
  convert H using 1 <;> simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
    rows,nativeActualMinimumFourCenteredForest_original_q,Cw] <;> ring

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000

theorem actual_minimum_four_longitudinal_restoration_forest_profile_le_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star U : ℕ} (ho : MassOrdered 0 as)
    (hs : star < U) (hU : U ≤ as.length)
    {Temp Cf W cK B : ℝ} (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    (HS : ActualOriginalQSmallSourceClocks M Temp Cf) (hxs : M.xs ≤ 1)
    (hW : 0 < W) (hcK : 0 < cK) (hB : 0 ≤ B)
    (hK : cK*W ≤ nativeContinuumMixedClock n M.sweepBf M.sweepHf as star)
    (right : Bool) (depth : ℕ) (st : NativeActualResourceState (Spin n×Bool) as i star)
    {r : ℕ} (hr : st.tree.leaves ≤ r)
    (f2 R : ℕ→ℝ) (hf2 : ∀j,0 ≤ f2 j) (hR : ∀j,0 ≤ R j)
    (hf2lo : ∀j,j < U → f2 j=0) (hRlo : ∀j,j < U → R j=0)
    (Hrows : ∀Q∈nativeActualMinimumFourCenteredForest_original_q M hs hU W depth [st],
      |nativeActualOriginalFourLongitudinalError_original_q M U W Q right| ≤
        |Q.term.coefficient| *B*(Q.tree.forkCost f2+edgeBudget 0 as f2+
          W*(Q.tree.forkCost R+edgeBudget 0 as R))) :
    ((nativeActualMinimumFourCenteredForest_original_q M hs hU W depth [st]).map
      (fun Q=>|nativeActualOriginalFourLongitudinalError_original_q M U W Q right|)).sum ≤
      2*|st.term.coefficient| *B*
        nativeActualWeightedProfileFrontierCost nativeActualOriginalFourGCenteredBranches
          ((Temp+2*Cf)/(Real.exp (-4*(Temp+2*Cf))*cK)) 3 r depth*
        (st.tree.forkCost f2+edgeBudget 0 as f2+W*(st.tree.forkCost R+edgeBudget 0 as R)) := by
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let Γ:=nativeOriginalHighRowGamma (n:=n) (as:=as) U K
  let weight:=fun (Q : NativeActualResourceState (Spin n×Bool) as i star) tag=>
    nativeOriginalClockParentWeight W U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag)
  let rows:=nativeActualMinimumFourCenteredForest_original_q M hs hU W depth [st]
  let Cw:=(Temp+2*Cf)/(Real.exp (-4*(Temp+2*Cf))*cK)
  have hCw : 0 ≤ Cw:=by dsimp only [Cw];positivity
  have HW Q tag : |weight Q tag| ≤ Cw:=
    actual_continuum_four_G_weight_bound_of_small_source_clocks_original_q M hCf HS hxs hW hcK as ho hs hU hK Q tag
  have Hf:=nativeActualFourCenteredForest_wholeProfile_le ho Γ
    (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one ho U K Q p) hs (hs.le.trans hU) weight
    hCw HW depth [st] r (by intro Q hQ;obtain rfl:=List.mem_singleton.mp hQ;exact hr)
    f2 hf2 hf2lo
  have HR:=nativeActualFourCenteredForest_wholeProfile_le ho Γ
    (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one ho U K Q p) hs (hs.le.trans hU) weight
    hCw HW depth [st] r (by intro Q hQ;obtain rfl:=List.mem_singleton.mp hQ;exact hr)
    R hR hRlo
  have Hsum : (rows.map (fun Q=>|nativeActualOriginalFourLongitudinalError_original_q M U W Q right|)).sum ≤
      B*((rows.map (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost f2+edgeBudget 0 as f2))).sum+
        W*(rows.map (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost R+edgeBudget 0 as R))).sum) := by
    apply (List.sum_le_sum Hrows).trans_eq
    simp only [←List.sum_map_mul_left,←List.sum_map_add]
    congr 1
    apply List.map_congr_left
    intro Q hQ
    ring
  have H:=mul_le_mul_of_nonneg_left (add_le_add Hf (mul_le_mul_of_nonneg_left HR hW.le)) hB
  apply Hsum.trans
  convert H using 1 <;> simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
    rows,nativeActualMinimumFourCenteredForest_original_q,Cw] <;> ring

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000

def nativeActualResourceGammaSecondRestoration_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) (high : Bool) : ℝ :=
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let Pc:=nativeOriginalCenteredRestTest n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C)
  nativeGammaProjectedSecondRestoration high T P.live.test.target star U q b h K
    (restCenteredFixedForkKernel n b C star 0) Pc

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 20000000

theorem native_actual_four_gamma_restoration_contrast_eq_resources_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) (ho : MassOrdered 0 as) (high : Bool) :
    let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    nativeActualOriginalFourOtherCategoryContrast_original_q M U st (nativeActualGammaRestorationCategory high)=
      chi*(nativeActualResourceGammaSecondRestoration_original_q M U st.term high-
        (1/2:ℝ)*nativeActualResourceGammaSecondRestoration_original_q M U (st.term.retarget 0) high) := by
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have HQ : cutFullVariance n q U 1 1 b h K=finitePhysicalCavitySquareVariance n U as b h 1 1:=
    native_full_endpoint_clock_mixed_independent n q U 1 b h K (finitePhysicalMixedClock (n+1) as b h)
  have Hread:=native_actual_centered_resource_fresh_rest_readout (U:=U) q b h K C st.tree st.term ho
  dsimp only at Hread
  rw [HQ] at Hread
  dsimp only
  cases high <;>
    simp only [nativeActualGammaRestorationCategory,Bool.false_eq_true,ite_false,ite_true] <;>
    unfold nativeActualOriginalFourOtherCategoryContrast_original_q
      nativeActualOriginalOtherSourceCategory nativeActualResourceGammaSecondRestoration_original_q
       <;>
    simp only [nativeGammaProjectedSecondRestoration,Bool.false_eq_true,ite_false,ite_true] <;>
    rw [Hread] <;>
    dsimp only [b,h,K,C,q,NativeResourceTerm.retarget,NativeResourceMonomial.retarget,
      NativeGeneratedTest.retarget] <;>
    ring

def nativeActualOriginalFourGammaRestorationError_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ) (W : ℝ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) (high : Bool) : ℝ :=
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  (1/(chi*K star))*((W⁻¹)^st.generation*
    nativeActualOriginalFourOtherCategoryContrast_original_q M U st (nativeActualGammaRestorationCategory high))

theorem actual_minimum_four_gamma_restoration_error_abs_le_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp Cf : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hCf : 0 ≤ Cf) (HS : ActualOriginalQSmallSourceClocks M Temp Cf) (hxs : M.xs ≤ 1)
    {as : List PositiveMass} {i star U : ℕ}
    (st : NativeActualResourceState (Spin n×Bool) as i star)
    (ho : MassOrdered 0 as) (hs : star<U) (hU : U ≤ as.length) (high : Bool)
    {W cK B : ℝ} (hW : 0 < W) (hcK : 0 < cK) (hB : 0 ≤ B)
    (hstarK : cK*W ≤ nativeContinuumMixedClock n M.sweepBf M.sweepHf as star)
    (H0 : |(W⁻¹)^st.generation*nativeActualResourceGammaSecondRestoration_original_q M U st.term high| ≤
      |st.term.coefficient| *W*B)
    (H1 : |(W⁻¹)^st.generation*nativeActualResourceGammaSecondRestoration_original_q M U (st.term.retarget 0) high| ≤
      |st.term.coefficient| *W*B) :
    |nativeActualOriginalFourGammaRestorationError_original_q M U W st high| ≤
      |st.term.coefficient| *(2/(Real.exp (-4*(Temp+2*Cf))*cK))*B := by
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  let Cd:=Real.exp (-4*(Temp+2*Cf))*cK
  have hCd : 0 < Cd:=by dsimp only [Cd];positivity
  obtain ⟨hden,hchi1,hdenlo⟩:=actual_minimum_four_denominator_bounds_of_small_source_clocks_original_q M
    hCf HS hxs hW hcK ho hs hU hstarK
  have hKpos : 0 < K star:=(mul_pos hcK hW).trans_le hstarK
  have hchi0 : 0 ≤ chi:=by nlinarith
  have hchi : |chi|≤1:=by rw [abs_of_nonneg hchi0];exact hchi1
  have Hdiff : |(W⁻¹)^st.generation*nativeActualResourceGammaSecondRestoration_original_q M U st.term high-
      (1/2:ℝ)*((W⁻¹)^st.generation*nativeActualResourceGammaSecondRestoration_original_q M U (st.term.retarget 0) high)| ≤
      2*(|st.term.coefficient| *W*B) := by
    apply (abs_sub _ _).trans
    rw [abs_mul (1/2:ℝ),abs_of_pos (show (0:ℝ)<1/2 by norm_num)]
    nlinarith [show 0≤|st.term.coefficient| *W*B by positivity]
  have Hcat : |(W⁻¹)^st.generation*nativeActualOriginalFourOtherCategoryContrast_original_q M U st
      (nativeActualGammaRestorationCategory high)|≤2*(|st.term.coefficient| *W*B) := by
    rw [native_actual_four_gamma_restoration_contrast_eq_resources_original_q M U st ho high]
    have HE : (W⁻¹)^st.generation*(chi*(nativeActualResourceGammaSecondRestoration_original_q M U st.term high-
        (1/2:ℝ)*nativeActualResourceGammaSecondRestoration_original_q M U (st.term.retarget 0) high))=
        chi*((W⁻¹)^st.generation*nativeActualResourceGammaSecondRestoration_original_q M U st.term high-
          (1/2:ℝ)*((W⁻¹)^st.generation*nativeActualResourceGammaSecondRestoration_original_q M U (st.term.retarget 0) high)) := by ring
    rw [HE,abs_mul]
    exact (mul_le_mul hchi Hdiff (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  unfold nativeActualOriginalFourGammaRestorationError_original_q
  dsimp only
  rw [abs_mul,abs_of_pos (div_pos zero_lt_one hden)]
  apply (mul_le_mul_of_nonneg_left Hcat (div_nonneg zero_le_one hden.le)).trans
  have Hfrac : 1/(chi*K star) ≤ 1/(Cd*W):=div_le_div_of_nonneg_left zero_le_one (mul_pos hCd hW) hdenlo
  apply (mul_le_mul_of_nonneg_right Hfrac (by positivity)).trans_eq
  dsimp only [Cd]
  field_simp

end OAI.SKFluctuations.Cavity
