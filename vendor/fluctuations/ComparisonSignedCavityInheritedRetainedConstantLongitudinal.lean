module

public import ComparisonSignedCavityInheritedConstantLongitudinalRate
public import ComparisonSignedCavityActualInheritedClockMeanSaving
public import ComparisonSignedCavityContinuumMixedClock
public import ComparisonSignedCavityActualGLawRestoration

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000

theorem eventually_actual_shell_history_retained_constant_longitudinal_rate
    (rBound : ℕ) (Bclock Temp Cf Ccut : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c) :
    ∃C : ℝ,0 < C ∧∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (Tbase epsilon shell : ℝ) (ts : List ComparisonHistoryTerm),
        NativeActualSmallSourceClocks M Temp Cf →
        (∀u,M.b u=historyMatrixClock Tbase epsilon shell ts u) →
        (∀u,M.h u=historyFieldClock ts u) →
        (∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ Temp) → M.h 0=0 →
        M.xs^2 ≤ Cs*laplaceComparisonStrength M.context.d M.lam M.xs →
        M.canonicalDirectTestBandScale ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let W:=M.canonicalDirectTestBandScale
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock n M.bf M.hf as
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U ≤ as.length → T.leaves ≤ rBound →
        2*c*W ≤ partitionPoint 0 as U → partitionPoint 0 as U ≤ Ccut*W →
        (∀f : ℕ→ℝ,(∀j,j < U → f j=0) → T.forkCost f=0) →∀a : T.Slot,
          |nativeRetainedLongitudinalPairing n q U b h K T (fun _=>1) a| ≤
            (M.context.N^(-(1:ℝ)/3)+C*M.context.N^(-(actualMassSavingExponent m delta/256)))*M.xs^2 := by
  obtain ⟨C,hC,Hrest⟩:=eventually_actual_shell_history_constant_longitudinal_restoration_rate
    (D:=D) (Cs:=Cs) rBound Bclock Temp Cf Ccut hTemp hCf hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  have Hmean:=eventually_actual_inherited_original_clock_longitudinal_mean_saving
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) rBound Bclock Temp hTemp hm hC0
  refine ⟨C,hC,?_⟩
  filter_upwards [Hrest,Hmean] with n hnRest hnMean
  intro M Tbase epsilon shell ts hsource hb hh htotal hroot hsmall hW1 L us hus hret hmesh
  filter_upwards [hnRest M Tbase epsilon shell ts hsource hb hh hsmall hW1 L us hus hret hmesh,
    hnMean M htotal hroot us hus] with jGrid hgridRest hgridMean
  dsimp only at hgridRest hgridMean ⊢
  intro U T hU hT hcutlo hcutup hFork a
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=nativePhysicalResourceCenter n M.bf M.hf as
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have Hcenter : (fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j))=S:=by
    funext j
    exact native_ordered_source_center_eq_completed n M.bf M.hf
      M.inherited_bf_monotone M.inherited_hf_monotone (partitionPoint_mem as ho j)
  have HR:=hgridRest U T hU hT hcutlo hcutup hFork a
  change |nativeOriginalLongitudinalRestoration n q U b h K
    (fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)) T (fun _=>1) a| ≤ _ at HR
  rw [Hcenter] at HR
  have HM:=hgridMean K T U a hT
  have HM' : |nativeOriginalLongitudinalPairing n 0 (cutFullVariance n q U 1 1 b h K) 0 U K b S
      T (fun _=>1) a| ≤ M.context.N^(-(1:ℝ)/3)*M.xs^2:=by
    unfold nativeOriginalLongitudinalMean at HM
    have Hpath : cavityPath n U 1 1 q b h K=cutFullVariance n q U 1 1 b h K:=rfl
    change |((T.markedAttach 0).map (fun p=>p.coeff*
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*
        ((r.tree.markedAttach 0).map (fun z=>z.coeff*
          z.tree.disorderExpect (fullWeight n) (fullFeature n) 0 (cavityPath n U 1 1 q b h K)
            (nativeOriginalHighGAtom z.tree U K b S (z.embed (r.embed (p.embed a)))
              (z.embed (r.embed p.mark)) (z.embed r.mark) z.mark) 0)).sum)).sum)).sum| ≤ _ at HM
    rw [Hpath] at HM
    simpa only [nativeOriginalLongitudinalPairing,one_mul,NativeOverlapContext.N] using HM
  have hKS : ∀j,K j=h j+b j*S j:=native_continuum_mixed_clock_eq_original_center n M.bf M.hf
    M.inherited_bf_monotone M.inherited_hf_monotone as ho
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.bf u:ℝ) ≤ M.bf v from M.inherited_bf_monotone hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.hf u:ℝ) ≤ M.hf v from M.inherited_hf_monotone hu hv huv) as ho
  have hq0 : ∀j i,0 ≤ q j i:=by
    intro j i
    cases i <;> exact NNReal.coe_nonneg _
  have hqm : ∀i,Monotone (fun j=>q j i):=by
    intro i
    cases i <;> first | exact hbm | exact hhm
  have HK0:=native_continuum_mixed_clock_nonneg n M.bf M.hf M.inherited_bf_monotone M.inherited_hf_monotone as ho
  have HKm:=native_continuum_mixed_clock_monotone n M.bf M.hf M.inherited_bf_monotone M.inherited_hf_monotone as ho
  have Hlaw:=native_original_longitudinal_eq_retained_add_restoration n q U b h K S hKS
    T ho (fun _=>1) a hU hq0 hqm (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _)
    HK0 hbm hhm HKm
  have Hret : nativeRetainedLongitudinalPairing n q U b h K T (fun _=>1) a=
      nativeOriginalLongitudinalPairing n 0 (cutFullVariance n q U 1 1 b h K) 0 U K b S T (fun _=>1) a-
        nativeOriginalLongitudinalRestoration n q U b h K S T (fun _=>1) a:=by
    simpa only [add_sub_cancel_right] using congrArg (fun z=>z-nativeOriginalLongitudinalRestoration n q U b h K S T (fun _=>1) a) Hlaw.symm
  rw [Hret]
  exact (abs_sub _ _).trans (by nlinarith only [HM',HR])

end OAI.SKFluctuations.Cavity
