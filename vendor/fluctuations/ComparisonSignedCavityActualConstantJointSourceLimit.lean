module

public import ComparisonSignedCavityActualConstantJointRestoration
public import ComparisonSignedCavityOriginalInheritedConstantEndpoints

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators NNReal Topology
set_option maxHeartbeats 24000000

def nativeActualConstantJointStarSource
    (n : ℕ) (as : List PositiveMass) (star U : ℕ) (b h K S : ℕ→ℝ) : ℝ :=
  let T:=ClockTree.single (S:=Spin n×Bool) as
  let q:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let s:=singleSlot as
  let g:=nativeFreshAtSlot T 0 s star
  let qfull:=cutFullVariance n q U 1 1 b h K
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  let A:=fun σ τ : Spin n×Bool=>deletedOverlap n (joinSpin σ) (joinSpin τ)-S star
  chi*K star*
    (nativeRetainedLongitudinalPairing n q U b h K g.tree (fun _=>1) (g.embed s)+
     nativeRetainedLongitudinalPairing n q U b h K g.tree (fun _=>1) g.mark)+
  chi^2*b star*(finitePhysicalMean (n+1) as b h star-
    finitePhysicalMean (n+1) as b h star/(n+1:ℕ)-S star)+
  b star*(chi*nativeOriginalLongitudinalPairing n 0 qfull 0 U K b S g.tree
      (fun σ=>A (T.atSlot (g.restrict σ) s) (g.spin σ)) (g.embed s)+
    nativeOriginalFreshPartnerLResponse n 0 qfull 0 U K b S T s star
      (fun _ c d=>A c d))+
  nativeActualJointRestoredForwardTaylorError n q U b h K S g.tree (fun _=>1) (g.embed s) g.mark

theorem native_actual_constant_joint_source_eq_original_mean_gap
    (n : ℕ) (as : List PositiveMass) (star U : ℕ)
    (hs : star<U) (hU : U≤as.length) (ho : MassOrdered 0 as) (b h K S : ℕ→ℝ)
    (hKS : ∀j,K j=h j+b j*S j)
    (hb : ∀j,0≤b j) (hh : ∀j,0≤h j) (hK : ∀j,0≤K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    nativeActualConstantJointStarSource n as star U b h K S=
      finitePhysicalMean (n+1) as b h star-nativeOriginalScalarPairMean as K star :=
  (actual_original_constant_gap_eq_jointly_restored_star_responses n as star U hs hU ho b h K S
    hKS hb hh hK hbm hhm hKm).symm

theorem actual_inherited_joint_constant_source_tendsto_original_gap
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hTemp : 0<Temp) (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤Temp) (hroot : M.h 0=0)
    (us : List PositiveMass) (hus : ∀u∈us,u.val≤1) (u : PositiveMass) (hu : u∈us)
    (U : ℕ→ℕ)
    (hcut : ∀ᶠk : ℕ in atTop,retainedMassPrefixIndex u.val (finiteCutMasses us k)<U k ∧
      U k≤(finiteCutMasses us k).length) :
    Tendsto (fun k=>
      let as:=finiteCutMasses us k
      nativeActualConstantJointStarSource n as (retainedMassPrefixIndex u.val as) (U k)
        (fun j=>(M.bf (partitionPoint 0 as j):ℝ)) (fun j=>(M.hf (partitionPoint 0 as j):ℝ))
        (nativeContinuumMixedClock n M.bf M.hf as) (nativePhysicalResourceCenter n M.bf M.hf as))
      atTop (𝓝 (orderedPathS (n+1) M.bf M.hf u.val-
        scalarCovarianceResponse hTemp (M.inheritedScalarMassProfile hTemp htotal)
          (actualMixedClock (n+1) M.bf M.hf u.val))) := by
  apply (M.inherited_continuum_retained_scalar_mean_gap_tendsto hTemp htotal hroot us hus u hu).congr'
  filter_upwards [hcut] with k hk
  let as:=finiteCutMasses us k
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let S:=nativePhysicalResourceCenter n M.bf M.hf as
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus k
  have hKS : ∀j,K j=h j+b j*S j:=
    native_continuum_mixed_clock_eq_original_center n M.bf M.hf M.inherited_bf_monotone
      M.inherited_hf_monotone as ho
  have hb : ∀j,0≤b j:=fun j=>NNReal.coe_nonneg _
  have hh : ∀j,0≤h j:=fun j=>NNReal.coe_nonneg _
  have hbm : Monotone b:=by
    intro i j hij
    exact M.inherited_bf_monotone (partitionPoint_mem as ho i) (partitionPoint_mem as ho j)
      (partitionPoint_mono as ho hij)
  have hhm : Monotone h:=by
    intro i j hij
    exact M.inherited_hf_monotone (partitionPoint_mem as ho i) (partitionPoint_mem as ho j)
      (partitionPoint_mono as ho hij)
  have hK:=native_continuum_mixed_clock_nonneg n M.bf M.hf M.inherited_bf_monotone M.inherited_hf_monotone as ho
  have hKm:=native_continuum_mixed_clock_monotone n M.bf M.hf M.inherited_bf_monotone M.inherited_hf_monotone as ho
  exact (native_actual_constant_joint_source_eq_original_mean_gap n as
    (retainedMassPrefixIndex u.val as) (U k) hk.1 hk.2 ho b h K S hKS hb hh hK hbm hhm hKm).symm

end OAI.SKFluctuations.Cavity
