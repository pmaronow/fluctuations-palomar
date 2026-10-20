module

public import ComparisonSignedCavityOriginalCMarkedCanonicalSource
public import ComparisonSignedCavityLowFactorGMarkedSource
public import ComparisonSignedCavityLowFactorGInsertedRestSource
public import ComparisonSignedCavityInheritedGRestorationLowMoments
public import ComparisonSignedCavityInheritedConstantGRestoration
public import ComparisonSignedCavityGRestorationDiagonal
public import ComparisonSignedCavityInheritedConstantGWordRestoration
public import ComparisonSignedCavityInheritedConstantLongitudinalProfile
public import ComparisonSignedCavityConstantInheritedLowRestorationLedger
public import ComparisonSignedCavityInheritedBondedLowGRestoration
public import ComparisonSignedCavityInheritedBondedLowGPairRestoration
public import ComparisonSignedCavityInheritedFourGLowRestoration
public import ComparisonSignedCavityInheritedCTwoHighProfileProducer
public import ComparisonSignedCavityActualConstantHighTaylorProfile
public import ComparisonSignedCavityActualTargetThirdLowBudget
public import SKProof.Port.ComparisonActualOriginalQOriginalTargetB0
public import ComparisonNativeActualUniformBandL1Density

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 42000000
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

theorem original_thermal_intervalIntegrable_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    IntervalIntegrable (fun u=>orderedPathB (n+1) M.sweepBf M.sweepHf u-
      (orderedPathS (n+1) M.sweepBf M.sweepHf u)^2) volume 0 1 :=
  physicalOrderedThermal_intervalIntegrable n M.sweepBf M.sweepHf M.sweep_bf_monotone M.sweep_hf_monotone

theorem original_band_l1_density_on_all_final_nets_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    ∀ᶠjGrid in atTop,∀us : List PositiveMass,(∀u∈us,u.val≤1) →
      let as:=finiteCutMasses us jGrid
      ∀U V : ℕ,U≤V → V≤as.length → ClockTree.edgeBudget 0 as
        (fun j=>if j<U then 0 else if j<V then nativeOriginalCutLowErrorRadius n M.sweepBf M.sweepHf as j+1/(n+1:ℕ) else 0) ≤
        (∫u in partitionPoint 0 as U..partitionPoint 0 as V,Real.sqrt
          (orderedPathB (n+1) M.sweepBf M.sweepHf u-(orderedPathS (n+1) M.sweepBf M.sweepHf u)^2))+3/(n+1:ℕ) :=
  original_band_l1_density_on_all_final_nets n M.sweepBf M.sweepHf M.sweep_bf_monotone M.sweep_hf_monotone

namespace ActualNaturalBoundaryShape
variable {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
theorem nativeCMarkedLift_canonical_restProduct_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNaturalBoundaryShape n a T) (f : Fin a→NativeSourceFactorForm)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0) (σ : p.tree.cavityLeft.Assignment) :
    ((G.nativeCMarkedLift p hp).canonicalOriginalQSource M f).restProduct σ=
      (G.canonicalOriginalQSource M f).restProduct (p.restRestrict σ) := by
  simp only [restProduct,canonicalOriginalQSource,nativeCMarkedLift,sourceLowMass,
    (T.markedAttach_embed_preserves 0 p hp).2,p.restRestrict_at]

end ActualNaturalBoundaryShape

namespace ActualNaturalBoundaryShape
variable {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
theorem nativeCMarkedLift_canonical_product_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNaturalBoundaryShape n a T) (f : Fin a→NativeSourceFactorForm)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0) (σ : p.tree.Assignment) :
    ((G.nativeCMarkedLift p hp).canonicalOriginalQSource M f).product σ=
      (G.canonicalOriginalQSource M f).restProduct (p.restRestrict (p.tree.cavityAssignment σ).1) := by
  rw [product_eq_restProduct,nativeCMarkedLift_canonical_restProduct_original_q]

end ActualNaturalBoundaryShape

namespace ActualNaturalBoundaryShape
variable {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
theorem nativeCDoubleMarkedLift_canonical_product_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNaturalBoundaryShape n a T) (f : Fin a→NativeSourceFactorForm)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0) (σ : r.tree.Assignment) :
    (((G.nativeCMarkedLift p hp).nativeCMarkedLift r hr).canonicalOriginalQSource M f).product σ=
      (G.canonicalOriginalQSource M f).restProduct
        (p.restRestrict (r.restRestrict (r.tree.cavityAssignment σ).1)) := by
  rw [nativeCMarkedLift_canonical_product_original_q,nativeCMarkedLift_canonical_restProduct_original_q]

end ActualNaturalBoundaryShape

namespace ActualNaturalBoundaryShape
variable {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
theorem nativeC_inserted_canonical_low_test_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNaturalBoundaryShape n a T) (f : Fin a→NativeSourceFactorForm)
    (U : ℕ) (b S : ℕ→ℝ) (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
    (hlow : r.tree.splitIndex (r.embed p.mark) r.mark < U) :
    (fun σ=>insertedRestTest (G.canonicalOriginalQSource M f).restProduct
      (restCenteredLowKernel n U b S) p r (r.tree.cavityAssignment σ).1)=
      fun σ=>(((G.nativeCMarkedLift p hp).nativeCMarkedLift r hr).canonicalOriginalQSource M f).product σ*
        (b (r.tree.splitIndex (r.embed p.mark) r.mark)*
          (deletedOverlap n (joinSpin (r.tree.atSlot σ (r.embed p.mark)))
            (joinSpin (r.tree.atSlot σ r.mark))-S (r.tree.splitIndex (r.embed p.mark) r.mark))) := by
  funext σ
  rw [nativeCDoubleMarkedLift_canonical_product_original_q]
  simp only [insertedRestTest,restCenteredLowKernel,hlow,ite_true,
    ClockTree.MarkedPlacement.restSpin,r.restRestrict_at,r.tree.atSlot_cavityLeft]
  simp [deletedOverlap,joinSpin]

end ActualNaturalBoundaryShape

theorem ActualNaturalBoundaryShape.native_double_marked_low_pair_test_original_q
    {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (G : ActualNaturalBoundaryShape n a T)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (forms : Fin a→NativeSourceFactorForm) (b S : ℕ→ℝ) (u z : T.Slot)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0) :
    (fun σ=>(G.canonicalOriginalQSource M forms).restProduct
        (p.restRestrict (r.restRestrict (r.tree.cavityAssignment σ).1))*
      (b (T.splitIndex u z)*(deletedOverlap n
        (joinSpin (T.cavityLeft.atSlot (p.restRestrict (r.restRestrict (r.tree.cavityAssignment σ).1)) (T.cavityLeftSlot u),false))
        (joinSpin (T.cavityLeft.atSlot (p.restRestrict (r.restRestrict (r.tree.cavityAssignment σ).1)) (T.cavityLeftSlot z),false))-
          S (T.splitIndex u z))))=
    fun σ=>(((G.nativeCMarkedLift p hp).nativeCMarkedLift r hr).canonicalOriginalQSource M forms).product σ*
      (b (r.tree.splitIndex (r.embed (p.embed u)) (r.embed (p.embed z)))*
        (deletedOverlap n (joinSpin (r.tree.atSlot σ (r.embed (p.embed u))))
          (joinSpin (r.tree.atSlot σ (r.embed (p.embed z))))-
          S (r.tree.splitIndex (r.embed (p.embed u)) (r.embed (p.embed z))))) := by
  funext σ
  rw [G.nativeCDoubleMarkedLift_canonical_product_original_q M forms p hp r hr]
  rw [(p.tree.markedAttach_embed_preserves 0 r hr).2,(T.markedAttach_embed_preserves 0 p hp).2]
  simp only [p.restRestrict_at,r.restRestrict_at,r.tree.atSlot_cavityLeft]
  simp [deletedOverlap,joinSpin]

theorem actual_minimum_original_G_diagonal_restoration_zero_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (J : T.Assignment→ℝ) (a c e : T.Slot) :
    let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
    let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
    let K:=fun j=>h j+b j*S j
    let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    nativeActualLawRestorationRemainder n q U b h K T
      (fun σ=>J σ*nativeOriginalHighGAtom T U K b S a c e e σ)=0 := by
  dsimp only
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.sweepBf M.sweepHf
    (M.sweep_bf_monotone) (M.sweep_hf_monotone) (partitionPoint_mem as ho j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepBf u:ℝ)≤M.sweepBf v from M.sweep_bf_monotone hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepHf u:ℝ)≤M.sweepHf v from M.sweep_hf_monotone hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.sweepBf M.sweepHf
      (M.sweep_bf_monotone) (M.sweep_hf_monotone)) as ho
  have hK0 j : 0≤K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HS j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HS i).1 (NNReal.coe_nonneg _))
  exact native_actual_law_restoration_zero_test n _ U b h K T ho _
    (fun σ=>by simp only [nativeOriginalHighGAtom,ne_eq,not_true_eq_false,and_false,ite_false,mul_zero])
    (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
    (fun i=>by cases i <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm

theorem ActualNaturalBoundaryShape.native_inserted_canonical_low_rest_test_original_q
    {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (G : ActualNaturalBoundaryShape n a T)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (forms : Fin a→NativeSourceFactorForm) (U : ℕ) (b S : ℕ→ℝ)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
    (hlow : r.tree.splitIndex (r.embed p.mark) r.mark<U) :
    insertedRestTest (G.canonicalOriginalQSource M forms).restProduct (restCenteredLowKernel n U b S) p r=
      fun σ=>(((G.nativeCMarkedLift p hp).nativeCMarkedLift r hr).canonicalOriginalQSource M forms).restProduct σ*
        (b (r.tree.splitIndex (r.embed p.mark) r.mark)*(deletedOverlap n
          (joinSpin (r.tree.cavityLeft.atSlot σ (r.tree.cavityLeftSlot (r.embed p.mark)),false))
          (joinSpin (r.tree.cavityLeft.atSlot σ (r.tree.cavityLeftSlot r.mark),false))-
          S (r.tree.splitIndex (r.embed p.mark) r.mark))) := by
  funext σ
  rw [ActualNaturalBoundaryShape.nativeCMarkedLift_canonical_restProduct_original_q,
    ActualNaturalBoundaryShape.nativeCMarkedLift_canonical_restProduct_original_q]
  simp only [insertedRestTest,restCenteredLowKernel,hlow,ite_true,
    MarkedPlacement.restSpin,r.restRestrict_at]
  simp [deletedOverlap,joinSpin]

theorem eventually_actual_minimum_inherited_original_low_profile_fourth_original_q
    (Bclock Temp Cf Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cq : ℝ,0 < Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (l t s W : ℝ),U ≤ as.length →
          l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → s∈Icc (0:ℝ) 1 → M.xs ≤ W →
          partitionPoint 0 as U ≤ Ccut*W →
        ∀j,(ClockTree.pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0
          (cutFullVariance n q U l t b h K)
          (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U s b h K) j
            (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^4) 0 ≤ (Cq*W)^4 := by
  obtain ⟨Cq,hCq,HQ⟩:=eventually_actual_minimum_inherited_continuum_low_profile_moment_original_q
    (D:=D) 2 (by norm_num) Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cq*(1+Ccut),by positivity,?_⟩
  filter_upwards [HQ] with n hnQ
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hnQ M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U l t s W hU hl ht hs hxW hcut j
  have hxs0:=M.hxs.le
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  change (ClockTree.pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0
    (cutFullVariance n (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) U l t b h K)
    (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U s b h K) j
      (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^4) 0 ≤ _
  by_cases hj : j<U
  · have H:=hgrid U l t s hl ht hs j (by omega)
    have Hmass : partitionPoint 0 as j ≤ partitionPoint 0 as U:=partitionPoint_mono as ho (by omega)
    have Hscale : Cq*(M.xs+partitionPoint 0 as j) ≤ (Cq*(1+Ccut))*W:=by
      have HH:=mul_le_mul_of_nonneg_left (show M.xs+partitionPoint 0 as j ≤ (1+Ccut)*W by nlinarith) hCq.le
      nlinarith only [HH]
    exact H.trans (pow_le_pow_left₀ (by positivity [(partitionPoint_mem as ho j).1]) Hscale 4)
  · have HE (σ τ : Spin n×Bool) : ReplicaTree.coordinateProfile (fullFeature n)
        (cutLSlope n U s b h K) j σ τ=0:=scalarPhysicalSquareLowKernel_at_high n U b h K s hj σ τ
    simp_rw [HE,abs_zero,zero_pow (by norm_num : (4:ℕ)≠0)]
    simp only [ClockTree.disorderExpect,mul_zero,Finset.sum_const_zero]
    positivity

theorem actual_inherited_constant_G_high_restoration_bound_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp Cf : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hsource : ActualOriginalQSmallSourceClocks M Temp Cf) (hTemp : 0 ≤ Temp)
    (p : ℝ) (hp : 2 < p) (rBound : ℕ)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (U : ℕ)
    (T : ClockTree (Spin n×Bool) as) (t : ℝ)
    (hU : U ≤ as.length) (ht : t∈Icc (0:ℝ) 1) (hT : T.leaves ≤ rBound)
    (a c e f : T.Slot) (hef : e≠f) :
    let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
    let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
    let K:=fun j=>h j+b j*S j
    let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    let law:=cutFullVariance n q U 0 t b h K
    let high:=cutTSlope n U 0 b h K
    |cutMixedJet n q U b h K T (nativeOriginalHighGAtom T U K b S a c e f) 0 0 0 t| ≤
      |(1/2:ℝ)*fullScalarCutConnected4 T U K a c e f| *
        (ClockTree.pairForkVariation rBound*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*
          (nativeWholeLawErrorRadius n as law high (T.splitIndex e f))^(2/p)*
          nativeWholeLawProfileCost n law high T (2/p)) := by
  dsimp only
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let law:=cutFullVariance n q U 0 t b h K
  let high:=cutTSlope n U 0 b h K
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.sweepBf M.sweepHf
    (M.sweep_bf_monotone) (M.sweep_hf_monotone) (partitionPoint_mem as ho j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepBf u:ℝ) ≤ M.sweepBf v from M.sweep_bf_monotone hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepHf u:ℝ) ≤ M.sweepHf v from M.sweep_hf_monotone hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.sweepBf M.sweepHf (M.sweep_bf_monotone) (M.sweep_hf_monotone)) as ho
  have hK0 j : 0 ≤ K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HS j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HS i).1 (NNReal.coe_nonneg _))
  have Hb j : b j ≤ Temp:=
    (hsource _ (partitionPoint_mem as ho j)).1
  have HPmoment : T.disorderExpect (fullWeight n) (fullFeature n) 0 law
      (fun _=>|(1:ℝ)|^(2*(p/(p-2)))) 0 ≤ (1:ℝ)^(2*(p/(p-2))) := by
    simp only [abs_one,Real.one_rpow]
    exact (T.disorderExpect_one (fullWeight_pos n) (fullFeature n) ho 0 law 0).le
  have Hcap:=native_centered_high_kernel_abs_le n U b h S (fun _=>NNReal.coe_nonneg _) Hb HS
  have H:=native_original_G_profile_restoration_bound n U b h K S (fun _=>rfl)
    T ho hU hT law (fun _=>1) a c e f hef high (by norm_num : (0:ℝ) ≤ 1) hp
    (by positivity) (by positivity) HPmoment Hcap Hcap
  rw [native_cutMixedJet_zero_eq_profile n q U b h K T ho _ 0
    (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
    (fun i=>by cases i <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm (by norm_num) ht]
  simpa only [one_mul,mul_one] using H

theorem eventually_actual_minimum_inherited_constant_G_low_restoration_original_q
    (rBound : ℕ)
    (Bclock Temp Cf Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cq : ℝ,0 < Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l : ℝ),
          U ≤ as.length → l∈Icc (0:ℝ) 1 → T.leaves ≤ rBound →
        ∀W : ℝ,M.xs ≤ W → partitionPoint 0 as U ≤ Ccut*W →
        ∀a c e f : T.Slot,e≠f →
          let law:=cutFullVariance n q U l 1 b h K
          let high:=cutTSlope n U 0 b h K
          |cutLowJet n q U b h K T (nativeOriginalHighGAtom T U K b S a c e f) 0 1 l 1| ≤
            |(1/2:ℝ)*fullScalarCutConnected4 T U K a c e f| *
              (ClockTree.absJetVariation rBound 1*
                1*
                nativeWholeLawErrorRadius n as law high (T.splitIndex e f)*(Cq*W)) := by
  obtain ⟨Cq,hCq,HQ⟩:=eventually_actual_minimum_inherited_original_low_profile_fourth_original_q
    (D:=D) Bclock Temp Cf Ccut hTemp hCf hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cq,hCq,?_⟩
  filter_upwards [HQ] with n hnQ
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hnQ M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgridQ
  dsimp only at hgridQ ⊢
  intro U T l hU hl hT W hxW hcut a c e f hef
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let law:=cutFullVariance n q U l 1 b h K
  let high:=cutTSlope n U 0 b h K
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.sweepBf M.sweepHf
    (M.sweep_bf_monotone) (M.sweep_hf_monotone) (partitionPoint_mem as ho j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepBf u:ℝ) ≤ M.sweepBf v from M.sweep_bf_monotone hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepHf u:ℝ) ≤ M.sweepHf v from M.sweep_hf_monotone hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.sweepBf M.sweepHf (M.sweep_bf_monotone) (M.sweep_hf_monotone)) as ho
  have hK0 j : 0 ≤ K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HS j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HS i).1 (NNReal.coe_nonneg _))
  have HPmoment : T.disorderExpect (fullWeight n) (fullFeature n) 0 law
      (fun _=>|(1:ℝ)|^4) 0 ≤ (1:ℝ)^4 := by
    simp only [abs_one,one_pow]
    exact (T.disorderExpect_one (fullWeight_pos n) (fullFeature n) ho 0 law 0).le
  have HQmoment:=hgridQ U l 1 1 W hU hl (by norm_num) (by norm_num) hxW hcut
  have H:=native_original_G_raw_profile_restoration_bound n U b h K S (fun _=>rfl)
    T ho hU hT law (fun _=>1) a c e f hef (cutLSlope n U 1 b h K) (by norm_num : (0:ℝ) ≤ 1)
    (mul_pos hCq (M.hxs.trans_le hxW)) HPmoment HQmoment
  rw [cutLowJet_eq_profileJets n q U b h K T ho _ 0
    (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
    (fun i=>by cases i <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm 1 hl (by norm_num)]
  simpa only [List.replicate_one,one_mul,mul_one] using H

theorem actual_minimum_G_word_diagonal_restoration_zero_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (g : NativeOriginalGMarkedWord T) (U : ℕ) (P : T.Assignment→ℝ) (a : T.Slot)
    (hdiag : g.z.embed g.r.mark=g.z.mark) :
    let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
    let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
    let K:=fun j=>h j+b j*S j
    let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    nativeActualLawRestorationRemainder n q U b h K g.tree
      (g.originalRestorationTest U K b S P a)=0 := by
  dsimp only
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.sweepBf M.sweepHf
    (M.sweep_bf_monotone) (M.sweep_hf_monotone) (partitionPoint_mem as ho j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepBf u:ℝ) ≤ M.sweepBf v from M.sweep_bf_monotone hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepHf u:ℝ) ≤ M.sweepHf v from M.sweep_hf_monotone hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.sweepBf M.sweepHf (M.sweep_bf_monotone) (M.sweep_hf_monotone)) as ho
  have hK0 j : 0 ≤ K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HS j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HS i).1 (NNReal.coe_nonneg _))
  exact native_actual_law_restoration_zero_test n _ U b h K g.tree ho _
    (g.originalRestorationTest_diagonal_zero U K b S P a hdiag)
    (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
    (fun i=>by cases i <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm

theorem eventually_actual_minimum_inherited_constant_G_word_restoration_original_budget_original_q
    (rBound : ℕ)
    (p : ℝ) (hp : 2 < p)
    (Bclock Temp Cf Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cq : ℝ,0 < Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U ≤ as.length → T.leaves ≤ rBound →
        ∀W : ℝ,M.xs ≤ W → partitionPoint 0 as U ≤ Ccut*W →
        ∀(g : NativeOriginalGMarkedWord T) (a : T.Slot),
          |nativeActualLawRestorationRemainder n q U b h K g.tree
            (g.originalRestorationTest U K b S (fun _=>1) a)| ≤
            nativeOriginalGWordRestorationCost g U (rBound+3) M.sweepBf M.sweepHf K a Mclock Temp p
              1
              1 (Cq*W) := by
  obtain ⟨Cq,hCq,HL⟩:=eventually_actual_minimum_inherited_constant_G_low_restoration_original_q
    (D:=D) (rBound+3) Bclock Temp Cf Ccut hTemp hCf hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cq,hCq,?_⟩
  filter_upwards [HL] with n hnL
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hnL M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgridL
  dsimp only at hgridL ⊢
  intro U T hU hT W hxW hcut g a
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let Mclock:=4*Cf+2*Temp
  let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as Mclock Temp
  let j:=g.tree.splitIndex (g.z.embed g.r.mark) g.z.mark
  let κ:=|(1/2:ℝ)*fullScalarCutConnected4 g.tree U K
    (g.z.embed (g.r.embed (g.p.embed a))) (g.z.embed (g.r.embed g.p.mark))
    (g.z.embed g.r.mark) g.z.mark|
  let CH : ℝ:=1
  let CL : ℝ:=1
  let BH:=κ*(ClockTree.pairForkVariation (rBound+3)*CH*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*
    (R j)^(2/p)*(g.tree.forkCost (fun j=>(R j)^(2/p))+ClockTree.edgeBudget 0 as (fun j=>(R j)^(2/p))))
  let BL:=κ*(ClockTree.absJetVariation (rBound+3) 1*CL*R j*(Cq*W))
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  by_cases hdiag : g.z.embed g.r.mark=g.z.mark
  · rw [nativeOriginalGWordRestorationCost,ite_eq_left hdiag,
      actual_minimum_G_word_diagonal_restoration_zero_original_q M T ho g U (fun _=>1) a hdiag,abs_zero]
  · have hCH : 0 ≤ CH:=by dsimp [CH];positivity
    have hCL : 0 ≤ CL:=by dsimp [CL];positivity
    have hκ : 0 ≤ κ:=abs_nonneg _
    have hW : 0 ≤ W := M.hxs.le.trans hxW
    have hPV := ClockTree.pairForkVariation_nonneg (rBound+3)
    have hAV := ClockTree.absJetVariation_nonneg (rBound+3) 1
    have hR (j : ℕ) : 0 ≤ R j:=by
      dsimp only [R,nativeOriginalHighErrorEnvelope]
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg Mclock hTemp)
          (add_nonneg (Real.sqrt_nonneg _) (by positivity))
    have hH (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
        |cutMixedJet n q U b h K g.tree
          (g.originalRestorationTest U K b S (fun _=>1) a) 0 0 0 t| ≤ BH:=by
      have Htest : g.originalRestorationTest U K b S (fun _=>1) a=
          nativeOriginalHighGAtom g.tree U K b S
            (g.z.embed (g.r.embed (g.p.embed a))) (g.z.embed (g.r.embed g.p.mark))
            (g.z.embed g.r.mark) g.z.mark := by
        funext σ
        simp only [NativeOriginalGMarkedWord.originalRestorationTest,one_mul]
      rw [Htest]
      have Hleaves : g.tree.leaves ≤ rBound+3:=g.leaves_le.trans (by omega)
      have H:=actual_inherited_constant_G_high_restoration_bound_original_q M hsource hTemp p hp (rBound+3)
        as ho U g.tree t hU ht Hleaves
        (g.z.embed (g.r.embed (g.p.embed a))) (g.z.embed (g.r.embed g.p.mark))
        (g.z.embed g.r.mark) g.z.mark hdiag
      dsimp only at H
      change _ ≤ κ*(pairForkVariation (rBound+3)*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*
        (nativeWholeLawErrorRadius n as (cutFullVariance n q U 0 t b h K) (cutTSlope n U 0 b h K) j)^(2/p)*
        nativeWholeLawProfileCost n (cutFullVariance n q U 0 t b h K) (cutTSlope n U 0 b h K) g.tree (2/p)) at H
      have HC : pairForkVariation (rBound+3)=pairForkVariation (rBound+3)*CH:=by simp only [CH,mul_one]
      rw [HC] at H
      apply H.trans
      have HR:=Real.rpow_le_rpow (nativeWholeLawErrorRadius_nonneg n as _ _ j)
        (actual_minimum_inherited_current_high_error_radius_le_original_original_q (l:=0) (t:=t) M Temp Cf hTemp hCf hsource hxs ho U
          (by norm_num) ht j (g.tree.splitIndex_le_clockLength _ _)) (show 0 ≤ 2/p by positivity)
      have HC:=actual_minimum_inherited_current_high_profile_le_original_original_q (l:=0) (t:=t) M Temp Cf hTemp hCf hsource hxs g.tree ho U
        (by norm_num) ht (show 0 ≤ 2/p by positivity)
      have hProf := native_whole_law_profile_cost_nonneg n ho
        (cutFullVariance n q U 0 t b h K) (cutTSlope n U 0 b h K) g.tree (2/p)
      have hRj := hR j
      dsimp only [BH]
      gcongr
    have hL (l : ℝ) (hl : l∈Icc (0:ℝ) 1) :
        |cutLowJet n q U b h K g.tree
          (g.originalRestorationTest U K b S (fun _=>1) a) 0 1 l 1| ≤ BL:=by
      have Htest : g.originalRestorationTest U K b S (fun _=>1) a=
          nativeOriginalHighGAtom g.tree U K b S
            (g.z.embed (g.r.embed (g.p.embed a))) (g.z.embed (g.r.embed g.p.mark))
            (g.z.embed g.r.mark) g.z.mark := by
        funext σ
        simp only [NativeOriginalGMarkedWord.originalRestorationTest,one_mul]
      rw [Htest]
      have Hleaves : g.tree.leaves ≤ rBound+3:=g.leaves_le.trans (by omega)
      have H:=hgridL U g.tree l hU hl Hleaves W hxW hcut
        (g.z.embed (g.r.embed (g.p.embed a))) (g.z.embed (g.r.embed g.p.mark))
        (g.z.embed g.r.mark) g.z.mark hdiag
      apply H.trans
      have HR:=actual_minimum_inherited_current_high_error_radius_le_original_original_q (l:=l) (t:=1) M Temp Cf hTemp hCf hsource hxs ho U
        hl (by norm_num) j (g.tree.splitIndex_le_clockLength _ _)
      dsimp only [BL]
      gcongr
    have H:=native_actual_law_restoration_abs_le n q U b h K g.tree
      (g.originalRestorationTest U K b S (fun _=>1) a) BH BL hH hL
    rw [nativeOriginalGWordRestorationCost,ite_eq_right hdiag]
    convert H using 1
    dsimp only [BH,BL,κ,CH,CL,R,j,Mclock,K,b,h,S,as]
    ring

theorem eventually_actual_minimum_inherited_constant_longitudinal_restoration_profile_original_q
    (rBound : ℕ) (p : ℝ) (hp : 2 < p)
    (Bclock Temp Cf Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cq : ℝ,0 < Cq ∧∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U ≤ as.length → T.leaves ≤ rBound →
        ∀W : ℝ,M.xs ≤ W → partitionPoint 0 as U ≤ Ccut*W →∀a : T.Slot,
          let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as Mclock Temp
          let f2:=fun j=>((R j)^(2/p))^2
          |nativeOriginalLongitudinalRestoration n q U b h K S T (fun _=>1) a| ≤
            (pairForkVariation (rBound+3)*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p))*
              nativeOriginalRestorationProfileVariation rBound*(T.forkCost f2+edgeBudget 0 as f2)+
            (absJetVariation (rBound+3) 1*(Cq*W))*forkVariation rBound 3*
              (T.forkCost R+edgeBudget 0 as R) := by
  obtain ⟨Cq,hCq,H⟩:=eventually_actual_minimum_inherited_constant_G_word_restoration_original_budget_original_q
    (D:=D) rBound p hp Bclock Temp Cf Ccut hTemp hCf hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cq,hCq,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U T hU hT W hxW hcut a
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  have Hsum : |nativeOriginalLongitudinalRestoration n
      (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) U b h K S T (fun _=>1) a| ≤
      ((nativeOriginalGMarkedWords T).map (fun g=>|g.coefficient| *
        nativeOriginalGWordRestorationCost g U (rBound+3) M.sweepBf M.sweepHf K a (4*Cf+2*Temp) Temp p 1 1 (Cq*W))).sum := by
    rw [native_original_longitudinal_restoration_eq_words]
    exact native_original_G_word_weighted_sum_abs_le T _ _
      (fun g _=>hgrid U T hU hT W hxW hcut g a)
  have Hwords:=native_original_G_word_restoration_sum_le_profiles T
    (finiteCutMasses_ordered us hus jGrid) U (rBound+3) rBound hT M.sweepBf M.sweepHf K a
    (4*Cf+2*Temp) Temp p 1 1 (Cq*W) hTemp (by norm_num) (by norm_num)
    (mul_nonneg hCq.le (M.hxs.le.trans hxW))
  exact Hsum.trans (by simpa only [mul_one] using Hwords)

theorem eventually_actual_minimum_inherited_constant_low_restoration_ledger_original_q
    (rBound : ℕ)
    (Bclock Temp Cf Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cq : ℝ,0 < Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U ≤ as.length → T.leaves ≤ rBound →
        ∀W : ℝ,M.xs ≤ W → partitionPoint 0 as U ≤ Ccut*W →
        ∀a z : T.Slot,T.splitIndex a z < U →
          |nativeCenteredLowGammaLowRestoration n q U b h K S T
            (fun _=>1) a z|≤
            4*(rBound:ℝ)*(rBound+1)*ClockTree.absJetVariation (rBound+2) 2*

              (actualLowErrorComparisonConstant Mclock Temp*
                (nativeOriginalCutLowErrorRadius n M.sweepBf M.sweepHf as (T.splitIndex a z)+1/(n+1:ℕ)))*
              (Cq*(1+Ccut)*W)^2 := by
  obtain ⟨Cq,hCq,HQ⟩:=eventually_actual_minimum_inherited_continuum_low_profile_moment_original_q
    (D:=D) 4 (by norm_num) Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cq,hCq,?_⟩
  filter_upwards [HQ] with n hnQ
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hnQ M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgridQ
  dsimp only at hgridQ ⊢
  intro U T hU hT W hxW hcut a z haz
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let Mclock:=4*Cf+2*Temp
  let C : ℝ:=1
  let rho:=Cq*(1+Ccut)*W
  let d:=actualLowErrorComparisonConstant Mclock Temp*
    (nativeOriginalCutLowErrorRadius n M.sweepBf M.sweepHf as (T.splitIndex a z)+1/(n+1:ℕ))
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.sweepBf M.sweepHf
    (M.sweep_bf_monotone) (M.sweep_hf_monotone) (partitionPoint_mem as ho j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepBf u:ℝ) ≤ M.sweepBf v from M.sweep_bf_monotone hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepHf u:ℝ) ≤ M.sweepHf v from M.sweep_hf_monotone hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.sweepBf M.sweepHf (M.sweep_bf_monotone) (M.sweep_hf_monotone)) as ho
  have hK0 j : 0 ≤ K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HS j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HS i).1 (NNReal.coe_nonneg _))
  have HM : 0 ≤ Mclock:=by dsimp [Mclock];positivity
  have HC : 0 ≤ C := by norm_num [C]
  have HW : 0 < W:=M.hxs.trans_le hxW
  have Hrho : 0 < rho:=by dsimp [rho];positivity
  have Hd : 0 ≤ d:=mul_nonneg (actualLowErrorComparisonConstant_nonneg Mclock hTemp)
    (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have Hclock j (_hj : j ≤ as.length) : |b j|≤Mclock∧|h j|≤Mclock∧|K j|≤Mclock := by
    have Hfield:=hsource _ (partitionPoint_mem as ho j)
    have Hh : h j ≤ 2*Cf := by
      have H:=mul_le_mul_of_nonneg_left
        (show M.xs+partitionPoint 0 as j ≤ 2 by linarith [(partitionPoint_mem as ho j).2]) hCf
      exact Hfield.2.trans (by linarith only [H])
    have HK : K j ≤ 2*Cf+Temp := by
      have H:=mul_le_mul_of_nonneg_left (HS j).2 (NNReal.coe_nonneg (M.sweepBf (partitionPoint 0 as j)))
      dsimp only [K]
      linarith [Hfield.1]
    rw [abs_of_nonneg (NNReal.coe_nonneg _),abs_of_nonneg (NNReal.coe_nonneg _),abs_of_nonneg (hK0 j)]
    dsimp only [Mclock]
    exact ⟨by linarith [Hfield.1],by linarith,by linarith⟩
  have HQmoment l (hl : l∈Icc (0:ℝ) 1) j (hj : j ≤ as.length) : (ClockTree.pairClock as j).disorderExpect
      (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l 1 b h K)
      (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U 1 b h K) j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^8) 0 ≤ rho^8 := by
    by_cases hju : j < U
    · have Hraw:=hgridQ U l 1 1 hl (by norm_num) (by norm_num) j hj
      apply Hraw.trans
      apply pow_le_pow_left₀ (mul_nonneg hCq.le (add_nonneg M.hxs.le (partitionPoint_mem as ho j).1))
      dsimp only [rho]
      have Hmass:=partitionPoint_mono as ho hju.le
      have Hscale : M.xs+partitionPoint 0 as j ≤ (1+Ccut)*W := by nlinarith only [hxW,hcut,Hmass]
      exact (mul_le_mul_of_nonneg_left Hscale hCq.le).trans_eq (by ring)
    · have HE : (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U 1 b h K) j
          (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^8)=fun _=>0 := by
        funext σ
        simp only [ReplicaTree.coordinateProfile,cutLSlope,hju,ite_false,Pi.zero_apply,
          zero_mul,Finset.sum_const_zero,abs_zero,zero_pow (by norm_num : (8:ℕ)≠0)]
      rw [HE]
      simp only [ClockTree.disorderExpect,mul_zero,Finset.sum_const_zero]
      exact pow_nonneg Hrho.le _
  have HE := native_centered_low_gamma_low_restoration_wholeLaw_bound n U q b h S T ho hT
    (fun _=>1) a z hU haz HC Hrho HM Hd
    (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
    (fun i=>by cases i <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm
    (by
      intro l hl
      have H:=T.disorderExpect_one (fullWeight_pos n) (fullFeature n) ho 0
        (cutFullVariance n q U l 1 b h K) 0
      simpa only [abs_one,one_pow,C] using H.le) Hclock (by
      intro l hl
      have H:=actual_minimum_inherited_current_low_error_radius_le_original_original_q M Temp Cf hTemp hCf hsource hxs
        ho U hl (show (1:ℝ)∈Icc 0 1 by norm_num) _ (T.splitIndex_le_clockLength a z)
      dsimp only at H
      simp only [haz,ite_true] at H
      exact H) HQmoment
  simpa only [C,mul_one] using HE

theorem eventually_actual_minimum_inherited_low_factor_G_restoration_original_q
    (aDegree dOrder rBound : ℕ) (hd : 0<dOrder)
    (p : ℝ) (hp : 2<p) (hOrder : p/(p-2)≤(dOrder:ℝ))
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0<delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct) :
    ∃Ch Cl Cq : ℝ,0<Ch ∧ 0<Cl ∧ 0<Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U≤as.length → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (W : ℝ),M.xs≤W →
          partitionPoint 0 as U≤Ccut*W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale M.xs W initial e) →
        ∀u z a c e f : T.Slot,u≠z → T.splitIndex u z<U → e≠f →
          let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as Mclock Temp
          let CH:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Ch^(aDegree+1)*
            (W*sourceMonomialScale M.xs W initial)
          let CL:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cl^(aDegree+1)*
            (W*sourceMonomialScale M.xs W initial)
          let J:=fun σ=>(G.canonicalOriginalQSource M forms).product σ*
            (b (T.splitIndex u z)*(deletedOverlap n (joinSpin (T.atSlot σ u))
              (joinSpin (T.atSlot σ z))-S (T.splitIndex u z)))
          |nativeActualLawRestorationRemainder n q U b h K T
            (fun σ=>J σ*nativeOriginalHighGAtom T U K b S a c e f σ)|≤
            |(1/2:ℝ)*fullScalarCutConnected4 T U K a c e f| *
              (ClockTree.pairForkVariation rBound*CH*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*
                (R (T.splitIndex e f))^(2/p)*
                (T.forkCost (fun j=>(R j)^(2/p))+ClockTree.edgeBudget 0 as (fun j=>(R j)^(2/p)))+
                ClockTree.absJetVariation rBound 1*CL*R (T.splitIndex e f)*(Cq*(1+Ccut)*W)) := by
  obtain ⟨Ch,hCh,HH⟩:=eventually_actual_minimum_inherited_low_factor_G_high_profile_original_q
    (D:=D) aDegree dOrder rBound hd p hp hOrder Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cl,Cq,hCl,hCq,HL⟩:=eventually_actual_minimum_inherited_low_factor_G_low_profile_original_q
    (D:=D) aDegree rBound Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Ch,Cl,Cq,hCh,hCl,hCq,?_⟩
  filter_upwards [HH,HL] with n hnH hnL
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hnH M hs0 hsxs hsource hxs L us hus hret hmesh,
    hnL M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgridH hgridL
  dsimp only at hgridH hgridL ⊢
  intro U T hU hT G forms initial W hxW hcut hmass u z a c e f huz huzcut hef
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let Mclock:=4*Cf+2*Temp
  let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as Mclock Temp
  let CH:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Ch^(aDegree+1)*
    (W*sourceMonomialScale M.xs W initial)
  let CL:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cl^(aDegree+1)*
    (W*sourceMonomialScale M.xs W initial)
  let J:=fun σ=>(G.canonicalOriginalQSource M forms).product σ*
    (b (T.splitIndex u z)*(deletedOverlap n (joinSpin (T.atSlot σ u))
      (joinSpin (T.atSlot σ z))-S (T.splitIndex u z)))
  let κ:=|(1/2:ℝ)*fullScalarCutConnected4 T U K a c e f|
  let BH:=κ*(ClockTree.pairForkVariation rBound*CH*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*
    (R (T.splitIndex e f))^(2/p)*
    (T.forkCost (fun j=>(R j)^(2/p))+ClockTree.edgeBudget 0 as (fun j=>(R j)^(2/p))))
  let BL:=κ*(ClockTree.absJetVariation rBound 1*CL*R (T.splitIndex e f)*(Cq*(1+Ccut)*W))
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.sweepBf M.sweepHf
    (M.sweep_bf_monotone) (M.sweep_hf_monotone) (partitionPoint_mem as ho j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepBf u:ℝ)≤M.sweepBf v from M.sweep_bf_monotone hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepHf u:ℝ)≤M.sweepHf v from M.sweep_hf_monotone hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.sweepBf M.sweepHf
      (M.sweep_bf_monotone) (M.sweep_hf_monotone)) as ho
  have hK0 j : 0≤K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HS j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HS i).1 (NNReal.coe_nonneg _))
  have hW : 0≤W:=M.hxs.le.trans hxW
  have hscale : 0 ≤ sourceMonomialScale M.xs W initial:=by
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun i _=>(source_factor_scale_pos M.hxs (M.hxs.trans_le hxW) initial i).le
  have hCH : 0≤CH:=by dsimp [CH];positivity
  have hCL : 0≤CL:=by dsimp [CL];positivity
  have hR j : 0≤R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg Mclock hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hH (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
      |cutMixedJet n q U b h K T (fun σ=>J σ*nativeOriginalHighGAtom T U K b S a c e f σ) 0 0 0 t|≤BH:=by
    rw [native_cutMixedJet_zero_eq_profile n q U b h K T ho _ 0
      (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
      (fun i=>by cases i <;> first | exact hbm | exact hhm)
      (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm (by norm_num) ht]
    have H:=hgridH U T 0 t hU (by norm_num) ht hT G forms initial W hxW hcut hmass u z a c e f huz huzcut hef
    apply H.trans
    have HR:=Real.rpow_le_rpow (nativeWholeLawErrorRadius_nonneg n as _ _ (T.splitIndex e f))
      (actual_minimum_inherited_current_high_error_radius_le_original_original_q (l:=0) (t:=t) M Temp Cf hTemp hCf hsource hxs ho U
        (by norm_num) ht (T.splitIndex e f) (T.splitIndex_le_clockLength e f)) (show 0≤2/p by positivity)
    have HC:=actual_minimum_inherited_current_high_profile_le_original_original_q (l:=0) (t:=t) M Temp Cf hTemp hCf hsource hxs T ho U
      (by norm_num) ht (show 0≤2/p by positivity)
    have Hprof:=native_whole_law_profile_cost_nonneg n ho
      (cutFullVariance n q U 0 t b h K) (cutTSlope n U 0 b h K) T (2/p)
    have Hpv:=ClockTree.pairForkVariation_nonneg rBound
    have HRj:=hR (T.splitIndex e f)
    dsimp only [BH,κ]
    gcongr
  have hL (l : ℝ) (hl : l∈Icc (0:ℝ) 1) :
      |cutLowJet n q U b h K T (fun σ=>J σ*nativeOriginalHighGAtom T U K b S a c e f σ) 0 1 l 1|≤BL:=by
    rw [cutLowJet_eq_profileJets n q U b h K T ho _ 0
      (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
      (fun i=>by cases i <;> first | exact hbm | exact hhm)
      (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm 1 hl (by norm_num)]
    simp only [List.replicate_one]
    have H:=hgridL U T l 1 hU hl (by norm_num) hT G forms initial W hxW hcut hmass u z a c e f huz huzcut hef
    apply H.trans
    have HR:=actual_minimum_inherited_current_high_error_radius_le_original_original_q (l:=l) (t:=1) M Temp Cf hTemp hCf hsource hxs ho U
      hl (by norm_num) (T.splitIndex e f) (T.splitIndex_le_clockLength e f)
    have Hav:=ClockTree.absJetVariation_nonneg rBound 1
    have HRj:=hR (T.splitIndex e f)
    dsimp only [BL,κ]
    gcongr
  have H:=native_actual_law_restoration_abs_le n q U b h K T
    (fun σ=>J σ*nativeOriginalHighGAtom T U K b S a c e f σ) BH BL hH hL
  convert H using 1
  dsimp only [BH,BL,κ,CH,CL,R,J,Mclock,K,b,h,S,q,as]
  ring

theorem eventually_actual_minimum_inherited_low_factor_G_pair_restoration_original_q
    (aDegree dOrder rBound : ℕ) (hd : 0<dOrder)
    (p : ℝ) (hp : 2<p) (hOrder : p/(p-2)≤(dOrder:ℝ))
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0<delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct) :
    ∃Ch Cl Cq : ℝ,0<Ch ∧ 0<Cl ∧ 0<Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U≤as.length → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (W : ℝ),M.xs≤W →
          partitionPoint 0 as U≤Ccut*W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale M.xs W initial e) →
        ∀u z a c : T.Slot,u≠z → T.splitIndex u z<U →
          let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as Mclock Temp
          let f2:=fun j=>((R j)^(2/p))^2
          let CH:=Real.exp (wholeLawRowComparisonConstant (rBound+2)*Mclock)*Ch^(aDegree+1)*
            (W*sourceMonomialScale M.xs W initial)
          let CL:=Real.exp (wholeLawRowComparisonConstant (rBound+2)*Mclock)*Cl^(aDegree+1)*
            (W*sourceMonomialScale M.xs W initial)
          let AH:=pairForkVariation (rBound+2)*CH*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*((rBound:ℝ)+3)
          let AL:=absJetVariation (rBound+2) 1*CL*(Cq*(1+Ccut)*W)
          let J:=fun σ=>(G.canonicalOriginalQSource M forms).restProduct σ*
            (b (T.splitIndex u z)*(deletedOverlap n (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot u),false))
              (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot z),false))-S (T.splitIndex u z)))
          |nativeOriginalHighPairRestoration n q U b h K S T J a c|≤
            AH*pairForkVariation rBound*(T.forkCost f2+edgeBudget 0 as f2)+
              AL*pairForkVariation rBound*(T.forkCost R+edgeBudget 0 as R) := by
  obtain ⟨Ch,Cl,Cq,hCh,hCl,hCq,H⟩:=eventually_actual_minimum_inherited_low_factor_G_restoration_original_q
    (D:=D) aDegree dOrder (rBound+2) hd p hp hOrder Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Ch,Cl,Cq,hCh,hCl,hCq,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U T hU hT G forms initial W hxW hcut hmass u z a c huz huzcut
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let Mclock:=4*Cf+2*Temp
  let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as Mclock Temp
  let f2:=fun j=>((R j)^(2/p))^2
  let CH:=Real.exp (wholeLawRowComparisonConstant (rBound+2)*Mclock)*Ch^(aDegree+1)*
    (W*sourceMonomialScale M.xs W initial)
  let CL:=Real.exp (wholeLawRowComparisonConstant (rBound+2)*Mclock)*Cl^(aDegree+1)*
    (W*sourceMonomialScale M.xs W initial)
  let AH0:=pairForkVariation (rBound+2)*CH*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)
  let AH:=AH0*((rBound:ℝ)+3)
  let AL:=absJetVariation (rBound+2) 1*CL*(Cq*(1+Ccut)*W)
  let J:=fun σ=>(G.canonicalOriginalQSource M forms).restProduct σ*
    (b (T.splitIndex u z)*(deletedOverlap n (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot u),false))
      (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot z),false))-S (T.splitIndex u z)))
  let F:=fun (p : MarkedPlacement T) (r : MarkedPlacement p.tree)=>
    nativeActualLawRestorationRemainder n q U b h K r.tree
      (fun σ=>J (p.restRestrict (r.restRestrict (r.tree.cavityAssignment σ).1))*
        nativeOriginalHighGAtom r.tree U K b S (r.embed (p.embed a)) (r.embed (p.embed c))
          (r.embed p.mark) r.mark σ)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hscale : 0 ≤ sourceMonomialScale M.xs W initial:=by
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos M.hxs (M.hxs.trans_le hxW) initial e).le
  have hW : 0≤W:=M.hxs.le.trans hxW
  have hAH0 : 0≤AH0:=by
    dsimp only [AH0,CH]
    exact mul_nonneg (mul_nonneg (mul_nonneg (pairForkVariation_nonneg _) (by positivity))
      (Real.rpow_nonneg (by positivity) _)) (Real.rpow_nonneg (by positivity) _)
  have hAH : 0≤AH:=mul_nonneg hAH0 (by positivity)
  have hCL : 0≤CL:=by dsimp [CL];positivity
  have hAL : 0≤AL:=mul_nonneg (mul_nonneg (absJetVariation_nonneg _ _) hCL) (by positivity)
  have hR j : 0≤R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg Mclock hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hf2 j : 0≤f2 j:=sq_nonneg _
  have HF (p0 : MarkedPlacement T) (hp0 : p0∈T.markedAttach 0)
      (r : MarkedPlacement p0.tree) (hr : r∈p0.tree.markedAttach 0) :
      |F p0 r|≤AH*(r.tree.forkCost f2+edgeBudget 0 as f2)+AL*(r.tree.forkCost R+edgeBudget 0 as R) := by
    by_cases hdiag : r.embed p0.mark=r.mark
    · have Hzero:=actual_minimum_original_G_diagonal_restoration_zero_original_q M r.tree ho U
        (fun σ=>J (p0.restRestrict (r.restRestrict (r.tree.cavityAssignment σ).1)))
        (r.embed (p0.embed a)) (r.embed (p0.embed c)) r.mark
      dsimp only [F]
      rw [hdiag,Hzero,abs_zero]
      exact add_nonneg (mul_nonneg hAH (add_nonneg (r.tree.forkCost_nonneg hf2) (edgeBudget_nonneg ho hf2)))
        (mul_nonneg hAL (add_nonneg (r.tree.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)))
    · let Gr:=(G.nativeCMarkedLift p0 hp0).nativeCMarkedLift r hr
      have hGr e : Gr.sourceLowMass e≤Cmass*sourceFactorScale M.xs W initial e:=by
        simpa only [Gr,ActualNaturalBoundaryShape.nativeCMarkedLift_sourceLowMass] using hmass e
      have hleaf : r.tree.leaves≤rBound+2:=by
        have H1:=T.markedAttach_leaves 0 p0 hp0
        have H2:=p0.tree.markedAttach_leaves 0 r hr
        omega
      have hlow : r.tree.splitIndex (r.embed (p0.embed u)) (r.embed (p0.embed z))<U:=by
        rwa [(p0.tree.markedAttach_embed_preserves 0 r hr).2,(T.markedAttach_embed_preserves 0 p0 hp0).2]
      have hdistinct : r.embed (p0.embed u)≠r.embed (p0.embed z):=by
        intro HH
        exact huz ((T.markedAttach_embed_preserves 0 p0 hp0).1 ((p0.tree.markedAttach_embed_preserves 0 r hr).1 HH))
      have Hrest:=hgrid U r.tree hU hleaf Gr forms initial W hxW hcut hGr
        (r.embed (p0.embed u)) (r.embed (p0.embed z))
        (r.embed (p0.embed a)) (r.embed (p0.embed c)) (r.embed p0.mark) r.mark hdistinct hlow hdiag
      have Htest:=G.native_double_marked_low_pair_test_original_q M forms b S u z p0 hp0 r hr
      change |nativeActualLawRestorationRemainder n q U b h K r.tree _|≤_
      have Hleft:=congrArg (fun J0 : r.tree.Assignment→ℝ=>
        nativeActualLawRestorationRemainder n q U b h K r.tree
          (fun σ=>J0 σ*nativeOriginalHighGAtom r.tree U K b S (r.embed (p0.embed a))
            (r.embed (p0.embed c)) (r.embed p0.mark) r.mark σ)) Htest
      rw [Hleft]
      apply Hrest.trans
      let ff:=fun j=>(R j)^(2/p)
      have hff j : 0≤ff j:=Real.rpow_nonneg (hR j) _
      have HY:=native_distinct_pair_profile_product_le r.tree ho ff (r.embed p0.mark) r.mark hdiag
      have HS:=r.tree.split_le_forkCost hR (r.embed p0.mark) r.mark hdiag
      have HE:=edgeBudget_nonneg ho hR
      have HP:=add_nonneg (r.tree.forkCost_nonneg hf2) (edgeBudget_nonneg ho hf2)
      have hleafr : (r.tree.leaves:ℝ)+1≤(rBound:ℝ)+3:=by exact_mod_cast (by omega : r.tree.leaves+1≤rBound+3)
      have Hκ:=native_full_scalar_connected_four_abs_le_two r.tree ho U K
        (r.embed (p0.embed a)) (r.embed (p0.embed c)) (r.embed p0.mark) r.mark
      have Hκ' : |(1/2:ℝ)*fullScalarCutConnected4 r.tree U K
          (r.embed (p0.embed a)) (r.embed (p0.embed c)) (r.embed p0.mark) r.mark|≤1:=by
        rw [abs_mul]
        norm_num only [abs_of_nonneg (show (0:ℝ)≤1/2 by norm_num)]
        linarith
      have Hprod:=mul_le_mul_of_nonneg_left HY hAH0
      have Hleaf:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hleafr hAH0) HP
      have Hlow:=mul_le_mul_of_nonneg_left (HS.trans (le_add_of_nonneg_right HE)) hAL
      have Hnonneg : 0≤AH0*(ff (r.tree.splitIndex (r.embed p0.mark) r.mark)*
          (r.tree.forkCost ff+edgeBudget 0 as ff))+AL*R (r.tree.splitIndex (r.embed p0.mark) r.mark):=by
        exact add_nonneg (mul_nonneg hAH0 (mul_nonneg (hff _)
          (add_nonneg (r.tree.forkCost_nonneg hff) (edgeBudget_nonneg ho hff)))) (mul_nonneg hAL (hR _))
      have Hscalar:=mul_le_of_le_one_left Hnonneg Hκ'
      dsimp only [Gr,CH,CL,AH0,AH,AL,R,ff,f2,Mclock] at Hprod Hleaf Hlow Hscalar ⊢
      nlinarith only [Hprod,Hleaf,Hlow,Hscalar]
  have Hsum:=(T.signedPair_abs_le_pairAbsSum F).trans (T.pairAbsSum_mono HF)
  rw [T.pairAbsSum_add,T.pairAbsSum_const_mul AH,T.pairAbsSum_const_mul AL] at Hsum
  have HH:=T.pairAbsSum_forkBudget_le ho hT hf2 (d:=0) (by norm_num)
  have HL:=T.pairAbsSum_forkBudget_le ho hT hR (d:=0) (by norm_num)
  simp only [add_zero] at HH HL
  have HB:=add_le_add (mul_le_mul_of_nonneg_left HH hAH) (mul_le_mul_of_nonneg_left HL hAL)
  apply Hsum.trans
  convert HB using 1
  dsimp only [F,J,AH,AH0,AL,CH,CL,R,f2,q,b,h,K,S,Mclock,as,nativeOriginalHighPairRestoration]
  ring

theorem actual_minimum_original_zero_test_restoration_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (J : T.Assignment→ℝ) (hJ : ∀σ,J σ=0) :
    let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
    let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
    let K:=fun j=>h j+b j*S j
    let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    nativeActualLawRestorationRemainder n q U b h K T
      J=0 := by
  dsimp only
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.sweepBf M.sweepHf
    M.sweep_bf_monotone M.sweep_hf_monotone (partitionPoint_mem as ho j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepBf u:ℝ)≤M.sweepBf v from M.sweep_bf_monotone hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepHf u:ℝ)≤M.sweepHf v from M.sweep_hf_monotone hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.sweepBf M.sweepHf
      M.sweep_bf_monotone M.sweep_hf_monotone) as ho
  have hK0 j : 0≤K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HS j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HS i).1 (NNReal.coe_nonneg _))
  exact native_actual_law_restoration_zero_test n _ U b h K T ho _
    hJ
    (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
    (fun i=>by cases i <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm

theorem actual_minimum_original_high_pair_restoration_zero_payload_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (P : T.cavityLeft.Assignment→ℝ) (hP : ∀σ,P σ=0) (a c : T.Slot) :
    let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
    let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
    let K:=fun j=>h j+b j*S j
    let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    nativeOriginalHighPairRestoration n q U b h K S T P a c=0 := by
  dsimp only
  unfold nativeOriginalHighPairRestoration
  apply List.sum_eq_zero
  intro y hy
  obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hy
  apply mul_eq_zero.mpr
  right
  apply List.sum_eq_zero
  intro y hy
  obtain ⟨r,hr,rfl⟩:=List.mem_map.mp hy
  rw [actual_minimum_original_zero_test_restoration_original_q M r.tree ho U _
    (fun σ=>by rw [hP,zero_mul])]
  exact mul_zero _

theorem eventually_actual_minimum_inherited_canonical_four_G_low_restoration_original_q
    (aDegree dOrder rBound : ℕ) (hd : 0<dOrder)
    (p : ℝ) (hp : 2<p) (hOrder : p/(p-2)≤(dOrder:ℝ))
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0<delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct) :
    ∃Ch Cl Cq : ℝ,0<Ch ∧ 0<Cl ∧ 0<Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U≤as.length → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (W : ℝ),M.xs≤W →
          partitionPoint 0 as U≤Ccut*W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale M.xs W initial e) →
        ∀a z : T.Slot,
          let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as Mclock Temp
          let f2:=fun j=>((R j)^(2/p))^2
          let CH:=Real.exp (wholeLawRowComparisonConstant (rBound+4)*Mclock)*Ch^(aDegree+1)*
            (W*sourceMonomialScale M.xs W initial)
          let CL:=Real.exp (wholeLawRowComparisonConstant (rBound+4)*Mclock)*Cl^(aDegree+1)*
            (W*sourceMonomialScale M.xs W initial)
          let AH:=pairForkVariation (rBound+4)*CH*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*((rBound:ℝ)+5)*pairForkVariation (rBound+2)
          let AL:=absJetVariation (rBound+4) 1*CL*(Cq*(1+Ccut)*W)*pairForkVariation (rBound+2)
          |nativeOriginalGKernelLowRestoration n q U b h K S T
            (G.canonicalOriginalQSource M forms).restProduct a z (restCenteredLowKernel n U b S)|≤
            2*AH*pairForkVariation rBound*(T.forkCost f2+edgeBudget 0 as f2)+
              2*AL*pairForkVariation rBound*(T.forkCost R+edgeBudget 0 as R) := by
  obtain ⟨Ch,Cl,Cq,hCh,hCl,hCq,H⟩:=eventually_actual_minimum_inherited_low_factor_G_pair_restoration_original_q
    (D:=D) aDegree dOrder (rBound+2) hd p hp hOrder Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Ch,Cl,Cq,hCh,hCl,hCq,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U T hU hT G forms initial W hxW hcut hmass a z
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let Mclock:=4*Cf+2*Temp
  let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as Mclock Temp
  let f2:=fun j=>((R j)^(2/p))^2
  let CH:=Real.exp (wholeLawRowComparisonConstant (rBound+4)*Mclock)*Ch^(aDegree+1)*
    (W*sourceMonomialScale M.xs W initial)
  let CL:=Real.exp (wholeLawRowComparisonConstant (rBound+4)*Mclock)*Cl^(aDegree+1)*
    (W*sourceMonomialScale M.xs W initial)
  let AH:=pairForkVariation (rBound+4)*CH*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*
    ((rBound:ℝ)+5)*pairForkVariation (rBound+2)
  let AL:=absJetVariation (rBound+4) 1*CL*(Cq*(1+Ccut)*W)*pairForkVariation (rBound+2)
  let P:=(G.canonicalOriginalQSource M forms).restProduct
  let A:=restCenteredLowKernel n U b S
  let F:=fun (p0 : MarkedPlacement T) (r : MarkedPlacement p0.tree)=>
    fullScalarCutGamma r.tree U K (r.embed (p0.embed z)) r.mark*
      nativeOriginalHighPairRestoration n q U b h K S r.tree (insertedRestTest P A p0 r)
        (r.embed (p0.embed a)) (r.embed p0.mark)+
    fullScalarCutGamma r.tree U K (r.embed (p0.embed z)) (r.embed p0.mark)*
      nativeOriginalHighPairRestoration n q U b h K S r.tree (insertedRestTest P A p0 r)
        (r.embed (p0.embed a)) r.mark+
    fullScalarCutGamma r.tree U K (r.embed (p0.embed a)) (r.embed p0.mark)*
      nativeOriginalHighPairRestoration n q U b h K S r.tree (insertedRestTest P A p0 r)
        (r.embed (p0.embed z)) r.mark+
    fullScalarCutGamma r.tree U K (r.embed (p0.embed a)) r.mark*
      nativeOriginalHighPairRestoration n q U b h K S r.tree (insertedRestTest P A p0 r)
        (r.embed (p0.embed z)) (r.embed p0.mark)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hW : 0≤W:=M.hxs.le.trans hxW
  have hscale : 0 ≤ sourceMonomialScale M.xs W initial:=by
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos M.hxs (M.hxs.trans_le hxW) initial e).le
  have hCH : 0≤CH:=by dsimp [CH];positivity
  have hCL : 0≤CL:=by dsimp [CL];positivity
  have hAH : 0≤AH:=by
    dsimp only [AH]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (pairForkVariation_nonneg _) hCH) (Real.rpow_nonneg (by positivity) _))
      (Real.rpow_nonneg (by positivity) _)) (by positivity)) (pairForkVariation_nonneg _)
  have hAL : 0≤AL:=mul_nonneg (mul_nonneg (mul_nonneg (absJetVariation_nonneg _ _) hCL)
    (by positivity)) (pairForkVariation_nonneg _)
  have hR j : 0≤R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg Mclock hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hf2 j : 0≤f2 j:=sq_nonneg _
  have HF (p0 : MarkedPlacement T) (hp0 : p0∈T.markedAttach 0)
      (r : MarkedPlacement p0.tree) (hr : r∈p0.tree.markedAttach 0) :
      |F p0 r|≤4*AH*(r.tree.forkCost f2+edgeBudget 0 as f2)+4*AL*(r.tree.forkCost R+edgeBudget 0 as R) := by
    let B:=AH*(r.tree.forkCost f2+edgeBudget 0 as f2)+AL*(r.tree.forkCost R+edgeBudget 0 as R)
    have hB : 0≤B:=add_nonneg (mul_nonneg hAH (add_nonneg (r.tree.forkCost_nonneg hf2) (edgeBudget_nonneg ho hf2)))
      (mul_nonneg hAL (add_nonneg (r.tree.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)))
    have Hpair (x y : r.tree.Slot) :
        |nativeOriginalHighPairRestoration n q U b h K S r.tree (insertedRestTest P A p0 r) x y|≤B:=by
      by_cases hlow : r.tree.splitIndex (r.embed p0.mark) r.mark<U
      · have hcd : r.embed p0.mark≠r.mark:=by
          intro HH
          rw [HH,r.tree.splitIndex_self] at hlow
          omega
        let Gr:=(G.nativeCMarkedLift p0 hp0).nativeCMarkedLift r hr
        have hGr e : Gr.sourceLowMass e≤Cmass*sourceFactorScale M.xs W initial e:=by
          simpa only [Gr,ActualNaturalBoundaryShape.nativeCMarkedLift_sourceLowMass] using hmass e
        have hleaf : r.tree.leaves≤rBound+2:=by
          have H1:=T.markedAttach_leaves 0 p0 hp0
          have H2:=p0.tree.markedAttach_leaves 0 r hr
          omega
        rw [show insertedRestTest P A p0 r=_ from G.native_inserted_canonical_low_rest_test_original_q M forms U b S p0 hp0 r hr hlow]
        have Hinner:=hgrid U r.tree hU hleaf Gr forms initial W hxW hcut hGr
          (r.embed p0.mark) r.mark x y hcd hlow
        convert Hinner using 1
        dsimp only [B,AH,AL,CH,CL,R,f2,Mclock,Gr]
        push_cast
        ring
      · have Hzero : ∀σ,insertedRestTest P A p0 r σ=0:=by
          intro σ
          simp only [insertedRestTest,A,restCenteredLowKernel,hlow,ite_false,mul_zero]
        rw [actual_minimum_original_high_pair_restoration_zero_payload_original_q M r.tree ho U _ Hzero x y,abs_zero]
        exact hB
    have Hterm (x y x' y' : r.tree.Slot) :
        |fullScalarCutGamma r.tree U K x y*
          nativeOriginalHighPairRestoration n q U b h K S r.tree (insertedRestTest P A p0 r) x' y'|≤B:=by
      rw [abs_mul]
      have Hgam:=native_full_scalar_cut_moment_abs_le_one r.tree ho U K [x,y]
      exact (mul_le_mul Hgam (Hpair x' y') (abs_nonneg _) zero_le_one).trans_eq (one_mul B)
    have H1:=Hterm (r.embed (p0.embed z)) r.mark (r.embed (p0.embed a)) (r.embed p0.mark)
    have H2:=Hterm (r.embed (p0.embed z)) (r.embed p0.mark) (r.embed (p0.embed a)) r.mark
    have H3:=Hterm (r.embed (p0.embed a)) (r.embed p0.mark) (r.embed (p0.embed z)) r.mark
    have H4:=Hterm (r.embed (p0.embed a)) r.mark (r.embed (p0.embed z)) (r.embed p0.mark)
    have Hsum : |F p0 r|≤4*B:=by
      dsimp only [F]
      exact ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
        (add_le_add ((abs_add_le _ _).trans (add_le_add H1 H2)) H3)) H4)).trans_eq (by ring)
    simpa only [B,mul_add,mul_assoc] using Hsum
  have Hsum:=(T.signedPair_abs_le_pairAbsSum F).trans (T.pairAbsSum_mono HF)
  rw [T.pairAbsSum_add,T.pairAbsSum_const_mul (4*AH),T.pairAbsSum_const_mul (4*AL)] at Hsum
  have HH:=T.pairAbsSum_forkBudget_le ho hT hf2 (d:=0) (by norm_num)
  have HL:=T.pairAbsSum_forkBudget_le ho hT hR (d:=0) (by norm_num)
  simp only [add_zero] at HH HL
  have HX:=Hsum.trans (add_le_add (mul_le_mul_of_nonneg_left HH (mul_nonneg (by norm_num) hAH))
    (mul_le_mul_of_nonneg_left HL (mul_nonneg (by norm_num) hAL)))
  change |_/2|≤_
  rw [abs_div,show |(2:ℝ)|=2 by norm_num]
  change |((T.markedAttach 0).map (fun p0=>p0.coeff*
    ((p0.tree.markedAttach 0).map (fun r=>r.coeff*F p0 r)).sum)).sum|/2≤_
  dsimp only [AH,AL,CH,CL,R,f2,q,b,h,K,S,Mclock,as] at HX ⊢
  nlinarith only [HX]

theorem eventually_actual_minimum_inherited_canonical_C_two_high_profile_budget_original_q
    (aDegree dOrder rBound : ℕ) (hd : 0 < dOrder)
    (pexp : ℝ) (hpExp : 2 < pexp) (hOrder : pexp/(pexp-2) ≤ (dOrder:ℝ))
    (Bclock Temp Cf Cmass : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cp : ℝ,0 < Cp ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1→
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1)→(∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹ ≤ M.xs→
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U ≤ as.length→T.leaves ≤ rBound→
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (W : ℝ),M.xs ≤ W→partitionPoint 0 as U ≤ Cmass*W→
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale M.xs W initial e)→
        ∀a z : T.Slot,T.splitIndex a z < U→
          let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as Mclock Temp
          let f:=fun j=>(R j)^(4/pexp)
          |nativeCenteredLowGammaHighSecondRemainder n q U b h K S T
            (G.canonicalOriginalQSource M forms).restProduct a z| ≤
            pairForkVariation (rBound+2)*pairForkVariation (rBound+4)*
              (Real.exp (wholeLawRowComparisonConstant (rBound+2)*Mclock)*Cp^(aDegree+1)*
                (W*sourceMonomialScale M.xs W initial))*(2*Temp)^((pexp-2)/pexp)*(2*Temp)^((pexp-2)/pexp)*
              pairForkVariation rBound*(T.forkCost f+edgeBudget 0 as f) := by
  obtain ⟨Cp,hCp,H⟩:=eventually_actual_minimum_inherited_canonical_two_high_low_factor_original_q
    (D:=D) aDegree dOrder (rBound+2) hd pexp hpExp hOrder Bclock Temp Cf Cmass hTemp hCf hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,hCp,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs hsource hxs1 L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs1 L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U T hU hT G forms initial W hxW hcut hmass a z haz
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let Mclock:=4*Cf+2*Temp
  let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as Mclock Temp
  let f:=fun j=>(R j)^(4/pexp)
  let Phi:=pairForkVariation (rBound+2)*pairForkVariation (rBound+4)*
    (Real.exp (wholeLawRowComparisonConstant (rBound+2)*Mclock)*Cp^(aDegree+1)*
      (W*sourceMonomialScale M.xs W initial))*(2*Temp)^((pexp-2)/pexp)*(2*Temp)^((pexp-2)/pexp)
  let P:=(G.canonicalOriginalQSource M forms).restProduct
  let F:=fun (p : MarkedPlacement T) (r : MarkedPlacement p.tree)=>
    nativeLowScalarPairing r.tree U K (r.embed (p.embed a)) (r.embed (p.embed z)) (r.embed p.mark) r.mark*
      (∫t in (0:ℝ)..1,(1-t)*cutFrozenLowHighJet n q U b h K r.tree
        (fun σ=>insertedRestTest P (restCenteredLowKernel n U b S) p r (r.tree.cavityAssignment σ).1) 0 0 2 t)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hW : 0 ≤ W:=M.hxs.le.trans hxW
  have hscale : 0 ≤ sourceMonomialScale M.xs W initial := by
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos M.hxs (M.hxs.trans_le hxW) initial e).le
  have hPhi : 0 ≤ Phi := by
    dsimp only [Phi]
    exact mul_nonneg (mul_nonneg
      (mul_nonneg (mul_nonneg (pairForkVariation_nonneg _) (pairForkVariation_nonneg _)) (by positivity))
      (Real.rpow_nonneg (by positivity) _)) (Real.rpow_nonneg (by positivity) _)
  have hR j : 0 ≤ R j := by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg Mclock hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hf j : 0 ≤ f j:=Real.rpow_nonneg (hR j) _
  have HF (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
      (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0) :
      |F p r| ≤ 2*Phi*(r.tree.forkCost f+edgeBudget 0 as f) := by
    let Pi:=nativeLowScalarPairing r.tree U K (r.embed (p.embed a)) (r.embed (p.embed z)) (r.embed p.mark) r.mark
    have hProfile : 0 ≤ r.tree.forkCost f+edgeBudget 0 as f:=
      add_nonneg (r.tree.forkCost_nonneg hf) (edgeBudget_nonneg ho hf)
    by_cases hPi : Pi=0
    · change |Pi*_| ≤ _
      rw [hPi,zero_mul,abs_zero]
      exact mul_nonneg (mul_nonneg (by norm_num) hPhi) hProfile
    · have hold : r.tree.splitIndex (r.embed (p.embed a)) (r.embed (p.embed z))=T.splitIndex a z := by
        rw [(p.tree.markedAttach_embed_preserves 0 r hr).2,(T.markedAttach_embed_preserves 0 p hp).2]
      have hsplit : r.tree.splitIndex (r.embed p.mark) r.mark=T.splitIndex a z := by
        have H:=native_low_scalar_pairing_split_weight r.tree ho U K
          (fun j=>if j=T.splitIndex a z then (1:ℝ) else 0)
          (r.embed (p.embed a)) (r.embed (p.embed z)) (r.embed p.mark) r.mark hU (by rwa [hold])
        rw [hold,ite_eq_left rfl,one_mul] at H
        by_contra hne
        rw [ite_eq_right hne,zero_mul] at H
        exact hPi H.symm
      have hlow : r.tree.splitIndex (r.embed p.mark) r.mark < U:=by rwa [hsplit]
      have hcd : r.embed p.mark≠r.mark := by
        intro H
        rw [H,r.tree.splitIndex_self] at hlow
        omega
      have hleaf : r.tree.leaves ≤ rBound+2 := by
        have H1:=T.markedAttach_leaves 0 p hp
        have H2:=p.tree.markedAttach_leaves 0 r hr
        omega
      let Gr:=(G.nativeCMarkedLift p hp).nativeCMarkedLift r hr
      have hGr e : Gr.sourceLowMass e ≤ Cmass*sourceFactorScale M.xs W initial e := by
        simpa only [Gr,ActualNaturalBoundaryShape.nativeCMarkedLift_sourceLowMass] using hmass e
      have hnew : partitionPoint 0 as (r.tree.splitIndex (r.embed p.mark) r.mark) ≤ Cmass*W :=
        (partitionPoint_mono as ho hlow.le).trans hcut
      have Htest:=G.nativeC_inserted_canonical_low_test_original_q M forms U b S p hp r hr hlow
      have Hjet t (ht : t∈Icc (0:ℝ) 1) :
          |cutFrozenLowHighJet n q U b h K r.tree
            (fun σ=>insertedRestTest P (restCenteredLowKernel n U b S) p r (r.tree.cavityAssignment σ).1) 0 0 2 t|≤
          Phi*(r.tree.forkCost f+edgeBudget 0 as f) := by
        have Hraw:=hgrid U r.tree t ht hleaf Gr forms initial W hxW hGr (r.embed p.mark) r.mark hcd hnew
        have Hprof:=actual_minimum_inherited_current_high_profile_le_original_original_q M Temp Cf hTemp hCf hsource hxs1
          r.tree ho U (l:=0) (t:=t) (by norm_num) ht (e:=4/pexp)
            (div_nonneg (by norm_num) (by linarith))
        have HH:=mul_le_mul_of_nonneg_left Hprof hPhi
        rw [Htest]
        exact Hraw.trans HH
      have HI:=weighted_unit_integral_abs_le (mul_nonneg hPhi hProfile) Hjet 1
      have HPi:=native_low_scalar_pairing_abs_le_two r.tree ho U K
        (r.embed (p.embed a)) (r.embed (p.embed z)) (r.embed p.mark) r.mark
      change |Pi*_|≤_
      rw [abs_mul]
      have HH:=mul_le_mul HPi (by simpa only [pow_one] using HI) (abs_nonneg _) (by norm_num : (0:ℝ)≤2)
      nlinarith only [HH]
  have HT:=T.signedPair_abs_le_pairAbsSum F
  have HM:=(HT.trans (T.pairAbsSum_mono HF))
  rw [T.pairAbsSum_const_mul (2*Phi)] at HM
  have HB:=T.pairAbsSum_forkBudget_le ho hT hf (d:=0) (by norm_num)
  simp only [add_zero] at HB
  have HX:=HM.trans (mul_le_mul_of_nonneg_left HB (mul_nonneg (by norm_num : (0:ℝ)≤2) hPhi))
  change |_/2|≤_
  rw [abs_div,show |(2:ℝ)|=2 by norm_num]
  dsimp only [nativeCenteredLowGammaHighSecondRemainder,F,P,Phi,R,f,q,b,h,K,S,Mclock] at HX ⊢
  nlinarith only [HX]

theorem eventually_actual_minimum_inherited_constant_HIGH_parts_profile_original_q
    (rBound dOrder : ℕ) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Temp Cf Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U ≤ as.length → T.leaves ≤ rBound →
        ∀W : ℝ,M.xs ≤ W → W ≤ 1 → partitionPoint 0 as U ≤ Ccut*W →
        ∀(a z : T.Slot) (l t : ℝ),l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → ∀part : Fin 3,
          let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as (4*Cf+2*Temp) Temp
          |nativeActualHigherHighPart part n q U b h K T (fun _=>1) a z l t| ≤
            C*W*
              (T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+
                W*(T.forkCost R+edgeBudget 0 as R)) := by
  have hLowOrder : 2*(p/(p-2)) ≤ ((2*dOrder:ℕ):ℝ):=by
    push_cast
    linarith
  obtain ⟨C₀,hC₀,H₀⟩:=eventually_actual_minimum_inherited_constant_centered_fixed_low_two_one_high_budget_original_q
    (D:=D) rBound Bclock Temp Cf Ccut hTemp hCf hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨C₁,hC₁,H₁⟩:=eventually_actual_minimum_inherited_constant_centered_fixed_low_one_two_high_budget_original_q
    (D:=D) rBound dOrder hd p hp hLowOrder Bclock Temp Cf Ccut hTemp hCf hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨C₂,hC₂,H₂⟩:=eventually_actual_minimum_inherited_constant_centered_transient_HIGH_budget_original_q
    (D:=D) rBound Bclock Temp Cf Ccut hTemp hCf hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  let C:=C₀+C₁+C₂+1
  have hC : 0 < C:=by dsimp only [C];linarith
  refine ⟨C,hC,?_⟩
  filter_upwards [H₀,H₁,H₂] with n hn₀ hn₁ hn₂
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn₀ M hs0 hsxs hsource hxs L us hus hret hmesh,
    hn₁ M hs0 hsxs hsource hxs L us hus hret hmesh,hn₂ M hs0 hsxs hsource hxs L us hus hret hmesh]
    with jGrid hj₀ hj₁ hj₂
  dsimp only at hj₀ hj₁ hj₂ ⊢
  intro U T hU hT W hxW hW₁ hcut a z l t hl ht part
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as (4*Cf+2*Temp) Temp
  let F₁:=T.forkCost R+edgeBudget 0 as R
  let F₂:=T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))
  let Z : ℝ:=1
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hW : 0 ≤ W:=(M.hxs.trans_le hxW).le
  have hZ : 0 ≤ Z:=zero_le_one
  have hR j : 0 ≤ R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg (4*Cf+2*Temp) hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hF₁ : 0 ≤ F₁:=add_nonneg (T.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
  have hF₂ : 0 ≤ F₂:=add_nonneg (T.forkCost_nonneg (fun j=>Real.rpow_nonneg (hR j) _))
    (edgeBudget_nonneg ho (fun j=>Real.rpow_nonneg (hR j) _))
  have HP₀:=actual_minimum_inherited_current_high_profile_le_original_original_q M Temp Cf hTemp hCf hsource hxs
    T ho U (show (0:ℝ)∈Icc 0 1 by norm_num) ht (e:=1) (by norm_num)
  simp only [Real.rpow_one] at HP₀
  have HP₁:=actual_minimum_inherited_current_high_profile_le_original_original_q M Temp Cf hTemp hCf hsource hxs
    T ho U (show (0:ℝ)∈Icc 0 1 by norm_num) ht (e:=4/p) (by positivity)
  have HP₂:=actual_minimum_inherited_current_high_profile_le_original_original_q M Temp Cf hTemp hCf hsource hxs
    T ho U hl ht (e:=1) (by norm_num)
  simp only [Real.rpow_one] at HP₂
  fin_cases part
  · change |nativeCenteredFixedLowHigh n q U b h K T (fun _=>1) a z 2 1 t| ≤ _
    have H:=hj₀ U T t hU ht hT W hxW hcut a z
    apply (H.trans (mul_le_mul_of_nonneg_left HP₀ (by positivity))).trans
    simpa only [Z,mul_one] using actual_high_one_error_price_le hC.le (by dsimp only [C];linarith) hW hZ hF₁ hF₂
  · change |nativeCenteredFixedLowHigh n q U b h K T (fun _=>1) a z 1 2 t| ≤ _
    have H:=hj₁ U T t hU ht hT W hxW hcut a z
    apply (H.trans (mul_le_mul_of_nonneg_left HP₁ (by positivity))).trans
    simpa only [Z,mul_one] using actual_high_two_error_price_le hC.le (by dsimp only [C];linarith) hW hZ hF₁ hF₂
  · change |nativeCenteredTransientHighThird n q U b h K T (fun _=>1) a z l t| ≤ _
    have H:=hj₂ U T l t hU hl ht hT W hxW hcut a z
    apply (H.trans (mul_le_mul_of_nonneg_left HP₂ (by positivity))).trans
    simpa only [Z,mul_one] using actual_high_transient_price_le hC.le hC₂.le (by dsimp only [C];linarith) hW hW₁ hZ hF₁ hF₂

theorem eventually_actual_minimum_inherited_target_third_LOW_integral_budget_original_q
    (Bclock Temp Cf Ccut : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0<C ∧ ∀ᶠn in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(i U : ℕ) (x : ℝ),i<U → U≤as.length → M.xs≤x → x≤1 → Ccut*x≤1 →
          partitionPoint 0 as U≤Ccut*x →
        let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i
        let Cerr:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp
        let di:=nativeOriginalCutLowErrorRadius n M.sweepBf M.sweepHf as i+1/(n+1:ℕ)
        ∀(l t : ℝ),l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 →
          |nativeActualCenteredThirdLowPart n q U b h K g.tree (fun _=>1)
            (g.embed (singleSlot as)) g.mark l t|≤
              C*x^2*Cerr*di+C*x*Cerr*
                (∫u in 0..Ccut*x,Real.sqrt (orderedPathB (n+1) M.sweepBf M.sweepHf u-
                  (orderedPathS (n+1) M.sweepBf M.sweepHf u)^2)) := by
  obtain ⟨C,hC,HC⟩:=eventually_actual_minimum_inherited_constant_centered_third_LOW_profile_original_q
    (D:=D) 2 Bclock Temp Cf Ccut hTemp hCf hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨4*C,by positivity,?_⟩
  filter_upwards [HC] with n hn
  intro M hs0 hsxs HS hxs1 L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs HS hxs1 L us hus hret hmesh,
    original_band_l1_density_on_all_final_nets_original_q M] with jGrid hj hband
  dsimp only at hj ⊢
  intro i U x hi hU hxsx hx1 hcut1 hcut l t hl ht
  let as:=finiteCutMasses us jGrid
  let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let R:=nativeWholeLawErrorRadius n as (cutFullVariance n q U l t b h K) (cutLowError n U b h K)
  let Cerr:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp
  let di:=nativeOriginalCutLowErrorRadius n M.sweepBf M.sweepHf as i+1/(n+1:ℕ)
  let I:=(∫u in 0..Ccut*x,Real.sqrt (orderedPathB (n+1) M.sweepBf M.sweepHf u-
    (orderedPathS (n+1) M.sweepBf M.sweepHf u)^2))
  have hx : 0<x:=M.hxs.trans_le hxsx
  have hCe : 0≤Cerr:=actualLowErrorComparisonConstant_nonneg _ hTemp
  have hdi : 0≤di:=add_nonneg (Real.sqrt_nonneg _) (by positivity)
  have hsite : (1/(n+1:ℕ):ℝ)≤di:=le_add_of_nonneg_left (Real.sqrt_nonneg _)
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hg : g.tree.leaves≤2:=by
    have H:=(single (S:=Spin n×Bool) as).markedAttach_leaves 0 g (nativeFreshAtSlot_mem _ _ _ _)
    simpa only [single_leaves_exact] using H
  have HR : R i≤Cerr*di:=by
    have H:=actual_minimum_inherited_current_low_error_radius_le_original_original_q M Temp Cf hTemp hCf
      HS hxs1 ho U hl ht i (hi.le.trans hU)
    change R i≤ if i<U then Cerr*di else 0 at H
    simpa only [hi,ite_true] using H
  have HF : g.tree.forkCost R=R i:=by
    rw [nativeFreshAtSlot_forkCost,single_forkCost,zero_add,Nat.min_eq_left (hi.le.trans hU)]
  have HD : edgeBudget 0 as R≤Cerr*(I+3/(n+1:ℕ)):=by
    have Hmono:=actual_low_edgeBudget_mono ho (fun j hj=>
      actual_minimum_inherited_current_low_error_radius_le_original_original_q M Temp Cf hTemp hCf HS hxs1
        ho U hl ht j hj)
    have Heq : (fun j=>if j<U then Cerr*(nativeOriginalCutLowErrorRadius n M.sweepBf M.sweepHf as j+1/(n+1:ℕ)) else 0)=
        (fun j=>Cerr*(if j<U then nativeOriginalCutLowErrorRadius n M.sweepBf M.sweepHf as j+1/(n+1:ℕ) else 0)+0*(0:ℝ)):=by
      funext j
      split_ifs <;> simp
    change edgeBudget 0 as R≤edgeBudget 0 as _ at Hmono
    rw [Heq,actual_low_edgeBudget_linear] at Hmono
    simp only [zero_mul,add_zero] at Hmono
    have HB:=hband us hus 0 U (Nat.zero_le _) hU
    simp only [Nat.not_lt_zero,ite_false] at HB
    have hz : partitionPoint 0 (finiteCutMasses us jGrid) 0=0:=by cases finiteCutMasses us jGrid <;> rfl
    rw [hz] at HB
    change edgeBudget 0 as (fun j=>if j<U then nativeOriginalCutLowErrorRadius n M.sweepBf M.sweepHf as j+1/(n+1:ℕ) else 0)≤
      (∫u in 0..partitionPoint 0 as U,Real.sqrt
        (orderedPathB (n+1) M.sweepBf M.sweepHf u-(orderedPathS (n+1) M.sweepBf M.sweepHf u)^2))+3/(n+1:ℕ) at HB
    have HI:=native_intervalIntegrable_sqrt_of_intervalIntegrable
      ((original_thermal_intervalIntegrable_original_q M).mono_set (by
        rw [uIcc_of_le (mul_nonneg hCcut hx.le),uIcc_of_le zero_le_one]
        exact Icc_subset_Icc le_rfl hcut1))
    have HImono : (∫u in 0..partitionPoint 0 as U,Real.sqrt
        (orderedPathB (n+1) M.sweepBf M.sweepHf u-(orderedPathS (n+1) M.sweepBf M.sweepHf u)^2))≤I:=
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
