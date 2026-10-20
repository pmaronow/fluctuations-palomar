module

public import ComparisonSignedCavityInheritedSmallCutLowMoment
public import ComparisonSignedCavityInheritedSmallCutAtomicProducer
public import ComparisonSignedCavityInitialInheritedAtomDichotomy
public import ComparisonSignedCavityInitialInheritedAtomModulusBudget
public import ComparisonSignedCavityInitialInheritedWordModulusBudget
public import ComparisonSignedCavityInitialInheritedPlainWordModulusBudget
public import ComparisonSignedCavityInitialInheritedJetModulusBudget
public import ComparisonSignedCavityInitialInheritedCenteredModulusBudget
public import ComparisonActualHighOnlyLowResourceReadoutSourceAlong
public import ComparisonActualHighOnlyLowPhysicalSourceAlong
public import ComparisonActualHighOnlyOriginalTargetB0
public import ComparisonActualHighOnlyPhysicalTaylorProfiles
public import ComparisonActualHighOnlyRawResourcePairBudget

@[expose] public section
noncomputable section
set_option maxHeartbeats 32000000
set_option linter.unusedVariables false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
private theorem ActualNaturalBoundaryShape.low_source_onMarked_canonical_product
    {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (G : ActualNaturalBoundaryShape n a T) (p : ClockTree.MarkedPlacement T) (hp : p∈T.markedAttach 0)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (forms : Fin a→NativeSourceFactorForm) (σ : p.tree.Assignment) :
    ((G.onMarked p hp).canonicalHighOnlySource M forms).product σ=
      (G.canonicalHighOnlySource M forms).product (p.restrict σ) := by
  unfold ActualNaturalBoundaryShape.product fullBoundaryAffineProduct
  apply Finset.prod_congr rfl
  intro e _
  simp only [ActualNaturalBoundaryShape.canonicalHighOnlySource]
  rw [G.onMarked_sourceLowMass p hp e]
  simp only [ActualNaturalBoundaryShape.onMarked,p.restrict_at]

end OAI.SKFluctuations.Cavity
namespace OAI.SKFluctuations.Hierarchy.ClockTree.NativeInitialInsertionWord
open OAI.SKFluctuations.Cavity OAI.SKFluctuations.Hierarchy OAI.SKFluctuations.LaplaceWindowFormalization
 variable {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {k : ℕ}
 private theorem low_source_initial_canonicalShape_product (g : ClockTree.NativeInitialInsertionWord T k)
    (G : ActualNaturalBoundaryShape n a T)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (forms : Fin a→NativeSourceFactorForm) (σ : g.tree.Assignment) :
    ((g.canonicalShape G).canonicalHighOnlySource M forms).product σ=
      (G.canonicalHighOnlySource M forms).product (g.restrict σ) := by
  induction g with
  | done T=>rfl
  | pair p hp r hr tail ih=>
    dsimp only [tree] at σ
    change ((tail.canonicalShape ((G.onMarked p hp).onMarked r hr)).canonicalHighOnlySource M forms).product σ=
      (G.canonicalHighOnlySource M forms).product (p.restrict (r.restrict (tail.restrict σ)))
    rw [ih]
    rw [(G.onMarked p hp).low_source_onMarked_canonical_product r hr M forms,
      G.low_source_onMarked_canonical_product p hp M forms]

end OAI.SKFluctuations.Hierarchy.ClockTree.NativeInitialInsertionWord
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
 theorem native_initial_terminal_word_test_eq_physical_atom_high_only
    (n U i k : ℕ) (b h K : ℕ→ℝ) (t : ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (g : NativeInitialInsertionWord T (k+1))
    {aDegree : ℕ} (G : ActualNaturalBoundaryShape n aDegree T)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (forms : Fin aDegree→NativeSourceFactorForm) (a z : T.Slot)
    (hsplit : g.tree.splitIndex (g.pairSlots (Fin.last k)).1 (g.pairSlots (Fin.last k)).2=i)
    (σ : g.tree.Assignment) :
    g.test (nativeInitialTerminalLowDirections n U i k b h K t)
      (fun τ=>(G.canonicalHighOnlySource M forms).product τ*sitePair T a z (T.cavityAssignment τ).2) σ=
      nativeOldInitialRowProduct n g.tree ((g.canonicalShape G).canonicalHighOnlySource M forms).restProduct
        (nativeSmallCutOldErrorRestKernel n U b h K)
        (g.pairSlots (Fin.last k)).1 (g.pairSlots (Fin.last k)).2
        (fun e : Fin (k+1)=>nativeSmallCutOrdinaryRestKernel n U b h K
          (Fin.cases true (fun _ : Fin k=>false) e) (Fin.cases 0 (fun _ : Fin k=>t) e))
        (Fin.cases (g.embed a) (fun e=> (g.pairSlots e.castSucc).1))
        (Fin.cases (g.embed z) (fun e=> (g.pairSlots e.castSucc).2)) σ := by
  rw [g.test_eq_joint_product,Fin.prod_univ_castSucc]
  simp only [nativeInitialTerminalLowDirections,Fin.lastCases_castSucc,Fin.lastCases_last,hsplit,ite_true,
    sitePair_apply,g.restrict_at]
  rw [←NativeInitialInsertionWord.low_source_initial_canonicalShape_product g G M forms]
  unfold nativeOldInitialRowProduct
  rw [Fin.prod_univ_succ]
  simp only [Fin.cases_zero,Fin.cases_succ,nativeSmallCutOrdinaryRestKernel,Bool.false_eq_true,ite_false,ite_true]
  rw [native_small_cut_old_error_eq_original_profile]
  simp_rw [native_small_cut_moving_kernel_eq_original_profile]
  rw [←((g.canonicalShape G).canonicalHighOnlySource M forms).product_eq_restProduct]
  simp only [nativeRestRowKernel,one_mul,hsplit]
  ring

 theorem native_initial_terminal_word_test_eq_physical_atom_plain_high_only
    (n U i k : ℕ) (b h K : ℕ→ℝ) (t : ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (g : NativeInitialInsertionWord T (k+1))
    {aDegree : ℕ} (G : ActualNaturalBoundaryShape n aDegree T)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (forms : Fin aDegree→NativeSourceFactorForm)
    (hsplit : g.tree.splitIndex (g.pairSlots (Fin.last k)).1 (g.pairSlots (Fin.last k)).2=i)
    (σ : g.tree.Assignment) :
    g.test (nativeInitialTerminalLowDirections n U i k b h K t) (G.canonicalHighOnlySource M forms).product σ=
      nativeOldInitialRowProduct n g.tree ((g.canonicalShape G).canonicalHighOnlySource M forms).restProduct
        (nativeSmallCutOldErrorRestKernel n U b h K)
        (g.pairSlots (Fin.last k)).1 (g.pairSlots (Fin.last k)).2
        (fun _ : Fin k=>nativeSmallCutOrdinaryRestKernel n U b h K false t)
        (fun e=> (g.pairSlots e.castSucc).1) (fun e=> (g.pairSlots e.castSucc).2) σ := by
  rw [g.test_eq_joint_product,Fin.prod_univ_castSucc]
  simp only [nativeInitialTerminalLowDirections,Fin.lastCases_castSucc,Fin.lastCases_last,hsplit,ite_true]
  rw [←NativeInitialInsertionWord.low_source_initial_canonicalShape_product g G M forms]
  unfold nativeOldInitialRowProduct
  rw [native_small_cut_old_error_eq_original_profile]
  simp only [nativeSmallCutOrdinaryRestKernel,Bool.false_eq_true,ite_false]
  simp_rw [native_small_cut_moving_kernel_eq_original_profile]
  rw [←((g.canonicalShape G).canonicalHighOnlySource M forms).product_eq_restProduct]
  rw [hsplit]
  ring

theorem eventually_actual_minimum_inherited_small_cut_low_moment_high_only
    (order : ℕ) (horder : 0 < order) (Bclock Temp Cf Ccut : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cq : ℝ,0 < Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U V : ℕ),V ≤ U → partitionPoint 0 as V ≤ Ccut*M.xs →
        ∀(l t s : ℝ),l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → s∈Icc (0:ℝ) 1 →
        ∀j ≤ as.length,
          (ClockTree.pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0
            (cutFullVariance n q U l t b h K)
            (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n)
              (cutLSlope n V s (relocatedClock U l b) (relocatedClock U l h) (relocatedClock U l K)) j
              (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^(2*order)) 0 ≤
            (Cq*(1+Ccut)*M.xs)^(2*order) := by
  obtain ⟨Cq,hCq,HQ⟩:=eventually_actual_minimum_inherited_continuum_low_profile_moment_high_only
    (D:=D) order horder Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cq,hCq,?_⟩
  filter_upwards [HQ] with n hnQ
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hnQ M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgridQ
  dsimp only at hgridQ ⊢
  intro U V hVU hcut l t s hl ht hs j hj
  let as:=finiteCutMasses us jGrid
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  by_cases hjV : j < V
  · have Hraw:=hgridQ U l t s hl ht hs j hj
    have HE (σ : (ClockTree.pairClock as j).Assignment) :=
      native_small_cut_low_profile_eq_scaled n U V hVU l s
        (fun j=>(M.bf (partitionPoint 0 as j):ℝ))
        (fun j=>(M.hf (partitionPoint 0 as j):ℝ))
        (fun j=>(M.hf (partitionPoint 0 as j):ℝ)+(M.bf (partitionPoint 0 as j):ℝ)*
          orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)) j hjV
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2
    dsimp only [as] at HE
    conv_lhs => simp only [HE,abs_mul,abs_of_nonneg hl.1,mul_pow]
    rw [ClockTree.disorderExpect_const_mul (fullWeight_pos n) (fullFeature n) _ ho]
    have Hl : l^(2*order) ≤ 1:=pow_le_one₀ hl.1 hl.2
    have Hnonneg : 0 ≤ (ClockTree.pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0
        (cutFullVariance n (fun j=>Sum.elim (fun _=>(M.bf (partitionPoint 0 as j):ℝ))
          (fun _=>(M.hf (partitionPoint 0 as j):ℝ))) U l t
          (fun j=>(M.bf (partitionPoint 0 as j):ℝ)) (fun j=>(M.hf (partitionPoint 0 as j):ℝ))
          (fun j=>(M.hf (partitionPoint 0 as j):ℝ)+(M.bf (partitionPoint 0 as j):ℝ)*
            orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)))
        (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n)
          (cutLSlope n U s (fun j=>(M.bf (partitionPoint 0 as j):ℝ))
            (fun j=>(M.hf (partitionPoint 0 as j):ℝ))
            (fun j=>(M.hf (partitionPoint 0 as j):ℝ)+(M.bf (partitionPoint 0 as j):ℝ)*
              orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j))) j
          (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^(2*order)) 0:=by
      unfold ClockTree.disorderExpect
      exact Finset.sum_nonneg fun σ _=>mul_nonneg
        (((ClockTree.pairClock as j).disorderWeight_probability
          (fullWeight_pos n) (fullFeature n) ho _ _ _).1 σ)
        (pow_nonneg (abs_nonneg _) _)
    apply (mul_le_of_le_one_left Hnonneg Hl).trans
    apply Hraw.trans
    apply pow_le_pow_left₀ (mul_nonneg hCq.le (add_nonneg M.hxs.le (partitionPoint_mem as ho j).1))
    have Hmass:=partitionPoint_mono as ho hjV.le
    have Hscale : M.xs+partitionPoint 0 as j ≤ (1+Ccut)*M.xs:=by nlinarith only [hcut,Hmass]
    exact (mul_le_mul_of_nonneg_left Hscale hCq.le).trans_eq (by ring)
  · have HE : (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n)
        (cutLSlope n V s (relocatedClock U l (fun j=>(M.bf (partitionPoint 0 as j):ℝ)))
          (relocatedClock U l (fun j=>(M.hf (partitionPoint 0 as j):ℝ)))
          (relocatedClock U l (fun j=>(M.hf (partitionPoint 0 as j):ℝ)+
            (M.bf (partitionPoint 0 as j):ℝ)*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)))) j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^(2*order))=fun _=>0:=by
      funext σ
      simp only [ReplicaTree.coordinateProfile,cutLSlope,hjV,ite_false,Pi.zero_apply,
        zero_mul,Finset.sum_const_zero,abs_zero,zero_pow (by omega : 2*order≠0)]
    rw [HE]
    simp only [ClockTree.disorderExpect,mul_zero,Finset.sum_const_zero]
    exact pow_nonneg (mul_nonneg (mul_nonneg hCq.le (add_nonneg zero_le_one hCcut)) M.hxs.le) _

theorem eventually_actual_minimum_inherited_small_cut_old_initial_atom_high_only
    (aDegree aRows rBound : ℕ) (Bclock Temp Cf Cmass Ccut : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃Cp Cr Cq : ℝ,0<Cp ∧ 0<Cr ∧ 0<Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        let ep:=Real.exp (ClockTree.jetVariation 2 1*Mclock)
        ∀(U V : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),
          U≤as.length → 0<V → V≤U → partitionPoint 0 as V≤Ccut*M.xs →
          l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs≤x → x≤W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e) →
        ∀(u z : T.Slot),T.splitIndex u z<V →
        ∀(site : Fin aRows→Bool) (v : Fin aRows→ℝ) (s w : Fin aRows→T.Slot),
          (∀i,v i∈Icc (0:ℝ) 1) → (∀i,V≤T.splitIndex (s i) (w i)) → (∀i,s i≠w i) →
          let p0:=sourceMonomialScale x W initial
          let C:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*p0
          let d:=actualLowErrorComparisonConstant Mclock Temp*
            (nativeOriginalCutLowErrorRadius n M.bf M.hf as (T.splitIndex u z)+1/(n+1:ℕ))
          let r:=fun i=>nativeSmallCutOrdinaryScale M.xs Cr as (site i) (T.splitIndex (s i) (w i))
          |T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l t b h K)
            (nativeOldInitialRowProduct n T (G.canonicalHighOnlySource M forms).restProduct
              (nativeSmallCutOldErrorRestKernel n U b h K) u z
              (fun i=>nativeSmallCutOrdinaryRestKernel n U b h K (site i) (v i)) s w) 0|≤
            ClockTree.absJetVariation T.leaves 1*
              (Real.exp (ClockTree.jetVariation T.leaves 1*Mclock)*C)*(ep*d)*
              (∏i,ep*r i)*(ep*(Cq*(1+Ccut)*M.xs)) := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_inherited_canonical_continuum_even_all_degree_high_only
    (D:=D) aDegree 2 rBound (by norm_num) Bclock Temp Cf Cmass hTemp hCf hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cr,hCr,HR⟩:=eventually_actual_minimum_inherited_continuum_low_profile_moment_high_only
    (D:=D) (2*(aRows+1)) (by omega) Bclock Temp Cf hTemp hCf
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cq,hCq,HQ⟩:=eventually_actual_minimum_inherited_small_cut_low_moment_high_only
    (D:=D) (2*(aRows+1)) (by omega) Bclock Temp Cf Ccut hTemp hCf hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,Cr,Cq,hCp,hCr,hCq,?_⟩
  filter_upwards [HP,HR,HQ] with n hnP hnR hnQ
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hnP M hs0 hsxs hsource hxs L us hus hret hmesh,
    hnR M hs0 hsxs hsource hxs L us hus hret hmesh,
    hnQ M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgridP hgridR hgridQ
  dsimp only at hgridP hgridR hgridQ ⊢
  intro U V T l t hU hV0 hVU hcut hl ht hT G forms initial x W hxsx hxW hmass u z huz
    site v s w hv hsw hne
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let law:=cutFullVariance n q U l t b h K
  let Mclock:=4*Cf+2*Temp
  let C:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*
    sourceMonomialScale x W initial
  let d:=actualLowErrorComparisonConstant Mclock Temp*
    (nativeOriginalCutLowErrorRadius n M.bf M.hf as (T.splitIndex u z)+1/(n+1:ℕ))
  let r:=fun i=>nativeSmallCutOrdinaryScale M.xs Cr as (site i) (T.splitIndex (s i) (w i))
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hV : V≤as.length:=hVU.trans hU
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.bf u:ℝ)≤M.bf v from M.bf_monotone hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.hf u:ℝ)≤M.hf v from M.hf_monotone hu hv huv) as ho
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.bf M.hf
    M.bf_monotone M.hf_monotone (partitionPoint_mem as ho j)
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.bf M.hf M.bf_monotone M.hf_monotone) as ho
  have hK0 j : 0≤K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HS j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HS i).1 (NNReal.coe_nonneg _))
  have HM : 0≤Mclock:=by dsimp [Mclock];positivity
  have Hb j : b j≤Temp:=(hsource _ (partitionPoint_mem as ho j)).1
  have Hh j : h j≤2*Cf := by
    have Hsource:=hsource _ (partitionPoint_mem as ho j)
    have HH:=mul_le_mul_of_nonneg_left
      (show M.xs+partitionPoint 0 as j≤2 by linarith [(partitionPoint_mem as ho j).2]) hCf
    exact Hsource.2.trans (by linarith only [HH])
  have Hclock j : |K j|+|h j|+|b j|≤Mclock := by
    rw [abs_of_nonneg (hK0 j),abs_of_nonneg (NNReal.coe_nonneg _),abs_of_nonneg (NNReal.coe_nonneg _)]
    have HK:=mul_le_mul_of_nonneg_left (HS j).2 (NNReal.coe_nonneg (M.bf (partitionPoint 0 as j)))
    dsimp only [K,Mclock]
    linarith [Hh j,Hb j]
  have HC : 0≤C:=by
    dsimp only [C]
    rw [←source_factor_scale_product]
    exact mul_nonneg (by positivity) (Finset.prod_nonneg fun e _=>
      (source_factor_scale_pos (M.hxs.trans_le hxsx) (M.hxs.trans_le (hxsx.trans hxW)) initial e).le)
  have Hd : 0≤d:=mul_nonneg (actualLowErrorComparisonConstant_nonneg Mclock hTemp)
    (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have Hnewpos : 0<Cq*(1+Ccut)*M.xs:=mul_pos (mul_pos hCq (by linarith)) M.hxs
  apply native_old_initial_row_product_abs_le_original_moments n q U V hV0 b h K T ho hV
    (G.canonicalHighOnlySource M forms).restProduct (nativeSmallCutOldErrorRestKernel n U b h K) u z huz
    (fun i=>nativeSmallCutOrdinaryRestKernel n U b h K (site i) (v i)) s w hsw hne 0
    (by intro i;rfl) (by intro i;rfl)
    (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
    (fun i=>by cases i <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm
    HM HC Hd Hnewpos (fun j _=>Hclock j) r
    (fun i=>native_small_cut_ordinary_scale_pos M.hxs hCr ho (site i) _ ) hl ht
  · have H:=hgridP U T l t hl ht hT G forms initial x W hxsx hxW hmass
    simp_rw [(G.canonicalHighOnlySource M forms).product_eq_restProduct] at H
    simpa only [Nat.mul_succ,Nat.mul_zero,Nat.add_zero,C,Mclock,law,q,b,h,S,K,as] using H
  · rw [native_small_cut_old_error_eq_original_profile]
    change nativeWholeLawErrorSecond n as law (cutLowError n U b h K) (T.splitIndex u z)≤d^2
    rw [nativeWholeLawErrorSecond_eq_radius_sq n ho law]
    apply pow_le_pow_left₀ (nativeWholeLawErrorRadius_nonneg _ _ _ _ _) _ 2
    have H:=native_actual_low_error_radius_le_original (M:=Mclock) n U M.bf M.hf
      M.bf_monotone M.hf_monotone ho hl ht hTemp
      (fun j _=>Hb j) (by
        have HH:=Hclock as.length
        rw [abs_of_nonneg (hK0 _),abs_of_nonneg (NNReal.coe_nonneg _),abs_of_nonneg (NNReal.coe_nonneg _)] at HH
        dsimp only [K,b,h,S] at HH
        linarith only [HH]) (T.splitIndex u z) (T.splitIndex_le_clockLength u z)
    rw [ite_eq_left (huz.trans_le hVU)] at H
    exact H
  · intro i
    cases hsite : site i
    · dsimp only [nativeSmallCutOrdinaryRestKernel,nativeSmallCutOrdinaryScale,r]
      simp only [hsite,Bool.false_eq_true,ite_false]
      rw [native_small_cut_moving_kernel_eq_original_profile]
      simpa only [←Nat.mul_assoc,law,q,b,h,S,K,as] using
        hgridR U l t (v i) hl ht (hv i) (T.splitIndex (s i) (w i)) (T.splitIndex_le_clockLength _ _)
    · dsimp only [nativeSmallCutOrdinaryRestKernel,nativeSmallCutOrdinaryScale,r]
      simp only [hsite,ite_true,native_small_cut_site_row_abs_one,one_pow]
      exact le_of_eq (ClockTree.disorderExpect_one (fullWeight_pos n) (fullFeature n) _ ho 0 law 0)
  · intro j
    by_cases hj : j≤as.length
    · simpa only [←Nat.mul_assoc,q,b,h,S,K,as] using hgridQ U V hVU hcut l t t hl ht ht j hj
    · have hjV : ¬j<V:=by omega
      simp only [ReplicaTree.coordinateProfile,cutLSlope,hjV,ite_false,Pi.zero_apply,zero_mul,
        Finset.sum_const_zero,abs_zero,zero_pow (by omega : 4*(aRows+1)≠0),
        ClockTree.disorderExpect,mul_zero,Finset.sum_const_zero]
      exact pow_nonneg Hnewpos.le _

theorem eventually_actual_minimum_inherited_initial_atom_dichotomy_high_only
    (aDegree aRows rBound : ℕ) (Bclock Temp Cf Cmass Ccut : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃Cp Cr CpS CrS Cq : ℝ,0<Cp ∧ 0<Cr ∧ 0<CpS ∧ 0<CrS ∧ 0<Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        let ep:=Real.exp (ClockTree.jetVariation 2 1*Mclock)
        ∀(U V : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),
          U≤as.length → 0<V → V≤U → partitionPoint 0 as V≤Ccut*M.xs →
          l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs≤x → x≤W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e) →
        ∀(u z : T.Slot),T.splitIndex u z<V →
        ∀(site : Fin aRows→Bool) (v : Fin aRows→ℝ) (s w : Fin aRows→T.Slot),
          (∀i,v i∈Icc (0:ℝ) 1) → (∀i,s i≠w i) →
          let p0:=sourceMonomialScale x W initial
          let C:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*p0
          let d:=actualLowErrorComparisonConstant Mclock Temp*
            (nativeOriginalCutLowErrorRadius n M.bf M.hf as (T.splitIndex u z)+1/(n+1:ℕ))
          let r:=fun i=>nativeSmallCutOrdinaryScale M.xs Cr as (site i) (T.splitIndex (s i) (w i))
          let CS:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*CpS^aDegree*p0
          let rS:=fun i=>nativeSmallCutOrdinaryScale M.xs CrS as (site i) (T.splitIndex (s i) (w i))
          (|T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l t b h K)
            (nativeOldInitialRowProduct n T (G.canonicalHighOnlySource M forms).restProduct
              (nativeSmallCutOldErrorRestKernel n U b h K) u z
              (fun i=>nativeSmallCutOrdinaryRestKernel n U b h K (site i) (v i)) s w) 0|≤
            C*d*(∏i,r i)) ∧
          ((∀i,V≤T.splitIndex (s i) (w i)) →
          |T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l t b h K)
            (nativeOldInitialRowProduct n T (G.canonicalHighOnlySource M forms).restProduct
              (nativeSmallCutOldErrorRestKernel n U b h K) u z
              (fun i=>nativeSmallCutOrdinaryRestKernel n U b h K (site i) (v i)) s w) 0|≤
            ClockTree.absJetVariation T.leaves 1*
              (Real.exp (ClockTree.jetVariation T.leaves 1*Mclock)*CS)*(ep*d)*
              (∏i,ep*rS i)*(ep*(Cq*(1+Ccut)*M.xs))) := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_inherited_canonical_continuum_even_all_degree_high_only
    (D:=D) aDegree 2 rBound (by norm_num) Bclock Temp Cf Cmass hTemp hCf hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cr,hCr,HR⟩:=eventually_actual_minimum_inherited_continuum_low_profile_moment_high_only
    (D:=D) (2*(aRows+1)) (by omega) Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨CpS,CrS,Cq,hCpS,hCrS,hCq,HS⟩:=eventually_actual_minimum_inherited_small_cut_old_initial_atom_high_only
    (D:=D) aDegree aRows rBound Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,Cr,CpS,CrS,Cq,hCp,hCr,hCpS,hCrS,hCq,?_⟩
  filter_upwards [HP,HR,HS] with n hnP hnR hnS
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hnP M hs0 hsxs hsource hxs L us hus hret hmesh,
    hnR M hs0 hsxs hsource hxs L us hus hret hmesh,hnS M hs0 hsxs hsource hxs L us hus hret hmesh]
    with jGrid hgridP hgridR hgridS
  dsimp only at hgridP hgridR hgridS ⊢
  intro U V T l t hU hV0 hVU hcut hl ht hT G forms initial x W hxsx hxW hmass
    u z huz site v s w hv hne
  constructor
  · let as:=finiteCutMasses us jGrid
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
    let K:=fun j=>h j+b j*S j
    let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    let law:=cutFullVariance n q U l t b h K
    let Mclock:=4*Cf+2*Temp
    let C:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*
      sourceMonomialScale x W initial
    let d:=actualLowErrorComparisonConstant Mclock Temp*
      (nativeOriginalCutLowErrorRadius n M.bf M.hf as (T.splitIndex u z)+1/(n+1:ℕ))
    let r:=fun e=>nativeSmallCutOrdinaryScale M.xs Cr as (site e) (T.splitIndex (s e) (w e))
    have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
    have HC : 0≤C:=by
      dsimp only [C]
      rw [←source_factor_scale_product]
      exact mul_nonneg (by positivity) (Finset.prod_nonneg fun e _=>
        (source_factor_scale_pos (M.hxs.trans_le hxsx) (M.hxs.trans_le (hxsx.trans hxW)) initial e).le)
    have Hd : 0≤d:=mul_nonneg (actualLowErrorComparisonConstant_nonneg Mclock hTemp)
      (add_nonneg (Real.sqrt_nonneg _) (by positivity))
    have Hne : u≠z:=by
      intro H
      rw [H,T.splitIndex_self] at huz
      omega
    have HPmoment : T.disorderExpect (fullWeight n) (fullFeature n) 0 law
        (fun σ=>|(G.canonicalHighOnlySource M forms).product σ|^4) 0≤C^4:=
      hgridP U T l t hl ht hT G forms initial x W hxsx hxW hmass
    have Herror : (ClockTree.pairClock as (T.splitIndex u z)).disorderExpect (fullWeight n) (fullFeature n) 0 law
        (fun σ=>(nativeRestRowKernel n (nativeSmallCutOldErrorRestKernel n U b h K) (T.splitIndex u z)
          (ClockTree.pairSpin as (T.splitIndex u z) σ).1
          (ClockTree.pairSpin as (T.splitIndex u z) σ).2)^2) 0≤d^2:=by
      rw [native_small_cut_old_error_eq_original_profile]
      change nativeWholeLawErrorSecond n as law (cutLowError n U b h K) (T.splitIndex u z)≤d^2
      rw [nativeWholeLawErrorSecond_eq_radius_sq n ho law]
      apply pow_le_pow_left₀ (nativeWholeLawErrorRadius_nonneg _ _ _ _ _) _ 2
      have H:=actual_minimum_inherited_current_low_error_radius_le_original_high_only M Temp Cf hTemp hCf hsource hxs
        ho U hl ht (T.splitIndex u z) (T.splitIndex_le_clockLength u z)
      rw [ite_eq_left (huz.trans_le hVU)] at H
      exact H
    have HE e : (ClockTree.pairClock as (T.splitIndex (s e) (w e))).disorderExpect
        (fullWeight n) (fullFeature n) 0 law
        (fun σ=>|nativeRestRowKernel n (nativeSmallCutOrdinaryRestKernel n U b h K (site e) (v e))
          (T.splitIndex (s e) (w e)) (ClockTree.pairSpin as (T.splitIndex (s e) (w e)) σ).1
          (ClockTree.pairSpin as (T.splitIndex (s e) (w e)) σ).2|^(4*(aRows+1))) 0≤(r e)^(4*(aRows+1)):=by
      cases hsite : site e
      · dsimp only [nativeSmallCutOrdinaryRestKernel,nativeSmallCutOrdinaryScale,r]
        simp only [hsite,Bool.false_eq_true,ite_false]
        rw [native_small_cut_moving_kernel_eq_original_profile]
        simpa only [←Nat.mul_assoc,law,q,b,h,S,K,as] using
          hgridR U l t (v e) hl ht (hv e) (T.splitIndex (s e) (w e)) (T.splitIndex_le_clockLength _ _)
      · dsimp only [nativeSmallCutOrdinaryRestKernel,nativeSmallCutOrdinaryScale,r]
        simp only [hsite,ite_true,native_small_cut_site_row_abs_one,one_pow]
        exact le_of_eq (ClockTree.disorderExpect_one (fullWeight_pos n) (fullFeature n) _ ho 0 law 0)
    have H:=ClockTree.native_initial_observed_error_product_abs_le (fullWeight_pos n) (fullFeature n) T ho
      0 law 0 (G.canonicalHighOnlySource M forms).product HC Hd HPmoment
      (nativeRestRowKernel n (nativeSmallCutOldErrorRestKernel n U b h K)) u z Hne Herror
      (fun e=>nativeRestRowKernel n (nativeSmallCutOrdinaryRestKernel n U b h K (site e) (v e))) s w hne
      r (fun e=>native_small_cut_ordinary_scale_pos M.hxs hCr ho (site e) _) HE
    change |T.disorderExpect (fullWeight n) (fullFeature n) 0 law
      (nativeOldInitialRowProduct n T (G.canonicalHighOnlySource M forms).restProduct
        (nativeSmallCutOldErrorRestKernel n U b h K) u z
        (fun e=>nativeSmallCutOrdinaryRestKernel n U b h K (site e) (v e)) s w) 0|≤C*d*(∏e,r e)
    unfold nativeOldInitialRowProduct
    simp_rw [(G.canonicalHighOnlySource M forms).product_eq_restProduct] at H
    exact H
  · intro hupper
    exact hgridS U V T l t hU hV0 hVU hcut hl ht hT G forms initial x W hxsx hxW hmass
      u z huz site v s w hv hupper hne

private theorem low_source_initial_coefficient_power_le {R : ℝ} (hR : 0≤R) {k a : ℕ} (hka : k≤a) :
    R^k≤(max 1 R)^a := by
  exact (pow_le_pow_left₀ hR (le_max_right _ _) _).trans
    (pow_le_pow_right₀ (le_max_left _ _) hka)

theorem eventually_actual_minimum_inherited_initial_atom_modulus_budget_high_only
    (aDegree aRows rBound : ℕ) (Bclock Temp Cf Cmass Ccut Couter : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcut : 0≤Ccut) (hCouter : 0≤Couter)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0<C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U V : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),
          U≤as.length → 0<V → V≤U → partitionPoint 0 as V≤Ccut*M.xs →
          l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs≤x → x≤W → W≤1 → partitionPoint 0 as U≤Couter*W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e) →
        ∀(u z : T.Slot),T.splitIndex u z<V →
        ∀(site : Fin aRows→Bool) (v : Fin aRows→ℝ) (s w : Fin aRows→T.Slot),
          (∀i,v i∈Icc (0:ℝ) 1) → (∀i,s i≠w i) →
          (∀e,site e=true → V≤T.splitIndex (s e) (w e)) →
          (∀e,site e=false → T.splitIndex (s e) (w e)<U) →
          let p0:=sourceMonomialScale x W initial
          let d:=actualLowErrorComparisonConstant Mclock Temp*
            (nativeOriginalCutLowErrorRadius n M.bf M.hf as (T.splitIndex u z)+1/(n+1:ℕ))
          |T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l t b h K)
            (nativeOldInitialRowProduct n T (G.canonicalHighOnlySource M forms).restProduct
              (nativeSmallCutOldErrorRestKernel n U b h K) u z
              (fun i=>nativeSmallCutOrdinaryRestKernel n U b h K (site i) (v i)) s w) 0|≤
            C*M.xs*d*p0*W^((nativeInitialOrdinaryRowSet site).card-1) := by
  obtain ⟨Cp,Cr,CpS,CrS,Cq,hCp,hCr,hCpS,hCrS,hCq,HD⟩:=
    eventually_actual_minimum_inherited_initial_atom_dichotomy_high_only (D:=D)
      aDegree aRows rBound Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
      hm hdelta hroom hcl hcu hAz hC0 hCt
  let Mclock:=4*Cf+2*Temp
  let A:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree
  let AS:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*CpS^aDegree
  let ep:=Real.exp (ClockTree.jetVariation 2 1*Mclock)
  let AV:=4*(rBound:ℝ)*(rBound+1)
  let ET:=Real.exp (2*(rBound:ℝ)*(rBound+1)*Mclock)
  let R:=Cr*(1+Couter)
  let RS:=CrS*(1+Couter)
  let Sraw:=Cr*(1+Ccut)
  let C1:=A*Sraw*(max 1 R)^aRows
  let C2:=AV*ET*AS*ep^(aRows+2)*Cq*(1+Ccut)*(max 1 RS)^aRows
  let C:=C1+C2+1
  have hR : 0<R:=mul_pos hCr (by linarith)
  have hRS : 0<RS:=mul_pos hCrS (by linarith)
  have hSraw : 0<Sraw:=mul_pos hCr (by linarith)
  have hA : 0<A:=by dsimp [A];positivity
  have hAS : 0<AS:=by dsimp [AS];positivity
  have hep : 0<ep:=Real.exp_pos _
  have hAV : 0≤AV:=by dsimp [AV];positivity
  have hET : 0<ET:=Real.exp_pos _
  have hC1 : 0≤C1:=by dsimp [C1];positivity
  have hC2 : 0≤C2:=by dsimp [C2];positivity
  have hC : 0<C:=by dsimp [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [HD] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U V T l t hU hV0 hVU hcut hl ht hT G forms initial x W hxsx hxW hW1 houter hmass
    u z huz site v s w hv hne hsiteupper hrowlow
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let law:=cutFullVariance n q U l t b h K
  let value:=T.disorderExpect (fullWeight n) (fullFeature n) 0 law
    (nativeOldInitialRowProduct n T (G.canonicalHighOnlySource M forms).restProduct
      (nativeSmallCutOldErrorRestKernel n U b h K) u z
      (fun e=>nativeSmallCutOrdinaryRestKernel n U b h K (site e) (v e)) s w) 0
  let p0:=sourceMonomialScale x W initial
  let d:=actualLowErrorComparisonConstant Mclock Temp*
    (nativeOriginalCutLowErrorRadius n M.bf M.hf as (T.splitIndex u z)+1/(n+1:ℕ))
  let r:=fun e=>nativeSmallCutOrdinaryScale M.xs Cr as (site e) (T.splitIndex (s e) (w e))
  let rS:=fun e=>nativeSmallCutOrdinaryScale M.xs CrS as (site e) (T.splitIndex (s e) (w e))
  let k:=(nativeInitialOrdinaryRowSet site).card
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hW : 0<W:=M.hxs.trans_le (hxsx.trans hxW)
  have hx : 0<M.xs:=M.hxs
  have hp0 : 0≤p0:=by
    dsimp [p0]
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos (M.hxs.trans_le hxsx) hW initial e).le
  have hd : 0≤d:=mul_nonneg (actualLowErrorComparisonConstant_nonneg Mclock hTemp)
    (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hr e : 0≤r e:=(native_small_cut_ordinary_scale_pos M.hxs hCr ho (site e) _).le
  have hrS e : 0≤rS e:=(native_small_cut_ordinary_scale_pos M.hxs hCrS ho (site e) _).le
  have hsites e (he : site e=true) : r e=1:=by simp only [r,nativeSmallCutOrdinaryScale,he,ite_true]
  have hsitesS e (he : site e=true) : rS e=1:=by simp only [rS,nativeSmallCutOrdinaryScale,he,ite_true]
  have hrows e (he : site e=false) : r e≤R*W:=by
    simp only [r,nativeSmallCutOrdinaryScale,he,Bool.false_eq_true,ite_false]
    have Hmass:partitionPoint 0 as (T.splitIndex (s e) (w e))≤Couter*W:=
      (partitionPoint_mono as ho (hrowlow e he).le).trans houter
    have Hscale : M.xs+partitionPoint 0 as (T.splitIndex (s e) (w e))≤(1+Couter)*W:=by nlinarith only [hxsx,hxW,Hmass]
    exact (mul_le_mul_of_nonneg_left Hscale hCr.le).trans_eq (by dsimp [R];ring)
  have hrowsS e (he : site e=false) : rS e≤RS*W:=by
    simp only [rS,nativeSmallCutOrdinaryScale,he,Bool.false_eq_true,ite_false]
    have Hmass:partitionPoint 0 as (T.splitIndex (s e) (w e))≤Couter*W:=
      (partitionPoint_mono as ho (hrowlow e he).le).trans houter
    have Hscale : M.xs+partitionPoint 0 as (T.splitIndex (s e) (w e))≤(1+Couter)*W:=by nlinarith only [hxsx,hxW,Hmass]
    exact (mul_le_mul_of_nonneg_left Hscale hCrS.le).trans_eq (by dsimp [RS];ring)
  have hka : k≤aRows:=by
    have H:=Finset.card_le_card (Finset.filter_subset (fun e=>site e=false) (Finset.univ : Finset (Fin aRows)))
    simpa only [k,nativeInitialOrdinaryRowSet,Finset.card_univ,Fintype.card_fin] using H
  have HH:=hgrid U V T l t hU hV0 hVU hcut hl ht hT G forms initial x W hxsx hxW hmass
    u z huz site v s w hv hne
  by_cases Hupper : ∀e,V≤T.splitIndex (s e) (w e)
  · have Hp:=native_initial_radius_product_le site rS (mul_nonneg hRS.le hW.le) hrS hsitesS hrowsS
    have Hpow:=low_source_initial_coefficient_power_le hRS.le hka
    have HWpow:=pow_le_pow_of_le_one hW.le hW1 (show k-1≤k by omega)
    have Hprod : (∏e,rS e)≤(max 1 RS)^aRows*W^(k-1):=by
      apply Hp.trans
      rw [mul_pow]
      exact mul_le_mul Hpow HWpow (pow_nonneg hW.le _) (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)
    have hleaf : (T.leaves:ℝ)≤rBound:=by exact_mod_cast hT
    have HAv : ClockTree.absJetVariation T.leaves 1≤AV:=by
      simp only [ClockTree.absJetVariation]
      dsimp [AV]
      nlinarith only [hleaf,(show 0≤(T.leaves:ℝ) from Nat.cast_nonneg _)]
    have HM : 0≤Mclock:=by
      dsimp [Mclock]
      positivity
    have HEt : Real.exp (ClockTree.jetVariation T.leaves 1*Mclock)≤ET:=by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_right _ HM
      simp only [ClockTree.jetVariation]
      nlinarith only [hleaf,(show 0≤(T.leaves:ℝ) from Nat.cast_nonneg _)]
    have Hcoeff : ClockTree.absJetVariation T.leaves 1*
        Real.exp (ClockTree.jetVariation T.leaves 1*Mclock)≤AV*ET:=
      mul_le_mul HAv HEt (Real.exp_nonneg _) hAV
    have HS:=HH.2 Hupper
    change |value|≤_ at HS ⊢
    have HprodEp : (∏e,ep*rS e)=ep^aRows*(∏e,rS e):=by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    change |value|≤
      ClockTree.absJetVariation T.leaves 1*(Real.exp (ClockTree.jetVariation T.leaves 1*Mclock)*(AS*p0))*(ep*d)*
        (∏e,ep*rS e)*(ep*(Cq*(1+Ccut)*M.xs)) at HS
    rw [HprodEp] at HS
    have Hrest : |value|≤C2*M.xs*d*p0*W^(k-1):=by
      apply HS.trans
      calc
        _=(ClockTree.absJetVariation T.leaves 1*Real.exp (ClockTree.jetVariation T.leaves 1*Mclock))*(∏e,rS e)*
          (AS*p0*ep^(aRows+2)*d*Cq*(1+Ccut)*M.xs):=by rw [pow_add];ring
        _≤(AV*ET)*((max 1 RS)^aRows*W^(k-1))*(AS*p0*ep^(aRows+2)*d*Cq*(1+Ccut)*M.xs):=
          mul_le_mul_of_nonneg_right (mul_le_mul Hcoeff Hprod (Finset.prod_nonneg fun e _=>hrS e)
            (mul_nonneg hAV hET.le)) (by positivity)
        _=C2*M.xs*d*p0*W^(k-1):=by dsimp [C2];ring
    apply Hrest.trans
    have HC2 : C2≤C:=by dsimp [C];linarith only [hC1]
    have Hc:=mul_le_mul_of_nonneg_right HC2
      (show 0≤M.xs*d*p0*W^(k-1) by positivity)
    convert Hc using 1 <;> ring
  · obtain ⟨e,he⟩:=not_forall.mp Hupper
    have hsmallSplit : T.splitIndex (s e) (w e)<V:=not_le.mp he
    have heSite : site e=false:=Bool.eq_false_iff.mpr (fun H=>he (hsiteupper e H))
    have Hsmall : r e≤Sraw*M.xs:=by
      simp only [r,nativeSmallCutOrdinaryScale,heSite,Bool.false_eq_true,ite_false]
      have Hmass:partitionPoint 0 as (T.splitIndex (s e) (w e))≤Ccut*M.xs:=
        (partitionPoint_mono as ho hsmallSplit.le).trans hcut
      have Hscale : M.xs+partitionPoint 0 as (T.splitIndex (s e) (w e))≤(1+Ccut)*M.xs:=by nlinarith only [Hmass]
      exact (mul_le_mul_of_nonneg_left Hscale hCr.le).trans_eq (by dsimp [Sraw];ring)
    have Hp:=native_initial_radius_product_one_small site r (mul_nonneg hR.le hW.le)
      (mul_nonneg hSraw.le M.hxs.le) hr hsites hrows e heSite Hsmall
    have Hpow:=low_source_initial_coefficient_power_le hR.le (show k-1≤aRows by omega)
    have Hprod : (∏e,r e)≤Sraw*(max 1 R)^aRows*M.xs*W^(k-1):=by
      apply Hp.trans
      rw [mul_pow]
      have H:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right Hpow (pow_nonneg hW.le (k-1)))
        (mul_nonneg hSraw.le M.hxs.le)
      convert H using 1;ring
    have HR:=HH.1
    change |value|≤A*p0*d*(∏e,r e) at HR
    have Hraw : |value|≤C1*M.xs*d*p0*W^(k-1):=by
      apply HR.trans
      have H:=mul_le_mul_of_nonneg_left Hprod (mul_nonneg (mul_nonneg hA.le hp0) hd)
      convert H using 1;dsimp [C1];ring
    apply Hraw.trans
    have HC1 : C1≤C:=by dsimp [C];linarith only [hC2]
    have Hc:=mul_le_mul_of_nonneg_right HC1
      (show 0≤M.xs*d*p0*W^(k-1) by positivity)
    convert Hc using 1 <;> ring

 theorem eventually_actual_minimum_inherited_initial_word_modulus_budget_high_only
    (aDegree k rBound : ℕ) (Bclock Temp Cf Cmass Ccut Couter : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcut : 0≤Ccut) (hCouter : 0≤Couter)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U V i : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),
          U≤as.length → 0 < V → V≤U → i < V → partitionPoint 0 as V≤Ccut*M.xs →
          l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs≤x → x≤W → W≤1 → partitionPoint 0 as U≤Couter*W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e) →
        ∀a z : T.Slot,a≠z → V≤T.splitIndex a z →
        ∀g : NativeInitialInsertionWord T (k+1),
          let p0:=sourceMonomialScale x W initial
          let d:=actualLowErrorComparisonConstant Mclock Temp*
            (nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ))
          |g.coefficient*g.tree.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l t b h K)
            (g.test (nativeInitialTerminalLowDirections n U i k b h K t)
              (fun σ=>(G.canonicalHighOnlySource M forms).product σ*sitePair T a z (T.cavityAssignment σ).2)) 0|≤
            |g.coefficient| *(C*M.xs*d*p0*W^(k-1)) := by
  obtain ⟨C,hC,HC⟩:=eventually_actual_minimum_inherited_initial_atom_modulus_budget_high_only
    (D:=D) aDegree (k+1) (rBound+2*(k+1)) Bclock Temp Cf Cmass Ccut Couter hTemp hCf hCmass hCcut hCouter
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [HC] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U V i T l t hU hV0 hVU hiV hcut hl ht hT G forms initial x W hxsx hxW hW1 houter hmass a z haz htarget g
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let law:=cutFullVariance n q U l t b h K
  let P:=fun σ=>(G.canonicalHighOnlySource M forms).product σ*sitePair T a z (T.cavityAssignment σ).2
  let Mclock:=4*Cf+2*Temp
  let p0:=sourceMonomialScale x W initial
  let d:=actualLowErrorComparisonConstant Mclock Temp*
    (nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ))
  let B:=C*M.xs*d*p0*W^(k-1)
  have hW : 0 < W:=M.hxs.trans_le (hxsx.trans hxW)
  have hp0 : 0≤p0:=by
    dsimp [p0]
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos (M.hxs.trans_le hxsx) hW initial e).le
  have hd : 0≤d:=mul_nonneg (actualLowErrorComparisonConstant_nonneg Mclock hTemp)
    (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hB : 0≤B:=by
    dsimp [B]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC.le M.hxs.le) hd) hp0) (pow_nonneg hW.le _)
  change |g.coefficient*g.tree.disorderExpect (fullWeight n) (fullFeature n) 0 law
    (g.test (nativeInitialTerminalLowDirections n U i k b h K t) P) 0|≤|g.coefficient| *B
  by_cases hcoef : g.coefficient=0
  · simp only [hcoef,zero_mul,abs_zero]
    exact le_rfl
  by_cases Hsplit : g.tree.splitIndex (g.pairSlots (Fin.last k)).1 (g.pairSlots (Fin.last k)).2=i
  · by_cases Hlow : ∀e : Fin k,g.tree.splitIndex (g.pairSlots e.castSucc).1 (g.pairSlots e.castSucc).2 < U
    · have Hleaf : g.tree.leaves≤rBound+2*(k+1):=(g.leaves_le).trans (Nat.add_le_add_right hT _)
      let Gn:=g.canonicalShape G
      let site : Fin (k+1)→Bool:=Fin.cases true (fun _=>false)
      let vn : Fin (k+1)→ℝ:=Fin.cases 0 (fun _=>t)
      let sn : Fin (k+1)→ g.tree.Slot:=Fin.cases (g.embed a) (fun e=> (g.pairSlots e.castSucc).1)
      let tn : Fin (k+1)→ g.tree.Slot:=Fin.cases (g.embed z) (fun e=> (g.pairSlots e.castSucc).2)
      have Hmass e : Gn.sourceLowMass e≤Cmass*sourceFactorScale x W initial e:=by
        rw [NativeInitialInsertionWord.canonicalShape_sourceLowMass]
        exact hmass e
      have HV : ∀e,vn e∈Icc (0:ℝ) 1:=fun e=>Fin.cases (by dsimp [vn];simp) (fun _=>ht) e
      have Hne : ∀e,sn e≠tn e:=fun e=>Fin.cases
        (fun H=>haz (g.embed_preserves.1 H))
        (fun e=>g.pair_distinct_of_coefficient_ne_zero hcoef e.castSucc) e
      have Hsiteupper : ∀e,site e=true→V≤g.tree.splitIndex (sn e) (tn e):=by
        intro e
        refine Fin.cases ?_ (fun e=>?_) e
        · intro _
          dsimp only [sn,tn,Fin.cases_zero]
          rw [g.embed_preserves.2]
          exact htarget
        · intro H
          dsimp only [site,Fin.cases_succ] at H
          contradiction
      have Hrowlow : ∀e,site e=false→ g.tree.splitIndex (sn e) (tn e) < U:=by
        intro e
        refine Fin.cases ?_ (fun e=>?_) e
        · intro H
          dsimp only [site,Fin.cases_zero] at H
          contradiction
        · intro _
          exact Hlow e
      have Hnorm:=hgrid U V g.tree l t hU hV0 hVU hcut hl ht Hleaf Gn forms initial x W hxsx hxW hW1 houter Hmass
        (g.pairSlots (Fin.last k)).1 (g.pairSlots (Fin.last k)).2 (Hsplit.trans_lt hiV)
        site vn sn tn HV Hne Hsiteupper Hrowlow
      rw [Hsplit] at Hnorm
      have Hcount : (nativeInitialOrdinaryRowSet site).card=k:=native_initial_terminal_site_count k
      rw [Hcount] at Hnorm
      have Htest : g.test (nativeInitialTerminalLowDirections n U i k b h K t) P=
          nativeOldInitialRowProduct n g.tree (Gn.canonicalHighOnlySource M forms).restProduct
            (nativeSmallCutOldErrorRestKernel n U b h K)
            (g.pairSlots (Fin.last k)).1 (g.pairSlots (Fin.last k)).2
            (fun e=>nativeSmallCutOrdinaryRestKernel n U b h K (site e) (vn e)) sn tn:=by
        funext σ
        exact native_initial_terminal_word_test_eq_physical_atom_high_only n U i k b h K t T g G M forms a z Hsplit σ
      rw [Htest,abs_mul]
      exact mul_le_mul_of_nonneg_left Hnorm (abs_nonneg _)
    · obtain ⟨e,he⟩:=not_forall.mp Hlow
      rw [native_initial_terminal_word_zero_high n U i k b h K t T g P e (not_lt.mp he)]
      simp only [disorderExpect,mul_zero,Finset.sum_const_zero,abs_zero]
      exact mul_nonneg (abs_nonneg _) hB
  · rw [native_initial_terminal_word_zero_error n U i k b h K t T g P Hsplit]
    simp only [disorderExpect,mul_zero,Finset.sum_const_zero,abs_zero]
    exact mul_nonneg (abs_nonneg _) hB

 theorem eventually_actual_minimum_inherited_initial_plain_word_modulus_budget_high_only
    (aDegree k rBound : ℕ) (Bclock Temp Cf Cmass Ccut Couter : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcut : 0≤Ccut) (hCouter : 0≤Couter)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U V i : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),
          U≤as.length → 0 < V → V≤U → i < V → partitionPoint 0 as V≤Ccut*M.xs →
          l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs≤x → x≤W → W≤1 → partitionPoint 0 as U≤Couter*W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e) →
        ∀g : NativeInitialInsertionWord T (k+1),
          let p0:=sourceMonomialScale x W initial
          let d:=actualLowErrorComparisonConstant Mclock Temp*
            (nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ))
          |g.coefficient*g.tree.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l t b h K)
            (g.test (nativeInitialTerminalLowDirections n U i k b h K t)
              (G.canonicalHighOnlySource M forms).product) 0|≤
            |g.coefficient| *(C*M.xs*d*p0*W^(k-1)) := by
  obtain ⟨C,hC,HC⟩:=eventually_actual_minimum_inherited_initial_atom_modulus_budget_high_only
    (D:=D) aDegree k (rBound+2*(k+1)) Bclock Temp Cf Cmass Ccut Couter hTemp hCf hCmass hCcut hCouter
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [HC] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U V i T l t hU hV0 hVU hiV hcut hl ht hT G forms initial x W hxsx hxW hW1 houter hmass g
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let law:=cutFullVariance n q U l t b h K
  let P:=(G.canonicalHighOnlySource M forms).product
  let Mclock:=4*Cf+2*Temp
  let p0:=sourceMonomialScale x W initial
  let d:=actualLowErrorComparisonConstant Mclock Temp*
    (nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ))
  let B:=C*M.xs*d*p0*W^(k-1)
  have hW : 0 < W:=M.hxs.trans_le (hxsx.trans hxW)
  have hp0 : 0≤p0:=by
    dsimp [p0]
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos (M.hxs.trans_le hxsx) hW initial e).le
  have hd : 0≤d:=mul_nonneg (actualLowErrorComparisonConstant_nonneg Mclock hTemp)
    (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hB : 0≤B:=by
    dsimp [B]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC.le M.hxs.le) hd) hp0) (pow_nonneg hW.le _)
  change |g.coefficient*g.tree.disorderExpect (fullWeight n) (fullFeature n) 0 law
    (g.test (nativeInitialTerminalLowDirections n U i k b h K t) P) 0|≤|g.coefficient| *B
  by_cases hcoef : g.coefficient=0
  · simp only [hcoef,zero_mul,abs_zero]
    exact le_rfl
  by_cases Hsplit : g.tree.splitIndex (g.pairSlots (Fin.last k)).1 (g.pairSlots (Fin.last k)).2=i
  · by_cases Hlow : ∀e : Fin k,g.tree.splitIndex (g.pairSlots e.castSucc).1 (g.pairSlots e.castSucc).2 < U
    · have Hleaf : g.tree.leaves≤rBound+2*(k+1):=(g.leaves_le).trans (Nat.add_le_add_right hT _)
      let Gn:=g.canonicalShape G
      let site : Fin k→Bool:=fun _=>false
      let vn : Fin k→ℝ:=fun _=>t
      let sn : Fin k→ g.tree.Slot:=fun e=> (g.pairSlots e.castSucc).1
      let tn : Fin k→ g.tree.Slot:=fun e=> (g.pairSlots e.castSucc).2
      have Hmass e : Gn.sourceLowMass e≤Cmass*sourceFactorScale x W initial e:=by
        rw [NativeInitialInsertionWord.canonicalShape_sourceLowMass]
        exact hmass e
      have HV : ∀e,vn e∈Icc (0:ℝ) 1:=fun _=>ht
      have Hne : ∀e,sn e≠tn e:=fun e=>g.pair_distinct_of_coefficient_ne_zero hcoef e.castSucc
      have Hsiteupper : ∀e,site e=true→V≤g.tree.splitIndex (sn e) (tn e):=by
        intro e H
        dsimp only [site] at H
        contradiction
      have Hrowlow : ∀e,site e=false→ g.tree.splitIndex (sn e) (tn e) < U:=fun e _=>Hlow e
      have Hnorm:=hgrid U V g.tree l t hU hV0 hVU hcut hl ht Hleaf Gn forms initial x W hxsx hxW hW1 houter Hmass
        (g.pairSlots (Fin.last k)).1 (g.pairSlots (Fin.last k)).2 (Hsplit.trans_lt hiV)
        site vn sn tn HV Hne Hsiteupper Hrowlow
      rw [Hsplit] at Hnorm
      have Hcount : (nativeInitialOrdinaryRowSet site).card=k:=by
        simp only [nativeInitialOrdinaryRowSet,site,Finset.filter_true,Finset.card_univ,Fintype.card_fin]
      rw [Hcount] at Hnorm
      have Htest : g.test (nativeInitialTerminalLowDirections n U i k b h K t) P=
          nativeOldInitialRowProduct n g.tree (Gn.canonicalHighOnlySource M forms).restProduct
            (nativeSmallCutOldErrorRestKernel n U b h K)
            (g.pairSlots (Fin.last k)).1 (g.pairSlots (Fin.last k)).2
            (fun e=>nativeSmallCutOrdinaryRestKernel n U b h K (site e) (vn e)) sn tn:=by
        funext σ
        exact native_initial_terminal_word_test_eq_physical_atom_plain_high_only n U i k b h K t T g G M forms Hsplit σ
      rw [Htest,abs_mul]
      exact mul_le_mul_of_nonneg_left Hnorm (abs_nonneg _)
    · obtain ⟨e,he⟩:=not_forall.mp Hlow
      rw [native_initial_terminal_word_zero_high n U i k b h K t T g P e (not_lt.mp he)]
      simp only [disorderExpect,mul_zero,Finset.sum_const_zero,abs_zero]
      exact mul_nonneg (abs_nonneg _) hB
  · rw [native_initial_terminal_word_zero_error n U i k b h K t T g P Hsplit]
    simp only [disorderExpect,mul_zero,Finset.sum_const_zero,abs_zero]
    exact mul_nonneg (abs_nonneg _) hB

 theorem eventually_actual_minimum_inherited_initial_jet_modulus_budget_high_only
    (aDegree k rBound : ℕ) (Bclock Temp Cf Cmass Ccut Couter : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcut : 0≤Ccut) (hCouter : 0≤Couter)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U V i star : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),
          U≤as.length → 0 < V → V≤U → i < V → partitionPoint 0 as V≤Ccut*M.xs →
          l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs≤x → x≤W → W≤1 → partitionPoint 0 as U≤Couter*W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e) →
        ∀a z : T.Slot,a≠z → V≤T.splitIndex a z →
          let p0:=sourceMonomialScale x W initial
          let d:=actualLowErrorComparisonConstant Mclock Temp*
            (nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ))
          |nativeTransientLowErrorPartJet n q i star U b h K T
            (fun σ=>(G.canonicalHighOnlySource M forms).product σ*sitePair T a z (T.cavityAssignment σ).2) 0 .initial k l t|≤
            absJetVariation rBound (k+1)*(C*M.xs*d*p0*W^(k-1)) := by
  obtain ⟨C,hC,HC⟩:=eventually_actual_minimum_inherited_initial_word_modulus_budget_high_only
    (D:=D) aDegree k rBound Bclock Temp Cf Cmass Ccut Couter hTemp hCf hCmass hCcut hCouter
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [HC] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U V i star T l t hU hV0 hVU hiV hcut hl ht hT G forms initial x W hxsx hxW hW1 houter hmass a z haz htarget
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let law:=cutFullVariance n q U l t b h K
  let P:=(fun σ=>(G.canonicalHighOnlySource M forms).product σ*sitePair T a z (T.cavityAssignment σ).2)
  let Mclock:=4*Cf+2*Temp
  let p0:=sourceMonomialScale x W initial
  let d:=actualLowErrorComparisonConstant Mclock Temp*
    (nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ))
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.bf u:ℝ)≤M.bf v from M.bf_monotone hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.hf u:ℝ)≤M.hf v from M.hf_monotone hu hv huv) as ho
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.bf M.hf
    M.bf_monotone M.hf_monotone (partitionPoint_mem as ho j)
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.bf M.hf M.bf_monotone M.hf_monotone) as ho
  have hK0 j : 0≤K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HS j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HS i).1 (NNReal.coe_nonneg _))
  have hW : 0<W:=M.hxs.trans_le (hxsx.trans hxW)
  have hp0 : 0≤p0:=by
    dsimp [p0]
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos (M.hxs.trans_le hxsx) hW initial e).le
  have hd : 0≤d:=mul_nonneg (actualLowErrorComparisonConstant_nonneg Mclock hTemp)
    (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hB : 0≤C*M.xs*d*p0*W^(k-1):=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC.le M.hxs.le) hd) hp0) (pow_nonneg hW.le _)
  rw [native_initial_LOW_jet_eq_terminal_word_sum n q i star U k b h K T ho
    (fun j z=>by cases z <;> exact NNReal.coe_nonneg _)
    (fun z=>by cases z <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm P 0 hl ht]
  apply native_initial_word_sum_abs_le T ho (k+1) rBound hT _ hB
  intro g
  exact hgrid U V i T l t hU hV0 hVU hiV hcut hl ht hT G forms initial x W hxsx hxW hW1 houter hmass a z haz htarget g

 theorem eventually_actual_minimum_inherited_initial_plain_jet_modulus_budget_high_only
    (aDegree k rBound : ℕ) (Bclock Temp Cf Cmass Ccut Couter : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcut : 0≤Ccut) (hCouter : 0≤Couter)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U V i star : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),
          U≤as.length → 0 < V → V≤U → i < V → partitionPoint 0 as V≤Ccut*M.xs →
          l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs≤x → x≤W → W≤1 → partitionPoint 0 as U≤Couter*W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e) →
          let p0:=sourceMonomialScale x W initial
          let d:=actualLowErrorComparisonConstant Mclock Temp*
            (nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ))
          |nativeTransientLowErrorPartJet n q i star U b h K T
            (G.canonicalHighOnlySource M forms).product 0 .initial k l t|≤
            absJetVariation rBound (k+1)*(C*M.xs*d*p0*W^(k-1)) := by
  obtain ⟨C,hC,HC⟩:=eventually_actual_minimum_inherited_initial_plain_word_modulus_budget_high_only
    (D:=D) aDegree k rBound Bclock Temp Cf Cmass Ccut Couter hTemp hCf hCmass hCcut hCouter
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [HC] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U V i star T l t hU hV0 hVU hiV hcut hl ht hT G forms initial x W hxsx hxW hW1 houter hmass
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let law:=cutFullVariance n q U l t b h K
  let P:=(G.canonicalHighOnlySource M forms).product
  let Mclock:=4*Cf+2*Temp
  let p0:=sourceMonomialScale x W initial
  let d:=actualLowErrorComparisonConstant Mclock Temp*
    (nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ))
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.bf u:ℝ)≤M.bf v from M.bf_monotone hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.hf u:ℝ)≤M.hf v from M.hf_monotone hu hv huv) as ho
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.bf M.hf
    M.bf_monotone M.hf_monotone (partitionPoint_mem as ho j)
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.bf M.hf M.bf_monotone M.hf_monotone) as ho
  have hK0 j : 0≤K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HS j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HS i).1 (NNReal.coe_nonneg _))
  have hW : 0<W:=M.hxs.trans_le (hxsx.trans hxW)
  have hp0 : 0≤p0:=by
    dsimp [p0]
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos (M.hxs.trans_le hxsx) hW initial e).le
  have hd : 0≤d:=mul_nonneg (actualLowErrorComparisonConstant_nonneg Mclock hTemp)
    (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hB : 0≤C*M.xs*d*p0*W^(k-1):=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC.le M.hxs.le) hd) hp0) (pow_nonneg hW.le _)
  rw [native_initial_LOW_jet_eq_terminal_word_sum n q i star U k b h K T ho
    (fun j z=>by cases z <;> exact NNReal.coe_nonneg _)
    (fun z=>by cases z <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm P 0 hl ht]
  apply native_initial_word_sum_abs_le T ho (k+1) rBound hT _ hB
  intro g
  exact hgrid U V i T l t hU hV0 hVU hiV hcut hl ht hT G forms initial x W hxsx hxW hW1 houter hmass g

 theorem eventually_actual_minimum_inherited_initial_centered_LOW_modulus_budget_high_only
    (aDegree rBound : ℕ) (Bclock Temp Cf Cmass Ccut Couter : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcut : 0≤Ccut) (hCouter : 0≤Couter)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U V i star : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),
          U≤as.length → 0 < V → V≤U → i < V → partitionPoint 0 as V≤Ccut*M.xs →
          l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs≤x → x≤W → W≤1 → partitionPoint 0 as U≤Couter*W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e) →
        ∀a z : T.Slot,a≠z → V≤T.splitIndex a z →
          let p0:=sourceMonomialScale x W initial
          let d:=actualLowErrorComparisonConstant Mclock Temp*
            (nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ))
          |nativeTransientCenteredLowErrorPart n q i star U b h K T
            (G.canonicalHighOnlySource M forms).restProduct (sitePair T a z) 0 .initial l t|≤
            C*W*M.xs*d*p0 := by
  obtain ⟨Cp0,hCp0,HP0⟩:=eventually_actual_minimum_inherited_initial_plain_jet_modulus_budget_high_only
    (D:=D) aDegree 0 rBound Bclock Temp Cf Cmass Ccut Couter hTemp hCf hCmass hCcut hCouter
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cp1,hCp1,HP1⟩:=eventually_actual_minimum_inherited_initial_plain_jet_modulus_budget_high_only
    (D:=D) aDegree 1 rBound Bclock Temp Cf Cmass Ccut Couter hTemp hCf hCmass hCcut hCouter
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cp2,hCp2,HP2⟩:=eventually_actual_minimum_inherited_initial_plain_jet_modulus_budget_high_only
    (D:=D) aDegree 2 rBound Bclock Temp Cf Cmass Ccut Couter hTemp hCf hCmass hCcut hCouter
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cp3,hCp3,HP3⟩:=eventually_actual_minimum_inherited_initial_plain_jet_modulus_budget_high_only
    (D:=D) aDegree 3 rBound Bclock Temp Cf Cmass Ccut Couter hTemp hCf hCmass hCcut hCouter
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨CJ2,hCJ2,HJ2⟩:=eventually_actual_minimum_inherited_initial_jet_modulus_budget_high_only
    (D:=D) aDegree 2 rBound Bclock Temp Cf Cmass Ccut Couter hTemp hCf hCmass hCcut hCouter
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨CJ3,hCJ3,HJ3⟩:=eventually_actual_minimum_inherited_initial_jet_modulus_budget_high_only
    (D:=D) aDegree 3 rBound Bclock Temp Cf Cmass Ccut Couter hTemp hCf hCmass hCcut hCouter
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Ck,hCk,HG⟩:=eventually_actual_minimum_inherited_original_scalar_low_jets_high_only
    (D:=D) rBound Bclock Temp Cf Couter hTemp hCf hCouter hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cp:=Cp0+Cp1+Cp2+Cp3+CJ2+CJ3+1
  have hCp : 0<Cp:=by dsimp [Cp];positivity
  let A : Fin 4→ℝ:=fun j=>absJetVariation rBound (j+1)*Cp
  let B : Fin 4→ℝ:=fun j=>jetVariation rBound j*Ck^(j:ℕ)
  have hA j : 0≤A j:=mul_nonneg (absJetVariation_nonneg _ _) hCp.le
  have hB j : 0≤B j:=mul_nonneg (jetVariation_nonneg _ _) (pow_nonneg hCk.le _)
  let c3:=A 3+B 0*A 3+3*B 1*A 2+3*B 2*A 1+B 3*A 0
  let c2:=A 2+B 0*A 2+2*B 1*A 1+B 2*A 0
  let C:=c3+3*c2+1
  have hc3 : 0≤c3:=native_centered_LOW_third_coefficient_nonneg hA hB
  have hc2 : 0≤c2:=native_centered_LOW_second_coefficient_nonneg hA hB
  have hC : 0<C:=by dsimp [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [HP0,HP1,HP2,HP3,HJ2,HJ3,HG] with n hn0 hn1 hn2 hn3 hnJ2 hnJ3 hng
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn0 M hs0 hsxs hsource hxs L us hus hret hmesh,hn1 M hs0 hsxs hsource hxs L us hus hret hmesh,
    hn2 M hs0 hsxs hsource hxs L us hus hret hmesh,hn3 M hs0 hsxs hsource hxs L us hus hret hmesh,
    hnJ2 M hs0 hsxs hsource hxs L us hus hret hmesh,hnJ3 M hs0 hsxs hsource hxs L us hus hret hmesh]
    with jGrid hgrid0 hgrid1 hgrid2 hgrid3 hgridJ2 hgridJ3
  dsimp only at hgrid0 hgrid1 hgrid2 hgrid3 hgridJ2 hgridJ3 ⊢
  intro U V i star T l t hU hV0 hVU hiV hcut hl ht hT G forms initial x W hxsx hxW hW1 houter hmass a z haz htarget
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let P:=(G.canonicalHighOnlySource M forms).product
  let Z:=sourceMonomialScale x W initial
  let Mclock:=4*Cf+2*Temp
  let d:=actualLowErrorComparisonConstant Mclock Temp*
    (nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ))
  let f : Fin 4→ℝ:=fun j=>nativeTransientLowErrorPartJet n q i star U b h K T P 0 .initial j l t
  let g : Fin 4→ℝ:=fun j=>cutLowJet n q U b h K T
    (fun σ=>sitePair T a z (T.cavityAssignment σ).2) (cavityEmbed 0) j l 0
  let J:=fun j=>nativeTransientLowErrorPartJet n q i star U b h K T
    (fun σ=>P σ*sitePair T a z (T.cavityAssignment σ).2) 0 .initial j l t
  have hW : 0<W:=M.hxs.trans_le (hxsx.trans hxW)
  have hZ : 0≤Z:=by
    dsimp [Z]
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos (M.hxs.trans_le hxsx) hW initial e).le
  have hd : 0≤d:=mul_nonneg (actualLowErrorComparisonConstant_nonneg Mclock hTemp)
    (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have Hcap (a : ℝ) (ha : a≤Cp) (k : ℕ) :
      absJetVariation rBound (k+1)*(a*M.xs*d*Z*W^(k-1))≤
        (absJetVariation rBound (k+1)*Cp)*W^(k-1)*Z*M.xs*d := by
    have H:=mul_le_mul_of_nonneg_left ha
      (mul_nonneg (absJetVariation_nonneg rBound (k+1))
        (mul_nonneg (mul_nonneg (mul_nonneg M.hxs.le hd) hZ) (pow_nonneg hW.le (k-1))))
    convert H using 1 <;> ring
  have Hf0:=hgrid0 U V i star T l t hU hV0 hVU hiV hcut hl ht hT G forms initial x W hxsx hxW hW1 houter hmass
  have Hf0' : |f 0|≤A 0*W^(0-1)*Z*M.xs*d:=by
    apply Hf0.trans
    exact Hcap Cp0 (by dsimp [Cp];linarith only [hCp0,hCp1,hCp2,hCp3,hCJ2,hCJ3]) 0
  have Hf1:=hgrid1 U V i star T l t hU hV0 hVU hiV hcut hl ht hT G forms initial x W hxsx hxW hW1 houter hmass
  have Hf1' : |f 1|≤A 1*W^(1-1)*Z*M.xs*d:=by
    apply Hf1.trans
    exact Hcap Cp1 (by dsimp [Cp];linarith only [hCp0,hCp1,hCp2,hCp3,hCJ2,hCJ3]) 1
  have Hf2:=hgrid2 U V i star T l t hU hV0 hVU hiV hcut hl ht hT G forms initial x W hxsx hxW hW1 houter hmass
  have Hf2' : |f 2|≤A 2*W^(2-1)*Z*M.xs*d:=by
    apply Hf2.trans
    exact Hcap Cp2 (by dsimp [Cp];linarith only [hCp0,hCp1,hCp2,hCp3,hCJ2,hCJ3]) 2
  have Hf3:=hgrid3 U V i star T l t hU hV0 hVU hiV hcut hl ht hT G forms initial x W hxsx hxW hW1 houter hmass
  have Hf3' : |f 3|≤A 3*W^(3-1)*Z*M.xs*d:=by
    apply Hf3.trans
    exact Hcap Cp3 (by dsimp [Cp];linarith only [hCp0,hCp1,hCp2,hCp3,hCJ2,hCJ3]) 3
  have hf j : |f j|≤A j*W^((j:ℕ)-1)*Z*M.xs*d:=by
    fin_cases j
    · exact Hf0'
    · exact Hf1'
    · exact Hf2'
    · exact Hf3'
  have hg j : |g j|≤B j*W^(j:ℕ):=by
    have H:=hng M hs0 hsxs hsource us jGrid hus U T W l (hxsx.trans hxW) houter hl hT a z (j:ℕ)
    convert H using 1
    dsimp [g,B]
    rw [mul_pow]
    ring
  have HJ2:=hgridJ2 U V i star T l t hU hV0 hVU hiV hcut hl ht hT G forms initial x W hxsx hxW hW1 houter hmass a z haz htarget
  have HJ2' : |J 2|≤A 2*W^(2-1)*Z*M.xs*d:=by
    apply HJ2.trans
    exact Hcap CJ2 (by dsimp [Cp];linarith only [hCp0,hCp1,hCp2,hCp3,hCJ2,hCJ3]) 2
  have HJ3:=hgridJ3 U V i star T l t hU hV0 hVU hiV hcut hl ht hT G forms initial x W hxsx hxW hW1 houter hmass a z haz htarget
  have HJ3' : |J 3|≤A 3*W^(3-1)*Z*M.xs*d:=by
    apply HJ3.trans
    exact Hcap CJ3 (by dsimp [Cp];linarith only [hCp0,hCp1,hCp2,hCp3,hCJ2,hCJ3]) 3
  have H:=native_centered_initial_LOW_modulus_product_bound hW hW1 hZ M.hxs.le hd hl
    A B f g (J 2) (J 3) hA hB (by simpa only [Nat.reduceSub,pow_one] using HJ2')
    (by simpa only [Nat.reduceSub] using HJ3') hf hg
  have Hleft : nativeTransientCenteredLowErrorPart n q i star U b h K T
      (G.canonicalHighOnlySource M forms).restProduct (sitePair T a z) 0 .initial l t=
      l*(J 3-productJet3 g f 3)+3*(J 2-productJet3 g f 2) := by
    dsimp only [nativeTransientCenteredLowErrorPart,J,f,g]
    simp_rw [←(G.canonicalHighOnlySource M forms).product_eq_restProduct]
    simp only [map_zero,P]
  rw [Hleft]
  apply H.trans
  have HC : c3+3*c2≤C:=by dsimp [C];linarith
  have Hcap:=mul_le_mul_of_nonneg_right HC (show 0≤W*Z*M.xs*d from mul_nonneg (mul_nonneg (mul_nonneg hW.le hZ) M.hxs.le) hd)
  convert Hcap using 1 <;> ring

end OAI.SKFluctuations.Cavity
