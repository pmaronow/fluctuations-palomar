module

public import ComparisonNativeBroadLocalDiameter

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 4400000
attribute [local instance] Classical.propDecidable

abbrev nativeNegativeSet (m : NativeBandModel) : Set ℝ :=
  Ioo (0:ℝ) 1 ∩ m.H ⁻¹' Iio 0

theorem nativeNegativeSet_open (m : NativeBandModel) : IsOpen (nativeNegativeSet m) := by
  have hc : ContinuousOn m.H (Icc (0:ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using m.hH.continuousOn
  exact (hc.mono Ioo_subset_Icc_self).isOpen_inter_preimage isOpen_Ioo isOpen_Iio

theorem nativeNegativeSet_subset (m : NativeBandModel) : nativeNegativeSet m⊆Icc (0:ℝ) 1 :=
  inter_subset_left.trans Ioo_subset_Icc_self

theorem actual_native_negative_component_endpoints (m : NativeBandModel) {r : ℝ}
    (hr : r∈nativeNegativeSet m) (hshort : nativeCapTravel m<1) :
    let C := ordConnectedComponent (nativeNegativeSet m) r
    ∃c : NativeActualCapInterval m,c.a=sInf C ∧ c.z=sSup C ∧ Ioo c.a c.z=C ∧
      ((m.H c.a=0 ∧ m.H c.z=0) ∨ (c.a=0 ∧ m.H c.z=0) ∨ (m.H c.a=0 ∧ c.z=1)) := by
  dsimp only
  let C := ordConnectedComponent (nativeNegativeSet m) r
  have hp := wholeCap_component_endpoints (nativeNegativeSet_open m) (nativeNegativeSet_subset m) hr
  have hC : C=Ioo (sInf C) (sSup C) := hp.2.2.2.2.1
  have hnon : C.Nonempty := nonempty_ordConnectedComponent.mpr hr
  have hsub : C⊆Icc (0:ℝ) 1 := ordConnectedComponent_subset.trans (nativeNegativeSet_subset m)
  have hclosed : IsClosed (Icc (0:ℝ) 1 ∩ m.H ⁻¹' Iic 0) :=
    (show ContinuousOn m.H (Icc (0:ℝ) 1) by
      simpa only [uIcc_of_le zero_le_one] using m.hH.continuousOn).preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_Iic
  have hCsub : C⊆Icc (0:ℝ) 1 ∩ m.H ⁻¹' Iic 0 := by
    intro t ht
    have hh := (ordConnectedComponent_subset ht).2
    change m.H t<0 at hh
    exact ⟨hsub ht,hh.le⟩
  have hlo : BddBelow C := ⟨0,fun t ht=>(hsub ht).1⟩
  have hhi : BddAbove C := ⟨1,fun t ht=>(hsub ht).2⟩
  have hleft0 : m.H (sInf C)≤0 :=
    (hclosed.closure_subset_iff.mpr hCsub (csInf_mem_closure hnon hlo)).2
  have hright0 : m.H (sSup C)≤0 :=
    (hclosed.closure_subset_iff.mpr hCsub (csSup_mem_closure hnon hhi)).2
  have hleft : m.H (sInf C)=0 ∨ sInf C=0 := by
    by_cases ha:sInf C=0
    · exact Or.inr ha
    · apply Or.inl
      apply le_antisymm hleft0
      by_contra hbad
      have ht : sInf C∈nativeNegativeSet m :=
        ⟨⟨lt_of_le_of_ne hp.1 (fun he=>ha he.symm),(hp.2.1.trans hp.2.2.1).trans_le hp.2.2.2.1⟩,lt_of_not_ge hbad⟩
      exact hp.2.2.2.2.2.1 ht
  have hright : m.H (sSup C)=0 ∨ sSup C=1 := by
    by_cases hz:sSup C=1
    · exact Or.inr hz
    · apply Or.inl
      apply le_antisymm hright0
      by_contra hbad
      have ht : sSup C∈nativeNegativeSet m :=
        ⟨⟨hp.1.trans_lt (hp.2.1.trans hp.2.2.1),lt_of_le_of_ne hp.2.2.2.1 hz⟩,lt_of_not_ge hbad⟩
      exact hp.2.2.2.2.2.2 ht
  let c : NativeActualCapInterval m := {
    a := sInf C
    z := sSup C
    ha := hp.1
    haz := hp.2.1.trans hp.2.2.1
    hz := hp.2.2.2.1
    negative := fun t ht=>(ordConnectedComponent_subset (hC.symm ▸ ht)).2 }
  refine ⟨c,rfl,rfl,hC.symm,?_⟩
  rcases hleft with ha|ha
  · rcases hright with hz|hz
    · exact Or.inl ⟨ha,hz⟩
    · exact Or.inr (Or.inr ⟨ha,hz⟩)
  · rcases hright with hz|hz
    · exact Or.inr (Or.inl ⟨ha,hz⟩)
    · have ht := actual_native_cap_travel m c
      change sSup C-sInf C≤ nativeCapTravel m at ht
      rw [ha,hz] at ht
      norm_num at ht
      exact False.elim (hshort.not_ge ht)

theorem native_mass_slice_quantile_mem (m : NativeBandModel) {l r u : ℝ}
    (hl : l∈Icc (0:ℝ) 1) (hr : r∈Icc (0:ℝ) 1) (hu : u∈Icc (0:ℝ) 1) :
    m.R u∈nativeBroadMassSlice m.hc m.hk m.hkc m.hm m.hM m.alpha l r ↔ u∈Ioo l r := by
  have hs := comparisonSweepQuantile_strictMono_native_geometry m.hc m.hk m.hkc m.hm m.hM m.alpha
  change (m.R l< m.R u ∧ m.R u< m.R r) ↔ (l< u ∧ u< r)
  constructor
  · intro h
    exact ⟨lt_of_not_ge (fun he=>h.1.not_ge ((comparisonSweepQuantile_monotone
      m.hc m.hk m.hkc m.hm m.hM m.alpha) he)),lt_of_not_ge (fun he=>h.2.not_ge
      ((comparisonSweepQuantile_monotone m.hc m.hk m.hkc m.hm m.hM m.alpha) he))⟩
  · exact fun h=>⟨hs hl hu h.1,hs hu hr h.2⟩

theorem native_mass_slice_profile_mem (m : NativeBandModel) {l r t : ℝ}
    (hl : l∈Icc (0:ℝ) 1) (hr : r∈Icc (0:ℝ) 1)
    (ht : t∈nativeBroadMassSlice m.hc m.hk m.hkc m.hm m.hM m.alpha l r) :
    m.alpha.val.val t∈Ioo l r := by
  have hlR := comparisonSweepQuantile_bounds m.hc m.hk m.hkc m.hm m.hM m.alpha l
  have hrR := comparisonSweepQuantile_bounds m.hc m.hk m.hkc m.hm m.hM m.alpha r
  have ht01 : t∈Icc (0:ℝ) 1 := ⟨hlR.1.trans ht.1.le,ht.2.le.trans hrR.2⟩
  have hs := inverseConstraint_strictMonoOn m.hc m.hk m.hkc m.alpha.property
  have hlow := hs hlR ht01 ht.1
  have hupp := hs ht01 hrR ht.2
  rw [comparisonSweepQuantile_spec m.hc m.hk m.hkc m.hm m.hM m.alpha hl] at hlow
  rw [comparisonSweepQuantile_spec m.hc m.hk m.hkc m.hm m.hM m.alpha hr] at hupp
  exact ⟨hlow,hupp⟩

structure NativeWholeCapBroadSampler (m : NativeBandModel) (c : NativeActualCapInterval m) where
  k : ℕ
  j : ℕ
  hnear : nativeDyadicMass m.U k≤ max (m.alpha.val.val c.a) m.U
  hnearNext : max (m.alpha.val.val c.a) m.U< nativeDyadicMass m.U (k+1)
  hright : nativeDyadicMass m.U j≤ m.alpha.val.val c.z
  hrightNext : m.alpha.val.val c.z< nativeDyadicMass m.U (j+1)
  hgap : k+3≤ j

namespace NativeWholeCapBroadSampler

abbrev count {m : NativeBandModel} {c : NativeActualCapInterval m} (f : NativeWholeCapBroadSampler m c) :=
  nativeBroadSliceCount f.k f.j

abbrev node {m : NativeBandModel} {c : NativeActualCapInterval m} (f : NativeWholeCapBroadSampler m c) :=
  nativeBroadSliceNode m.U (max (m.alpha.val.val c.a) m.U) (m.alpha.val.val c.z) f.k f.j

abbrev scale {m : NativeBandModel} {c : NativeActualCapInterval m} (f : NativeWholeCapBroadSampler m c)
    (i : Fin f.count) := nativeBroadSliceScale m.U f.k f.j i

abbrev slice {m : NativeBandModel} {c : NativeActualCapInterval m} (f : NativeWholeCapBroadSampler m c)
    (i : Fin f.count) := nativeBroadMassSlice m.hc m.hk m.hkc m.hm m.hM m.alpha (f.node i.val) (f.node (i.val+1))

theorem geometry {m : NativeBandModel} {c : NativeActualCapInterval m}
    (f : NativeWholeCapBroadSampler m c) (i : Fin f.count) :
    m.U≤ f.scale i ∧ f.scale i≤ f.node (i.val+1)-f.node i.val ∧
    f.scale i/2≤ f.node i.val ∧ f.node (i.val+1)≤4*f.scale i ∧
    max (m.alpha.val.val c.a) m.U≤ f.node i.val ∧ f.node (i.val+1)≤ m.alpha.val.val c.z ∧
    f.node i.val< f.node (i.val+1) :=
  nativeBroadSlice_geometry m.hU f.hnear f.hnearNext f.hright f.hrightNext f.hgap i

theorem nodes_mem {m : NativeBandModel} {c : NativeActualCapInterval m}
    (f : NativeWholeCapBroadSampler m c) (i : Fin f.count) :
    f.node i.val∈Icc (0:ℝ) 1 ∧ f.node (i.val+1)∈Icc (0:ℝ) 1 := by
  have hg := f.geometry i
  have hv : 0< f.scale i := m.hU.trans_le hg.1
  have hB := (m.alpha.val.property.1 c.z).2
  exact ⟨⟨by linarith [hg.2.2.1],hg.2.2.2.2.2.2.le.trans (hg.2.2.2.2.2.1.trans hB)⟩,
    ⟨by linarith [hg.2.1,hg.2.2.1],hg.2.2.2.2.2.1.trans hB⟩⟩

theorem contracts {m : NativeBandModel} {c : NativeActualCapInterval m}
    (f : NativeWholeCapBroadSampler m c) (i : Fin f.count) :
    m.U≤ f.scale i ∧ f.node (i.val+1)∈Icc (0:ℝ) 1 ∧ f.node (i.val+1)≤4*f.scale i ∧
    f.slice i⊆Ioo c.a c.z ∧
    (∀t∈f.slice i,m.alpha.val.val t≤ f.node (i.val+1)) ∧
    f.scale i≤∫t in f.slice i,deriv m.alpha.val.val t := by
  have hg := f.geometry i
  have hn := f.nodes_mem i
  refine ⟨hg.1,hn.2,hg.2.2.2.1,?_,?_,?_⟩
  · exact nativeBroadMassSlice_subset_cap m.hc m.hk m.hkc m.hm m.hM m.alpha
      ⟨c.ha,c.haz.le.trans c.hz⟩ ⟨c.ha.trans c.haz.le,c.hz⟩
      ((le_max_left _ _).trans hg.2.2.2.2.1) hg.2.2.2.2.2.1
  · exact fun t ht=>nativeBroadMassSlice_mass_ceiling m.hc m.hk m.hkc m.hm m.hM m.alpha hn.2 ht
  · rw [nativeBroadMassSlice_mass m.hc m.hk m.hkc m.hm m.hM m.alpha hn.1 hn.2 hg.2.2.2.2.2.2]
    exact hg.2.1

theorem disjoint {m : NativeBandModel} {c : NativeActualCapInterval m}
    (f : NativeWholeCapBroadSampler m c) : Pairwise (fun i j=>Disjoint (f.slice i) (f.slice j)) := by
  have hd := nativeBroadSlice_pairwise_disjoint m.hU f.hnear f.hnearNext f.hright f.hrightNext f.hgap
  intro i j hij
  apply Set.disjoint_left.mpr
  intro t hi hj
  have hmi := native_mass_slice_profile_mem m (f.nodes_mem i).1 (f.nodes_mem i).2 hi
  have hmj := native_mass_slice_profile_mem m (f.nodes_mem j).1 (f.nodes_mem j).2 hj
  exact Set.disjoint_left.mp (hd hij) ⟨hmi.1,hmi.2.le⟩ ⟨hmj.1,hmj.2.le⟩

theorem actual_cover_ae {m : NativeBandModel} {c : NativeActualCapInterval m}
    (f : NativeWholeCapBroadSampler m c) :
    ∀ᵐ u∂volume.restrict (Icc (0:ℝ) 1),m.R u∈Ioo c.a c.z→
      m.R u∈nativeBroadNearZero m ∨ ∃i:Fin f.count,m.R u∈f.slice i := by
  have hfinite : (Set.range (fun i:Fin f.count=>f.node (i.val+1))).Countable :=
    (Set.finite_range _).countable
  filter_upwards [ae_restrict_mem measurableSet_Icc,hfinite.ae_notMem (volume.restrict (Icc (0:ℝ) 1))]
    with u hu hcuts hcap
  have hr01 : m.R u∈Icc (0:ℝ) 1 := comparisonSweepQuantile_bounds m.hc m.hk m.hkc m.hm m.hM m.alpha u
  have hs := inverseConstraint_strictMonoOn m.hc m.hk m.hkc m.alpha.property
  have hA := hs ⟨c.ha,c.haz.le.trans c.hz⟩ hr01 hcap.1
  have hB := hs hr01 ⟨c.ha.trans c.haz.le,c.hz⟩ hcap.2
  rw [comparisonSweepQuantile_spec m.hc m.hk m.hkc m.hm m.hM m.alpha hu] at hA hB
  by_cases hlow:u≤ m.U
  · apply Or.inl
    apply (native_mass_slice_quantile_mem m (by norm_num)
      ⟨lt_min (mul_pos (by norm_num) m.hU) zero_lt_one |>.le,min_le_right _ _⟩ hu).mpr
    have hu0 : 0< u := (m.alpha.val.property.1 c.a).1.trans_lt hA
    have hu1 : u<1 := hB.trans_le (m.alpha.val.property.1 c.z).2
    exact ⟨hu0,lt_min (by linarith [m.hU]) hu1⟩
  · have hret : u∈Ioc (max (m.alpha.val.val c.a) m.U) (m.alpha.val.val c.z) :=
      ⟨max_lt hA (lt_of_not_ge hlow),hB.le⟩
    obtain ⟨i,hi⟩ := nativeBroadSlice_cover m.U (max (m.alpha.val.val c.a) m.U)
      (m.alpha.val.val c.z) f.hgap hret
    apply Or.inr
    refine ⟨i,(native_mass_slice_quantile_mem m (f.nodes_mem i).1 (f.nodes_mem i).2 hu).mpr ⟨hi.1,?_⟩⟩
    exact lt_of_le_of_ne hi.2 (fun he=>hcuts ⟨i,he.symm⟩)

end NativeWholeCapBroadSampler

theorem exists_actual_native_whole_cap_broad_sampler (m : NativeBandModel)
    (c : NativeActualCapInterval m)
    (hbroad : 8*max (m.alpha.val.val c.a) m.U< m.alpha.val.val c.z) :
    Nonempty (NativeWholeCapBroadSampler m c) := by
  obtain ⟨k,hk,hk1⟩ := nativeDyadicMass_exists_near m.hU (le_max_right (m.alpha.val.val c.a) m.U)
  have hUmax : m.U≤ m.alpha.val.val c.z := by
    have hh := le_max_right (m.alpha.val.val c.a) m.U
    have hp := m.hU
    linarith
  obtain ⟨j,hj,hj1⟩ := nativeDyadicMass_exists_near m.hU hUmax
  exact ⟨⟨k,j,hk,hk1,hj,hj1,native_broad_dyadic_index_gap m.hU hk hj1 hbroad⟩⟩

theorem actual_native_whole_cap_dyadic_classification (m : NativeBandModel)
    (c : NativeActualCapInterval m) :
    m.alpha.val.val c.z≤8*m.U ∨
      (∃k:ℕ,m.U≤ nativeDyadicMass m.U k ∧ nativeDyadicMass m.U k≤ m.alpha.val.val c.a ∧
        m.alpha.val.val c.z≤16*nativeDyadicMass m.U k ∧
        16*nativeDyadicMass m.U k+m.U≤32*(nativeDyadicMass m.U k/2+m.U)) ∨
      Nonempty (NativeWholeCapBroadSampler m c) := by
  by_cases hb:8*max (m.alpha.val.val c.a) m.U< m.alpha.val.val c.z
  · exact Or.inr (Or.inr (exists_actual_native_whole_cap_broad_sampler m c hb))
  · have hb' := le_of_not_gt hb
    by_cases ha:m.alpha.val.val c.a< m.U
    · exact Or.inl (by rw [max_eq_right ha.le] at hb';exact hb')
    · have hUA := le_of_not_gt ha
      have hB : m.alpha.val.val c.z≤8*m.alpha.val.val c.a := by
        rw [max_eq_left hUA] at hb';exact hb'
      obtain ⟨k,hk,hk1⟩ := nativeDyadicMass_exists_near m.hU hUA
      exact Or.inr (Or.inl ⟨k,native_comparable_cap_dyadic_enlargement m.hU hUA hB hk hk1⟩)

abbrev nativeBroadCapIndex {ι : Type*} (m : NativeBandModel) (c : ι→NativeActualCapInterval m) :=
  {i:ι // 8*max (m.alpha.val.val (c i).a) m.U< m.alpha.val.val (c i).z}

def nativeActualBroadCapSampler {ι : Type*} (m : NativeBandModel) (c : ι→NativeActualCapInterval m)
    (i : nativeBroadCapIndex m c) : NativeWholeCapBroadSampler m (c i.val) :=
  Classical.choice (exists_actual_native_whole_cap_broad_sampler m (c i.val) i.property)

abbrev nativeActualBroadSliceIndex {ι : Type*} (m : NativeBandModel) (c : ι→NativeActualCapInterval m) :=
  Σi:nativeBroadCapIndex m c,Fin (nativeActualBroadCapSampler m c i).count

abbrev nativeActualBroadSlice {ι : Type*} (m : NativeBandModel) (c : ι→NativeActualCapInterval m)
    (p : nativeActualBroadSliceIndex m c) : Set ℝ := (nativeActualBroadCapSampler m c p.1).slice p.2

abbrev nativeActualComparableCapUnion {ι : Type*} (m : NativeBandModel) (c : ι→NativeActualCapInterval m) : Set ℝ :=
  ⋃i:{i:ι // ¬8*max (m.alpha.val.val (c i).a) m.U< m.alpha.val.val (c i).z ∧
    8*m.U< m.alpha.val.val (c i).z},Ioo (c i.val).a (c i.val).z

theorem nativeActualBroadSlice_disjoint {ι : Type*} [Fintype ι]
    (m : NativeBandModel) (c : ι→NativeActualCapInterval m)
    (hd : Pairwise (fun i j=>Disjoint (Ioo (c i).a (c i).z) (Ioo (c j).a (c j).z))) :
    Pairwise (fun p q:nativeActualBroadSliceIndex m c=>
      Disjoint (nativeActualBroadSlice m c p) (nativeActualBroadSlice m c q)) := by
  rintro ⟨i,p⟩ ⟨j,q⟩ hpq
  by_cases hij:i=j
  · subst j
    apply (nativeActualBroadCapSampler m c i).disjoint
    intro he
    apply hpq
    cases he
    rfl
  · have hval : i.val≠j.val := fun he=>hij (Subtype.ext he)
    exact (hd hval).mono
      ((nativeActualBroadCapSampler m c i).contracts p).2.2.2.1
      ((nativeActualBroadCapSampler m c j).contracts q).2.2.2.1

theorem nativeActualBroadSlice_card_le_inv_U {ι : Type*} [Fintype ι]
    (m : NativeBandModel) (c : ι→NativeActualCapInterval m)
    (hd : Pairwise (fun i j=>Disjoint (Ioo (c i).a (c i).z) (Ioo (c j).a (c j).z))) :
    (Fintype.card (nativeActualBroadSliceIndex m c):ℝ)≤1/m.U := by
  let A := nativeActualBroadSlice m c
  have hi := (native_inverse_derivative_unit_mass m).1
  have hsub (p:nativeActualBroadSliceIndex m c) : A p⊆Icc (0:ℝ) 1 :=
    ((nativeActualBroadCapSampler m c p.1).contracts p.2).2.2.2.1.trans
      (Ioo_subset_Icc_self.trans (Icc_subset_Icc (c p.1.val).ha (c p.1.val).hz))
  have hdisjoint := nativeActualBroadSlice_disjoint m c hd
  have hsum : (∑p:nativeActualBroadSliceIndex m c,∫r in A p,deriv m.alpha.val.val r)≤1 := by
    have heq : (∫r in ⋃p,A p,deriv m.alpha.val.val r)=
        ∑p:nativeActualBroadSliceIndex m c,∫r in A p,deriv m.alpha.val.val r :=
      integral_iUnion_fintype (s:=A) (fun _=>measurableSet_Ioo) hdisjoint (fun p=>hi.mono_set (hsub p))
    rw [←heq]
    have hb := setIntegral_mono_set hi (ae_of_all _ (fun r=>m.alpha.val.property.2.deriv_nonneg))
      (ae_of_all _ (fun r hr=>by obtain ⟨p,hp⟩:=mem_iUnion.mp hr;exact hsub p hp))
    exact hb.trans_eq (native_inverse_derivative_unit_mass m).2
  have hsmall (p:nativeActualBroadSliceIndex m c) : m.U≤∫r in A p,deriv m.alpha.val.val r :=
    ((nativeActualBroadCapSampler m c p.1).contracts p.2).1.trans
      ((nativeActualBroadCapSampler m c p.1).contracts p.2).2.2.2.2.2
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun p _=>hsmall p)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hs
  exact (le_div_iff₀ m.hU).mpr (hs.trans hsum)

theorem nativeActualSmallCap_near_zero (m : NativeBandModel) (c : NativeActualCapInterval m)
    (hsmall : m.alpha.val.val c.z≤8*m.U) {u:ℝ} (hu:u∈Icc (0:ℝ) 1)
    (hcap : m.R u∈Ioo c.a c.z) : m.R u∈nativeBroadNearZero m := by
  have hr01 := comparisonSweepQuantile_bounds m.hc m.hk m.hkc m.hm m.hM m.alpha u
  have hs := inverseConstraint_strictMonoOn m.hc m.hk m.hkc m.alpha.property
  have hA := hs ⟨c.ha,c.haz.le.trans c.hz⟩ hr01 hcap.1
  have hB := hs hr01 ⟨c.ha.trans c.haz.le,c.hz⟩ hcap.2
  rw [comparisonSweepQuantile_spec m.hc m.hk m.hkc m.hm m.hM m.alpha hu] at hA hB
  apply (native_mass_slice_quantile_mem m (by norm_num)
    ⟨lt_min (mul_pos (by norm_num) m.hU) zero_lt_one |>.le,min_le_right _ _⟩ hu).mpr
  exact ⟨(m.alpha.val.property.1 c.a).1.trans_lt hA,
    lt_min (hB.trans_le hsmall) (hB.trans_le (m.alpha.val.property.1 c.z).2)⟩

theorem actual_native_finite_cap_cover_ae {ι : Type*} [Fintype ι]
    (m : NativeBandModel) (c : ι→NativeActualCapInterval m) :
    ∀ᵐ u∂volume.restrict (Icc (0:ℝ) 1),m.R u∈⋃i,Ioo (c i).a (c i).z→
      m.R u∈nativeBroadNearZero m ∨ m.R u∈nativeActualComparableCapUnion m c ∨
      ∃p:nativeActualBroadSliceIndex m c,m.R u∈nativeActualBroadSlice m c p := by
  have hae : ∀ᵐ u∂volume.restrict (Icc (0:ℝ) 1),∀i:nativeBroadCapIndex m c,
      m.R u∈Ioo (c i.val).a (c i.val).z→
      m.R u∈nativeBroadNearZero m ∨ ∃j,m.R u∈(nativeActualBroadCapSampler m c i).slice j :=
    ae_all_iff.mpr (fun i=>(nativeActualBroadCapSampler m c i).actual_cover_ae)
  filter_upwards [ae_restrict_mem measurableSet_Icc,hae] with u hu hcover hcap
  obtain ⟨i,hi⟩ := mem_iUnion.mp hcap
  by_cases hb:8*max (m.alpha.val.val (c i).a) m.U< m.alpha.val.val (c i).z
  · rcases hcover ⟨i,hb⟩ hi with hl|⟨j,hj⟩
    · exact Or.inl hl
    · exact Or.inr (Or.inr ⟨⟨⟨i,hb⟩,j⟩,hj⟩)
  · by_cases hs:m.alpha.val.val (c i).z≤8*m.U
    · exact Or.inl (nativeActualSmallCap_near_zero m (c i) hs hu hi)
    · exact Or.inr (Or.inl (mem_iUnion.mpr ⟨⟨i,hb,lt_of_not_ge hs⟩,hi⟩))

theorem actual_native_comparable_cap_enlargement {ι : Type*} (m : NativeBandModel)
    (c : ι→NativeActualCapInterval m)
    (i : {i:ι // ¬8*max (m.alpha.val.val (c i).a) m.U< m.alpha.val.val (c i).z ∧
      8*m.U< m.alpha.val.val (c i).z}) :
    ∃k:ℕ,m.U≤ nativeDyadicMass m.U k ∧ nativeDyadicMass m.U k≤ m.alpha.val.val (c i.val).a ∧
      m.alpha.val.val (c i.val).z≤16*nativeDyadicMass m.U k ∧
      16*nativeDyadicMass m.U k+m.U≤32*(nativeDyadicMass m.U k/2+m.U) := by
  have hb := le_of_not_gt i.property.1
  have hA : m.U≤ m.alpha.val.val (c i.val).a := by
    by_contra ha
    have hh := le_of_not_ge ha
    rw [max_eq_right hh] at hb
    exact i.property.2.not_ge hb
  rw [max_eq_left hA] at hb
  obtain ⟨k,hk,hk1⟩ := nativeDyadicMass_exists_near m.hU hA
  exact ⟨k,native_comparable_cap_dyadic_enlargement m.hU hA hb hk hk1⟩

theorem nativeBroadNearZero_thermal_eq_initial_mass (m : NativeBandModel) :
    (∫u in 0..1,(nativeBroadNearZero m).indicator (fun _=>1) (m.R u)*m.thermal u)=
      ∫u in 0..min (8*m.U) 1,m.thermal u := by
  let v := min (8*m.U) 1
  have hv : v∈Icc (0:ℝ) 1 := ⟨(lt_min (mul_pos (by norm_num) m.hU) zero_lt_one).le,min_le_right _ _⟩
  rw [←intervalIntegral.integral_indicator hv]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [volume.ae_ne v] with u huv hu
  have hu : u∈Ioc (0:ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using hu
  have hu01 : u∈Icc (0:ℝ) 1 := Ioc_subset_Icc_self hu
  have hm := native_mass_slice_quantile_mem m (show (0:ℝ)∈Icc (0:ℝ) 1 by norm_num) hv hu01
  change (m.R u∈nativeBroadNearZero m)↔u∈Ioo (0:ℝ) v at hm
  by_cases hle:u≤v
  · have hmem := hm.mpr ⟨hu.1,lt_of_le_of_ne hle huv⟩
    simp only [indicator_of_mem hmem,one_mul,indicator_of_mem (show u∈{x | x≤v} from hle)]
  · have hnot : m.R u∉nativeBroadNearZero m := fun hh=>hle (hm.mp hh).2.le
    simp only [indicator_of_notMem hnot,zero_mul,indicator_of_notMem (show u∉{x | x≤v} from hle)]

end OAI.SKFluctuations.LaplaceWindowFormalization
