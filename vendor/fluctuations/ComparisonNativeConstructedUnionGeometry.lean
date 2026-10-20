module

public import ComparisonNativeConstructedBandGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 12000000
attribute [local instance] Classical.propDecidable

def nativeConstructedBinSupport (m : NativeBandModel) (g : NativeBandRetainedCaps m)
    {bins : ℕ} (l u : Fin bins → ℝ) (b : Fin bins) : Set ℝ :=
  (Ioo m.ag m.zg ∩ NativeSelectedMask.fixedSupport g.a g.z m.H) ∩ Ioo (l b) (u b)

abbrev NativeConstructedKeptCap {m : NativeBandModel} (g : NativeBandRetainedCaps m)
    {bins : ℕ} (labels : Fin g.count → Fin bins) (keep : Fin bins → Bool) :=
  {t : Fin g.count // keep (labels t)=true}

def nativeConstructedUnionCaps (m : NativeBandModel) (g : NativeBandRetainedCaps m)
    {bins : ℕ} (labels : Fin g.count → Fin bins) (keep : Fin bins → Bool)
    (l u : Fin bins → ℝ) : NativeBandFixedCapGeometry m := by
  let B := NativeConstructedKeptCap g labels keep
  let e : Fin (Fintype.card B) ≃ B := (Fintype.equivFin B).symm
  let contact : ℝ → ℝ := (nativeKeptSupport (fun b => Ioo (l b) (u b)) keep).indicator (fun _ => 1)
  exact {
    count := Fintype.card B
    a := fun i => g.a (e i).val
    z := fun i => g.z (e i).val
    weight := fun _ => 1
    hga := fun i => g.hga (e i).val
    haz := fun i => g.haz (e i).val
    hgz := fun i => g.hgz (e i).val
    haH := fun i => g.haH (e i).val
    hzH := fun i => g.hzH (e i).val
    hnegative := fun i => g.hnegative (e i).val
    hamass := fun i => g.hamass (e i).val
    hzmass := fun i => g.hzmass (e i).val
    hweight := fun _ => zero_le_one
    contact := contact
    hmeas := measurable_const.indicator (nativeKeptSupport_measurable _ keep (fun _ => measurableSet_Ioo))
    bound := 1
    hb0 := zero_le_one
    hbound := fun r => by
      dsimp only [contact]
      by_cases h : r ∈ nativeKeptSupport (fun b => Ioo (l b) (u b)) keep <;> simp [h]
    hnonneg := fun r => indicator_nonneg (fun _ _ => zero_le_one) r }

theorem nativeConstructedUnion_caps_point
    (m : NativeBandModel) (g : NativeBandRetainedCaps m) {bins : ℕ}
    (labels : Fin g.count → Fin bins) (keep : Fin bins → Bool) (l u : Fin bins → ℝ)
    {r : ℝ} (hr : r ∈ Ioo m.ag m.zg)
    (hlabels : ∀t, r ∈ Ioo (g.a t) (g.z t) → ∀b,
      r ∈ nativeConstructedBinSupport m g l u b ↔ labels t=b) :
    (nativeConstructedUnionCaps m g labels keep l u).fixed r=
      (nativeKeptSupport (nativeConstructedBinSupport m g l u) keep).indicator (fun _ => 1) r := by
  let B := NativeConstructedKeptCap g labels keep
  let e : Fin (Fintype.card B) ≃ B := (Fintype.equivFin B).symm
  let A0 : Set ℝ := {r | r ∈ Ioo m.ag m.zg ∧ m.H r=0}
  let contact : ℝ → ℝ := (nativeKeptSupport (fun b => Ioo (l b) (u b)) keep).indicator (fun _ => 1)
  change fixedCapContactWeight (fun i => g.a (e i).val) (fun i => g.z (e i).val)
    (fun _ => 1) A0 contact r=_
  have hdis : Pairwise (fun i j : Fin (Fintype.card B) =>
      Disjoint (Ioo (g.a (e i).val) (g.z (e i).val)) (Ioo (g.a (e j).val) (g.z (e j).val))) := by
    intro i j hij
    apply g.hdisjoint
    intro he
    exact hij (e.injective (Subtype.ext he))
  have hcontact : ∀i : Fin (Fintype.card B), Disjoint (Ioo (g.a (e i).val) (g.z (e i).val)) A0 := by
    intro i
    apply Set.disjoint_left.mpr
    intro r hri hrA
    exact (g.hnegative (e i).val r hri).ne hrA.2
  by_cases hcap : ∃t, r ∈ Ioo (g.a t) (g.z t)
  · obtain ⟨t,hrt⟩ := hcap
    by_cases hk : keep (labels t)=true
    · let i := e.symm ⟨t,hk⟩
      have hi : r ∈ Ioo (g.a (e i).val) (g.z (e i).val) := by simpa only [i,Equiv.apply_symm_apply] using hrt
      rw [fixedCapContactWeight_at_cap _ _ _ A0 contact hdis hcontact i hi]
      have hmem : r ∈ nativeKeptSupport (nativeConstructedBinSupport m g l u) keep :=
        ⟨labels t,hk,(hlabels t hrt (labels t)).mpr rfl⟩
      rw [indicator_of_mem hmem]
    · have hout : ∀i : Fin (Fintype.card B), r ∉ Ioo (g.a (e i).val) (g.z (e i).val) := by
        intro i hi
        have he : (e i).val=t := by
          by_contra hne
          exact Set.disjoint_left.mp (g.hdisjoint hne) hi hrt
        exact hk (he ▸ (e i).property)
      have hnA : r ∉ A0 := fun h => (g.hnegative t r hrt).ne h.2
      rw [fixedCapContactWeight_outside _ _ _ A0 contact hout hnA]
      have hn : r ∉ nativeKeptSupport (nativeConstructedBinSupport m g l u) keep := by
        rintro ⟨b,hb,hF⟩
        exact hk ((hlabels t hrt b).mp hF ▸ hb)
      rw [indicator_of_notMem hn]
  · have hout : ∀i : Fin (Fintype.card B), r ∉ Ioo (g.a (e i).val) (g.z (e i).val) :=
      fun i hi => hcap ⟨(e i).val,hi⟩
    by_cases hH : m.H r=0
    · rw [fixedCapContactWeight_at_contact _ _ _ A0 contact hcontact ⟨hr,hH⟩]
      have hmem : r ∈ nativeKeptSupport (fun b => Ioo (l b) (u b)) keep ↔
          r ∈ nativeKeptSupport (nativeConstructedBinSupport m g l u) keep := by
        constructor
        · rintro ⟨b,hb,hI⟩
          exact ⟨b,hb,⟨hr,Or.inr hH⟩,hI⟩
        · rintro ⟨b,hb,hF⟩
          exact ⟨b,hb,hF.2⟩
      simp only [contact,Set.indicator_apply,hmem]
    · have hnA : r ∉ A0 := fun h => hH h.2
      rw [fixedCapContactWeight_outside _ _ _ A0 contact hout hnA]
      have hn : r ∉ nativeKeptSupport (nativeConstructedBinSupport m g l u) keep := by
        rintro ⟨b,_,hF⟩
        rcases hF.1.2 with ht|he
        · exact hcap ht
        · exact hH he
      rw [indicator_of_notMem hn]

theorem nativeConstructedUnion_caps_ae
    (m : NativeBandModel) (s : NativeBandRefinement m) (g : NativeBandRetainedCaps m)
    (bins : ℕ) (hbins : 0 < bins) (w : ℝ) (labels : Fin g.count → Fin bins)
    (hlabels : ∀j t,comparisonConstructedCapLabel m.hc m.hk m.hkc m.hm m.hM (m.n+1) bins hbins
      m.q m.alpha (s.as j) g.a g.z m.H g.D m.ag m.zg w m.capSet t=labels t)
    (keep : Fin bins → Bool) (l u : Fin bins → ℝ)
    (hgeom : ∀b,∀ᵐ r ∂volume.restrict (Ioo (0:ℝ) 1),∀ᶠ j in atTop,
      (r ∈ NativeSelectedMask.finiteSupport (fun i => m.R (partitionPoint 0 (s.as j) i))
        (g.bin (s.as j) bins w b) ↔ r ∈ nativeConstructedBinSupport m g l u b)) :
    ∀ᵐ r ∂volume.restrict (Ioo m.ag m.zg),
      (nativeConstructedUnionCaps m g labels keep l u).fixed r=
        (nativeKeptSupport (nativeConstructedBinSupport m g l u) keep).indicator (fun _ => 1) r := by
  have hsub : Ioo m.ag m.zg ⊆ Ioo (0:ℝ) 1 := fun r hr => ⟨m.hag.trans hr.1,hr.2.trans_le m.hzg⟩
  have hg := (ae_all_iff.mpr hgeom).filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  filter_upwards [hg,ae_restrict_mem measurableSet_Ioo] with r hr hrband
  apply nativeConstructedUnion_caps_point m g labels keep l u hrband
  intro t hrt b
  have hD : r ∉ g.D := fun hd => g.hinterior t r hd hrt
  have hc := comparisonConstructedBin_cap_support_eventually m.hc m.hk m.hkc m.hm m.hM
    (m.n+1) bins hbins m.q m.alpha s.as s.mesh s.ho s.he s.hm s.hmesh
    g.a g.z m.H g.D m.hag.le m.hzg g.hga g.hgz (fun _ => w) m.capSet g.hwhole labels hlabels t b hrt hD
  obtain ⟨j,hj⟩ := ((hr b).and hc).exists
  exact hj.1.symm.trans hj.2

theorem nativeConstructedKeptUnion_mask_point
    (m : NativeBandModel) (s : NativeBandRefinement m) (g : NativeBandRetainedCaps m)
    (bins : ℕ) (w : ℝ) (keep : Fin bins → Bool) (l u : Fin bins → ℝ)
    (hgeom : ∀b,∀ᵐ r ∂volume.restrict (Ioo (0:ℝ) 1),∀ᶠ j in atTop,
      (r ∈ NativeSelectedMask.finiteSupport (fun i => m.R (partitionPoint 0 (s.as j) i))
        (g.bin (s.as j) bins w b) ↔ r ∈ nativeConstructedBinSupport m g l u b)) :
    ∀ᵐ r ∂volume.restrict (Icc (0:ℝ) 1), Tendsto (fun j =>
      comparisonNativeUnitColumnWeight m.hc m.hk m.hkc m.hm m.hM m.q m.alpha (s.as j)
        (nativeKeptRows (fun b => g.bin (s.as j) bins w b) keep)
        (fun _ => (0:Fin 1)) (fun _ => 1) r) atTop
      (𝓝 ((nativeKeptSupport (nativeConstructedBinSupport m g l u) keep).indicator (fun _ => 1) r)) := by
  have hJ : ∀j,∀i ∈ nativeKeptRows (fun b => g.bin (s.as j) bins w b) keep,i.val < (s.as j).length := by
    intro j i hi
    obtain ⟨b,_,hib⟩ := (nativeKeptRows_mem _ keep i).mp hi
    exact g.row_nonterminal _ _ (comparisonConstructedBin_subset m.hc m.hk m.hkc m.hm m.hM
      (m.n+1) bins m.q m.alpha (s.as j) g.a g.z m.H g.D m.ag m.zg w m.capSet b hib)
  have hmem := comparisonNativeKeptUnion_support_eventually m.hc m.hk m.hkc m.hm m.hM m.q m.alpha
    s.as (fun j b => g.bin (s.as j) bins w b) keep (nativeConstructedBinSupport m g l u) hgeom
  have hp := (comparisonNativeMask_tendsto_of_support_eventually m.hc m.hk m.hkc m.hm m.hM m.q m.alpha
    s.as s.ho s.he (fun _ => 1) (fun j => nativeKeptRows (fun b => g.bin (s.as j) bins w b) keep)
    (fun _ _ => (0:Fin 1)) hJ (nativeKeptSupport (nativeConstructedBinSupport m g l u) keep) hmem).1
  simpa only [restrict_Ioo_eq_restrict_Icc] using hp

theorem exists_nativeConstructedUnionGeometry
    (m : NativeBandModel) (s : NativeBandRefinement m) (g : NativeBandRetainedCaps m)
    (bins : ℕ) (hbins : 0 < bins) (w : ℝ) (hleft : m.cutRadius ≤ m.ag)
    (labels : Fin g.count → Fin bins)
    (hlabels : ∀j t,comparisonConstructedCapLabel m.hc m.hk m.hkc m.hm m.hM (m.n+1) bins hbins
      m.q m.alpha (s.as j) g.a g.z m.H g.D m.ag m.zg w m.capSet t=labels t)
    (keep : Fin bins → Bool) (l u : Fin bins → ℝ)
    (hgeom : ∀b,∀ᵐ r ∂volume.restrict (Ioo (0:ℝ) 1),∀ᶠ j in atTop,
      (r ∈ NativeSelectedMask.finiteSupport (fun i => m.R (partitionPoint 0 (s.as j) i))
        (g.bin (s.as j) bins w b) ↔ r ∈ nativeConstructedBinSupport m g l u b))
    (v : ℝ) (hmasslim : Tendsto (fun j => physicalWindowMass (s.steps j) 0
      (nativeKeptRows (fun b => g.bin (s.as j) bins w b) keep)) atTop (𝓝 v)) :
    Nonempty (NativeBandUnionGeometry m s
      (fun j => nativeKeptRows (fun b => g.bin (s.as j) bins w b) keep) v) := by
  let caps := nativeConstructedUnionCaps m g labels keep l u
  let selected := fun j => nativeKeptRows (fun b => g.bin (s.as j) bins w b) keep
  have hsubset j : selected j ⊆ g.rows (s.as j) := by
    intro i hi
    obtain ⟨b,_,hib⟩ := (nativeKeptRows_mem _ keep i).mp hi
    exact comparisonConstructedBin_subset m.hc m.hk m.hkc m.hm m.hM (m.n+1) bins m.q m.alpha
      (s.as j) g.a g.z m.H g.D m.ag m.zg w m.capSet b hib
  have hpoint := nativeConstructedKeptUnion_mask_point m s g bins w keep l u hgeom
  have hrep := nativeConstructedUnion_caps_ae m s g bins hbins w labels hlabels keep l u hgeom
  have hsub : Ioo m.ag m.zg ⊆ Icc (0:ℝ) 1 := fun r hr => ⟨(m.hag.trans hr.1).le,(hr.2.trans_le m.hzg).le⟩
  have hpointBand := hpoint.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  have hL1 : Tendsto (fun j => ∫r in Ioo m.ag m.zg,
      |comparisonNativeUnitColumnWeight m.hc m.hk m.hkc m.hm m.hM m.q m.alpha (s.as j)
        (selected j) (fun _ => (0:Fin 1)) (fun _ => 1) r-caps.fixed r|) atTop (𝓝 0) := by
    apply bounded_contact_weights_tendsto_L1 (B:=1) (Ioo m.ag m.zg) (by simp)
    · exact fun j => (comparisonNativeUnitColumnWeight_measurable m.hc m.hk m.hkc m.hm m.hM
        m.q m.alpha (s.as j) (selected j) (fun _ => (0:Fin 1)) (fun _ => 1)).aestronglyMeasurable.restrict
    · intro j
      apply ae_of_all
      intro r
      have hb := radiusCellEnergyDensity_mem_Icc_bound _
        (comparisonSweepQuantile_monotone m.hc m.hk m.hkc m.hm m.hM m.alpha)
        (s.as j) (s.ho j) (nativeSelectedColumn (selected j) (fun _ => (0:Fin 1)) (fun _ => (1:ℝ)))
        zero_le_one (fun i => by unfold nativeSelectedColumn; split_ifs <;> norm_num) r
      simpa only [comparisonNativeUnitColumnWeight,Real.norm_eq_abs,abs_of_nonneg hb.1] using hb.2
    · filter_upwards [hpointBand,hrep] with r hp hr
      rw [←hr] at hp
      exact hp
  refine ⟨{
    fixedCaps := caps
    hmasslim := ?_
    hleft := fun j i hi => g.rows_lower (s.as j) hleft i (hsubset j hi)
    hsupport := fun j => g.column_support (s.as j) (selected j) (hsubset j) (fun _ => (0:Fin 1)) (fun _ => 1)
    hcolumns := hL1 }⟩
  simpa only [physicalSelectedCellMass,physicalWindowMass,Finset.sum_ite_mem,Finset.univ_inter] using hmasslim

end OAI.SKFluctuations.LaplaceWindowFormalization
