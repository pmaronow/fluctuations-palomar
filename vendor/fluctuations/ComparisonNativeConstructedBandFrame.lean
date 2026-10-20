module

public import ComparisonNativeConstructedBandGeometry
public import ComparisonNativeKeptBinMass

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
set_option maxHeartbeats 4800000
attribute [local instance] Classical.propDecidable

theorem nativeKeptRows_equiv {bins N B : ℕ} (J : Fin bins → Finset (Fin N))
    (keep : Fin bins → Bool) (e : Fin B≃{b : Fin bins // keep b=true}) :
    nativeKeptRows J keep=Finset.univ.biUnion (fun b=>J (e b).val) := by
  ext i
  rw [nativeKeptRows_mem]
  simp only [Finset.mem_biUnion,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨b,hb,hi⟩
    exact ⟨e.symm ⟨b,hb⟩,by simpa only [e.apply_symm_apply] using hi⟩
  · rintro ⟨b,hi⟩
    exact ⟨(e b).val,(e b).property,hi⟩

theorem nativeKeptSum_equiv {bins B : ℕ} (v : Fin bins → ℝ) (keep : Fin bins → Bool)
    (e : Fin B≃{b : Fin bins // keep b=true}) :
    (∑b,if keep b then v b else 0)=∑b,v (e b).val := by
  calc
    _=∑b∈Finset.univ.filter (fun b=>keep b=true),v b := (Finset.sum_filter _ _).symm
    _=∑b : {b : Fin bins // keep b=true},v b.val := Finset.sum_subtype _ (by simp) v
    _=_ := (e.sum_comp (fun b=>v b.val)).symm

theorem sum_physicalSelectedCellMass_eq_window {ι : Type} (steps : List (GaussianStep ι))
    (J : Finset (Fin (steps.length+1))) :
    (∑i,physicalSelectedCellMass steps J i)=physicalWindowMass steps 0 J := by
  simp [physicalSelectedCellMass,physicalWindowMass]

theorem constructedBandSides_mass_tendsto
    (m : NativeBandModel) (s : NativeBandRefinement m) (g : NativeBandRetainedCaps m)
    (bins : ℕ) (cut w : ℝ) (keep : Fin bins → Bool) (f : Fin bins → ℝ)
    (side : ∀b,keep b=true → NativeConstructedBandSideData m s g bins cut w b (f b)) :
    let B := {b : Fin bins // keep b=true}
    let e := (Fintype.equivFin B).symm
    Tendsto (fun j=>physicalWindowMass (s.steps j) 0
      (nativeKeptRows (fun b=>g.bin (s.as j) bins w b) keep)) atTop
      (𝓝 (∑b : Fin (Fintype.card B),(side (e b).val (e b).property).side.width)) := by
  dsimp only
  let B := {b : Fin bins // keep b=true}
  let e := (Fintype.equivFin B).symm
  have heq j : physicalWindowMass (s.steps j) 0
      (nativeKeptRows (fun b=>g.bin (s.as j) bins w b) keep)=
      ∑b : Fin (Fintype.card B),(side (e b).val (e b).property).side.widths j := by
    have hd : Pairwise (fun b c : Fin bins=>Disjoint (g.bin (s.as j) bins w b) (g.bin (s.as j) bins w c)) :=
      native_height_bins_disjoint _ _ _ w
    rw [native_kept_disjoint_mass (s.steps j) (fun b=>g.bin (s.as j) bins w b) keep hd,
      nativeKeptSum_equiv _ keep e]
    apply Finset.sum_congr rfl
    intro b _
    exact (side (e b).val (e b).property).widths_eq_mass j |>.symm
  simp_rw [heq]
  exact tendsto_finsetSum Finset.univ (fun b _=>(side (e b).val (e b).property).side.hwidthlim)

theorem exists_nativeBandFrame_of_constructed_sides
    (m : NativeBandModel) (s : NativeBandRefinement m) (g : NativeBandRetainedCaps m)
    (bins : ℕ) {cut w : ℝ} (hcut : 0<cut) (hleft : m.cutRadius ≤ m.ag)
    (hupper : m.xs+m.alpha.val.val m.zg ≤ m.y)
    (hband : m.alpha.val.val m.zg-m.alpha.val.val m.ag ≤ m.bandMass)
    (hlog : Real.log (1/cut) ≤ m.Lside)
    (hraw : ∀j,physicalRawRatio (m.n+1) m.l (s.steps j) 0 m.xs
      (Measure.pi fun a=>gaussianReal 0 (m.q 0 a)) id measurable_id ≤ m.Q)
    (keep : Fin bins → Bool) (hn : ∃b,keep b=true) (f : Fin bins → ℝ)
    (side : ∀b,keep b=true → NativeConstructedBandSideData m s g bins cut w b (f b))
    (F : Fin bins → Set ℝ) (hF : ∀b,MeasurableSet (F b))
    (hgeom : ∀b,∀ᵐ r ∂volume.restrict (Ioo (0:ℝ) 1),∀ᶠ j in atTop,
      (r∈NativeSelectedMask.finiteSupport (fun i=>m.R (partitionPoint 0 (s.as j) i))
        (g.bin (s.as j) bins w b) ↔ r∈F b))
    (unionGeometry : NativeBandUnionGeometry m s
      (fun j=>nativeKeptRows (fun b=>g.bin (s.as j) bins w b) keep)
      (∑b : Fin (Fintype.card {b : Fin bins // keep b=true}),
        (side ((Fintype.equivFin {b : Fin bins // keep b=true}).symm b).val
          ((Fintype.equivFin {b : Fin bins // keep b=true}).symm b).property).side.width)) :
    ∃frame : NativeBandFrame m s bins cut w,
      frame.mask=(nativeKeptSupport F keep).indicator (fun _=>1) ∧
      ∀j,frame.selected j=nativeKeptRows (fun b=>g.bin (s.as j) bins w b) keep := by
  let B := {b : Fin bins // keep b=true}
  let e := (Fintype.equivFin B).symm
  let ss := fun b : Fin (Fintype.card B)=>(side (e b).val (e b).property).side
  let selected := fun j=>Finset.univ.biUnion (fun b=> (ss b).selected j)
  have hselected j : selected j=nativeKeptRows (fun b=>g.bin (s.as j) bins w b) keep := by
    rw [nativeKeptRows_equiv _ keep e]
    dsimp only [selected]
    congr 1
    funext b
    exact (side (e b).val (e b).property).selected_eq j
  dsimp only [selected] at hselected
  have hsubset j : selected j⊆g.rows (s.as j) := by
    intro i hi
    change i∈Finset.univ.biUnion (fun b=>(ss b).selected j) at hi
    rw [hselected j] at hi
    obtain ⟨b,_,hb⟩ := (nativeKeptRows_mem _ keep i).mp hi
    exact comparisonConstructedBin_subset m.hc m.hk m.hkc m.hm m.hM (m.n+1) bins m.q m.alpha
      (s.as j) g.a g.z m.H g.D m.ag m.zg w m.capSet b hb
  have hv : 0<∑b : Fin (Fintype.card B),(ss b).width := by
    apply Finset.sum_pos
    · intro b _
      linarith [(ss b).hwidth]
    · obtain ⟨b,hb⟩ := hn
      exact ⟨e.symm ⟨b,hb⟩,Finset.mem_univ _⟩
  have hmasslim := constructedBandSides_mass_tendsto m s g bins cut w keep f side
  have hvUpper : (∑b : Fin (Fintype.card B),(ss b).width) ≤ m.bandMass := by
    apply le_of_tendsto hmasslim
    apply Eventually.of_forall
    intro j
    exact (g.selected_mass_le (s.as j) (s.ho j) _ (by simpa only [←hselected j] using hsubset j)).trans hband
  have hpoint := (comparisonNativeMask_tendsto_of_support_eventually m.hc m.hk m.hkc m.hm m.hM
    m.q m.alpha s.as s.ho s.he (fun _=>1)
    (fun j=>nativeKeptRows (fun b=>g.bin (s.as j) bins w b) keep) (fun _ _=>(0:Fin 1))
    (fun j i hi=>g.row_nonterminal (s.as j) i (hsubset j (by change i∈Finset.univ.biUnion (fun b=>(ss b).selected j);rw [hselected j];exact hi)))
    (nativeKeptSupport F keep)
    (comparisonNativeKeptUnion_support_eventually m.hc m.hk m.hkc m.hm m.hM m.q m.alpha
      s.as (fun j b=>g.bin (s.as j) bins w b) keep F hgeom)).1
  let frame : NativeBandFrame m s bins cut w := {
    B := Fintype.card B
    side := ss
    label := fun b=>(e b).val
    hlabel := fun b c h=>e.injective (Subtype.ext h)
    A := fun j=>g.rows (s.as j)
    K0 := fun j=>(s.steps j).length+1
    unit0 := fun j=>firstWholeUnitCell m.capSet
      (comparisonConstructedRowRadius m.hc m.hk m.hkc m.hm m.hM m.q m.alpha (s.as j))
    hpos := fun j=>g.row_positive (s.as j)
    hclass0 := fun j i _ t _=>firstWholeUnitCell_eq_iff m.capSet _ i t
    hmassUpper := fun j=>g.rows_massUpper (s.as j) (s.ho j) hupper
    rawUpper := hraw
    hbin := fun j b=>(side (e b).val (e b).property).selected_eq j
    hclass := fun j b=>(side (e b).val (e b).property).classes j
    horder := fun j b=>(side (e b).val (e b).property).order j
    hlower := fun j=>g.rows_lower (s.as j) hleft
    hsideLog := by
      intro j b
      have hp : 0<(ss b).widths j := by linarith [(ss b).hwidths j]
      exact (Real.log_le_log (div_pos hp hcut)
        (div_le_div_of_nonneg_right ((side (e b).val (e b).property).widths_le_one j) hcut.le)).trans hlog
    v := ∑b,(ss b).width
    hv := hv
    hsumWidth := rfl
    hvUpper := hvUpper
    unionGeometry := by simpa only [←hselected] using unionGeometry
    mask := (nativeKeptSupport F keep).indicator (fun _=>1)
    hmask := measurable_const.indicator (nativeKeptSupport_measurable F keep hF)
    hmaskBound := by intro r _;simp only [Set.indicator_apply];split_ifs <;> norm_num
    hmaskPoint := by
      simpa only [hselected,restrict_Ioo_eq_restrict_Icc] using hpoint }
  exact ⟨frame,rfl,hselected⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
