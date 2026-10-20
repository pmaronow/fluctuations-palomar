module

public import ComparisonNativeLocalCapOscillation

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 7000000
attribute [local instance] Classical.propDecidable

namespace NativeBandRefinement

def localDiameter {m : NativeBandModel} (s : NativeBandRefinement m) (D : ℝ) (j : ℕ) : ℝ :=
  D+2*(s.mesh j*m.Cnode)

theorem localDiameter_nonneg {m : NativeBandModel} (s : NativeBandRefinement m)
    {D : ℝ} (hD : 0 ≤ D) (j : ℕ) : 0 ≤ s.localDiameter D j :=
  add_nonneg hD (mul_nonneg (by norm_num) (mul_nonneg (s.hm0 j) m.Cnode_nonneg))

theorem localDiameter_tendsto {m : NativeBandModel} (s : NativeBandRefinement m) (D : ℝ) :
    Tendsto (s.localDiameter D) atTop (𝓝 D) := by
  change Tendsto (fun j=>D+2*(s.mesh j*m.Cnode)) atTop (𝓝 D)
  simpa only [mul_zero,zero_mul,add_zero] using
    ((s.hmesh.mul_const m.Cnode).const_mul 2).const_add D
end NativeBandRefinement

namespace NativeBandFrame
theorem thermal_le_local_native_budget {m : NativeBandModel} {s : NativeBandRefinement m}
    {bins : ℕ} {cut w : ℝ} (f : NativeBandFrame m s bins cut w)
    {D : ℝ} (hD : 0 < D) (hunit : ∀j,f.UnitOscillation j (s.localDiameter D j))
    (hcut : 0< cut) (hw : 0< w) (hRange : m.Q^2*m.y≤(bins:ℝ)*w) :
    (∫u in 0..1,f.mask (m.R u)*m.thermal u)≤
      nativeConditionalLedgerBudget f.B f.v cut (w+D)
        (m.AS*(f.B:ℝ)*m.Lside/(m.P*m.rho))
        (m.AC*f.v/(m.P*m.rho^2)) (m.reverse D) m.Lside := by
  let VS := m.AS*(f.B:ℝ)*m.Lside/(m.P*m.rho)
  let TC := m.AC*f.v/(m.P*m.rho^2)
  let C := 66+64*m.Lside+65536*(1+m.Lside)^2
  have hC : 0≤ C := by have hL := m.hLside; dsimp [C]; positivity
  have hDlim := s.localDiameter_tendsto D
  have hrev : Tendsto (fun j=>m.reverse (s.localDiameter D j)) atTop (𝓝 (m.reverse D)) :=
    (hDlim.rpow_const (Or.inl hD.ne')).mul_const _
  apply le_of_forall_pos_le_add
  intro t ht
  let err := t/(48+C+1)
  have herr : 0< err := div_pos ht (by linarith)
  have hv := f.sideFilled_eventually hcut herr
  have hc := f.unionGeometry.filled_eventually herr
  have hupper : ∀ᶠ j in atTop,f.defect j≤
      nativeConditionalLedgerBudget f.B (f.totalWidth j) cut (w+s.localDiameter D j)
        (VS+err) (TC+err) (m.reverse (s.localDiameter D j)) m.Lside := by
    filter_upwards [hv,hc] with j hvj hcj
    have hn := f.finite_budget_of_unit_oscillation hcut hw hRange j (s.localDiameter_nonneg hD.le j) (hunit j)
    unfold nativeConditionalLedgerBudget at hn ⊢
    have hT : C*f.unionGeometry.filled j≤ C*(TC+err) :=
      mul_le_mul_of_nonneg_left (by simpa only [div_mul_eq_mul_div] using hcj) hC
    dsimp only [VS,C] at *
    linarith
  have hlimUpper : Tendsto (fun j=>nativeConditionalLedgerBudget f.B (f.totalWidth j) cut
      (w+s.localDiameter D j) (VS+err) (TC+err) (m.reverse (s.localDiameter D j)) m.Lside) atTop
      (𝓝 (nativeConditionalLedgerBudget f.B f.v cut (w+D) (VS+err) (TC+err)
        (m.reverse D) m.Lside)) := by
    unfold nativeConditionalLedgerBudget
    exact (((tendsto_const_nhds.add
      ((f.totalWidth_tendsto.const_mul _).mul ((hDlim.const_add w).pow 2))).add
      ((f.totalWidth_tendsto.const_mul 32).mul hrev)).add tendsto_const_nhds).add
        tendsto_const_nhds
  have hlimit := le_of_tendsto_of_tendsto f.defect_tendsto hlimUpper hupper
  have herrbound : (48+C)*err≤ t := by
    dsimp [err]
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by linarith : 0 < 48+C+1)).mpr
    nlinarith
  dsimp only [VS,TC] at hlimit
  unfold nativeConditionalLedgerBudget at hlimit ⊢
  dsimp only [C] at herrbound
  nlinarith

theorem thermal_le_local_band_budget {m : NativeBandModel} {s : NativeBandRefinement m}
    {bins : ℕ} {cut w : ℝ} (f : NativeBandFrame m s bins cut w)
    {D : ℝ} (hD : 0 < D) (hunit : ∀j,f.UnitOscillation j (s.localDiameter D j))
    (hcut : 0< cut) (hw : 0< w) (hRange : m.Q^2*m.y≤(bins:ℝ)*w) :
    (∫u in 0..1,f.mask (m.R u)*m.thermal u)≤
      nativeConditionalLedgerBudget bins m.bandMass cut (w+D)
        (m.AS*(bins:ℝ)*m.Lside/(m.P*m.rho))
        (m.AC*m.bandMass/(m.P*m.rho^2)) (m.reverse D) m.Lside := by
  have hn := f.thermal_le_local_native_budget hD hunit hcut hw hRange
  have hB : f.B≤ bins := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f.label f.hlabel
  have hBR : (f.B:ℝ)≤ bins := by exact_mod_cast hB
  have hV := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBR m.AS_nonneg) m.hLside)
    (mul_pos m.P_pos m.rho_pos).le
  have hT := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left f.hvUpper m.AC_nonneg) (mul_pos m.P_pos (sq_pos_of_pos m.rho_pos)).le
  have hmean := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left f.hvUpper (by linarith [m.hLside] : 0≤76+64*m.Lside))
    (sq_nonneg (w+D))
  have hrev := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left f.hvUpper (by norm_num : (0:ℝ)≤32))
    (m.reverse_nonneg hD.le)
  have hcutB := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hBR (by norm_num : (0:ℝ)≤16)) hcut.le
  have hC : 0≤66+64*m.Lside+65536*(1+m.Lside)^2 := by have hL := m.hLside; positivity
  have hTc := mul_le_mul_of_nonneg_left hT hC
  unfold nativeConditionalLedgerBudget at hn ⊢
  nlinarith

end NativeBandFrame

theorem frame_unit_oscillation_of_constructed_rows
    {m : NativeBandModel} (s : NativeBandRefinement m) (g : NativeBandRetainedCaps m)
    {bins : ℕ} {cut w : ℝ} (f : NativeBandFrame m s bins cut w)
    (hA : ∀j,f.A j=g.rows (s.as j)) {v C : ℝ} (hv : 0 < v) (hC : 0 < C)
    (hleft : ∀t,v ≤ m.alpha.val.val (g.a t)+m.U)
    (hspan : ∀t,m.alpha.val.val (g.z t)-m.alpha.val.val (g.a t) ≤ C*v) :
    ∀j,f.UnitOscillation j (s.localDiameter (m.localDiameter v C) j) := by
  intro j i hi t ht heq
  have hiG : i∈g.rows (s.as j) := hA j ▸ hi
  have htG : t∈g.rows (s.as j) := hA j ▸ ht
  exact g.unit_oscillation_local s hv hC hleft hspan j i hiG t htG ((f.hclass0 j i hi t ht).mp heq)

theorem exists_nativeBandFrame_of_constructed_sides_with_rows
    (m : NativeBandModel) (s : NativeBandRefinement m) (g : NativeBandRetainedCaps m)
    (bins : ℕ) {cut w : ℝ} (hcut : 0 < cut) (hleft : m.cutRadius ≤ m.ag)
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
      (∀j,frame.selected j=nativeKeptRows (fun b=>g.bin (s.as j) bins w b) keep) ∧
      (∀j,frame.A j=g.rows (s.as j)) := by
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
  have hv : 0 < ∑b : Fin (Fintype.card B),(ss b).width := by
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
      have hp : 0 < (ss b).widths j := by linarith [(ss b).hwidths j]
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
  exact ⟨frame,rfl,hselected,fun j=>rfl⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
