module

public import ComparisonActualHighOnlySelectedColumnGeometry
public import ComparisonActualHighOnlySelectedCapMass
public import ComparisonActualHighOnlySelectedLedger
public import ComparisonActualHighOnlyFilledTraceRates
public import ComparisonNativeConstructedBandGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
set_option maxHeartbeats 30000000
attribute [local instance] Classical.propDecidable
namespace ActualHighOnlyOverlapMinimum.SelectedMasterFamily
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualHighOnlyOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
variable {P : a.Potential} {ι : Type*} [Fintype ι] {c : ι→ShiftedCapInterval a P}
variable {Dcuts : Finset ℝ} {ag zg w cut Q : ℝ} {bins ell : ℕ} {hbins : 0< bins}
variable (M : SelectedMasterFamily a P c Dcuts ag zg bins hbins w cut ell Q)

theorem bin_side_filled_eventually
    (hwhole : ∀t,∀r∈Ioo (c t).left (c t).right,wholeUnit P.negativeSet r=Ioo (c t).left (c t).right)
    (hcontacts : ∀t,P.H (c t).left=0 ∧ (P.H (c t).right=0 ∨ (c t).right=1))
    (hdisjoint : Pairwise (fun t u=>Disjoint (Ioo (c t).left (c t).right) (Ioo (c u).left (c u).right)))
    (hag : (0:ℝ)< ag) (hagz : ag≤ zg) (hzg : zg≤1)
    (hclock : NativePullbackClockRegularity a.alpha.val.val a.b a.h ag zg)
    (hleft : ∀t,ag≤(c t).left) (hright : ∀t,(c t).right≤ zg)
    (hinterior : ∀t,∀d∈Dcuts,d∉Ioo (c t).left (c t).right)
    {lo hi K0 : ℝ} (hlo : 0≤ lo) (hK : 1≤ K0)
    (hband : hi+comparisonSmallMass a.data.N a.data.E≤ K0*(lo+comparisonSmallMass a.data.N a.data.E))
    (hamass : ∀t,lo≤ a.alpha.val.val (c t).left) (hzmass : ∀t,a.alpha.val.val (c t).right≤ hi)
    (hN : 1≤ a.data.N) (hlog : 1≤ Real.log a.data.N) (hnd : 1/a.data.N≤ a.data.d)
    (hcut : 0< cut) (b : Fin bins) (hkept : M.keep b=true)
    (dphys : ℕ) (ephys : Fin (dphys+1)≃FeatureIndex (n+1))
    {epsilon : ℝ} (hepsilon : 0< epsilon) :
    let m:=a.shiftedNativeModel
    ∀ᶠj in atTop,
      (2*(∫r,deriv a.alpha.val.val r*m.unitColumn (M.as j) (M.bin j b) (M.co j b).unit
        (fun u=>sideSquareColumn (M.co j b).x cut (M.width j b) u.val) r
          ∂m.radiusMeasure dphys ephys (M.as j) (M.ho j))+4*M.mesh j/cut)/a.alpha.val.val ag≤
      (108*K0^2*(Real.log a.data.N)^2/((n+1:ℝ)*(laplaceComparisonStrength a.data.d a.lam) zg*a.alpha.val.val ag))*
        Real.log ((M.f b ⟨1,by simp⟩)/cut)+epsilon := by
  dsimp only
  let m:=a.shiftedNativeModel
  let C:=fun j=>M.co j b
  let B:={t : ι //M.labels t=b}
  let width:=M.f b ⟨1,by simp⟩
  let lc:=fun t : B=>comparisonContactLimitCoordinate (M.f b) (c t.val).left
  let rc:=fun t : B=>comparisonContactLimitCoordinate (M.f b) (c t.val).right
  let A:=(Ioo ag zg∩P.contactSet)∩Ioo (M.l b).val (M.u b).val
  let wcontact:=fun r=>pointSideColumn cut width (comparisonContactLimitCoordinate (M.f b) r)
  have hwidths j : 2*cut≤ M.width j b:=(M.cutoffs j b).mpr hkept
  have hwidth : 2*cut≤ width:=ge_of_tendsto (M.widths b) (Eventually.of_forall hwidths)
  have hrow j i (hi:i∈M.bin j b):=(P.retainedRows_mem c Dcuts ag zg (M.as j) i).mp
    (P.retainedBin_subset c Dcuts ag zg (M.as j) bins w b hi)
  have hhigh j i (hi:i∈M.bin j b) : m.u0≤ partitionPoint 0 (M.as j) i.val:=(hrow j i hi).2.2.2.1
  have hcoords (t : B):=P.retainedCap_coordinates_tendsto c Dcuts M.as M.mesh M.ho M.he M.hmesh
    M.mesh_nonneg M.mesh_tendsto hag hzg bins hbins (fun _=>w) hwhole t.val b
    (fun j=>(M.capLabels j t.val).trans t.property) (hleft t.val) (hright t.val) (hinterior t.val)
    (M.f b) (M.coordinates b)
  have hgap (t : B):=P.retainedCap_cumulative_gap c Dcuts M.as M.mesh M.ho M.he M.hmesh
    M.mesh_nonneg M.mesh_tendsto hag hzg bins hbins (fun _=>w) hwhole t.val b
    (fun j=>(M.capLabels j t.val).trans t.property) (hleft t.val) (hright t.val) (hinterior t.val)
    (M.f b) (M.coordinates b)
  have hcoordsL (t : B) : Tendsto (fun j=>(C j).x ((C j).unit
      (P.retainedCapFirst c Dcuts ag zg (M.as j) bins w t.val b)).val) atTop (𝓝 (lc t)):=by
    have ht:=(hcoords t).1
    have hrI : (c t.val).left∈Icc (0:ℝ) 1:=
      ⟨(le_refl (0:ℝ)).trans (c t.val).hleft,(c t.val).hlt.le.trans (c t.val).hright⟩
    simpa only [lc,comparisonContactLimitCoordinate,projIcc_of_mem zero_le_one hrI] using ht
  have hcoordsR (t : B) : Tendsto (fun j=>(C j).x (((C j).unit
      (P.retainedCapFirst c Dcuts ag zg (M.as j) bins w t.val b)).val+1)) atTop (𝓝 (rc t)):=by
    have ht:=(hcoords t).2
    have hrI : (c t.val).right∈Icc (0:ℝ) 1:=
      ⟨(le_refl (0:ℝ)).trans ((c t.val).hleft.trans (c t.val).hlt.le),(c t.val).hright⟩
    simpa only [rc,comparisonContactLimitCoordinate,projIcc_of_mem zero_le_one hrI] using ht
  have hA : MeasurableSet A:=(measurableSet_Ioo.inter P.contactSet_measurable).inter measurableSet_Ioo
  have hcontact (t : B) : Disjoint (Ioo (c t.val).left (c t.val).right) A:=by
    apply Set.disjoint_left.mpr
    intro r hr hrA
    have HH:=(c t.val).negative r hr
    rw [hrA.1.2.2] at HH
    exact lt_irrefl _ HH
  have hg:=P.retainedBin_column_geometry c Dcuts M.as M.mesh M.ho M.he M.hmesh M.mesh_nonneg
    M.mesh_tendsto hag hzg hleft hright bins hbins (fun _=>w) hwhole M.labels M.capLabels b
    (M.l b).val (M.u b).val (M.geometry b)
  have hfull:=m.sideColumn_full_L1_from_uniform_cumulative (le_refl (0:ℝ)) hag hzg hcut
    A hA (fun r hr=>hr.1.1) P.H P.negativeSet_open P.negativeSet_subset (fun r hr=>hr.2)
    M.as M.mesh M.ho M.he M.hmesh M.mesh_tendsto (fun j=>(C j).K) (fun j=>M.bin j b) hhigh
    (fun j=>(C j).unit) (fun j=>(C j).x) (fun j=>(C j).start)
    (fun j=>(C j).strict_of_width hcut (hwidths j)) (fun j=>(C j).mass) (fun j=>(C j).order)
    hwidths (fun j=>(M.width_mem j b).2) (fun j i hi=>(hrow j i hi).2.2.1)
    (fun j=>(C j).classes) hg.1 (M.f b) (M.coordinates b)
    (fun t : B=>(c t.val).left) (fun t=>(c t.val).right) lc rc
    (fun j t=>(C j).unit (P.retainedCapFirst c Dcuts ag zg (M.as j) bins w t.val b))
    (fun t=>(hgap t).2) hcoordsL hcoordsR
    (fun t u htu=>hdisjoint (fun h=>htu (Subtype.ext h))) hcontact hg.2.1 hg.2.2
  let enum : Fin (Fintype.card B)≃B:=(Fintype.equivFin B).symm
  let contact:=(Ioo (M.l b).val (M.u b).val).indicator wcontact
  let bound:=2*(cut⁻¹)^2*(width-2*cut)
  have hb0 : 0≤ bound:=by
    dsimp only [bound]
    exact mul_nonneg (by positivity) (sub_nonneg.mpr hwidth)
  have hb r : ‖contact r‖≤ bound:=by
    by_cases hr:r∈Ioo (M.l b).val (M.u b).val
    · rw [show contact r=wcontact r from indicator_of_mem hr _]
      exact pointSideColumn_coarse_norm_bound hcut hwidth _
    · rw [show contact r=0 from indicator_of_notMem hr _,norm_zero];exact hb0
  let fixed : FixedCapWeights a P:={
    ag:=ag
    zg:=zg
    lo:=lo
    hi:=hi
    K:=K0
    hag:=hag
    hagz:=hagz
    hzg:=hzg
    clockRegularity:=hclock
    hlo:=hlo
    hK:=hK
    hband:=hband
    count:=Fintype.card B
    caps:=fun i=>c (enum i).val
    hga:=fun i=>hleft (enum i).val
    hgz:=fun i=>hright (enum i).val
    haH:=fun i=>(hcontacts (enum i).val).1
    hzH:=fun i=>(hcontacts (enum i).val).2
    hamass:=fun i=>hamass (enum i).val
    hzmass:=fun i=>hzmass (enum i).val
    weight:=fun i=>sideSquareColumnLR cut width (lc (enum i)) (rc (enum i))
    hweight:=fun _=>sideSquareColumnLR_nonneg hwidth _ _
    contact:=contact
    hmeas:=(((pointSideColumn_continuous hcut hwidth).comp
      (comparisonContactLimitCoordinate_continuous (M.f b))).measurable).indicator measurableSet_Ioo
    W:=bound
    hW:=hb0
    hbound:=hb
    hnonneg:=fun r=>indicator_nonneg (fun _ _=>pointSideColumn_nonneg hwidth _) r }
  have hfixed : fixed.fixed=fixedCapContactWeight (fun t : B=>(c t.val).left)
      (fun t=>(c t.val).right) (fun t=>sideSquareColumnLR cut width (lc t) (rc t)) A wcontact:=
    fixedCapContactWeight_equiv_contact_restrict enum (fun t : B=>(c t.val).left)
      (fun t=>(c t.val).right) (fun t=>sideSquareColumnLR cut width (lc t) (rc t)) (Ioo ag zg∩P.contactSet)
      (Ioo (M.l b).val (M.u b).val) wcontact
  have hcolumns : Tendsto (fun j=>∫r in fixed.domain,
      |m.unitColumn (M.as j) (M.bin j b) (C j).unit
        (fun u=>sideSquareColumn (C j).x cut (M.width j b) u.val) r-fixed.fixed r|) atTop (𝓝 0):=by
    simpa only [hfixed,width,wcontact,SelectedMasterFamily.width,FixedCapWeights.domain] using hfull.2.2.2.1
  have ht:=fixed.side_filled_eventually hN hlog hnd dphys ephys M.as M.mesh M.ho M.he M.hmesh
    M.mesh_nonneg M.mesh_tendsto (fun j=>(C j).K) (fun j=>M.bin j b) (fun j=>(C j).unit)
    (fun j=>(C j).x) (fun j=>M.width j b) hcut hwidth hwidths (M.widths b)
    (fun j=>(C j).start) (fun _=>rfl) (fun j=>(C j).strict_of_width hcut (hwidths j))
    (fun j=>(C j).mass) hhigh hag (hagz.trans hzg) (fun j i hi=>(hrow j i hi).2.2.2.2.1)
    (fun j=>m.unitColumn_support_band (M.as j) (M.bin j b) (C j).unit _
      (fun i hi=>(hrow j i hi).2.2.2.2.1) (fun i hi=>(hrow j i hi).2.2.2.2.2)) hcolumns hepsilon
  exact ht.mono (fun j hj=>hj.1)

end ActualHighOnlyOverlapMinimum.SelectedMasterFamily
end OAI.SKFluctuations.LaplaceWindowFormalization
