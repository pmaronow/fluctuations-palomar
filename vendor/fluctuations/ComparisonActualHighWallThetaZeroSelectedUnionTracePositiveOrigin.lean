module

public import ComparisonActualHighWallSelectedUnionTrace
public import ComparisonActualHighWallThetaZeroSelectedColumnGeometryPositiveOrigin
public import ComparisonActualHighWallThetaZeroSelectedLedger
public import ComparisonActualHighWallThetaZeroSelectedCapMassPositiveOrigin
public import ComparisonActualHighWallThetaZeroFilledTraceRatesPositiveOrigin
public import ComparisonShiftedNativePositiveOriginColumnAssembly

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
set_option maxHeartbeats 32000000
attribute [local instance] Classical.propDecidable
namespace ActualThetaZeroOverlapMinimum.SelectedMasterFamily
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {W : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
variable {P : W.Potential} {ι : Type*} [Fintype ι] {c : ι→ShiftedCapInterval W P}
variable {Dcuts : Finset ℝ} {ag zg w cut Q : ℝ} {bins ell : ℕ} {hbins : 0< bins}
variable (M : SelectedMasterFamily W P c Dcuts ag zg bins hbins w cut ell Q)

theorem bin_union_filled_eventually_positive_origin
    (hwhole : ∀t,∀r∈Ioo (c t).left (c t).right,wholeUnit P.negativeSet r=Ioo (c t).left (c t).right)
    (hcontacts : ∀t,(P.H (c t).left=0 ∨ (c t).left=W.data.rmin) ∧ (P.H (c t).right=0 ∨ (c t).right=1))
    (hinitialU : ∀t,(c t).left=W.data.rmin → comparisonSmallMass W.data.N W.data.E≤
      W.alpha.val.val (c t).right-W.alpha.val.val (c t).left)
    (hdisjoint : Pairwise (fun t u=>Disjoint (Ioo (c t).left (c t).right) (Ioo (c u).left (c u).right)))
    (hag : W.data.rmin≤ ag) (hagz : ag≤ zg) (hzg : zg≤1)
    (hleft : ∀t,ag≤(c t).left) (hright : ∀t,(c t).right≤ zg)
    {lo hi K0 : ℝ} (hlo : 0≤ lo) (hK : 1≤ K0)
    (hband : hi+comparisonSmallMass W.data.N W.data.E≤ K0*(lo+comparisonSmallMass W.data.N W.data.E))
    (hamass : ∀t,lo≤ W.alpha.val.val (c t).left) (hzmass : ∀t,W.alpha.val.val (c t).right≤ hi)
    (hN : 1≤ W.data.N) (hlog : 1≤ Real.log W.data.N) (hnd : 1/W.data.N≤ W.data.d)
    (b : Fin bins) (dphys : ℕ) (ephys : Fin (dphys+1)≃FeatureIndex (n+1))
    {epsilon : ℝ} (hepsilon : 0< epsilon) :
    let m:=W.shiftedNativeModel
    ∀ᶠj in atTop,
      (2*(∫r,deriv W.alpha.val.val r*m.unitColumn (M.as j) (M.bin j b)
        (fun _=>(0:Fin 1)) (fun _=>1) r∂m.radiusMeasure dphys ephys (M.as j) (M.ho j))+
        2*M.mesh j)/(W.alpha.val.val ag)^2≤
      (108*K0^2*(Real.log W.data.N)^2/((n+1:ℝ)*laplaceComparisonStrength W.data.d W.lam zg*(W.alpha.val.val ag)^2))*
        (M.f b ⟨1,by simp⟩)+epsilon := by
  dsimp only
  let m:=W.shiftedNativeModel
  let C:=fun j=>M.co j b
  let B:={t : ι //M.labels t=b}
  let A:=(Ioo ag zg∩P.contactSet)∩Ioo (M.l b).val (M.u b).val
  have hrow j i (hi:i∈M.bin j b):=(P.retainedRows_mem c Dcuts ag zg (M.as j) i).mp
    (P.retainedBin_subset c Dcuts ag zg (M.as j) bins w b hi)
  have hhigh j i (hi:i∈M.bin j b) : m.u0≤ partitionPoint 0 (M.as j) i.val:=(hrow j i hi).2.2.2.1
  have hg:=P.retainedBin_column_geometry_positive_origin c Dcuts M.as M.mesh M.ho M.he M.hmesh M.mesh_nonneg
    M.mesh_tendsto hag hzg hleft hright bins hbins (fun _=>w) hwhole M.labels M.capLabels b
    (M.l b).val (M.u b).val (M.geometry b)
  let moving:=fun j=>m.unitColumn (M.as j) (M.bin j b) (fun _=>(0:Fin 1)) (fun _=>1)
  let base:=fixedCapContactWeight (fun t : B=>(c t.val).left) (fun t=>(c t.val).right)
    (fun _=>1) A (fun _=>1)
  have hdis : Pairwise (fun t u : B=>Disjoint (Ioo (c t.val).left (c t.val).right)
      (Ioo (c u.val).left (c u.val).right)):=fun t u htu=>hdisjoint (fun h=>htu (Subtype.ext h))
  have hcontact (t : B) : Disjoint (Ioo (c t.val).left (c t.val).right) A:=by
    apply Set.disjoint_left.mpr
    intro r hr hrA
    have HH:=(c t.val).negative r hr
    rw [hrA.1.2.2] at HH
    exact lt_irrefl _ HH
  have hband01 : Ioo ag zg⊆Ioo (0:ℝ) 1:=fun r hr=>
    ⟨W.data.hrbounds.1.le.trans_lt (lt_of_le_of_lt hag hr.1),hr.2.trans_le hzg⟩
  have hgeometry:=ae_mono (Measure.restrict_mono hband01 le_rfl) (M.geometry b)
  have hp : ∀ᵐr∂volume.restrict (Ioo ag zg),Tendsto (fun j=>moving j r) atTop (𝓝 (base r)):=by
    filter_upwards [hg.2.1,hg.2.2,hgeometry] with r hcap hout hgeom
    by_cases hc : ∃t : B,r∈Ioo (c t.val).left (c t.val).right
    · obtain ⟨t,ht⟩:=hc
      rw [show base r=1 from fixedCapContactWeight_at_cap _ _ _ A _ hdis hcontact t ht]
      apply tendsto_nhds_of_eventually_eq
      filter_upwards [hcap t ht] with j hj
      obtain ⟨i,hi,hil,_,hri⟩:=hj
      exact (m.unitColumn_on_original_cell (M.as j) (M.ho j) (M.bin j b) _ _ i hil hri).trans
        (ite_eq_left hi)
    · have hn:=not_exists.mp hc
      by_cases hrA : r∈A
      · rw [show base r=1 from fixedCapContactWeight_at_contact _ _ _ A _ hcontact hrA]
        apply tendsto_nhds_of_eventually_eq
        filter_upwards [hgeom] with j hj
        dsimp only [moving]
        have HS:=hj.mpr ⟨⟨hrA.1.1,Or.inr hrA.1.2.2⟩,hrA.2⟩
        rw [m.unitColumn_binary_eq_support (M.as j) (M.ho j) (M.bin j b) _
          (fun i hi=>(hrow j i hi).1) r,indicator_of_mem HS]
      · rw [show base r=0 from fixedCapContactWeight_outside _ _ _ A _ hn hrA]
        have HC:=hout hn hrA
        have HE j : m.unitColumn (M.as j) (M.bin j b) (C j).unit (fun _=>1) r=moving j r:=by
          dsimp only [moving]
          rw [m.unitColumn_binary_eq_support (M.as j) (M.ho j) (M.bin j b) _
            (fun i hi=>(hrow j i hi).1) r,
            m.unitColumn_binary_eq_support (M.as j) (M.ho j) (M.bin j b) _ (fun i hi=>(hrow j i hi).1) r]
        change Tendsto (fun j=>m.unitColumn (M.as j) (M.bin j b) (C j).unit (fun _=>1) r) atTop (𝓝 0) at HC
        simpa only [HE] using HC
  have hL1:=bounded_contact_weights_tendsto_L1 (B:=1) (Ioo ag zg) (by simp) moving base
    (fun j=>(m.unitColumn_measurable _ _ _ _).aestronglyMeasurable.restrict)
    (fun j=>ae_of_all _ (fun r=>by
      dsimp only [moving]
      rw [m.unitColumn_binary_eq_support (M.as j) (M.ho j) (M.bin j b) _ (fun i hi=>(hrow j i hi).1) r]
      simp only [Set.indicator_apply];split_ifs <;>norm_num)) hp
  let enum : Fin (Fintype.card B)≃B:=(Fintype.equivFin B).symm
  let contact:=(Ioo (M.l b).val (M.u b).val).indicator (fun _ : ℝ=>(1:ℝ))
  let fixed : PositiveOriginFixedCapWeights W P:={
    ag:=ag
    zg:=zg
    lo:=lo
    hi:=hi
    K:=K0
    hag:=hag
    hagz:=hagz
    hzg:=hzg
    hlo:=hlo
    hK:=hK
    hband:=hband
    count:=Fintype.card B
    caps:=fun i=>c (enum i).val
    hga:=fun i=>hleft (enum i).val
    hgz:=fun i=>hright (enum i).val
    haH:=fun i=>(hcontacts (enum i).val).1
    hinitialU:=fun i=>hinitialU (enum i).val
    hzH:=fun i=>(hcontacts (enum i).val).2
    hamass:=fun i=>hamass (enum i).val
    hzmass:=fun i=>hzmass (enum i).val
    weight:=fun _=>1
    hweight:=fun _=>zero_le_one
    contact:=contact
    hmeas:=measurable_const.indicator measurableSet_Ioo
    W:=1
    hW:=zero_le_one
    hbound:=fun r=>by simp only [contact,Set.indicator_apply];split_ifs <;>norm_num
    hnonneg:=fun r=>indicator_nonneg (fun _ _=>zero_le_one) r }
  have hfixed : fixed.fixed=base:=fixedCapContactWeight_equiv_contact_restrict enum
    (fun t : B=>(c t.val).left) (fun t=>(c t.val).right) (fun _=>1)
    (Ioo ag zg∩P.contactSet) (Ioo (M.l b).val (M.u b).val) (fun _=>1)
  have hcolumns : Tendsto (fun j=>∫r in fixed.domain,|moving j r-fixed.fixed r|) atTop (𝓝 0):=by
    simpa only [hfixed,PositiveOriginFixedCapWeights.domain] using hL1
  have hmasslim : Tendsto (fun j=>∑i,physicalSelectedCellMass (sampleClockSteps m.q 0 (M.as j))
      (M.bin j b) i) atTop (𝓝 (M.f b ⟨1,by simp⟩)):=by
    have HE j : (∑i,physicalSelectedCellMass (sampleClockSteps m.q 0 (M.as j)) (M.bin j b) i)=M.width j b:=by
      rw [sum_physicalSelectedCellMass_eq_window]
      exact (M.co j b).width.symm
    exact (M.widths b).congr (fun j=>(HE j).symm)
  have ht:=fixed.union_filled_eventually hN hlog hnd dphys ephys M.as M.mesh M.ho M.he M.hmesh
    M.mesh_nonneg M.mesh_tendsto (fun j=>M.bin j b) hhigh hag (hagz.trans hzg)
    (fun j i hi=>(hrow j i hi).2.2.2.2.1) hmasslim
    (fun j=>m.unitColumn_support_band (M.as j) (M.bin j b) (fun _=>(0:Fin 1)) _
      (fun i hi=>(hrow j i hi).2.2.2.2.1) (fun i hi=>(hrow j i hi).2.2.2.2.2)) hcolumns hepsilon
  exact ht.mono (fun j hj=>hj.1)

theorem union_filled_eventually_positive_origin
    (hwhole : ∀t,∀r∈Ioo (c t).left (c t).right,wholeUnit P.negativeSet r=Ioo (c t).left (c t).right)
    (hcontacts : ∀t,(P.H (c t).left=0 ∨ (c t).left=W.data.rmin) ∧ (P.H (c t).right=0 ∨ (c t).right=1))
    (hinitialU : ∀t,(c t).left=W.data.rmin → comparisonSmallMass W.data.N W.data.E≤
      W.alpha.val.val (c t).right-W.alpha.val.val (c t).left)
    (hdisjoint : Pairwise (fun t u=>Disjoint (Ioo (c t).left (c t).right) (Ioo (c u).left (c u).right)))
    (hag : W.data.rmin≤ ag) (hagz : ag≤ zg) (hzg : zg≤1)
    (hleft : ∀t,ag≤(c t).left) (hright : ∀t,(c t).right≤ zg)
    {lo hi K0 : ℝ} (hlo : 0≤ lo) (hK : 1≤ K0)
    (hband : hi+comparisonSmallMass W.data.N W.data.E≤ K0*(lo+comparisonSmallMass W.data.N W.data.E))
    (hamass : ∀t,lo≤ W.alpha.val.val (c t).left) (hzmass : ∀t,W.alpha.val.val (c t).right≤ hi)
    (hN : 1≤ W.data.N) (hlog : 1≤ Real.log W.data.N) (hnd : 1/W.data.N≤ W.data.d)
    {B : ℕ} (hB : 0< B) (label : Fin B→Fin bins) (hlabel : Function.Injective label)
    (dphys : ℕ) (ephys : Fin (dphys+1)≃FeatureIndex (n+1))
    {epsilon : ℝ} (hepsilon : 0< epsilon) :
    ∀ᶠj in atTop,M.unionFilled label dphys ephys j≤
      (108*K0^2*(Real.log W.data.N)^2/((n+1:ℝ)*laplaceComparisonStrength W.data.d W.lam zg*(W.alpha.val.val ag)^2))*
        (∑b,M.f (label b) ⟨1,by simp⟩)+epsilon := by
  let m:=W.shiftedNativeModel
  let price:=108*K0^2*(Real.log W.data.N)^2/((n+1:ℝ)*laplaceComparisonStrength W.data.d W.lam zg*(W.alpha.val.val ag)^2)
  let t:=fun j b=>(2*(∫r,deriv W.alpha.val.val r*m.unitColumn (M.as j) (M.bin j (label b))
      (fun _=>(0:Fin 1)) (fun _=>1) r∂m.radiusMeasure dphys ephys (M.as j) (M.ho j))+
      2*M.mesh j)/(W.alpha.val.val ag)^2
  have hBr : 0<(B:ℝ):=by exact_mod_cast hB
  have hc : 0< W.alpha.val.val ag:=m.profile_pos_of_positive_origin W.data.hs.1 hag (hagz.trans hzg)
  have ht : ∀ᶠj in atTop,∀b : Fin B,t j b≤ price*(M.f (label b) ⟨1,by simp⟩)+epsilon/(B:ℝ):=by
    apply Filter.eventually_all.mpr
    intro b
    exact M.bin_union_filled_eventually_positive_origin hwhole hcontacts hinitialU hdisjoint hag hagz hzg hleft hright
      hlo hK hband hamass hzmass hN hlog hnd (label b) dphys ephys (div_pos hepsilon hBr)
  have Hunion j : M.unionFilled label dphys ephys j≤∑b,t j b:=by
    let mu:=m.radiusMeasure dphys ephys (M.as j) (M.ho j)
    have HI b : Integrable (fun r=>deriv W.alpha.val.val r*m.unitColumn (M.as j) (M.bin j (label b))
        (fun _=>(0:Fin 1)) (fun _=>1) r) mu:=by
      have hhigh i (hi:i∈M.bin j (label b)) : m.u0≤ partitionPoint 0 (M.as j) i.val:=
        ((P.retainedRows_mem c Dcuts ag zg (M.as j) i).mp
          (P.retainedBin_subset c Dcuts ag zg (M.as j) bins w (label b) hi)).2.2.2.1
      have HX:=(m.original_coefficients_mass_radius_eq (M.as j) (M.ho j) _
        (m.nativeColumn_high_support (M.as j) (M.bin j (label b)) (fun _=>(0:Fin 1)) (fun _=>1) hhigh)).1
      exact HX.mono_measure (m.radiusMeasure_le_volume dphys ephys (M.as j) (M.ho j))
    have HE : (∫r,deriv W.alpha.val.val r*m.unitColumn (M.as j) (M.selected label j)
        (fun _=>(0:Fin 1)) (fun _=>1) r∂mu)=
        ∑b,∫r,deriv W.alpha.val.val r*m.unitColumn (M.as j) (M.bin j (label b))
          (fun _=>(0:Fin 1)) (fun _=>1) r∂mu:=by
      change (∫r,deriv W.alpha.val.val r*m.unitColumn (M.as j)
        (Finset.univ.biUnion (fun b=>M.bin j (label b))) (fun _=>(0:Fin 1)) (fun _=>1) r∂mu)=_
      simp_rw [m.unitColumn_binary_biUnion_eq_sum (M.as j) (fun b=>M.bin j (label b))
        (M.bin_disjoint label hlabel j),Finset.mul_sum]
      exact integral_finsetSum _ (fun b _=>HI b)
    have Hsum : (∑b,t j b)=
        (2*(∑b,∫r,deriv W.alpha.val.val r*m.unitColumn (M.as j) (M.bin j (label b))
          (fun _=>(0:Fin 1)) (fun _=>1) r∂mu)+2*(B:ℝ)*M.mesh j)/(W.alpha.val.val ag)^2:=by
      dsimp only [t]
      rw [←Finset.sum_div,Finset.sum_add_distrib,←Finset.mul_sum]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      dsimp only [mu]
      ring
    rw [Hsum]
    unfold unionFilled
    change (2*(∫r,deriv W.alpha.val.val r*m.unitColumn (M.as j) (M.selected label j)
      (fun _=>(0:Fin 1)) (fun _=>1) r∂mu)+2*M.mesh j)/(W.alpha.val.val ag)^2≤_
    rw [HE]
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    have hB1 : (1:ℝ)≤ B:=by exact_mod_cast (show 1≤ B by omega)
    nlinarith [M.mesh_nonneg j]
  filter_upwards [ht] with j hj
  have HS:=Finset.sum_le_sum (s:=Finset.univ) (fun (b : Fin B) _=>hj b)
  have HE : (∑b : Fin B,(price*(M.f (label b) ⟨1,by simp⟩)+epsilon/(B:ℝ)))=
      price*(∑b : Fin B,M.f (label b) ⟨1,by simp⟩)+epsilon:=by
    rw [Finset.sum_add_distrib,←Finset.mul_sum]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp [hBr.ne']
  exact (Hunion j).trans (HS.trans_eq HE)

end ActualThetaZeroOverlapMinimum.SelectedMasterFamily
end OAI.SKFluctuations.LaplaceWindowFormalization
