module

public import ComparisonNativeLocalDiameterAssembly

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 6000000
attribute [local instance] Classical.propDecidable

namespace NativeBandModel

def localDiameter (m : NativeBandModel) (v C : ℝ) : ℝ :=
  9*Real.log m.N*C*m.E/(m.N^m.delta*m.d^3*v)

theorem localDiameter_pos (m : NativeBandModel) {v C : ℝ} (hv : 0 < v) (hC : 0 < C) :
    0< m.localDiameter v C := by
  have hlog : 0 < Real.log m.N := by linarith [m.hlog]
  have hN : 0< m.N := zero_lt_one.trans_le m.hN
  have hd := m.hd;have hE := m.hE
  dsimp [localDiameter]
  positivity

theorem component_increment_local (m : NativeBandModel) {v C s t : ℝ}
    (hv : 0 < v) (_hC : 0 < C) (hs : s∈m.capSet) (ht : t∈ordConnectedComponent m.capSet s) (hst : s ≤ t)
    (hleft : v ≤ m.alpha.val.val (sInf (ordConnectedComponent m.capSet s))+m.U)
    (hspan : m.alpha.val.val (sSup (ordConnectedComponent m.capSet s))-
      m.alpha.val.val (sInf (ordConnectedComponent m.capSet s)) ≤ C*v) :
    orderedPathS (m.n+1) m.bf m.hf (m.alpha.val.val t)-
      orderedPathS (m.n+1) m.bf m.hf (m.alpha.val.val s) ≤ m.localDiameter v C := by
  obtain ⟨hlo,hls,hsz,hhi,heq,_,_⟩ := wholeCap_component_endpoints m.hopen
    (m.hcapSet.trans Ioo_subset_Icc_self) hs
  have hsI : s∈Ioo (sInf (ordConnectedComponent m.capSet s)) (sSup (ordConnectedComponent m.capSet s)) := ⟨hls,hsz⟩
  have htI := heq ▸ ht
  have hnegI : ∀r∈Ioo (sInf (ordConnectedComponent m.capSet s)) (sSup (ordConnectedComponent m.capSet s)),m.H r < 0 := by
    intro r hr;exact m.hnegative r (ordConnectedComponent_subset (heq.symm ▸ hr))
  have hbang : ∀ᵐ r,r∈Icc (0:ℝ) 1→m.H r < 0→deriv m.alpha.val.val r=
      comparisonCap m.N m.delta m.U m.Lcap m.E m.d (m.alpha.val.val r) := by
    filter_upwards [m.hbang] with r hr hri hrH
    simpa only [congrFun m.hMdef (m.alpha.val.val r)] using hr hri hrH
  have htravel := potential_comparison_cap_interval_travel (zero_lt_one.trans_le m.hN)
    m.hU m.hLcap m.hE m.hd (inverseIntegralConstraints_lipschitz m.hm m.hM m.alpha.property)
    (inverseConstraint_strictMonoOn m.hc m.hk m.hkc m.alpha.property)
    (fun r _=>m.alpha.val.property.1 r) hbang hlo hhi (hls.trans hsz).le hnegI
  have hwidth : sSup (ordConnectedComponent m.capSet s)-sInf (ordConnectedComponent m.capSet s) ≤
      C*m.E/(m.N^m.delta*m.d^3*v) := by
    calc
      _ ≤ (m.alpha.val.val (sSup (ordConnectedComponent m.capSet s))-
          m.alpha.val.val (sInf (ordConnectedComponent m.capSet s)))*m.E/(m.N^m.delta*m.d^3*v^2) := htravel.2.2 v hv hleft
      _ ≤ C*v*m.E/(m.N^m.delta*m.d^3*v^2) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hspan m.hE.le)
          (mul_nonneg (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans m.hN) _)
            (pow_nonneg m.hd.le _)) (sq_nonneg _))
      _ = _ := by field_simp
  have hinc : orderedPathS (m.n+1) m.bf m.hf (m.alpha.val.val t)-
      orderedPathS (m.n+1) m.bf m.hf (m.alpha.val.val s) ≤
      9*Real.log m.N*(sSup (ordConnectedComponent m.capSet s)-sInf (ordConnectedComponent m.capSet s)) := by
    rcases (m.hcomponent s hs).2 with hzH|hz1
    · exact (actual_variableEndpoint_comparison_cap_interior_geometry m.hc m.hk m.hkc m.hm m.hM
        m.hN m.hlog m.hd m.hnd m.hlam m.hld (m.n+1) (by omega) m.b m.h m.hb m.hlb m.hh m.hh0
        m.alpha m.H m.multiplier m.hH m.hJ m.hD hlo hhi hsI htI hst
        (m.hcomponent s hs).1 hzH (m.hnegative s hs) (m.hnegative t (ordConnectedComponent_subset ht))).1
    · rw [hz1] at hsI htI ⊢
      exact actual_variableEndpoint_comparison_terminal_cap_increment m.hc m.hk m.hkc m.hm m.hM
        m.hN m.hlog m.hd m.hnd m.hlam m.hld (m.n+1) (by omega) m.b m.h m.hb m.hlb m.hh m.hh0
        m.alpha m.H m.multiplier m.hH m.hJ m.hD hlo hsI htI hst
        (m.hcomponent s hs).1 (m.hnegative s hs) (m.hnegative t (ordConnectedComponent_subset ht))
  have hlog : 0 ≤ 9*Real.log m.N := by linarith [m.hlog]
  exact hinc.trans (by simpa only [localDiameter,mul_div_assoc,mul_assoc] using
    mul_le_mul_of_nonneg_left hwidth hlog)
end NativeBandModel

namespace NativeBandRetainedCaps

theorem unit_oscillation_local {m : NativeBandModel} (g : NativeBandRetainedCaps m)
    (s : NativeBandRefinement m) {v C : ℝ} (hv : 0 < v) (hC : 0 < C)
    (hleft : ∀t,v ≤ m.alpha.val.val (g.a t)+m.U)
    (hspan : ∀t,m.alpha.val.val (g.z t)-m.alpha.val.val (g.a t) ≤ C*v) (j : ℕ) :
    ∀i∈g.rows (s.as j),∀t∈g.rows (s.as j),
      wholeUnit m.capSet (m.R (physicalCutMass 0 (s.steps j) i.val))=
        wholeUnit m.capSet (m.R (physicalCutMass 0 (s.steps j) t.val))→
      physicalPathSecondMoment (m.n+1) (s.steps j) (m.q 0) t.val ≤
        physicalPathSecondMoment (m.n+1) (s.steps j) (m.q 0) i.val+
          (m.localDiameter v C+2*(s.mesh j*m.Cnode)) := by
  intro i hi t ht heunit
  have hs : OrderedSteps 0 (s.steps j) := sampleClockSteps_ordered m.q (s.as j) (s.ho j)
  have hDpos := m.localDiameter_pos hv hC
  have hD0 : 0 ≤ m.localDiameter v C+2*(s.mesh j*m.Cnode) :=
    add_nonneg hDpos.le (mul_nonneg (by norm_num) (mul_nonneg (s.hm0 j) m.Cnode_nonneg))
  by_cases hti : t.val ≤ i.val
  · have hm := physicalPathSecondMoment_mono (m.n+1) (s.steps j) hs (m.q 0) hti (by simp only [NativeBandRefinement.steps] at *;omega)
    linarith
  have hit : i.val < t.val := lt_of_not_ge hti
  have hpi := g.row_positive (s.as j) i hi
  have hmass : physicalCutMass 0 (s.steps j) i.val < physicalCutMass 0 (s.steps j) t.val := by
    rw [pathMassDifferences_eq_cutMass] at hpi
    have hm := physicalCutMass_monotone (s.steps j) hs (show i.val+1 ≤ t.val by omega)
    linarith
  have hrad := comparisonSweepQuantile_strictMono_native_geometry m.hc m.hk m.hkc m.hm m.hM m.alpha
    (physicalCutMass_mem _ hs _) (physicalCutMass_mem _ hs _) hmass
  obtain ⟨hiU,htU⟩ := equal_wholeUnits_of_strict_points_is_cap m.capSet heunit hrad
  have hil := g.row_nonterminal (s.as j) i hi
  have htl := g.row_nonterminal (s.as j) t ht
  have hci := physicalCutMass_sampleClockSteps m.q 0 (s.as j) i.val hil.le
  have hct := physicalCutMass_sampleClockSteps m.q 0 (s.as j) t.val htl.le
  have hnodeRight : m.R (partitionPoint 0 (s.as j) (i.val+1)) ≤
      m.R (physicalCutMass 0 (s.steps j) t.val) := by
    rw [hct]
    exact comparisonSweepQuantile_monotone m.hc m.hk m.hkc m.hm m.hM m.alpha
      (partitionPoint_mono (s.as j) (s.ho j) (by omega))
  have hglobal := (comparisonNativeSelectedRows_mem m.hc m.hk m.hkc m.hm m.hM m.q m.alpha
    (s.as j) g.a g.z m.H g.D i).mp
      (comparisonConstructedRows_subset m.hc m.hk m.hkc m.hm m.hM m.q m.alpha
        (s.as j) g.a g.z m.H g.D m.ag m.zg hi)
  have hcapWitness : ∃u,m.R (physicalCutMass 0 (s.steps j) i.val)∈Ioo (g.a u) (g.z u) := by
    rcases hglobal.2.2 with ⟨u,hu,_⟩|⟨r,hr,hrH⟩
    · exact ⟨u,by simpa only [hci] using hu⟩
    · obtain ⟨_,hlo,_,_,heq,_,_⟩ := wholeCap_component_endpoints m.hopen
        (m.hcapSet.trans Ioo_subset_Icc_self) hiU
      have htiI := heq ▸ htU
      have hrI : r∈ordConnectedComponent m.capSet (m.R (physicalCutMass 0 (s.steps j) i.val)) := by
        rw [heq]
        refine ⟨hlo.trans_le ?_,lt_of_le_of_lt (hr.2.trans hnodeRight) htiI.2⟩
        simpa only [hci] using hr.1
      have hh := m.hnegative r (ordConnectedComponent_subset hrI)
      rw [hrH] at hh
      exact (lt_irrefl 0 hh).elim
  obtain ⟨u,hu⟩ := hcapWitness
  have hcomp : ordConnectedComponent m.capSet (m.R (physicalCutMass 0 (s.steps j) i.val))=Ioo (g.a u) (g.z u) := by
    have hh := g.hwhole u _ hu
    simpa only [wholeUnit,ite_eq_left hiU] using hh
  have hcompLeft : sInf (ordConnectedComponent m.capSet (m.R (physicalCutMass 0 (s.steps j) i.val)))=g.a u := by
    rw [hcomp,csInf_Ioo (g.haz u)]
  have hcompRight : sSup (ordConnectedComponent m.capSet (m.R (physicalCutMass 0 (s.steps j) i.val)))=g.z u := by
    rw [hcomp,csSup_Ioo (g.haz u)]
  have hinc := m.component_increment_local hv hC hiU htU hrad.le
    (by simpa only [hcompLeft] using hleft u) (by simpa only [hcompLeft,hcompRight] using hspan u)
  have had := comparisonVariableEndpoint_clocks_admissible m.hc m.hk m.hkc m.hm m.hM
    m.b m.h m.hd.ne' m.hlam.le m.hlb m.hb m.hh m.hh0 m.alpha
  have hui : 0 < partitionPoint 0 (s.as j) i.val := by
    have haI : m.ag∈Icc (0:ℝ) 1 := ⟨m.hag.le,m.hagz.trans m.hzg⟩
    have hapos := inverseConstraint_strictMonoOn m.hc m.hk m.hkc m.alpha.property
      (show (0:ℝ)∈Icc (0:ℝ) 1 by simp) haI m.hag
    have hh := (g.row_mass_bounds (s.as j) (s.ho j) i hi).1
    rw [hci] at hh
    simpa only [m.alpha.property.1] using hapos.trans_le hh
  have herr := physicalSampledNodeSecondMoment_increment_le m.n m.bf m.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) (s.as j) (s.ho j) (s.he j) (s.hm j)
    hil.le htl.le hui (hui.trans_le (partitionPoint_mono (s.as j) (s.ho j) hit.le))
  rw [←comparisonSweepQuantile_spec m.hc m.hk m.hkc m.hm m.hM m.alpha (partitionPoint_mem (s.as j) (s.ho j) i.val),
    ←comparisonSweepQuantile_spec m.hc m.hk m.hkc m.hm m.hM m.alpha (partitionPoint_mem (s.as j) (s.ho j) t.val)] at herr
  rw [←hci,←hct] at herr
  change physicalPathSecondMoment (m.n+1) (s.steps j) (m.q 0) t.val-
    physicalPathSecondMoment (m.n+1) (s.steps j) (m.q 0) i.val ≤
    orderedPathS (m.n+1) m.bf m.hf (m.alpha.val.val (m.R (physicalCutMass 0 (s.steps j) t.val)))-
      orderedPathS (m.n+1) m.bf m.hf (m.alpha.val.val (m.R (physicalCutMass 0 (s.steps j) i.val)))+
        2*(s.mesh j*m.Cnode) at herr
  linarith
theorem unit_oscillation_outer {m : NativeBandModel} (g : NativeBandRetainedCaps m)
    (s : NativeBandRefinement m) (j : ℕ) :
    ∀i∈g.rows (s.as j),∀t∈g.rows (s.as j),
      wholeUnit m.capSet (m.R (physicalCutMass 0 (s.steps j) i.val))=
        wholeUnit m.capSet (m.R (physicalCutMass 0 (s.steps j) t.val))→
      physicalPathSecondMoment (m.n+1) (s.steps j) (m.q 0) t.val ≤
        physicalPathSecondMoment (m.n+1) (s.steps j) (m.q 0) i.val+
          (m.localDiameter (m.lo+m.U) m.Ko+2*(s.mesh j*m.Cnode)) := by
  have hv : 0 < m.lo+m.U := by linarith [m.hlo,m.hU]
  apply g.unit_oscillation_local s hv (zero_lt_one.trans_le m.hKo) _ _ j
  · intro t;linarith [g.hamass t]
  · intro t;linarith [g.hamass t,g.hzmass t,m.hband]

end NativeBandRetainedCaps
end OAI.SKFluctuations.LaplaceWindowFormalization
