module

public import ComparisonNativeLocalCapScaleBounds

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 5000000
attribute [local instance] Classical.propDecidable

structure NativeContactDyadicBandFamily (m : NativeBandModel) extends NativeDyadicBandFamily m where
  alpha : ∀j, (model j).alpha.val.val=m.alpha.val.val
  thermal : ∀j, (model j).thermal=m.thermal
  caps : ∀j, (model j).capSet=nativeContactLeftCaps m
  massLo : ∀j, (model j).lo=m.U*(2:ℝ)^(j:ℕ)/2
  massHi : ∀j, (model j).hi=min (16*(m.U*(2:ℝ)^(j:ℕ))) 1

namespace NativeOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}

def Potential.constantContactDyadicFamily
    {a : NativeOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
    (p : a.Potential) {T H : ℝ} (hb : ∀u,a.b u=T) (hh : ∀u,a.h u=H)
    (ell : ℕ) (hell : 2 < ell+1) (Q Lside : ℝ) (hQ : 1 ≤ Q) (hLside : 0 ≤ Lside)
    (dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (hlog : 1 ≤ Real.log a.context.N) (hnd : 1/a.context.N ≤ a.context.d) :
    NativeContactDyadicBandFamily
      (((p.constantClockGeometry hb hh).canonical 1 zero_lt_one le_rfl
        (ell+1) hell Q Lside hQ hLside).toModel dphys e hlog hnd) where
  toNativeDyadicBandFamily := (p.constantClockGeometry hb hh).canonicalDyadicFamily
    ell hell Q Lside hQ hLside dphys e hlog hnd
  alpha := fun _ => rfl
  thermal := fun _ => rfl
  caps := fun _ => rfl
  massLo := fun _ => rfl
  massHi := fun _ => rfl

end NativeOverlapMinimum

namespace NativeContactDyadicBandFamily

theorem comparable_cap_mem_group {m : NativeBandModel} (g : NativeContactDyadicBandFamily m)
    (c : NativeActualCapInterval m)
    (hcase : (m.H c.a=0 ∧ m.H c.z=0) ∨ (c.a=0 ∧ m.H c.z=0) ∨ (m.H c.a=0 ∧ c.z=1))
    {j : comparisonMassDyadicIndices m.U}
    (hleft : m.U*(2:ℝ)^(j:ℕ) ≤ m.alpha.val.val c.a)
    (hright : m.alpha.val.val c.z ≤ min (16*(m.U*(2:ℝ)^(j:ℕ))) 1)
    {r : ℝ} (hr : r∈Ioo c.a c.z) : r∈(g.model j).ordinarySupport := by
  let v := m.U*(2:ℝ)^(j:ℕ)
  have hv : 0 < v := (comparison_mass_dyadic_scale m.hU j).1
  have hmass : 0 < m.alpha.val.val c.a := hv.trans_le hleft
  have hcap := native_actual_cap_subset_contactLeft_of_positive_mass m c hcase hmass hr
  have hcomp : ordConnectedComponent (g.model j).capSet r=Ioo c.a c.z := by
    rw [g.caps, nativeContactLeftCaps_component m hcap, native_actual_cap_component m c hcase hr]
  have hml := comparisonSweepQuantile_monotone m.hc m.hk m.hkc m.hm m.hM m.alpha
    (show v/2 ≤ m.alpha.val.val c.a by dsimp [v] at *; linarith)
  have hmr := comparisonSweepQuantile_monotone m.hc m.hk m.hkc m.hm m.hM m.alpha hright
  rw [comparisonSweepQuantile_inverse m.hc m.hk m.hkc m.hm m.hM m.alpha
    (show c.a∈Icc (0:ℝ) 1 from ⟨c.ha,c.haz.le.trans c.hz⟩)] at hml
  rw [comparisonSweepQuantile_inverse m.hc m.hk m.hkc m.hm m.hM m.alpha
    (show c.z∈Icc (0:ℝ) 1 from ⟨c.ha.trans c.haz.le,c.hz⟩)] at hmr
  have hgl : (g.model j).ag ≤ c.a := by rw [g.left]; exact hml
  have hgr : c.z ≤ (g.model j).zg := by rw [g.right]; exact hmr
  refine ⟨⟨hgl.trans_lt hr.1,hr.2.trans_le hgr⟩,Or.inl ⟨?_,?_⟩⟩
  · rw [g.caps]
    exact hcap
  · unfold NativeBandModel.ordinaryCapAdmissible
    rw [hcomp,csInf_Ioo c.haz,csSup_Ioo c.haz]
    refine ⟨hgl,hgr,?_,?_⟩
    · rw [g.massLo,g.alpha]
      dsimp [v] at hv
      linarith
    · rw [g.massHi,g.alpha]
      exact hright

theorem relevant_comparable_cap_mem_group {ι : Type*} [Fintype ι]
    {m : NativeBandModel} (g : NativeContactDyadicBandFamily m)
    (c : ι→NativeActualCapInterval m) (A : Set ℝ)
    (hcase : ∀i,(m.H (c i).a=0 ∧ m.H (c i).z=0) ∨
      ((c i).a=0 ∧ m.H (c i).z=0) ∨ (m.H (c i).a=0 ∧ (c i).z=1))
    {lo hi : ℝ} (hA : ∀r∈A,lo ≤ m.alpha.val.val r ∧ m.alpha.val.val r ≤ hi)
    (i : NativeRelevantComparableCap m c A) :
    ∃j : comparisonMassDyadicIndices m.U,
      lo/16 ≤ m.U*(2:ℝ)^(j:ℕ) ∧ m.U*(2:ℝ)^(j:ℕ) ≤ hi ∧
      Ioo (c i.val).a (c i.val).z ⊆ (g.model j).ordinarySupport := by
  obtain ⟨j,hlo,hhi,hl,hr⟩ := native_relevant_comparable_cap_dyadic_scale m c A hA i
  exact ⟨j,hlo,hhi,fun _ ht=>g.comparable_cap_mem_group (c i.val) (hcase i.val) hl hr ht⟩

end NativeContactDyadicBandFamily
end OAI.SKFluctuations.LaplaceWindowFormalization
