module

public import ComparisonWholeCapDecomposition

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.WholeUnitSideKernel
open Set MeasureTheory Filter
open scoped Topology ENNReal
attribute [local instance] Classical.propDecidable

theorem bounded_open_ordConnected_eq_Ioo {C : Set ℝ} (hC : IsOpen C)
    (hc : C.Nonempty) (hlo : BddBelow C) (hhi : BddAbove C) [OrdConnected C] :
    C=Ioo (sInf C) (sSup C) := by
  have hstrict : ∀ x ∈ C, sInf C<x ∧ x<sSup C := by
    intro x hx
    obtain ⟨l,z,hlz,hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hC.mem_nhds hx)
    have hmlo : (l+x)/2 ∈ C := hsub ⟨by linarith [hlz.1],by linarith [hlz.1,hlz.2]⟩
    have hmhi : (x+z)/2 ∈ C := hsub ⟨by linarith [hlz.1,hlz.2],by linarith [hlz.2]⟩
    exact ⟨(csInf_le hlo hmlo).trans_lt (by linarith [hlz.1]),
      lt_of_lt_of_le (by linarith [hlz.2]) (le_csSup hhi hmhi)⟩
  apply Subset.antisymm hstrict
  intro x hx
  obtain ⟨l,hl,hlx⟩ := exists_lt_of_csInf_lt hc hx.1
  obtain ⟨z,hz,hxz⟩ := exists_lt_of_lt_csSup hc hx.2
  apply (inferInstance : OrdConnected C).uIcc_subset hl hz
  rw [uIcc_of_le (hlx.trans hxz).le]
  exact ⟨hlx.le,hxz.le⟩

theorem wholeCap_component_endpoints {U : Set ℝ} {a b r : ℝ}
    (hopen : IsOpen U) (hbounded : U⊆Icc a b) (hr : r∈U) :
    let C := ordConnectedComponent U r
    a ≤ sInf C ∧ sInf C < r ∧ r < sSup C ∧ sSup C ≤ b ∧
      C = Ioo (sInf C) (sSup C) ∧ sInf C ∉ U ∧ sSup C ∉ U := by
  let C := ordConnectedComponent U r
  have hc : C.Nonempty := nonempty_ordConnectedComponent.mpr hr
  have hsubset : C⊆Icc a b := ordConnectedComponent_subset.trans hbounded
  have hlo : BddBelow C := ⟨a,fun x hx => (hsubset hx).1⟩
  have hhi : BddAbove C := ⟨b,fun x hx => (hsubset hx).2⟩
  have heq : C=Ioo (sInf C) (sSup C) :=
    bounded_open_ordConnected_eq_Ioo (wholeCap_component_isOpen hopen r) hc hlo hhi
  have hrC : r∈C := self_mem_ordConnectedComponent.mpr hr
  have hrI : r∈Ioo (sInf C) (sSup C) := heq ▸ hrC
  have hinf : sInf C∉U := by
    intro hbad
    have hcap : sInf C∈C := by
      apply mem_ordConnectedComponent.mpr
      rw [uIcc_of_ge hrI.1.le]
      intro x hx
      rcases eq_or_lt_of_le hx.1 with hxl|hxl
      · simpa only [hxl] using hbad
      · exact ordConnectedComponent_subset
          (heq.symm ▸ (show x∈Ioo (sInf C) (sSup C) from ⟨hxl,hx.2.trans_lt hrI.2⟩))
    have hfalse : sInf C∈Ioo (sInf C) (sSup C) := heq ▸ hcap
    exact lt_irrefl _ hfalse.1
  have hsup : sSup C∉U := by
    intro hbad
    have hcap : sSup C∈C := by
      apply mem_ordConnectedComponent.mpr
      rw [uIcc_of_le hrI.2.le]
      intro x hx
      rcases eq_or_lt_of_le hx.2 with hxz|hxz
      · simpa only [hxz] using hbad
      · exact ordConnectedComponent_subset
          (heq.symm ▸ (show x∈Ioo (sInf C) (sSup C) from ⟨hrI.1.trans_le hx.1,hxz⟩))
    have hfalse : sSup C∈Ioo (sInf C) (sSup C) := heq ▸ hcap
    exact lt_irrefl _ hfalse.2
  exact ⟨le_csInf hc (fun x hx => (hsubset hx).1),hrI.1,hrI.2,
    csSup_le hc (fun x hx => (hsubset hx).2),heq,hinf,hsup⟩

theorem wholeCap_component_endpoint_atoms_retained {U : Set ℝ} {a b r : ℝ}
    (hopen : IsOpen U) (hbounded : U⊆Icc a b) (hr : r∈U)
    (F : Finset (ordConnectedSection U)) :
    sInf (ordConnectedComponent U r)∈wholeCapRetainedRegion a b U F ∧
      sSup (ordConnectedComponent U r)∈wholeCapRetainedRegion a b U F := by
  obtain ⟨hlo,hlr,hrz,hhi,_,hlU,hzU⟩ := wholeCap_component_endpoints hopen hbounded hr
  exact ⟨Or.inl ⟨⟨hlo,hlr.le.trans (hbounded hr).2⟩,hlU⟩,
    Or.inl ⟨⟨(hbounded hr).1.trans hrz.le,hhi⟩,hzU⟩⟩

end OAI.SKFluctuations.WholeUnitSideKernel
