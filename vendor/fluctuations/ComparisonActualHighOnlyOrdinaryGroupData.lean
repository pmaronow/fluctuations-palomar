module

public import ComparisonActualHighOnlyCapEndpointLedger
public import ComparisonActualHighOnlyOrdinaryCover

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 10000000
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualHighOnlyOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}

abbrev Potential.OrdinaryCapIndex (P : a.Potential) {ι : Type*}
    (c : ι→ShiftedCapInterval a P) (A : Set ℝ) (K v : ℝ):=
  {t : ι // (A∩Ioo (c t).left (c t).right).Nonempty ∧
    v ≤ a.alpha.val.val (c t).left ∧ a.alpha.val.val (c t).right ≤ min (K*v) 1}

def Potential.ordinaryCapFamily (P : a.Potential) {ι : Type*}
    (c : ι→ShiftedCapInterval a P) (A : Set ℝ) (K v : ℝ)
    (t : P.OrdinaryCapIndex c A K v) : ShiftedCapInterval a P:=c t.val

theorem Potential.ordinary_group_geometry (P : a.Potential) {ι : Type*}
    (c : ι→ShiftedCapInterval a P) (A : Set ℝ) {K v : ℝ}
    (hK : 1 ≤ K) (hv : 0< v) (hv1 : v ≤ 1) (hs : a.data.s< v/2) :
    let m:=a.shiftedNativeModel
    let ag:=m.R (v/2)
    let zg:=m.R (min (K*v) 1)
    (0:ℝ)< ag ∧ zg ≤ 1 ∧ ag ≤ zg ∧
      a.alpha.val.val ag=v/2 ∧ a.alpha.val.val zg=min (K*v) 1 ∧
      ∀t : P.OrdinaryCapIndex c A K v,
        ag ≤ (P.ordinaryCapFamily c A K v t).left ∧
        (P.ordinaryCapFamily c A K v t).right ≤ zg ∧
        v ≤ a.alpha.val.val (P.ordinaryCapFamily c A K v t).left+
          comparisonSmallMass a.data.N a.data.E ∧
        a.alpha.val.val (P.ordinaryCapFamily c A K v t).right-
          a.alpha.val.val (P.ordinaryCapFamily c A K v t).left ≤ K*v := by
  dsimp only
  let m:=a.shiftedNativeModel
  have hlo : v/2∈Icc m.u0 1:=⟨hs.le,by linarith⟩
  have hKV : v/2 ≤ K*v:=by nlinarith [mul_le_mul_of_nonneg_right hK hv.le]
  have hhi : min (K*v) 1∈Icc m.u0 1:=⟨hs.le.trans (le_min hKV (by linarith)),min_le_right _ _⟩
  have hag : (0:ℝ)< m.R (v/2):=by
    simpa only [m.R_left] using m.R_strictMonoOn ⟨le_rfl,m.hu.2⟩ hlo hs
  refine ⟨hag,(m.R_bounds _).2,m.R_monotone (le_min hKV (by linarith)),m.R_spec hlo,m.R_spec hhi,?_⟩
  intro t
  have ht:=t.property
  have hleft : m.R (v/2) ≤ (c t.val).left:=by
    calc
      m.R (v/2) ≤ m.R (a.alpha.val.val (c t.val).left):=
        m.R_monotone ((by linarith : v/2 ≤ v).trans ht.2.1)
      _ = (c t.val).left:=m.R_inverse ⟨(c t.val).hleft,(c t.val).hlt.le.trans (c t.val).hright⟩
  have hright : (c t.val).right ≤ m.R (min (K*v) 1):=by
    calc
      (c t.val).right=m.R (a.alpha.val.val (c t.val).right):=
        (m.R_inverse ⟨(c t.val).hleft.trans (c t.val).hlt.le,(c t.val).hright⟩).symm
      _ ≤ _:=m.R_monotone ht.2.2
  refine ⟨hleft,hright,ht.2.1.trans (le_add_of_nonneg_right a.data.hU.le),?_⟩
  have hα0:=(a.alpha.val.property.1 (c t.val).left).1
  have hαr:=ht.2.2.trans (min_le_left _ _)
  change a.alpha.val.val (c t.val).right-a.alpha.val.val (c t.val).left ≤ K*v
  linarith

theorem Potential.ordinary_group_contacts (P : a.Potential) {ι : Type*}
    (c : ι→ShiftedCapInterval a P) (A : Set ℝ) {K v : ℝ} (hs : a.data.s< v)
    (hcontacts : ∀t,(P.H (c t).left=0 ∨ (c t).left=(0:ℝ)) ∧
      (P.H (c t).right=0 ∨ (c t).right=1)) :
    ∀t : P.OrdinaryCapIndex c A K v,
      P.H (P.ordinaryCapFamily c A K v t).left=0 ∧
        (P.H (P.ordinaryCapFamily c A K v t).right=0 ∨
          (P.ordinaryCapFamily c A K v t).right=1) := by
  intro t
  refine ⟨?_,(hcontacts t.val).2⟩
  rcases (hcontacts t.val).1 with HH|HH
  · exact HH
  · have HX:=t.property.2.1
    rw [HH,a.alpha.property.1] at HX
    exact False.elim (hs.not_ge HX)

theorem Potential.ordinaryGroup_eq_retainedSupport (P : a.Potential) {ι : Type*}
    (c : ι→ShiftedCapInterval a P) (A : Set ℝ) {K : ℝ} (hK : 1 ≤ K)
    (j : comparisonMassDyadicIndices (comparisonSmallMass a.data.N a.data.E))
    (hv1 : comparisonSmallMass a.data.N a.data.E*(2:ℝ)^(j:ℕ) ≤ 1)
    (hs : a.data.s<(comparisonSmallMass a.data.N a.data.E*(2:ℝ)^(j:ℕ))/2) :
    let v:=comparisonSmallMass a.data.N a.data.E*(2:ℝ)^(j:ℕ)
    let m:=a.shiftedNativeModel
    P.ordinaryGroup c A K j=P.retainedSupport (P.ordinaryCapFamily c A K v)
      (m.R (v/2)) (m.R (min (K*v) 1)) := by
  dsimp only
  let v:=comparisonSmallMass a.data.N a.data.E*(2:ℝ)^(j:ℕ)
  let m:=a.shiftedNativeModel
  have hv : 0< v:=(comparison_mass_dyadic_scale a.data.hU j).1
  obtain ⟨hag,hzg,_,_,_,hcap⟩:=P.ordinary_group_geometry c A hK hv hv1 hs
  ext r
  change (r∈P.contactSet∩Ioo (m.R (v/2)) (m.R (min (K*v) 1)) ∨
    r∈⋃t : P.OrdinaryCapIndex c A K v,Ioo (c t.val).left (c t.val).right) ↔
    r∈Ioo (m.R (v/2)) (m.R (min (K*v) 1)) ∧
      ((∃t : P.OrdinaryCapIndex c A K v,r∈Ioo (c t.val).left (c t.val).right) ∨ P.H r=0)
  constructor
  · rintro (⟨hrH,hrBand⟩|hrCap)
    · exact ⟨hrBand,Or.inr hrH.2⟩
    · obtain ⟨t,ht⟩:=mem_iUnion.mp hrCap
      exact ⟨⟨(hcap t).1.trans_lt ht.1,ht.2.trans_le (hcap t).2.1⟩,Or.inl ⟨t,ht⟩⟩
  · rintro ⟨hrBand,⟨t,ht⟩|hrH⟩
    · exact Or.inr (mem_iUnion.mpr ⟨t,ht⟩)
    · exact Or.inl ⟨⟨⟨hag.le.trans hrBand.1.le,hrBand.2.le.trans hzg⟩,hrH⟩,hrBand⟩

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
