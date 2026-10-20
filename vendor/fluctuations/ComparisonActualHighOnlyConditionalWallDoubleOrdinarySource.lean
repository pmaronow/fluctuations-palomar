module

public import ComparisonActualHighOnlyOrdinaryPhysicalBudget
public import ComparisonActualHighOnlyCanonicalMassBudgets

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 16000000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
attribute [local instance] Classical.propDecidable
open ActualHighOnlyOverlapMinimum

theorem eventually_actual_high_only_wall_double_ordinary_source_budget
    (ell : ℕ) (hell : 2 < ell) (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Q:ℝ,1 ≤ Q ∧ ∀ᶠn:ℕ in atTop,
      ∀(a:ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (hs:a.data.s ≤ 1/4) (hsxs:a.data.s ≤ a.xs) (hspos:0 < a.data.s) (P:a.Potential)
        (ι:Type*) [Fintype ι] (c:ι→ShiftedCapInterval a P) (ag:ℝ),
      (∀t,∀r∈Ioo (c t).left (c t).right,wholeUnit P.negativeSet r=Ioo (c t).left (c t).right) →
      (∀t,P.H (c t).left=0 ∧ (P.H (c t).right=0 ∨ (c t).right=1)) →
      Pairwise (fun t u=>Disjoint (Ioo (c t).left (c t).right) (Ioo (c u).left (c u).right)) →
      0 < ag → ag ≤ a.R (min (32*a.data.s) 1) →
      NativePullbackClockRegularity a.alpha.val.val a.b a.h ag (a.R (min (32*a.data.s) 1)) →
      (∀t,ag ≤ (c t).left) → (∀t,a.alpha.val.val (c t).right ≤ min (32*a.data.s) 1) →
      ∀Lside cut:ℝ,0 ≤ Lside → 0 < cut → Real.log (1/cut) ≤ Lside →
      (∫u in 0..1,(P.retainedSupport c ag (a.R (min (32*a.data.s) 1))).indicator (fun _=>1)
        (a.R u)*a.shiftedNativeModel.thermal u) ≤ a.canonicalOrdinaryMassBudget ell Q Lside cut (2*a.data.s) := by
  obtain ⟨Q,hQ,Hphysical⟩:=eventually_actual_high_only_ordinary_optimized_budget ell hell Bclock
    (D:=D) hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Q,hQ,?_⟩
  filter_upwards [Hphysical] with n hn
  intro a hs hsxs hspos P ι inst c ag hwhole hcontacts hdisjoint hag hagz hclock hleft hright
    Lside cut hLside hcut hlogcut
  let zg:=a.R (min (32*a.data.s) 1)
  have hmass:min (32*a.data.s) 1∈Icc a.data.s 1:=by
    refine ⟨le_min (by linarith) a.data.hs1,min_le_right _ _⟩
  have hzg:zg ≤ 1:=(a.shiftedNativeModel.R_bounds _).2
  have hspec:a.alpha.val.val zg=min (32*a.data.s) 1:=a.shiftedNativeModel.R_spec hmass
  have hlow:a.data.s ≤ a.alpha.val.val ag:=
    (inverseConstraint_mass_mem zero_le_one a.data.hc a.data.hk a.data.hkc a.alpha ⟨hag.le,hagz.trans hzg⟩).1
  have hαleft t:a.data.s ≤ a.alpha.val.val (c t).left:=
    (inverseConstraint_mass_mem zero_le_one a.data.hc a.data.hk a.data.hkc a.alpha
      ⟨(c t).hleft,(c t).hlt.le.trans (c t).hright⟩).1
  have hrightRadius t:(c t).right ≤ zg:=by
    calc
      (c t).right=a.R (a.alpha.val.val (c t).right):=
        (a.shiftedNativeModel.R_inverse ⟨(c t).hleft.trans (c t).hlt.le,(c t).hright⟩).symm
      _ ≤ zg:=a.shiftedNativeModel.R_monotone (hright t)
  have hspan t:a.alpha.val.val (c t).right-a.alpha.val.val (c t).left ≤ 32*a.data.s:=by
    have HH:0 ≤ a.alpha.val.val (c t).left:=(a.alpha.val.property.1 _).1
    linarith [hright t,min_le_left (32*a.data.s) 1]
  have hY:0 < a.xs+min (32*a.data.s) 1:=by
    have Hxs:=a.hxs
    positivity
  have H:=hn a hs hsxs P ι c ag zg a.data.s (min (32*a.data.s) 1) 32 (32*a.data.s) (a.data.s/2)
    (a.xs+min (32*a.data.s) 1) a.data.s 32 Lside cut hwhole hcontacts hdisjoint hag hagz hzg hclock
    hleft hrightRadius a.data.hs.1 (by norm_num)
    (by have HU:=a.data.hU;linarith [min_le_left (32*a.data.s) 1]) hαleft hright
    (by positivity) (by rw [hspec];have Hα:0 ≤ a.alpha.val.val ag:=(a.alpha.val.property.1 _).1;linarith [min_le_left (32*a.data.s) 1])
    (by positivity) (by linarith) hY (by rw [hspec]) hspos (by norm_num)
    (fun t=>(hαleft t).trans (le_add_of_nonneg_right a.data.hU.le)) hspan hLside hcut hlogcut
  exact H.trans_eq (by
    dsimp only [ActualHighOnlyOverlapMinimum.ordinaryOptimizedBudget,
      ActualHighOnlyOverlapMinimum.canonicalOrdinaryMassBudget,ActualHighOnlyOverlapMinimum.canonicalMassPower,
      ActualHighOnlyOverlapMinimum.canonicalMassHeight,ActualHighOnlyOverlapMinimum.canonicalMassReverse,
      ActualHighOnlyOverlapMinimum.localCapDiameter,zg]
    simp only [show 16*(2*a.data.s)=32*a.data.s by ring,show 2*a.data.s/4=a.data.s/2 by ring])

end OAI.SKFluctuations.LaplaceWindowFormalization
