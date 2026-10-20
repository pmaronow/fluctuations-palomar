module

public import ComparisonActualHighOnlyOrdinaryPhysicalBudget
public import ComparisonActualHighOnlyOrdinaryGroupData

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 6000000
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}

def Potential.canonicalOrdinarySupport
    {a : ActualHighOnlyOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
    (P : a.Potential) (F : Finset (ordConnectedSection P.negativeSet)) (A : Set ℝ) (v : ℝ) : Set ℝ :=
  P.retainedSupport (P.ordinaryCapFamily (P.capFamily F) A 16 v)
    (a.shiftedNativeModel.R (v/2)) (a.shiftedNativeModel.R (min (16*v) 1))

end ActualHighOnlyOverlapMinimum

theorem eventually_actual_high_only_ordinary_mass_budget
    (ell : ℕ) (hell : 2 < ell) (Bclock : ℝ) {margin delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < margin) (hdelta : 0 < delta) (hroom : delta < 3*margin)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0  ≤  Az) (hC0 : 0 < C0) (hCt : 0  ≤  Ct) :
    ∃Q : ℝ,1  ≤  Q ∧ ∀ᶠn : ℕ in atTop,
      ∀a : ActualHighOnlyOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock,
      a.data.s  ≤  1/4 → a.data.s  ≤  a.xs → ∀P : a.Potential,
      NativePullbackClockRegularity a.alpha.val.val a.b a.h 0 1 →
      ∀F : Finset (ordConnectedSection P.negativeSet),∀A : Set ℝ,∀v Lside cut : ℝ,
      0 < v → v  ≤  1 → a.data.s < v/2 → 0  ≤  Lside → 0 < cut → Real.log (1/cut)  ≤  Lside →
      (∫u in 0..1,(P.canonicalOrdinarySupport F A v).indicator (fun _=>1)
        (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u)  ≤ 
        a.canonicalOrdinaryMassBudget ell Q Lside cut v := by
  obtain ⟨Q,hQ,Hphysical⟩:=eventually_actual_high_only_ordinary_optimized_budget ell hell Bclock
    (D:=D) hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Q,hQ,?_⟩
  filter_upwards [Hphysical] with n hn
  intro a hs hsxs P hclock F A v Lside cut hv hv1 hstart hLside hcut hlogcut
  let m:=a.shiftedNativeModel
  let c:=P.ordinaryCapFamily (P.capFamily F) A 16 v
  let ag:=m.R (v/2)
  let zg:=m.R (min (16*v) 1)
  have hgeom:=P.ordinary_group_geometry (P.capFamily F) A (by norm_num : (1:ℝ)  ≤  16) hv hv1 hstart
  dsimp only at hgeom
  obtain ⟨hag,hzg,hagz,hagmass,hzgmass,hcap⟩:=hgeom
  have hwhole : ∀t,∀r∈Ioo (c t).left (c t).right,
      wholeUnit P.negativeSet r=Ioo (c t).left (c t).right := by
    intro t r hr
    exact P.capFamily_wholeUnit F t.val hr
  have hcontacts:=P.ordinary_group_contacts (P.capFamily F) A (K:=16)
    (show a.data.s < v by linarith) (P.capFamily_contacts F)
  have hdisjoint : Pairwise (fun t u=>Disjoint (Ioo (c t).left (c t).right)
      (Ioo (c u).left (c u).right)) := by
    intro t u htu
    exact P.capFamily_disjoint F (Subtype.val_injective.ne htu)
  have hY : 0 < a.xs+min (16*v) 1 := add_pos_of_pos_of_nonneg a.hxs (le_min (by positivity) zero_le_one)
  have H:=hn a hs hsxs P _ c ag zg v (min (16*v) 1) 32 (16*v) (v/4)
    (a.xs+min (16*v) 1) v 16 Lside cut hwhole hcontacts hdisjoint hag hagz hzg
    (hclock.restrict hag.le hzg) (fun t=>(hcap t).1) (fun t=>(hcap t).2.1)
    hv.le (by norm_num)
    (by have H:=min_le_left (16*v) 1;have hu:=a.data.hU; nlinarith)
    (fun t=>t.property.2.1) (fun t=>t.property.2.2)
    (by positivity) (by rw [hagmass,hzgmass];have H:=min_le_left (16*v) 1;linarith)
    (by positivity) (by rw [hagmass];linarith) hY (by rw [hzgmass]) hv (by norm_num)
    (fun t=>(hcap t).2.2.1) (fun t=>(hcap t).2.2.2) hLside hcut hlogcut
  change (∫u in 0..1,(P.retainedSupport c ag zg).indicator (fun _=>1) (m.R u)*m.thermal u)  ≤  _
  exact H.trans_eq (by
    dsimp only [ActualHighOnlyOverlapMinimum.ordinaryOptimizedBudget,
      ActualHighOnlyOverlapMinimum.canonicalOrdinaryMassBudget,
      ActualHighOnlyOverlapMinimum.canonicalMassPower,
      ActualHighOnlyOverlapMinimum.canonicalMassHeight,
      ActualHighOnlyOverlapMinimum.canonicalMassReverse,
      ActualHighOnlyOverlapMinimum.localCapDiameter,zg,m]
    rfl)

end OAI.SKFluctuations.LaplaceWindowFormalization
