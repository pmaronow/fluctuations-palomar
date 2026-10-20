module

public import SKProof.Port.ComparisonActualOriginalQOrdinaryPhysicalAtDiameter
public import SKProof.Port.ComparisonActualOriginalQOrdinaryMassBudget
public import SKProof.Port.ComparisonActualOriginalQLocalDiameterBudgetDefinitions
public import SKProof.Port.ComparisonActualOriginalQOrdinaryGroupData

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 6000000
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}

end ActualThetaZeroOverlapMinimum

theorem eventually_actual_local_ordinary_mass_budget_original_q
    (ell : ℕ) (hell : 2 < ell) (Bclock : ℝ) {margin delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < margin) (hdelta : 0 < delta) (hroom : delta < 3*margin)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0  ≤  Az) (hC0 : 0 < C0) (hCt : 0  ≤  Ct) :
    ∃Q : ℝ,1  ≤  Q ∧ ∀ᶠn : ℕ in atTop,
      ∀a : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock,
      a.data.s  ≤  1/4 → a.data.s  ≤  a.xs → ∀P : a.Potential,
      NativePullbackClockRegularity a.alpha.val.val a.b a.h a.data.rmin 1 →
      ∀F : Finset (ordConnectedSection P.negativeSet),∀A : Set ℝ,∀v Lside cut : ℝ,
      0 < v → v  ≤  1 → a.data.s < v/2 → 0  ≤  Lside → 0 < cut → Real.log (1/cut)  ≤  Lside →
      (∫u in 0..1,(P.canonicalOrdinarySupport F A v).indicator (fun _=>1)
        (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u)  ≤ 
        a.canonicalOrdinaryMassBudgetAtDiameter ell Q Lside cut v (a.canonicalLocalMassDiameter v) := by
  obtain ⟨Q,hQ,Hphysical⟩:=eventually_actual_ordinary_optimized_budget_at_diameter_original_q ell hell Bclock
    (D:=D) hm hdelta hroom hcl hcu hAz hC0 hCt
  have Hdepth:=(tendsto_add_atTop_nat 1).eventually (eventually_comparisonLowerScale_depth hC0 hm)
  have Hlog:=(tendsto_add_atTop_nat 1).eventually
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (1:ℝ))
  refine ⟨Q,hQ,?_⟩
  filter_upwards [Hphysical,Hdepth,Hlog] with n hn hnDepth hnLog
  intro a hs hsxs P hclock F A v Lside cut hv hv1 hstart hLside hcut hlogcut
  have hN : 1 ≤ a.data.N := by
    dsimp only [ActualHighWallData.N]
    exact_mod_cast Nat.succ_pos n
  have hlog : 1 ≤ Real.log a.data.N := hnLog
  have hnd : 1/a.data.N ≤ a.data.d := by
    have HD:=hnDepth a.data.E a.data.d a.data.hE a.data.hd a.hlower
    have HS : comparisonLowerScale (n+1:ℕ) a.data.E a.data.d ≤ a.data.d:=by
      unfold comparisonLowerScale
      exact (div_le_iff₀ a.data.hd).mpr (by simpa only [pow_two] using a.hupper)
    exact HD.trans HS
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
  let baseDiameter:=a.canonicalLocalMassDiameter v
  have hbaseDiameter : 0 < baseDiameter := by
    have hE:=a.data.hE
    have hd:=a.data.hd
    have hU:=a.data.hU
    have hNp:=a.data.hN
    dsimp [baseDiameter,ActualThetaZeroOverlapMinimum.canonicalLocalMassDiameter]
    positivity
  have hinc : ∀t,∀s∈Ioo (c t).left (c t).right,∀r∈Ioo (c t).left (c t).right,s ≤ r →
      a.radiusS r-a.radiusS s ≤ baseDiameter := by
    intro t s hs r hr hsr
    have hvfloor : 0 < v/2+a.data.U := by have hU:=a.data.hU;positivity
    have hleftFloor : v/2+a.data.U ≤ a.alpha.val.val (c t).left+a.data.U := by
      have H:=t.property.2.1
      change v ≤ a.alpha.val.val (c t).left at H
      linarith
    have hspanFloor : a.alpha.val.val (c t).right-a.alpha.val.val (c t).left ≤ 32*(v/2+a.data.U) := by
      have H:=(hcap t).2.2.2
      change a.alpha.val.val (c t).right-a.alpha.val.val (c t).left ≤ 16*v at H
      linarith [a.data.hU]
    have hgate : (c t).WallGate :=
      (c t).wallGate_of_left_ne (ne_of_gt (hag.trans_le (hcap t).1))
    exact (c t).radiusS_increment_local_chosen hN hlog hnd
      (Or.inl (hcontacts t).1) (hcontacts t).2 hgate hvfloor hleftFloor hspanFloor hs hr hsr
  have H:=hn a hs hsxs P _ c ag zg v (min (16*v) 1) 32 (16*v) (v/4)
    (a.xs+min (16*v) 1) v 16 Lside cut baseDiameter hwhole hcontacts hdisjoint hag hagz hzg
    (hclock.restrict hag.le hzg) (fun t=>(hcap t).1) (fun t=>(hcap t).2.1)
    hv.le (by norm_num)
    (by have H:=min_le_left (16*v) 1;have hu:=a.data.hU; nlinarith)
    (fun t=>t.property.2.1) (fun t=>t.property.2.2)
    (by positivity) (by rw [hagmass,hzgmass];have H:=min_le_left (16*v) 1;linarith)
    (by positivity) (by rw [hagmass];linarith) hY (by rw [hzgmass]) hv (by norm_num)
    (fun t=>(hcap t).2.2.1) (fun t=>(hcap t).2.2.2) hbaseDiameter hinc hLside hcut hlogcut
  change (∫u in 0..1,(P.retainedSupport c ag zg).indicator (fun _=>1) (m.R u)*m.thermal u)  ≤  _
  exact H.trans_eq (by
    dsimp only [ActualThetaZeroOverlapMinimum.ordinaryOptimizedBudgetAtDiameter,
      ActualThetaZeroOverlapMinimum.canonicalOrdinaryMassBudgetAtDiameter,
      ActualThetaZeroOverlapMinimum.canonicalMassPower,
      ActualThetaZeroOverlapMinimum.canonicalMassHeight,
      ActualThetaZeroOverlapMinimum.canonicalMassReverseAtDiameter,
      baseDiameter,zg,m]
    rfl)

end OAI.SKFluctuations.LaplaceWindowFormalization
