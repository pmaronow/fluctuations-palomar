module

public import ComparisonSignedCavitySecondLowObservedFreshOccupiedSum
public import ComparisonSignedCavitySecondLowInitialPhysicalSource

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 35000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

def nativeSecondLowOldCBaselineErrorAtom (n U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (f c z : T.Slot) (firstError : Bool) : T.Assignment→ℝ :=
  if firstError then
    nativeOldInitialRowProduct n T P (nativeSmallCutOldErrorRestKernel n U b h K) f c
      (fun e : Fin 2=>nativeSmallCutOrdinaryRestKernel n U b h K (![false,true] e) (![1,0] e))
      ![c,f] ![z,z]
  else
    nativeOldInitialRowProduct n T P (nativeSmallCutOldErrorRestKernel n U b h K) c z
      (fun e : Fin 2=>nativeSmallCutOrdinaryRestKernel n U b h K (![false,true] e) (![0,0] e))
      ![f,f] ![c,z]

theorem native_second_low_old_c_baseline_payload_eq_error_atoms
    (n U : ℕ) (b h K : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (P : T.cavityLeft.Assignment→ℝ) (f c z : T.Slot) :
    (fun σ:T.Assignment=>nativeSecondLowUnweightedCOldPayload n U b h K T f c z P
      (T.cavityAssignment σ).1)=
      fun σ=>nativeSecondLowOldCBaselineErrorAtom n U b h K T P f c z true σ+
        nativeSecondLowOldCBaselineErrorAtom n U b h K T P f c z false σ := by
  funext σ
  simp only [nativeSecondLowOldCBaselineErrorAtom,ite_true,Bool.false_eq_true,ite_false,
    nativeOldInitialRowProduct,nativeRestRowKernel,Fin.prod_univ_two,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  simp only [nativeSmallCutOrdinaryRestKernel,Bool.false_eq_true,ite_false,ite_true]
  simp_rw [←native_second_low_error_eq_small_cut_old_error n U b h K,
    ←native_second_low_raw_rest_eq_small_cut_moving_one n U b h K,
    ←native_second_low_scalar_eq_small_cut_moving_zero n U b h K]
  simp only [nativeSecondLowUnweightedCOldPayload,nativeSecondLowErrorKernel,
    nativeSecondLowScalarValue,T.atSlot_cavityLeft]
  cases hf : (T.atSlot σ f).2 <;> cases hc : (T.atSlot σ c).2 <;> cases hz : (T.atSlot σ z).2
  all_goals (simp only [spinValue,Bool.false_eq_true,ite_false,ite_true]; ring)

theorem native_second_low_old_c_baseline_expect_eq_error_atoms
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (f c z : T.Slot) :
    T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (nativeSecondLowUnweightedCOldPayload n U b h K T f c z P) 0=
      T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 0 0 b h K)
        (nativeSecondLowOldCBaselineErrorAtom n U b h K T P f c z true) 0+
      T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 0 0 b h K)
        (nativeSecondLowOldCBaselineErrorAtom n U b h K T P f c z false) 0 := by
  rw [←native_decoupled_rest_expect n q U b h K T ho,
    native_second_low_old_c_baseline_payload_eq_error_atoms]
  simp only [ClockTree.disorderExpect,mul_add,Finset.sum_add_distrib]

def nativeSecondLowCanonicalOldCBaselineSource
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (a c z : T.Slot) : ℝ :=
  ((nativeHighMarkedRows T a (U-1) 0).map (fun p=>p.coeff*
    fullScalarCutGamma p.tree U K (p.embed a) p.mark*partitionPoint 0 as U*
    p.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (nativeSecondLowUnweightedCOldPayload n U b h K p.tree p.mark (p.embed c) (p.embed z)
        (fun old=>P (p.restRestrict old))) 0)).sum

def nativeSecondLowCanonicalCReplacementSource
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (a c z : T.Slot) : ℝ :=
  ((nativeHighMarkedRows T a (U-1) 0).map (fun p=>p.coeff*
    fullScalarCutGamma p.tree U K (p.embed a) p.mark*
    nativeSecondLowUnweightedCReplacementRow n q U b h K p.tree p.mark (p.embed c) (p.embed z)
      (fun old=>P (p.restRestrict old)))).sum

theorem native_second_low_canonical_unweighted_eq_old_baseline_add_replacement
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (hU0 : 0<U) (hU : U≤as.length) (P : T.cavityLeft.Assignment→ℝ) (a c z : T.Slot) :
    nativeSecondLowCanonicalUnweightedCSource n q U b h K T P a c z=
      nativeSecondLowCanonicalOldCBaselineSource n q U b h K T P a c z+
      nativeSecondLowCanonicalCReplacementSource n q U b h K T P a c z := by
  unfold nativeSecondLowCanonicalUnweightedCSource nativeSecondLowCanonicalOldCBaselineSource
    nativeSecondLowCanonicalCReplacementSource
  simp_rw [native_second_low_unweighted_c_eq_old_baseline_add_forest_replacement
    n q U b h K _ ho hU0 hU]
  simp only [mul_add,List.sum_map_add,mul_assoc]

theorem native_second_low_fresh_occupied_old_c_equal_LOW_cuts
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (s : T.Slot) (i star U : ℕ) (hU : U≤as.length) (hi : i ≤ star) (hs : star<U)
    (hT : NativePersistentLowForks i star U T)
    (B : NativeSecondLowFreshOccupiedMiddleBlock T s star U hU)
    (p : MarkedPlacement (nativeFreshAtSlot T 0 s star).tree)
    (hp : p∈nativeHighMarkedRows (nativeFreshAtSlot T 0 s star).tree
      ((nativeFreshAtSlot T 0 s star).embed s) (U-1) 0) :
    let g:=nativeFreshAtSlot T 0 s star
    let c:=nativeSecondLowOccupiedBlockRepresentative g.tree U hU B.val
    (p.tree.splitIndex p.mark (p.embed c)=i ∧ p.tree.splitIndex (p.embed c) (p.embed g.mark)=i) ∨
    (p.tree.splitIndex p.mark (p.embed c)=star ∧ p.tree.splitIndex (p.embed c) (p.embed g.mark)=star) := by
  dsimp only
  let g:=nativeFreshAtSlot T 0 s star
  let v:=nativeSecondLowFreshOccupiedOldSlot T s star U hU B
  have Hslot:=native_second_low_fresh_occupied_old_slot_exact T s star U hU B
  have Hfork:=native_second_low_fresh_occupied_old_slot_low_forks T s i star U hU hi hT B
  change (T.splitIndex v s=i ∨ T.splitIndex v s=star) ∧ T.splitIndex s v ≤ star at Hfork
  obtain ⟨hp0,Hp⟩:=(mem_nativeHighMarkedRows g.tree (g.embed s) (U-1) 0 p).mp hp
  have HpU : U≤p.tree.splitIndex (p.embed (g.embed s)) p.mark:=by omega
  have Hsv : T.splitIndex s v<U:=Hfork.2.trans_lt hs
  have Hfc : p.tree.splitIndex p.mark (p.embed (g.embed v))=T.splitIndex s v:=by
    rw [p.tree.splitIndex_symm]
    rw [native_second_low_high_mark_low_split g.tree U (g.embed v) (g.embed s) p hp0 HpU]
    · rw [(nativeFreshAtSlot_old_splits T 0 s star).2,T.splitIndex_symm]
    · rw [(nativeFreshAtSlot_old_splits T 0 s star).2,T.splitIndex_symm]
      exact Hsv
  have Hcz : p.tree.splitIndex (p.embed (g.embed v)) (p.embed g.mark)=T.splitIndex s v:=by
    rw [(g.tree.markedAttach_embed_preserves 0 p hp0).2,g.tree.splitIndex_symm,nativeFreshAtSlot_split,
      Nat.min_eq_right Hfork.2]
  rw [Hslot,Hfc,Hcz]
  rcases Hfork.1 with H|H
  · left
    rw [T.splitIndex_symm] at H
    exact ⟨H,H⟩
  · right
    rw [T.splitIndex_symm] at H
    exact ⟨H,H⟩

theorem native_second_low_fresh_HIGH_mark_tooth_split_eq_star
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (s : T.Slot) (star U : ℕ) (hU : U≤as.length) (hs : star<U)
    (p : MarkedPlacement (nativeFreshAtSlot T 0 s star).tree)
    (hp : p∈nativeHighMarkedRows (nativeFreshAtSlot T 0 s star).tree
      ((nativeFreshAtSlot T 0 s star).embed s) (U-1) 0) :
    p.tree.splitIndex p.mark (p.embed (nativeFreshAtSlot T 0 s star).mark)=star := by
  let g:=nativeFreshAtSlot T 0 s star
  obtain ⟨hp0,Hp⟩:=(mem_nativeHighMarkedRows g.tree (g.embed s) (U-1) 0 p).mp hp
  have HpU : U≤p.tree.splitIndex (p.embed (g.embed s)) p.mark:=by omega
  have Hgz : g.tree.splitIndex g.mark (g.embed s)=star:=by
    rw [nativeFreshAtSlot_split,T.splitIndex_self,Nat.min_eq_left (hs.le.trans hU)]
  rw [p.tree.splitIndex_symm,
    native_second_low_high_mark_low_split g.tree U g.mark (g.embed s) p hp0 HpU (Hgz.trans_lt hs),Hgz]

 def nativeSecondLowFreshOccupiedOldCBaselineSource
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (star : ℕ)
    (hU : U≤as.length) (P : T.cavityLeft.Assignment→ℝ) : ℝ :=
  let g:=nativeFreshAtSlot T 0 s star
  ∑B : NativeSecondLowFreshOccupiedMiddleBlock T s star U hU,
    nativeSecondLowCanonicalOldCBaselineSource n q U b h K g.tree
      (fun old=>P (g.restRestrict old)) (g.embed s)
      (nativeSecondLowOccupiedBlockRepresentative g.tree U hU B.val) g.mark

 def nativeSecondLowFreshOccupiedCReplacementSource
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (star : ℕ)
    (hU : U≤as.length) (P : T.cavityLeft.Assignment→ℝ) : ℝ :=
  let g:=nativeFreshAtSlot T 0 s star
  ∑B : NativeSecondLowFreshOccupiedMiddleBlock T s star U hU,
    nativeSecondLowCanonicalCReplacementSource n q U b h K g.tree
      (fun old=>P (g.restRestrict old)) (g.embed s)
      (nativeSecondLowOccupiedBlockRepresentative g.tree U hU B.val) g.mark

 theorem native_second_low_fresh_occupied_unweighted_eq_old_baseline_add_replacement
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (s : T.Slot) (star : ℕ) (hs : star<U) (hU : U≤as.length) (P : T.cavityLeft.Assignment→ℝ) :
    nativeSecondLowFreshOccupiedUnweightedCSource n q U b h K T s star hU P=
      nativeSecondLowFreshOccupiedOldCBaselineSource n q U b h K T s star hU P+
      nativeSecondLowFreshOccupiedCReplacementSource n q U b h K T s star hU P := by
  unfold nativeSecondLowFreshOccupiedUnweightedCSource nativeSecondLowFreshOccupiedOldCBaselineSource
    nativeSecondLowFreshOccupiedCReplacementSource
  dsimp only
  simp_rw [native_second_low_canonical_unweighted_eq_old_baseline_add_replacement n q U b h K _ ho
    (by omega) hU]
  exact Finset.sum_add_distrib

end OAI.SKFluctuations.Cavity
