module

public import ComparisonSignedCavityActualGhostProfileRow
public import ComparisonSignedCavityActualHighPairingMarginal

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

def nativeFullScalarRootDirection (n : ℕ) : FullCoordinate n→ℝ :=
  cavityEmbed (Sum.elim (fun _ : RestCoordinate n=>(0:ℝ)) (fun _ : Fin 1=>(1:ℝ)))

theorem fullFeature_nativeFullScalarRootDirection (n : ℕ) (σ : Spin n×Bool) :
    fullFeature n σ (nativeFullScalarRootDirection n)=spinValue σ.2 := by
  unfold nativeFullScalarRootDirection
  rw [←ContinuousLinearMap.comp_apply,fullFeature_restrict]
  simp only [productFeature_apply,Sum.elim_inl,Sum.elim_inr]
  change (restFeature n σ.1) 0+(scalarFeature σ.2) 1=spinValue σ.2
  rw [map_zero,zero_add,scalarFeature_apply_spin]
  simp

def nativeRetainedObservedHigh (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (a : T.Slot) : ℝ :=
  ((T.markedAttach 0).map (fun p=>p.coeff*
    retainedSignedJets n q U b h K [restHighKernel n U b h K] p.tree
      (fun σ=>P (p.restRestrict σ)) [p.embed a,p.mark])).sum

theorem native_retained_observed_high_eq_profile_row (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a : T.Slot) :
    nativeRetainedObservedHigh n q U b h K T P a=
      nativeMarkedProfileRow (fullWeight n) (fullFeature n) T 0 (cutFullVariance n q U 0 0 b h K)
        [ReplicaTree.coordinateProfile (fullFeature n) (cutTSlope n U 0 b h K)]
        (fun σ=>P (T.cavityAssignment σ).1*spinValue (T.atSlot σ a).2)
        (fun σ=>fullFeature n σ (nativeFullScalarRootDirection n)) 0 := by
  unfold nativeRetainedObservedHigh nativeMarkedProfileRow
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  rw [←actual_site_rest_jets_eq_retained n q U b h K [restHighKernel n U b h K]
    p.tree ho (fun σ=>P (p.restRestrict σ)) [p.embed a,p.mark]]
  simp only [List.map_cons,List.map_nil,siteRestKernel_eq_cut_high]
  congr 2
  funext σ
  simp only [siteMonomial,mul_one,p.restRestrict_actual,p.restrict_at,p.spin_at,
    fullFeature_nativeFullScalarRootDirection]
  ring

private theorem nativeMarkedProfileRow_clipDirections
    {S ι : Type} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) {as : List PositiveMass}
    (T : ClockTree S as) (v : ι→ℝ) (q : ℕ→ι→ℝ) (Ds : List (ℕ→ι→ℝ))
    (P : T.Assignment→ℝ) (B : S→ℝ) (x : ι→ℝ) :
    nativeMarkedProfileRow w φ T v q (Ds.map (ReplicaTree.coordinateProfile φ)) P B x=
      nativeMarkedProfileRow w φ T v q
        ((Ds.map (clipDirection as.length)).map (ReplicaTree.coordinateProfile φ)) P B x := by
  unfold nativeMarkedProfileRow
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  rw [disorderProfileJets_eq_clipDirections]

theorem native_retained_observed_high_marked_preserves (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a : T.Slot)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (hq0 : ∀j i,0≤q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0≤b j) (hh : ∀j,0≤h j) (hK : ∀j,0≤K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    nativeRetainedObservedHigh n q U b h K p.tree (fun σ=>P (p.restRestrict σ)) (p.embed a)=
      nativeRetainedObservedHigh n q U b h K T P a := by
  classical
  let D:=cutTSlope n U 0 b h K
  let B : ℝ:=∑j : Fin (as.length+1),∑i : FullCoordinate n,|D j.val i|
  have hB : 0≤B:=Finset.sum_nonneg fun _ _=>Finset.sum_nonneg fun _ _=>abs_nonneg _
  have hD : ∀A∈[D],∀j,j≤as.length→∀i,|A j i|≤B := by
    intro A hA j hj i
    simp only [List.mem_singleton] at hA
    subst A
    let r : Fin (as.length+1):=⟨j,by omega⟩
    have H₁ : |D j i|≤∑z : FullCoordinate n,|D j z| :=
      Finset.single_le_sum (s:=Finset.univ) (f:=fun z : FullCoordinate n=>|D j z|)
        (fun _ _=>abs_nonneg _) (Finset.mem_univ i)
    have H₂ : (∑z : FullCoordinate n,|D j z|)≤B := by
      simpa only [B,r] using (Finset.single_le_sum
        (s:=Finset.univ) (f:=fun t : Fin (as.length+1)=>∑z : FullCoordinate n,|D t.val z|)
        (fun _ _=>Finset.sum_nonneg fun _ _=>abs_nonneg _) (Finset.mem_univ r))
    exact H₁.trans H₂
  have HQ : ∀i,Monotone (fun j=>cutFullVariance n q U 0 0 b h K j i) :=
    cutFullVariance_monotone n q U (by norm_num) (by norm_num) hq hb hh hK hbm hhm hKm
  have HQ0 : ∀i,(0 : FullCoordinate n→ℝ) i≤cutFullVariance n q U 0 0 b h K 0 i :=
    fun i=>cutFullVariance_nonneg n q U (by norm_num) (by norm_num) hq0 hb hh hK 0 i
  have H:=native_marked_profile_row_marginal (fullWeight_pos n) (fullFeature n) T ho p hp
    0 (cutFullVariance n q U 0 0 b h K) HQ HQ0 ([D].map (clipDirection as.length)) hB
    (clipDirection_bounded as.length [D] hB hD)
    (fun σ=>P (T.cavityAssignment σ).1*spinValue (T.atSlot σ a).2)
    (nativeFullScalarRootDirection n) 0
  rw [native_retained_observed_high_eq_profile_row n q U b h K p.tree ho,
    native_retained_observed_high_eq_profile_row n q U b h K T ho]
  change nativeMarkedProfileRow _ _ p.tree _ _ ([D].map (ReplicaTree.coordinateProfile (fullFeature n))) _ _ _=
    nativeMarkedProfileRow _ _ T _ _ ([D].map (ReplicaTree.coordinateProfile (fullFeature n))) _ _ _
  conv_lhs=>rw [nativeMarkedProfileRow_clipDirections]
  conv_rhs=>rw [nativeMarkedProfileRow_clipDirections]
  simpa only [p.restRestrict_actual,p.restrict_at] using H

theorem native_retained_longitudinal_eq_observed_sub (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a : T.Slot)
    (hq0 : ∀j i,0≤q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0≤b j) (hh : ∀j,0≤h j) (hK : ∀j,0≤K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) (hU0 : 0<U) :
    nativeRetainedLongitudinalPairing n q U b h K T P a=
      nativeRetainedObservedHigh n q U b h K T P a-
      (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*
        retainedSignedJets n q U b h K [restHighKernel n U b h K] T P [] := by
  unfold nativeRetainedLongitudinalPairing nativeRetainedHighPairing
  have H : (T.markedAttach 0).map (fun p=>p.coeff*
      (retainedSignedJets n q U b h K [restHighKernel n U b h K] p.tree
        (fun σ=>P (p.restRestrict σ)) [p.embed a,p.mark]-
       fullScalarCutGamma p.tree U K (p.embed a) p.mark*
       retainedSignedJets n q U b h K [restHighKernel n U b h K] p.tree
        (fun σ=>P (p.restRestrict σ)) []))=
    (T.markedAttach 0).map (fun p=>p.coeff*
      retainedSignedJets n q U b h K [restHighKernel n U b h K] p.tree
        (fun σ=>P (p.restRestrict σ)) [p.embed a,p.mark]-
      (p.coeff*fullScalarCutGamma p.tree U K (p.embed a) p.mark)*
       retainedSignedJets n q U b h K [restHighKernel n U b h K] T P []) := by
    apply List.map_congr_left
    intro p hp
    rw [native_retained_high_marked_preserves n q U b h K T ho P p hp
      hq0 hq hb hh hK hbm hhm hKm]
    ring
  rw [H,sum_map_sub_explicit,List.sum_map_mul_right,
    native_full_gamma_row_hessian n T ho 0 ho U hU0 K a]
  rfl

theorem native_retained_longitudinal_marked_preserves (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a : T.Slot)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (hq0 : ∀j i,0≤q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0≤b j) (hh : ∀j,0≤h j) (hK : ∀j,0≤K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) (hU0 : 0<U) :
    nativeRetainedLongitudinalPairing n q U b h K p.tree (fun σ=>P (p.restRestrict σ)) (p.embed a)=
      nativeRetainedLongitudinalPairing n q U b h K T P a := by
  rw [native_retained_longitudinal_eq_observed_sub n q U b h K p.tree ho _ _
      hq0 hq hb hh hK hbm hhm hKm hU0,
    native_retained_longitudinal_eq_observed_sub n q U b h K T ho _ _
      hq0 hq hb hh hK hbm hhm hKm hU0,
    native_retained_observed_high_marked_preserves n q U b h K T ho P a p hp
      hq0 hq hb hh hK hbm hhm hKm,
    native_retained_high_marked_preserves n q U b h K T ho P p hp
      hq0 hq hb hh hK hbm hhm hKm]

end OAI.SKFluctuations.Cavity
