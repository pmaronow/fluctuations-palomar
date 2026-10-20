module

public import ComparisonSignedCavitySecondLowCanonicalPartnerSource
public import ComparisonSignedCavitySecondLowUnweightedCRowSource
public import ComparisonSignedCavitySecondLowOutsideFreshHighWords

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators
set_option maxHeartbeats 40000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

def nativeSecondLowCanonicalUnweightedCSource (n : ℕ) (q : ℕ→RestCoordinate n→ℝ)
    (U : ℕ) (b h K : ℕ→ℝ) {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (a v z : T.Slot) : ℝ :=
  ((nativeHighMarkedRows T a (U-1) 0).map (fun p=>p.coeff*fullScalarCutGamma p.tree U K (p.embed a) p.mark*
    nativeSecondLowUnweightedCRow n q U b h K p.tree p.mark (p.embed v) (p.embed z)
      (fun old=>P (p.restRestrict old)))).sum

def nativeSecondLowCanonicalObservedResidualSource (n : ℕ) (q : ℕ→RestCoordinate n→ℝ)
    (U : ℕ) (b h K : ℕ→ℝ) {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (a v z : T.Slot) : ℝ :=
  ((nativeHighMarkedRows T a (U-1) 0).map (fun p=>p.coeff*fullScalarCutGamma p.tree U K (p.embed a) p.mark*
    ((nativeHighMarkedRows p.tree (p.embed v) (U-1) 0).map (fun r=>r.coeff*
      nativeSecondLowObservedMiddleResidual n q U b h K r.tree r.mark (r.embed (p.embed z))
        (nativeSecondLowCanonicalPartnerOldTest P p r)
        (nativeSecondLowCanonicalPartnerLowFactor n U b h p r))).sum)).sum

private theorem canonical_middle_weighted_linear_sum {α : Type} (L : List α) (w F G : α→ℝ) (χ : ℝ) :
    (L.map (fun x=>w x*(χ^2*F x+χ*G x))).sum=
      χ^2*(L.map (fun x=>w x*F x)).sum+χ*(L.map (fun x=>w x*G x)).sum := by
  induction L with
  | nil=>simp
  | cons x L ih=>simp only [List.map_cons,List.sum_cons,ih];ring

theorem native_second_low_canonical_partner_source_eq_unweighted_c_add_residual
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U star : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (hstar : star<U) (hU : U≤as.length) (P : T.cavityLeft.Assignment→ℝ) (a v z : T.Slot)
    (hz : NativeTargetStarSingleton T z star) (Haz : T.splitIndex a z ≤ star)
    (Hvz : T.splitIndex v z ≤ star) (Hav : T.splitIndex a v<U)
    (hP : ∀τ u,P (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot z) τ u)=P τ) :
    nativeSecondLowCanonicalMiddlePartnerSource n q U b h K T P a v z=
      ((scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0)^2*
        nativeSecondLowCanonicalUnweightedCSource n q U b h K T P a v z+
      (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*
        nativeSecondLowCanonicalObservedResidualSource n q U b h K T P a v z := by
  let χ:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  have hU0 : 0<U:=by omega
  have Hrow (p : MarkedPlacement T) (hp : p∈nativeHighMarkedRows T a (U-1) 0)
      (r : MarkedPlacement p.tree) (hr : r∈nativeHighMarkedRows p.tree (p.embed v) (U-1) 0) :
      nativeSecondLowObservedMiddlePartnerRow n q U b h K r.tree r.mark (r.embed (p.embed z))
        (nativeSecondLowCanonicalPartnerOldTest P p r) (nativeSecondLowCanonicalPartnerLowFactor n U b h p r)
        (fun _=>nativeSecondLowCanonicalPartnerScalar U K z p r)=
      χ^2*r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
        (nativeSecondLowUnweightedCPayload n U b h K p.tree p.mark (p.embed v) (p.embed z)
          (fun old=>P (p.restRestrict old)) r) 0+
      χ*nativeSecondLowObservedMiddleResidual n q U b h K r.tree r.mark (r.embed (p.embed z))
        (nativeSecondLowCanonicalPartnerOldTest P p r) (nativeSecondLowCanonicalPartnerLowFactor n U b h p r) := by
    obtain ⟨hp',Hp⟩:=(mem_nativeHighMarkedRows T a (U-1) 0 p).mp hp
    obtain ⟨hr',Hr⟩:=(mem_nativeHighMarkedRows p.tree (p.embed v) (U-1) 0 r).mp hr
    have HpU : U ≤ p.tree.splitIndex (p.embed a) p.mark:=by omega
    have HrU : U ≤ r.tree.splitIndex (r.embed (p.embed v)) r.mark:=by omega
    have HpZ : p.tree.splitIndex (p.embed z) p.mark=T.splitIndex z a:=
      native_second_low_high_mark_low_split T U z a p hp' HpU
        (by rw [T.splitIndex_symm];omega)
    have HpV : p.tree.splitIndex p.mark (p.embed v)=T.splitIndex a v:=by
      rw [p.tree.splitIndex_symm]
      exact (native_second_low_high_mark_low_split T U v a p hp' HpU
        (by rw [T.splitIndex_symm];exact Hav)).trans (T.splitIndex_symm v a)
    have Hfc : r.tree.splitIndex (r.embed p.mark) r.mark=p.tree.splitIndex p.mark (p.embed v):=
      native_second_low_high_mark_low_split p.tree U p.mark (p.embed v) r hr' HrU (by rw [HpV];exact Hav)
    have Hcz : r.tree.splitIndex r.mark (r.embed (p.embed z))=p.tree.splitIndex (p.embed v) (p.embed z):=by
      rw [r.tree.splitIndex_symm]
      exact (native_second_low_high_mark_low_split p.tree U (p.embed z) (p.embed v) r hr' HrU
        (by rw [(T.markedAttach_embed_preserves 0 p hp').2,T.splitIndex_symm];omega)).trans
          (p.tree.splitIndex_symm _ _)
    have HczStar : r.tree.splitIndex r.mark (r.embed (p.embed z)) ≤ star:=by
      rw [Hcz,(T.markedAttach_embed_preserves 0 p hp').2]
      exact Hvz
    have HfzStar : r.tree.splitIndex (r.embed p.mark) (r.embed (p.embed z)) ≤ star:=by
      rw [(p.tree.markedAttach_embed_preserves 0 r hr').2,p.tree.splitIndex_symm,HpZ,T.splitIndex_symm]
      exact Haz
    have Hzp : NativeTargetStarSingleton p.tree (p.embed z) star:=
      hz.retain_outside_mark p hp' (by rw [HpZ,T.splitIndex_symm];exact Haz)
    have Hzr : NativeTargetStarSingleton r.tree (r.embed (p.embed z)) star:=
      Hzp.retain_outside_mark r hr' (by simpa only [r.tree.splitIndex_symm] using HczStar)
    have HP : ∀τ u,nativeSecondLowCanonicalPartnerOldTest P p r
        (nativeReplaceAtSlot r.tree.cavityLeft (r.tree.cavityLeftSlot (r.embed (p.embed z))) τ u)=
        nativeSecondLowCanonicalPartnerOldTest P p r τ := by
      intro τ u
      unfold nativeSecondLowCanonicalPartnerOldTest
      rw [r.restRestrict_replace_target (p.tree.markedAttach_embed_preserves 0 r hr').1,
        p.restRestrict_replace_target (T.markedAttach_embed_preserves 0 p hp').1,hP]
    have HFslot (τ : r.tree.cavityLeft.Assignment) : nativeSecondLowCanonicalPartnerLowFactor n U b h p r τ=
        restLowKernel n U b h (r.tree.splitIndex (r.embed p.mark) r.mark)
          (r.tree.cavityLeft.atSlot τ (r.tree.cavityLeftSlot (r.embed p.mark)))
          (r.tree.cavityLeft.atSlot τ (r.tree.cavityLeftSlot r.mark)) := by
      unfold nativeSecondLowCanonicalPartnerLowFactor MarkedPlacement.restSpin
      rw [r.restRestrict_at]
    have Hfn : r.tree.cavityLeftSlot (r.embed p.mark)≠r.tree.cavityLeftSlot (r.embed (p.embed z)):=by
      intro HH
      have H:=r.tree.cavityLeftSlot.injective HH
      rw [H,r.tree.splitIndex_self] at HfzStar
      omega
    have Hcn : r.tree.cavityLeftSlot r.mark≠r.tree.cavityLeftSlot (r.embed (p.embed z)):=by
      intro HH
      have H:=r.tree.cavityLeftSlot.injective HH
      rw [H,r.tree.splitIndex_self] at HczStar
      omega
    have HF : ∀τ u,nativeSecondLowCanonicalPartnerLowFactor n U b h p r
        (nativeReplaceAtSlot r.tree.cavityLeft (r.tree.cavityLeftSlot (r.embed (p.embed z))) τ u)=
        nativeSecondLowCanonicalPartnerLowFactor n U b h p r τ := by
      intro τ u
      rw [HFslot,HFslot,nativeReplaceAtSlot_at,nativeReplaceAtSlot_at,ite_eq_right Hfn,ite_eq_right Hcn]
    have H:=native_second_low_observed_middle_eq_baseline_add_residual n q U b h K r.tree ho
      r.mark (r.embed (p.embed z)) star hstar hU Hzr HczStar
      (nativeSecondLowCanonicalPartnerOldTest P p r) (nativeSecondLowCanonicalPartnerLowFactor n U b h p r)
      (fun _=>nativeSecondLowCanonicalPartnerScalar U K z p r) HP HF (fun _ _=>rfl)
    have HB : (fun τ : r.tree.cavityLeft.Assignment=>nativeSecondLowCanonicalPartnerOldTest P p r τ*
        (nativeSecondLowCanonicalPartnerLowFactor n U b h p r τ*
          restLowKernel n U b h (r.tree.splitIndex r.mark (r.embed (p.embed z)))
            (r.tree.cavityLeft.atSlot τ (r.tree.cavityLeftSlot r.mark))
            (r.tree.cavityLeft.atSlot τ (r.tree.cavityLeftSlot (r.embed (p.embed z))))-
          nativeSecondLowCanonicalPartnerScalar U K z p r))=
      nativeSecondLowUnweightedCPayload n U b h K p.tree p.mark (p.embed v) (p.embed z)
        (fun old=>P (p.restRestrict old)) r := by
      funext τ
      simp only [nativeSecondLowCanonicalPartnerOldTest,nativeSecondLowCanonicalPartnerLowFactor,
        nativeSecondLowCanonicalPartnerScalar,nativeSecondLowUnweightedCPayload,nativeSecondLowScalarValue,
        MarkedPlacement.restSpin,Hfc,Hcz,←r.restRestrict_at]
    rw [HB] at H
    exact H
  calc
    _=((nativeHighMarkedRows T a (U-1) 0).map (fun p=>p.coeff*fullScalarCutGamma p.tree U K (p.embed a) p.mark*
      ((nativeHighMarkedRows p.tree (p.embed v) (U-1) 0).map (fun r=>r.coeff*
        (χ^2*r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (nativeSecondLowUnweightedCPayload n U b h K p.tree p.mark (p.embed v) (p.embed z)
            (fun old=>P (p.restRestrict old)) r) 0+
        χ*nativeSecondLowObservedMiddleResidual n q U b h K r.tree r.mark (r.embed (p.embed z))
          (nativeSecondLowCanonicalPartnerOldTest P p r) (nativeSecondLowCanonicalPartnerLowFactor n U b h p r)))).sum)).sum:=by
      unfold nativeSecondLowCanonicalMiddlePartnerSource
      apply congrArg List.sum
      apply List.map_congr_left
      intro p hp
      congr 1
      apply congrArg List.sum
      apply List.map_congr_left
      intro r hr
      rw [Hrow p hp r hr]
    _= _:=by
      unfold nativeSecondLowCanonicalUnweightedCSource nativeSecondLowCanonicalObservedResidualSource nativeSecondLowUnweightedCRow
      simp_rw [canonical_middle_weighted_linear_sum]
      rfl

theorem native_second_low_canonical_raw_source_eq_unweighted_c_add_residual
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U star : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (hstar : star<U) (hU : U≤as.length) (P : T.cavityLeft.Assignment→ℝ) (a v z : T.Slot)
    (hz : NativeTargetStarSingleton T z star) (Haz : T.splitIndex a z ≤ star)
    (Hvz : T.splitIndex v z ≤ star) (Hav : T.splitIndex a v<U)
    (hP : ∀τ u,P (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot z) τ u)=P τ) :
    nativeSecondLowFourHighSum T (nativeSecondLowChronologicalTargets 0 a v z) (U-1)
      (fun p r s t=>nativeSecondLowGammaWordValue n q U b h K P a z 0 p r s t)=
      ((scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0)^2*
        nativeSecondLowCanonicalUnweightedCSource n q U b h K T P a v z+
      (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*
        nativeSecondLowCanonicalObservedResidualSource n q U b h K T P a v z := by
  rw [native_second_low_canonical_raw_source_eq_middle_partner_source n q U b h K T ho (by omega) hU P a v z
    (by omega)]
  exact native_second_low_canonical_partner_source_eq_unweighted_c_add_residual n q U star b h K T ho
    hstar hU P a v z hz Haz Hvz Hav hP

theorem native_second_low_fresh_rest_replace_restrict {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (z : T.Slot) (star : ℕ)
    (τ : (nativeFreshAtSlot T 0 z star).tree.cavityLeft.Assignment) (u : Spin n) :
    let g:=nativeFreshAtSlot T 0 z star
    g.restRestrict (nativeReplaceAtSlot g.tree.cavityLeft (g.tree.cavityLeftSlot g.mark) τ u)=g.restRestrict τ := by
  dsimp only
  apply T.cavityLeft.assignment_ext
  intro c
  obtain ⟨d,rfl⟩:=T.cavityLeftSlot.surjective c
  rw [(nativeFreshAtSlot T 0 z star).restRestrict_at,(nativeFreshAtSlot T 0 z star).restRestrict_at,
    nativeReplaceAtSlot_at,ite_eq_right]
  exact fun H=>nativeFreshAtSlot_distinct T 0 z star d
    ((nativeFreshAtSlot T 0 z star).tree.cavityLeftSlot.injective H).symm

theorem native_second_low_actual_fresh_canonical_source_eq_unweighted_c_add_residual
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U star : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (hstar : star<U) (hU : U≤as.length) (P : T.cavityLeft.Assignment→ℝ) (a v z : T.Slot)
    (Hav : T.splitIndex a v<U) :
    let g:=nativeFreshAtSlot T 0 z star
    let Pg:=fun τ=>P (g.restRestrict τ)
    nativeSecondLowFourHighSum g.tree (nativeSecondLowChronologicalTargets 0 (g.embed a) (g.embed v) g.mark) (U-1)
      (fun p r s t=>nativeSecondLowGammaWordValue n q U b h K Pg (g.embed a) g.mark 0 p r s t)=
      ((scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0)^2*
        nativeSecondLowCanonicalUnweightedCSource n q U b h K g.tree Pg (g.embed a) (g.embed v) g.mark+
      (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*
        nativeSecondLowCanonicalObservedResidualSource n q U b h K g.tree Pg (g.embed a) (g.embed v) g.mark := by
  dsimp only
  let g:=nativeFreshAtSlot T 0 z star
  apply native_second_low_canonical_raw_source_eq_unweighted_c_add_residual n q U star b h K g.tree ho hstar hU
    (fun τ=>P (g.restRestrict τ)) (g.embed a) (g.embed v) g.mark (native_fresh_target_star_singleton T 0 z star)
  · rw [g.tree.splitIndex_symm,nativeFreshAtSlot_split]
    exact Nat.min_le_left _ _
  · rw [g.tree.splitIndex_symm,nativeFreshAtSlot_split]
    exact Nat.min_le_left _ _
  · rw [(nativeFreshAtSlot_old_splits T 0 z star).2]
    exact Hav
  · intro τ u
    rw [native_second_low_fresh_rest_replace_restrict T z star]

theorem native_second_low_actual_fresh_outside_high_word_numeric
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (D : NativeObservedDiagram T) (z : T.Slot) (star U : ℕ)
    (hstar : star<U) (hU : U≤as.length) (cs : List T.Slot)
    (E : NativeObservedDiagram T→ℝ) :
    ((nativeSecondLowObservedHighWord (D.fresh z star 0) (U-1) cs).map (fun w=>w.1*E w.2)).sum=
      ((nativeSecondLowObservedHighWord D (U-1) cs).map (fun w=>w.1*E (w.2.fresh z star 0))).sum := by
  rw [native_second_low_observed_high_word_fresh_any cs D z star (U-1) (by omega) (by omega) 0]
  simp only [List.map_map,Function.comp_def]

theorem native_second_low_actual_fresh_constant_canonical_source_eq_unweighted_c_add_residual
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U star : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (hstar : star<U) (hU : U≤as.length) (a v z : T.Slot) (Hav : T.splitIndex a v<U) :
    let g:=nativeFreshAtSlot T 0 z star
    nativeSecondLowFourHighSum g.tree (nativeSecondLowChronologicalTargets 0 (g.embed a) (g.embed v) g.mark) (U-1)
      (fun p r s t=>nativeSecondLowGammaWordValue n q U b h K (fun _=>1) (g.embed a) g.mark 0 p r s t)=
      ((scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0)^2*
        nativeSecondLowCanonicalUnweightedCSource n q U b h K g.tree (fun _=>1) (g.embed a) (g.embed v) g.mark+
      (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*
        nativeSecondLowCanonicalObservedResidualSource n q U b h K g.tree (fun _=>1) (g.embed a) (g.embed v) g.mark :=
  native_second_low_actual_fresh_canonical_source_eq_unweighted_c_add_residual n q U star b h K T ho hstar hU
    (fun _=>1) a v z Hav

end OAI.SKFluctuations.Cavity
