module

public import ComparisonSignedCavitySecondLowOccupiedGammaCanonicalValue
public import ComparisonSignedCavitySecondLowObservedMiddleReduction

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
open scoped BigOperators
set_option maxHeartbeats 35000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem native_second_low_high_rows_eq_of_same_cut {S : Type} {as : List PositiveMass}
    (T : ClockTree S as) (U : ℕ) (hU0 : 0<U) (hU : U≤as.length) (a c : T.Slot)
    (Hac : U≤T.splitIndex a c) : nativeHighMarkedRows T a (U-1) 0=nativeHighMarkedRows T c (U-1) 0 := by
  rw [nativeHighMarkedRows_eq_filter,nativeHighMarkedRows_eq_filter]
  apply List.filter_congr
  intro p hp
  have Hsame : p.tree.cutBlock U hU (p.embed a)=p.tree.cutBlock U hU (p.embed c):=
    (p.tree.cutBlock_eq_iff U hU _ _).mpr (by rw [(T.markedAttach_embed_preserves 0 p hp).2];exact Hac)
  have HA : (U-1<p.tree.splitIndex (p.embed a) p.mark)↔U≤p.tree.splitIndex (p.embed a) p.mark:=by omega
  have HC : (U-1<p.tree.splitIndex (p.embed c) p.mark)↔U≤p.tree.splitIndex (p.embed c) p.mark:=by omega
  have Hiff : (U-1<p.tree.splitIndex (p.embed a) p.mark)↔
      (U-1<p.tree.splitIndex (p.embed c) p.mark):=by
    rw [HA,HC,←p.tree.cutBlock_eq_iff U hU,←p.tree.cutBlock_eq_iff U hU,Hsame]
  simp only [Hiff]

def nativeSecondLowMiddlePartnerPairValue (n : ℕ) (q : ℕ→RestCoordinate n→ℝ)
    (U : ℕ) (b h K : ℕ→ℝ) {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (c z : T.Slot) (P F G : T.cavityLeft.Assignment→ℝ)
    (s : MarkedPlacement T) (t : MarkedPlacement s.tree) : ℝ :=
  fullScalarCutGamma s.tree U K (s.embed c) s.mark*
    fullScalarCutGamma t.tree U K (t.embed (s.embed z)) t.mark*
    t.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (fun τ=>P (s.restRestrict (t.restRestrict τ))*
        (F (s.restRestrict (t.restRestrict τ))*
          restLowKernel n U b h (t.tree.splitIndex (t.embed s.mark) t.mark)
            (s.restSpin (t.restRestrict τ)) (t.restSpin τ)-G (s.restRestrict (t.restRestrict τ)))) 0

theorem native_second_low_two_gamma_high_rows_eq_middle_partner
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (hU0 : 0<U) (hU : U≤as.length) (c z : T.Slot) (P F G : T.cavityLeft.Assignment→ℝ) :
    ((nativeHighMarkedRows T c (U-1) 0).map (fun s=>s.coeff*
      ((nativeHighMarkedRows s.tree (s.embed z) (U-1) 0).map (fun t=>t.coeff*
        nativeSecondLowMiddlePartnerPairValue n q U b h K T c z P F G s t)).sum)).sum=
      nativeSecondLowObservedMiddlePartnerRow n q U b h K T c z P F G := by
  have H:=native_two_high_nested_full_of_support T c z (U-1) 0
    (nativeSecondLowMiddlePartnerPairValue n q U b h K T c z P F G)
    (by
      intro s hs t _ht Hno
      have Hlow : s.tree.splitIndex (s.embed c) s.mark<U:=by omega
      unfold nativeSecondLowMiddlePartnerPairValue
      rw [fullScalarCutGamma_cross_zero s.tree ho U K (s.embed c) s.mark hU Hlow,zero_mul,zero_mul])
    (by
      intro s _hs t _ht Hno
      have Hlow : t.tree.splitIndex (t.embed (s.embed z)) t.mark<U:=by omega
      unfold nativeSecondLowMiddlePartnerPairValue
      rw [fullScalarCutGamma_cross_zero t.tree ho U K (t.embed (s.embed z)) t.mark hU Hlow,mul_zero,zero_mul])
  rw [H]
  unfold nativeSecondLowObservedMiddlePartnerRow nativeSecondLowFreshPartnerProductRow
  apply congrArg List.sum
  apply List.map_congr_left
  intro s _hs
  simp only [←List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t _ht
  unfold nativeSecondLowMiddlePartnerPairValue
  simp only [MarkedPlacement.restSpin]
  ring

def nativeSecondLowCanonicalPartnerOldTest {n : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (P : T.cavityLeft.Assignment→ℝ)
    (p : MarkedPlacement T) (r : MarkedPlacement p.tree) (τ : r.tree.cavityLeft.Assignment) : ℝ :=
  P (p.restRestrict (r.restRestrict τ))

def nativeSecondLowCanonicalPartnerLowFactor (n U : ℕ) (b h : ℕ→ℝ) {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (p : MarkedPlacement T) (r : MarkedPlacement p.tree)
    (τ : r.tree.cavityLeft.Assignment) : ℝ :=
  restLowKernel n U b h (r.tree.splitIndex (r.embed p.mark) r.mark)
    (p.restSpin (r.restRestrict τ)) (r.restSpin τ)

def nativeSecondLowCanonicalPartnerScalar (U : ℕ) (K : ℕ→ℝ) {n : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (z : T.Slot)
    (p : MarkedPlacement T) (r : MarkedPlacement p.tree) : ℝ :=
  nativeSecondLowScalarValue U K (r.tree.splitIndex (r.embed p.mark) r.mark)*
    nativeSecondLowScalarValue U K (r.tree.splitIndex r.mark (r.embed (p.embed z)))

theorem native_second_low_canonical_gamma_atom_eq_partner_pair
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (p : MarkedPlacement T) (_hp : p∈T.markedAttach 0)
    (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
    (Hcz : r.tree.splitIndex r.mark (r.embed (p.embed z))<U)
    (s : MarkedPlacement r.tree) (hs : s∈r.tree.markedAttach 0)
    (Hs : U ≤ s.tree.splitIndex (s.embed r.mark) s.mark)
    (t : MarkedPlacement s.tree) (ht : t∈s.tree.markedAttach 0)
    (Ht : U ≤ t.tree.splitIndex (t.embed (s.embed (r.embed (p.embed z)))) t.mark) :
    nativeSecondLowGammaWordValue n q U b h K P a z 0 p r s t=
      fullScalarCutGamma p.tree U K (p.embed a) p.mark*
        nativeSecondLowMiddlePartnerPairValue n q U b h K r.tree r.mark (r.embed (p.embed z))
          (nativeSecondLowCanonicalPartnerOldTest P p r)
          (nativeSecondLowCanonicalPartnerLowFactor n U b h p r)
          (fun _=>nativeSecondLowCanonicalPartnerScalar U K z p r) s t := by
  have Hez : s.tree.splitIndex s.mark (s.embed (r.embed (p.embed z)))=
      r.tree.splitIndex r.mark (r.embed (p.embed z)) := by
    rw [s.tree.splitIndex_symm]
    have H:=native_second_low_high_mark_low_split r.tree U (r.embed (p.embed z)) r.mark s hs Hs
      (by simpa only [r.tree.splitIndex_symm _ r.mark] using Hcz)
    exact H.trans (r.tree.splitIndex_symm _ _)
  have Hed:=native_second_low_high_mark_low_split s.tree U s.mark (s.embed (r.embed (p.embed z)))
    t ht Ht (by rw [Hez];exact Hcz)
  have Htest : nativeSecondLowJointRestTest n U b h K P p r s t=
      fun τ=>nativeSecondLowCanonicalPartnerOldTest P p r (s.restRestrict (t.restRestrict τ))*
        (nativeSecondLowCanonicalPartnerLowFactor n U b h p r (s.restRestrict (t.restRestrict τ))*
          restLowKernel n U b h (t.tree.splitIndex (t.embed s.mark) t.mark)
            (s.restSpin (t.restRestrict τ)) (t.restSpin τ)-nativeSecondLowCanonicalPartnerScalar U K z p r) := by
    funext τ
    rw [native_second_low_joint_rest_test_product]
    simp only [nativeSecondLowCanonicalPartnerOldTest,nativeSecondLowCanonicalPartnerLowFactor,
      nativeSecondLowCanonicalPartnerScalar,Hed,Hez]
  unfold nativeSecondLowGammaWordValue nativeSecondLowMiddlePartnerPairValue
  rw [Htest]
  simp only [nativeSecondLowPathGamma,Fin.val_zero]
  rw [fullScalarCutGamma_double_preserves r.tree ho U K (r.embed (p.embed a)) (r.embed p.mark) s hs t ht,
    fullScalarCutGamma_marked_preserves p.tree ho U K (p.embed a) p.mark r hr,
    fullScalarCutGamma_marked_preserves s.tree ho U K (s.embed r.mark) s.mark t ht,
    fullScalarCutGamma_symm t.tree U K t.mark (t.embed (s.embed (r.embed (p.embed z))))]
  ring

def nativeSecondLowCanonicalMiddlePartnerSource (n : ℕ) (q : ℕ→RestCoordinate n→ℝ)
    (U : ℕ) (b h K : ℕ→ℝ) {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (a v z : T.Slot) : ℝ :=
  ((nativeHighMarkedRows T a (U-1) 0).map (fun p=>p.coeff*fullScalarCutGamma p.tree U K (p.embed a) p.mark*
    ((nativeHighMarkedRows p.tree (p.embed v) (U-1) 0).map (fun r=>r.coeff*
      nativeSecondLowObservedMiddlePartnerRow n q U b h K r.tree r.mark (r.embed (p.embed z))
        (nativeSecondLowCanonicalPartnerOldTest P p r)
        (nativeSecondLowCanonicalPartnerLowFactor n U b h p r)
        (fun _=>nativeSecondLowCanonicalPartnerScalar U K z p r))).sum)).sum

theorem native_second_low_canonical_raw_source_eq_middle_partner_source
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (hU0 : 0<U) (hU : U≤as.length) (P : T.cavityLeft.Assignment→ℝ) (a v z : T.Slot)
    (Hvz : T.splitIndex v z<U) :
    nativeSecondLowFourHighSum T (nativeSecondLowChronologicalTargets 0 a v z) (U-1)
      (fun p r s t=>nativeSecondLowGammaWordValue n q U b h K P a z 0 p r s t)=
      nativeSecondLowCanonicalMiddlePartnerSource n q U b h K T P a v z := by
  unfold nativeSecondLowFourHighSum nativeSecondLowCanonicalMiddlePartnerSource
  simp [nativeSecondLowChronologicalTargets]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  simp only [←List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro r hr
  obtain ⟨hp',Hp⟩:=(mem_nativeHighMarkedRows T a (U-1) 0 p).mp hp
  obtain ⟨hr',Hr⟩:=(mem_nativeHighMarkedRows p.tree (p.embed v) (U-1) 0 r).mp hr
  have HrU : U ≤ r.tree.splitIndex (r.embed (p.embed v)) r.mark:=by omega
  have Hcz : r.tree.splitIndex r.mark (r.embed (p.embed z))<U := by
    rw [r.tree.splitIndex_symm]
    have H:=native_second_low_high_mark_low_split p.tree U (p.embed z) (p.embed v) r hr' HrU
      (by rw [(T.markedAttach_embed_preserves 0 p hp').2,T.splitIndex_symm z v];exact Hvz)
    rw [H,(T.markedAttach_embed_preserves 0 p hp').2,T.splitIndex_symm z v]
    exact Hvz
  have Hsame:=native_second_low_high_rows_eq_of_same_cut r.tree U hU0 hU (r.embed (p.embed v)) r.mark HrU
  rw [Hsame]
  rw [←native_second_low_two_gamma_high_rows_eq_middle_partner n q U b h K r.tree ho hU0 hU
    r.mark (r.embed (p.embed z)) (nativeSecondLowCanonicalPartnerOldTest P p r)
    (nativeSecondLowCanonicalPartnerLowFactor n U b h p r) (fun _=>nativeSecondLowCanonicalPartnerScalar U K z p r)]
  simp only [←List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro s hs
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  obtain ⟨hs',Hs⟩:=(mem_nativeHighMarkedRows r.tree r.mark (U-1) 0 s).mp hs
  obtain ⟨ht',Ht⟩:=(mem_nativeHighMarkedRows s.tree (s.embed (r.embed (p.embed z))) (U-1) 0 t).mp ht
  rw [native_second_low_canonical_gamma_atom_eq_partner_pair n q U b h K T ho P a z
    p hp' r hr' Hcz s hs' (by omega) t ht' (by omega)]
  ring

end OAI.SKFluctuations.Cavity
