module

public import CavityRetainedFrozenExpansion
public import ComparisonSignedCavitySharedStarLaw

@[expose] public section

noncomputable section
set_option maxHeartbeats 7500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy

theorem fullScalarCutMoment_nil {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (K : ℕ→ℝ) : fullScalarCutMoment T U K []=1 := by
  unfold fullScalarCutMoment scalarCutMoment
  simp only [List.map_nil,ClockTree.slotProduct]
  exact T.cavityRight.disorderExpect_one
    (by intro s; norm_num : ∀ s : Bool,(0:ℝ)<1/2) scalarFeature ho
    0 (fun j _=>relocatedClock U 0 K j) 0

theorem native_decoupled_rest_expect (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (P : T.cavityLeft.Assignment→ℝ) :
    T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cutFullVariance n q U 0 0 b h K)
      (fun σ=>P (T.cavityAssignment σ).1) 0=
      T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q P 0 := by
  have H:=cut_full_monomial_eq_retained n q U b h K T ho P []
  simpa only [siteMonomial,fullScalarCutMoment_nil T ho,mul_one] using H

theorem fullScalarCutGamma_cross_zero {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (K : ℕ→ℝ) (a z : T.Slot) (hU : U ≤ as.length)
    (haz : T.splitIndex a z < U) : fullScalarCutGamma T U K a z=0 := by
  have H:=scalarSitePair_zero n 0 U 0 0 K T ho a z hU haz 0
    (by intro i; rfl)
  change T.cavityRight.disorderExpect (fun _:Bool=>(1/2:ℝ)) scalarFeature 0
    (fun j _=>relocatedClock U 0 K j)
    (fun σ=>spinValue (T.cavityRight.atSlot σ (T.cavityRightSlot a))*
      spinValue (T.cavityRight.atSlot σ (T.cavityRightSlot z))) 0=0 at H
  simpa only [fullScalarCutGamma,fullScalarCutMoment,scalarCutMoment,
    List.map_cons,List.map_nil,ClockTree.slotProduct,sitePair,mul_one] using H

theorem fullScalarCutMoment_four_swap {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (U : ℕ) (K : ℕ→ℝ) (a z c d : T.Slot) :
    fullScalarCutMoment T U K [a,z,c,d]=fullScalarCutMoment T U K [a,c,z,d] := by
  unfold fullScalarCutMoment scalarCutMoment
  congr 1
  funext σ
  simp only [List.map_cons,List.map_nil,ClockTree.slotProduct]
  ring

theorem fullScalarCutMoment_low_pairing {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (K : ℕ→ℝ) (a z c d : T.Slot) (hU : U ≤ as.length)
    (haz : T.splitIndex a z < U) (hcd : T.splitIndex c d < U) :
    fullScalarCutMoment T U K [a,z,c,d]=
      fullScalarCutGamma T U K a c*fullScalarCutGamma T U K z d+
      fullScalarCutGamma T U K a d*fullScalarCutGamma T U K z c := by
  classical
  have hU0 : 0 < U := by omega
  let B:=T.cutBlock U hU
  have hB (s t : T.Slot) : B s=B t ↔ U ≤ T.splitIndex s t :=
    T.cutBlock_eq_iff U hU s t
  have hazB : B a ≠ B z := fun H=>not_le.mpr haz ((hB a z).mp H)
  have hzG (s t : T.Slot) (H : B s ≠ B t) : fullScalarCutGamma T U K s t=0 :=
    fullScalarCutGamma_cross_zero T ho U K s t hU
      (lt_of_not_ge (fun h=>H ((hB s t).mpr h)))
  by_cases hj : joins (B a) (B z) (B c) (B d)
  · rcases hj with ⟨hca,hdz⟩ | ⟨hcz,hda⟩
    · have hcross : ∀ s∈[a,c], ∀ t∈[z,d], T.splitIndex s t < U := by
        intro s hs t ht
        have hn : B s ≠ B t := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hs ht
          rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
          all_goals simpa only [hca,hdz] using hazB
        exact lt_of_not_ge (fun h=>hn ((hB s t).mpr h))
      have HF:=fullScalarCutMoment_factor T ho U hU0 hU K [a,c] [z,d] hcross
      simp only [List.cons_append,List.nil_append] at HF
      rw [fullScalarCutMoment_four_swap T U K,HF]
      have had : B a ≠ B d := by simpa only [hdz] using hazB
      rw [hzG a d had]
      simp only [zero_mul,add_zero,fullScalarCutGamma]
    · have hcross : ∀ s∈[a,d], ∀ t∈[z,c], T.splitIndex s t < U := by
        intro s hs t ht
        have hn : B s ≠ B t := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hs ht
          rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
          all_goals simpa only [hcz,hda] using hazB
        exact lt_of_not_ge (fun h=>hn ((hB s t).mpr h))
      have he : fullScalarCutMoment T U K [a,z,c,d]=fullScalarCutMoment T U K [a,d,z,c] := by
        unfold fullScalarCutMoment scalarCutMoment
        congr 1
        funext σ
        simp only [List.map_cons,List.map_nil,ClockTree.slotProduct]
        ring
      have HF:=fullScalarCutMoment_factor T ho U hU0 hU K [a,d] [z,c] hcross
      simp only [List.cons_append,List.nil_append] at HF
      rw [he,HF,hzG a c (by simpa only [hcz] using hazB)]
      simp only [zero_mul,zero_add,fullScalarCutGamma]
  · have H:=cutDisorderExpect_one_low_edge_zero n 0 U hU0 0 0 0 K T hU
      (fun _=>1) 0 (by intro i; rfl) (by intro i; rfl) a z c d
      (not_le.mpr haz) (not_le.mpr hcd) hj
    rw [cut_full_monomial_eq_retained n 0 U 0 0 K T ho (fun _=>1) [a,z,c,d]] at H
    rw [T.cavityLeft.disorderExpect_one (restWeight_pos n) (restFeature n) ho,one_mul] at H
    rw [H]
    have hf : fullScalarCutGamma T U K a c*fullScalarCutGamma T U K z d=0 := by
      by_cases hac : B a=B c
      · have hzd : B z ≠ B d := fun h=>hj (Or.inl ⟨hac.symm,h.symm⟩)
        rw [hzG z d hzd,mul_zero]
      · rw [hzG a c hac,zero_mul]
    have hb : fullScalarCutGamma T U K a d*fullScalarCutGamma T U K z c=0 := by
      by_cases had : B a=B d
      · have hzc : B z ≠ B c := fun h=>hj (Or.inr ⟨h.symm,had.symm⟩)
        rw [hzG z c hzc,mul_zero]
      · rw [hzG a d had,zero_mul]
    rw [hf,hb,zero_add]

theorem retained_one_low_eq_gamma_allocations (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (A : ℕ→Spin n→Spin n→ℝ)
    (hA : ∀ j, U ≤ j → ∀ σ τ,A j σ τ=0)
    (a z : T.Slot) (hU : U ≤ as.length) (haz : T.splitIndex a z < U) :
    retainedSignedJets n q U b h K [A] T P [a,z]=
    ((T.markedAttach 0).map (fun p=>p.coeff*
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*
        r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (insertedRestTest P A p r) 0*
        (fullScalarCutGamma r.tree U K (r.embed (p.embed a)) (r.embed p.mark)*
          fullScalarCutGamma r.tree U K (r.embed (p.embed z)) r.mark+
         fullScalarCutGamma r.tree U K (r.embed (p.embed a)) r.mark*
          fullScalarCutGamma r.tree U K (r.embed (p.embed z)) (r.embed p.mark)))).sum)).sum/2 := by
  simp only [retainedSignedJets]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro r hr
  have hab' : r.tree.splitIndex (r.embed (p.embed a)) (r.embed (p.embed z)) < U := by
    rw [(p.tree.markedAttach_embed_preserves 0 r hr).2,
      (T.markedAttach_embed_preserves 0 p hp).2]
    exact haz
  by_cases H : r.tree.splitIndex (r.embed p.mark) r.mark < U
  · rw [show insertedSiteSlots [a,z] p r=
      [r.embed (p.embed a),r.embed (p.embed z),r.embed p.mark,r.mark] from rfl,
      fullScalarCutMoment_low_pairing r.tree ho U K _ _ _ _ hU hab' H]
    ring
  · have he : insertedRestTest P A p r=fun _=>0 := by
      funext τ
      simp only [insertedRestTest,hA _ (le_of_not_gt H),mul_zero]
    rw [he]
    simp only [ClockTree.disorderExpect,mul_zero,Finset.sum_const_zero,zero_mul]

theorem native_rest_marked_restrict_preserves (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (p : ClockTree.MarkedPlacement T)
    (hp : p∈T.markedAttach 0) :
    p.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (fun τ=>P (p.restRestrict τ)) 0=
      T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q P 0 := by
  have H:=T.markedAttach_disorderPreserves_actual (fullWeight_pos n) (fullFeature n) ho
    p hp 0 (cutFullVariance n q U 0 0 b h K)
    (fun σ=>P (T.cavityAssignment σ).1) 0
  simp only [p.restRestrict_actual] at H
  rw [native_decoupled_rest_expect n q U b h K p.tree ho (fun τ=>P (p.restRestrict τ)),
    native_decoupled_rest_expect n q U b h K T ho P] at H
  exact H

def restCenteredLowKernel (n U : ℕ) (b S : ℕ→ℝ)
    (j : ℕ) (σ τ : Spin n) : ℝ :=
  if j<U then b j*((∑ i,spinValue (σ i)*spinValue (τ i))/(n+1:ℕ)-S j) else 0

theorem native_inserted_low_centering (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K S : ℕ→ℝ)
    (hKS : ∀ j,K j=h j+b j*S j) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ)
    (p : ClockTree.MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (r : ClockTree.MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0) :
    r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (insertedRestTest P (restLowKernel n U b h) p r) 0=
    r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (insertedRestTest P (restCenteredLowKernel n U b S) p r) 0+
    T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q P 0*
      r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
        (insertedRestTest (fun _=>1) (restLowKernel n U 0 K) p r) 0 := by
  let j:=r.tree.splitIndex (r.embed p.mark) r.mark
  have Hpres : r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (fun τ=>P (p.restRestrict (r.restRestrict τ))) 0=
      T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q P 0 :=
    (native_rest_marked_restrict_preserves n q U b h K p.tree ho
      (fun τ=>P (p.restRestrict τ)) r hr).trans
      (native_rest_marked_restrict_preserves n q U b h K T ho P p hp)
  by_cases hj : j<U
  · have hf : insertedRestTest P (restLowKernel n U b h) p r=
        fun τ=>insertedRestTest P (restCenteredLowKernel n U b S) p r τ+
          K j*P (p.restRestrict (r.restRestrict τ)) := by
      funext τ
      dsimp only [insertedRestTest,restLowKernel,restCenteredLowKernel]
      simp only [show r.tree.splitIndex (r.embed p.mark) r.mark<U from hj,ite_true,hKS j]
      dsimp only [j]
      ring
    have hc : insertedRestTest (fun _=>1) (restLowKernel n U 0 K) p r=fun _=>K j := by
      funext τ
      simp only [insertedRestTest,restLowKernel,show r.tree.splitIndex (r.embed p.mark) r.mark<U from hj,
        ite_true,Pi.zero_apply,zero_mul,add_zero,one_mul]
      rfl
    rw [hf,hc]
    have Hadd : r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
        (fun τ=>insertedRestTest P (restCenteredLowKernel n U b S) p r τ+
          K j*P (p.restRestrict (r.restRestrict τ))) 0=
      r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
        (insertedRestTest P (restCenteredLowKernel n U b S) p r) 0+
      K j*r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
        (fun τ=>P (p.restRestrict (r.restRestrict τ))) 0 := by
      unfold ClockTree.disorderExpect
      simp only [mul_add,Finset.sum_add_distrib]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro τ _
      ring
    have HK : r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
        (fun _=>K j) 0=K j := by
      have HE:=r.tree.cavityLeft.disorderExpect_const_mul (restWeight_pos n) (restFeature n) ho
        0 q (fun _=>1) (K j) 0
      simpa only [mul_one,r.tree.cavityLeft.disorderExpect_one (restWeight_pos n) (restFeature n) ho] using HE
    rw [Hadd,Hpres,HK]
    ring
  · have h0 (A : ℕ→Spin n→Spin n→ℝ) (hA : ∀ σ τ,A j σ τ=0)
        (Q : T.cavityLeft.Assignment→ℝ) : insertedRestTest Q A p r=fun _=>0 := by
      funext τ
      simp only [insertedRestTest,show r.tree.splitIndex (r.embed p.mark) r.mark=j from rfl,hA,mul_zero]
    rw [h0 _ (by intro σ τ;simp only [restLowKernel,hj,ite_false]) P,
      h0 _ (by intro σ τ;simp only [restCenteredLowKernel,hj,ite_false]) P,
      h0 _ (by intro σ τ;simp only [restLowKernel,hj,ite_false]) (fun _=>1)]
    simp only [ClockTree.disorderExpect,mul_zero,Finset.sum_const_zero,zero_add]

theorem native_retained_one_low_centering (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K S : ℕ→ℝ)
    (hKS : ∀ j,K j=h j+b j*S j) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (es : List T.Slot) :
    retainedSignedJets n q U b h K [restLowKernel n U b h] T P es-
      T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q P 0*
        retainedSignedJets n q U b h K [restLowKernel n U 0 K] T (fun _=>1) es=
      retainedSignedJets n q U b h K [restCenteredLowKernel n U b S] T P es := by
  let c:=T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q P 0
  have hi (p : ClockTree.MarkedPlacement T) (hp : p∈T.markedAttach 0) :
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*
        r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (insertedRestTest P (restLowKernel n U b h) p r) 0*
        fullScalarCutMoment r.tree U K (insertedSiteSlots es p r))).sum=
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*
        r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (insertedRestTest P (restCenteredLowKernel n U b S) p r) 0*
        fullScalarCutMoment r.tree U K (insertedSiteSlots es p r))).sum+
      c*((p.tree.markedAttach 0).map (fun r=>r.coeff*
        r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (insertedRestTest (fun _=>1) (restLowKernel n U 0 K) p r) 0*
        fullScalarCutMoment r.tree U K (insertedSiteSlots es p r))).sum := by
    have he : (p.tree.markedAttach 0).map (fun r=>r.coeff*
        r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (insertedRestTest P (restLowKernel n U b h) p r) 0*
        fullScalarCutMoment r.tree U K (insertedSiteSlots es p r))=
      (p.tree.markedAttach 0).map (fun r=>
        r.coeff*r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (insertedRestTest P (restCenteredLowKernel n U b S) p r) 0*
          fullScalarCutMoment r.tree U K (insertedSiteSlots es p r)+
        c*(r.coeff*r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (insertedRestTest (fun _=>1) (restLowKernel n U 0 K) p r) 0*
          fullScalarCutMoment r.tree U K (insertedSiteSlots es p r))) := by
      apply List.map_congr_left
      intro r hr
      rw [native_inserted_low_centering n q U b h K S hKS T ho P p hp r hr]
      dsimp only [c]
      ring
    rw [he,List.sum_map_add,List.sum_map_mul_left]
  have he : (T.markedAttach 0).map (fun p=>p.coeff*
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*
        r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (insertedRestTest P (restLowKernel n U b h) p r) 0*
        fullScalarCutMoment r.tree U K (insertedSiteSlots es p r))).sum)=
    (T.markedAttach 0).map (fun p=>
      p.coeff*((p.tree.markedAttach 0).map (fun r=>r.coeff*
        r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (insertedRestTest P (restCenteredLowKernel n U b S) p r) 0*
        fullScalarCutMoment r.tree U K (insertedSiteSlots es p r))).sum+
      c*(p.coeff*((p.tree.markedAttach 0).map (fun r=>r.coeff*
        r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (insertedRestTest (fun _=>1) (restLowKernel n U 0 K) p r) 0*
        fullScalarCutMoment r.tree U K (insertedSiteSlots es p r))).sum)) := by
    apply List.map_congr_left
    intro p hp
    rw [hi p hp]
    ring
  have HS:=congrArg List.sum he
  rw [List.sum_map_add,List.sum_map_mul_left] at HS
  have Hdiv:=congrArg (fun v : ℝ=>v/2) HS
  dsimp only [c] at Hdiv
  simp only [retainedSignedJets,mul_assoc] at Hdiv ⊢
  nlinarith

end OAI.SKFluctuations.Cavity
