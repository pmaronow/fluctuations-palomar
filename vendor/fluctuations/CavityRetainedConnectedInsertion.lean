module

public import CavitySignedScalarInsertion
public import CavityDiagonalCancellation

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped BigOperators Topology NNReal

theorem fullScalarCutMoment_marked_preserves {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (K : ℕ→ℝ) (es : List T.Slot)
    (p : ClockTree.MarkedPlacement T) (hp : p∈T.markedAttach 0) :
    fullScalarCutMoment p.tree U K (es.map p.embed)=fullScalarCutMoment T U K es := by
  have H:=T.markedAttach_disorderPreserves_actual (fullWeight_pos n) (fullFeature n) ho
    p hp 0 (cutFullVariance n 0 U 0 0 0 0 K) (fun σ=>siteMonomial T σ es) 0
  have h1:=cut_full_monomial_eq_retained n 0 U 0 0 K p.tree ho (fun _=>1) (es.map p.embed)
  have h2:=cut_full_monomial_eq_retained n 0 U 0 0 K T ho (fun _=>1) es
  simp only [one_mul] at h1 h2
  rw [p.tree.cavityLeft.disorderExpect_one (restWeight_pos n) (restFeature n) ho] at h1
  rw [T.cavityLeft.disorderExpect_one (restWeight_pos n) (restFeature n) ho] at h2
  simp only [one_mul] at h1 h2
  simp only [siteMonomial_marked_restrict] at H
  rw [h1,h2] at H
  exact H

theorem fullScalarCutGamma_double_preserves {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (K : ℕ→ℝ) (a c : T.Slot)
    (p : ClockTree.MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (r : ClockTree.MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0) :
    fullScalarCutGamma r.tree U K (r.embed (p.embed a)) (r.embed (p.embed c))=
      fullScalarCutGamma T U K a c := by
  unfold fullScalarCutGamma
  have h1:=fullScalarCutMoment_marked_preserves T ho U K [a,c] p hp
  have h2:=fullScalarCutMoment_marked_preserves p.tree ho U K ([a,c].map p.embed) r hr
  simpa only [List.map_cons,List.map_nil] using h2.trans h1

theorem full_retained_six_connected_left {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (hU0 : 0<U) (hU : U≤as.length) (K : ℕ→ℝ)
    (a c z d e f : T.Slot)
    (hcross : ∀ s∈[a,c,e,f], ∀ t∈[z,d], T.splitIndex s t<U) :
    fullScalarCutMoment T U K [a,c,z,d,e,f]-
      fullScalarCutGamma T U K a c*fullScalarCutGamma T U K z d*fullScalarCutGamma T U K e f =
      fullScalarCutConnected4 T U K a c e f*fullScalarCutGamma T U K z d := by
  have he : fullScalarCutMoment T U K [a,c,z,d,e,f]=
      fullScalarCutMoment T U K [a,c,e,f,z,d] := by
    unfold fullScalarCutMoment scalarCutMoment
    congr 1
    funext σ
    simp only [List.map_cons,List.map_nil,ClockTree.slotProduct]
    ring
  have hf:=fullScalarCutMoment_factor T ho U hU0 hU K [a,c,e,f] [z,d] hcross
  simp only [List.cons_append,List.nil_append] at hf
  rw [he,hf]
  unfold fullScalarCutConnected4 fullScalarCutGamma
  ring

theorem full_retained_six_connected_right {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (hU0 : 0<U) (hU : U≤as.length) (K : ℕ→ℝ)
    (a c z d e f : T.Slot)
    (hcross : ∀ s∈[a,c], ∀ t∈[z,d,e,f], T.splitIndex s t<U) :
    fullScalarCutMoment T U K [a,c,z,d,e,f]-
      fullScalarCutGamma T U K a c*fullScalarCutGamma T U K z d*fullScalarCutGamma T U K e f =
      fullScalarCutGamma T U K a c*fullScalarCutConnected4 T U K z d e f := by
  have hf:=fullScalarCutMoment_factor T ho U hU0 hU K [a,c] [z,d,e,f] hcross
  simp only [List.cons_append,List.nil_append] at hf
  rw [hf]
  unfold fullScalarCutConnected4 fullScalarCutGamma
  ring

theorem full_retained_six_connected_outside {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (hU0 : 0<U) (hU : U≤as.length) (K : ℕ→ℝ)
    (a c z d e f : T.Slot)
    (h1 : ∀ s∈[a,c], ∀ t∈[z,d,e,f], T.splitIndex s t<U)
    (h2 : ∀ s∈[z,d], ∀ t∈[e,f], T.splitIndex s t<U) :
    fullScalarCutMoment T U K [a,c,z,d,e,f]-
      fullScalarCutGamma T U K a c*fullScalarCutGamma T U K z d*fullScalarCutGamma T U K e f=0 := by
  have hf1:=fullScalarCutMoment_factor T ho U hU0 hU K [a,c] [z,d,e,f] h1
  have hf2:=fullScalarCutMoment_factor T ho U hU0 hU K [z,d] [e,f] h2
  simp only [List.cons_append,List.nil_append] at hf1 hf2
  rw [hf1,hf2]
  unfold fullScalarCutGamma
  ring

theorem sum_map_sub_explicit {A : Type*} (L : List A) (F G : A→ℝ) :
    (L.map (fun x=>F x-G x)).sum=(L.map F).sum-(L.map G).sum := by
  induction L with
  | nil => simp
  | cons x L ih => simp only [List.map_cons,List.sum_cons,ih]; ring

theorem actual_connected_site_rest_jet_eq_signed (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (A : ℕ→Spin n→Spin n→ℝ) (a c z d : T.Slot) :
    ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0
      (cutFullVariance n q U 0 0 b h K) 0 [siteRestKernel n A] T
      (fun σ=>P (T.cavityAssignment σ).1*siteMonomial T σ [a,c,z,d]) -
    (fullScalarCutGamma T U K a c*fullScalarCutGamma T U K z d)*
      ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0
        (cutFullVariance n q U 0 0 b h K) 0 [siteRestKernel n A] T
        (fun σ=>P (T.cavityAssignment σ).1*siteMonomial T σ []) =
    ((T.markedAttach 0).map (fun p=>p.coeff*
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*
        r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (insertedRestTest P A p r) 0*
        (fullScalarCutMoment r.tree U K (insertedSiteSlots [a,c,z,d] p r)-
          fullScalarCutGamma r.tree U K (r.embed (p.embed a)) (r.embed (p.embed c))*
          fullScalarCutGamma r.tree U K (r.embed (p.embed z)) (r.embed (p.embed d))*
          fullScalarCutGamma r.tree U K (r.embed p.mark) r.mark))).sum)).sum/2 := by
  rw [actual_site_rest_jet_eq_signed_scalar_sum n q U b h K T ho,
    actual_site_rest_jet_eq_signed_scalar_sum n q U b h K T ho]
  have H : ((T.markedAttach 0).map (fun p=>p.coeff*
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*
        r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (insertedRestTest P A p r) 0*
        (fullScalarCutMoment r.tree U K (insertedSiteSlots [a,c,z,d] p r)-
          fullScalarCutGamma r.tree U K (r.embed (p.embed a)) (r.embed (p.embed c))*
          fullScalarCutGamma r.tree U K (r.embed (p.embed z)) (r.embed (p.embed d))*
          fullScalarCutGamma r.tree U K (r.embed p.mark) r.mark))).sum)).sum =
    ((T.markedAttach 0).map (fun p=>p.coeff*
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*
        r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (insertedRestTest P A p r) 0*
        (fullScalarCutMoment r.tree U K (insertedSiteSlots [a,c,z,d] p r)-
          fullScalarCutGamma T U K a c*fullScalarCutGamma T U K z d*
          fullScalarCutMoment r.tree U K (insertedSiteSlots [] p r)))).sum)).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro r hr
    rw [fullScalarCutGamma_double_preserves T ho U K a c p hp r hr,
      fullScalarCutGamma_double_preserves T ho U K z d p hp r hr]
    rfl
  rw [H]
  have hi (p : ClockTree.MarkedPlacement T) :
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*
        r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (insertedRestTest P A p r) 0*
        (fullScalarCutMoment r.tree U K (insertedSiteSlots [a,c,z,d] p r)-
          fullScalarCutGamma T U K a c*fullScalarCutGamma T U K z d*
          fullScalarCutMoment r.tree U K (insertedSiteSlots [] p r)))).sum =
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*
        r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (insertedRestTest P A p r) 0*
        fullScalarCutMoment r.tree U K (insertedSiteSlots [a,c,z,d] p r))).sum-
      (fullScalarCutGamma T U K a c*fullScalarCutGamma T U K z d)*
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*
        r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (insertedRestTest P A p r) 0*
        fullScalarCutMoment r.tree U K (insertedSiteSlots [] p r))).sum := by
    have he (r : ClockTree.MarkedPlacement p.tree) :
        r.coeff*r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (insertedRestTest P A p r) 0*
          (fullScalarCutMoment r.tree U K (insertedSiteSlots [a,c,z,d] p r)-
            fullScalarCutGamma T U K a c*fullScalarCutGamma T U K z d*
            fullScalarCutMoment r.tree U K (insertedSiteSlots [] p r)) =
        r.coeff*r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (insertedRestTest P A p r) 0*
          fullScalarCutMoment r.tree U K (insertedSiteSlots [a,c,z,d] p r)-
        (fullScalarCutGamma T U K a c*fullScalarCutGamma T U K z d)*
          (r.coeff*r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
            (insertedRestTest P A p r) 0*
            fullScalarCutMoment r.tree U K (insertedSiteSlots [] p r)) := by ring
    simp_rw [he]
    rw [sum_map_sub_explicit,List.sum_map_mul_left]
  simp_rw [hi]
  have ho (X Y : ℝ) (p : ClockTree.MarkedPlacement T) :
      p.coeff*(X-(fullScalarCutGamma T U K a c*fullScalarCutGamma T U K z d)*Y)=
      p.coeff*X-(fullScalarCutGamma T U K a c*fullScalarCutGamma T U K z d)*(p.coeff*Y) := by ring
  simp_rw [ho]
  rw [sum_map_sub_explicit,List.sum_map_mul_left]
  ring

end OAI.SKFluctuations.Cavity
