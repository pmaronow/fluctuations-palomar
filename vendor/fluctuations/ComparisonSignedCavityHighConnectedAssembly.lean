module

public import ComparisonSignedCavityScalarFirstCalibration
public import CavityFiniteProfilePermutation

@[expose] public section

noncomputable section
set_option maxHeartbeats 300000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem native_retained_low_high_eq_high_low (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (es : List T.Slot)
    (hq0 : ∀ j i,0 ≤ q j i) (hq : ∀ i,Monotone (fun j=>q j i))
    (hb : ∀ j,0 ≤ b j) (hh : ∀ j,0 ≤ h j) (hK : ∀ j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    retainedSignedJets n q U b h K [restLowKernel n U b h,restHighKernel n U b h K] T P es=
      retainedSignedJets n q U b h K [restHighKernel n U b h K,restLowKernel n U b h] T P es := by
  classical
  let L:=cutLSlope n U 1 b h K
  let H:=cutTSlope n U 0 b h K
  let B : ℝ := ∑ j : Fin (as.length + 1),
    (∑ i : FullCoordinate n, (|L j.val i| + |H j.val i|))
  have hB : 0 ≤ B := Finset.sum_nonneg fun j _ =>
    Finset.sum_nonneg fun i _ => add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hbound : ∀ D∈[L,H],∀ j,j ≤ as.length → ∀ i,|D j i| ≤ B := by
    intro D hD j hj i
    let r:Fin (as.length+1):=⟨j,by omega⟩
    have hi : |L j i| + |H j i| ≤
        ∑ z : FullCoordinate n, (|L j z| + |H j z|) :=
      Finset.single_le_sum (s := Finset.univ)
        (f := fun z : FullCoordinate n => |L j z| + |H j z|)
        (fun z _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ i)
    have hr : (∑ z : FullCoordinate n, (|L j z| + |H j z|)) ≤ B := by
      simpa only [B, r] using (Finset.single_le_sum
        (s := Finset.univ)
        (f := fun t : Fin (as.length + 1) =>
          ∑ z : FullCoordinate n, (|L t.val z| + |H t.val z|))
        (fun t _ => Finset.sum_nonneg fun z _ =>
          add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ r))
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hD
    rcases hD with rfl | rfl
    · exact (le_add_of_nonneg_right (abs_nonneg _)).trans (hi.trans hr)
    · exact (le_add_of_nonneg_left (abs_nonneg _)).trans (hi.trans hr)
  rw [←actual_site_rest_jets_eq_retained n q U b h K _ T ho P es,
    ←actual_site_rest_jets_eq_retained n q U b h K _ T ho P es]
  simp only [List.map_cons,List.map_nil,siteRestKernel_eq_cut_low n U b h K,siteRestKernel_eq_cut_high n U b h K]
  have HP : [L,H].Perm [H,L] := List.Perm.swap _ _ []
  exact T.actual_profileJets_perm_finite (fullWeight_pos n) (fullFeature n) ho 0
    (cutFullVariance n q U 0 0 b h K)
    (cutFullVariance_monotone n q U (by norm_num) (by norm_num) hq hb hh hK hbm hhm hKm)
    (fun i=>cutFullVariance_nonneg n q U (by norm_num) (by norm_num) hq0 hb hh hK 0 i)
    hB HP hbound _ 0

def nativeLowConnectedSix (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (a z e f : T.Slot) : ℝ :=
  ((T.markedAttach 0).map (fun p=>p.coeff*
    ((p.tree.markedAttach 0).map (fun r=>r.coeff*
      r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
        (insertedRestTest P (restLowKernel n U b h) p r) 0*
      (fullScalarCutMoment r.tree U K (insertedSiteSlots [a,z,e,f] p r)-
       fullScalarCutGamma r.tree U K (r.embed (p.embed e)) (r.embed (p.embed f))*
        (fullScalarCutGamma r.tree U K (r.embed (p.embed a)) (r.embed p.mark)*
          fullScalarCutGamma r.tree U K (r.embed (p.embed z)) r.mark+
         fullScalarCutGamma r.tree U K (r.embed (p.embed a)) r.mark*
          fullScalarCutGamma r.tree U K (r.embed (p.embed z)) (r.embed p.mark))))).sum)).sum/2

theorem native_low_connected_six_eq_retained_difference (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a z e f : T.Slot)
    (hU : U ≤ as.length) (haz : T.splitIndex a z < U) :
    nativeLowConnectedSix n q U b h K T P a z e f=
      retainedSignedJets n q U b h K [restLowKernel n U b h] T P [a,z,e,f]-
      fullScalarCutGamma T U K e f*
        retainedSignedJets n q U b h K [restLowKernel n U b h] T P [a,z] := by
  rw [retained_one_low_eq_gamma_allocations n q U b h K T ho P
    (restLowKernel n U b h) (by intro j hj σ τ;simp [restLowKernel,not_lt.mpr hj]) a z hU haz]
  unfold nativeLowConnectedSix
  have HI (p : ClockTree.MarkedPlacement T) (hp : p∈T.markedAttach 0) :
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*
        r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (insertedRestTest P (restLowKernel n U b h) p r) 0*
        (fullScalarCutMoment r.tree U K (insertedSiteSlots [a,z,e,f] p r)-
         fullScalarCutGamma r.tree U K (r.embed (p.embed e)) (r.embed (p.embed f))*
          (fullScalarCutGamma r.tree U K (r.embed (p.embed a)) (r.embed p.mark)*
            fullScalarCutGamma r.tree U K (r.embed (p.embed z)) r.mark+
           fullScalarCutGamma r.tree U K (r.embed (p.embed a)) r.mark*
            fullScalarCutGamma r.tree U K (r.embed (p.embed z)) (r.embed p.mark))))).sum=
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*
        r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (insertedRestTest P (restLowKernel n U b h) p r) 0*
        fullScalarCutMoment r.tree U K (insertedSiteSlots [a,z,e,f] p r))).sum-
      fullScalarCutGamma T U K e f*((p.tree.markedAttach 0).map (fun r=>r.coeff*
        r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (insertedRestTest P (restLowKernel n U b h) p r) 0*
        (fullScalarCutGamma r.tree U K (r.embed (p.embed a)) (r.embed p.mark)*
          fullScalarCutGamma r.tree U K (r.embed (p.embed z)) r.mark+
         fullScalarCutGamma r.tree U K (r.embed (p.embed a)) r.mark*
          fullScalarCutGamma r.tree U K (r.embed (p.embed z)) (r.embed p.mark)))).sum := by
    have HE : (p.tree.markedAttach 0).map (fun r=>r.coeff*
        r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (insertedRestTest P (restLowKernel n U b h) p r) 0*
        (fullScalarCutMoment r.tree U K (insertedSiteSlots [a,z,e,f] p r)-
         fullScalarCutGamma r.tree U K (r.embed (p.embed e)) (r.embed (p.embed f))*
          (fullScalarCutGamma r.tree U K (r.embed (p.embed a)) (r.embed p.mark)*
            fullScalarCutGamma r.tree U K (r.embed (p.embed z)) r.mark+
           fullScalarCutGamma r.tree U K (r.embed (p.embed a)) r.mark*
            fullScalarCutGamma r.tree U K (r.embed (p.embed z)) (r.embed p.mark))))=
      (p.tree.markedAttach 0).map (fun r=>
        r.coeff*r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (insertedRestTest P (restLowKernel n U b h) p r) 0*
          fullScalarCutMoment r.tree U K (insertedSiteSlots [a,z,e,f] p r)-
        fullScalarCutGamma T U K e f*(r.coeff*
          r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
            (insertedRestTest P (restLowKernel n U b h) p r) 0*
          (fullScalarCutGamma r.tree U K (r.embed (p.embed a)) (r.embed p.mark)*
            fullScalarCutGamma r.tree U K (r.embed (p.embed z)) r.mark+
           fullScalarCutGamma r.tree U K (r.embed (p.embed a)) r.mark*
            fullScalarCutGamma r.tree U K (r.embed (p.embed z)) (r.embed p.mark)))) := by
      apply List.map_congr_left
      intro r hr
      rw [fullScalarCutGamma_double_preserves T ho U K e f p hp r hr]
      ring
    rw [HE,sum_map_sub_explicit,List.sum_map_mul_left]
  have HE : (T.markedAttach 0).map (fun p=>p.coeff*
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*
        r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (insertedRestTest P (restLowKernel n U b h) p r) 0*
        (fullScalarCutMoment r.tree U K (insertedSiteSlots [a,z,e,f] p r)-
         fullScalarCutGamma r.tree U K (r.embed (p.embed e)) (r.embed (p.embed f))*
          (fullScalarCutGamma r.tree U K (r.embed (p.embed a)) (r.embed p.mark)*
            fullScalarCutGamma r.tree U K (r.embed (p.embed z)) r.mark+
           fullScalarCutGamma r.tree U K (r.embed (p.embed a)) r.mark*
            fullScalarCutGamma r.tree U K (r.embed (p.embed z)) (r.embed p.mark))))).sum)=
    (T.markedAttach 0).map (fun p=>
      p.coeff*((p.tree.markedAttach 0).map (fun r=>r.coeff*
        r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (insertedRestTest P (restLowKernel n U b h) p r) 0*
        fullScalarCutMoment r.tree U K (insertedSiteSlots [a,z,e,f] p r))).sum-
      fullScalarCutGamma T U K e f*(p.coeff*((p.tree.markedAttach 0).map (fun r=>r.coeff*
        r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (insertedRestTest P (restLowKernel n U b h) p r) 0*
        (fullScalarCutGamma r.tree U K (r.embed (p.embed a)) (r.embed p.mark)*
          fullScalarCutGamma r.tree U K (r.embed (p.embed z)) r.mark+
         fullScalarCutGamma r.tree U K (r.embed (p.embed a)) r.mark*
          fullScalarCutGamma r.tree U K (r.embed (p.embed z)) (r.embed p.mark)))).sum)) := by
    apply List.map_congr_left
    intro p hp
    rw [HI p hp]
    ring
  rw [HE,sum_map_sub_explicit,List.sum_map_mul_left]
  simp only [retainedSignedJets,mul_assoc]
  ring

def nativeLowHighConnectedCoefficient (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (a z e f : T.Slot) : ℝ :=
  retainedSignedJets n q U b h K [restLowKernel n U b h] T P [a,z,e,f]-
  K (T.splitIndex a z)*
    ((scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0)^2*
    T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q P 0*
    fullScalarCutGamma T U K e f

theorem native_low_high_connected_eq_defect_and_six (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K S : ℕ→ℝ)
    (hKS : ∀ j,K j=h j+b j*S j) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a z e f : T.Slot)
    (hU : U ≤ as.length) (haz : T.splitIndex a z < U) :
    nativeLowHighConnectedCoefficient n q U b h K T P a z e f=
      fullScalarCutGamma T U K e f*
        retainedSignedJets n q U b h K [restCenteredLowKernel n U b S] T P [a,z]+
      nativeLowConnectedSix n q U b h K T P a z e f := by
  have HC:=native_low_connected_six_eq_retained_difference n q U b h K T ho P a z e f hU haz
  have HD:=native_retained_one_low_centering n q U b h K S hKS T ho P [a,z]
  rw [native_scalar_first_retained_eq_K_hessian_sq n q U b h K T ho a z hU haz] at HD
  unfold nativeLowHighConnectedCoefficient
  calc
    _ = (retainedSignedJets n q U b h K [restLowKernel n U b h] T P [a,z,e,f]-
          fullScalarCutGamma T U K e f*
            retainedSignedJets n q U b h K [restLowKernel n U b h] T P [a,z])+
        fullScalarCutGamma T U K e f*
          (retainedSignedJets n q U b h K [restLowKernel n U b h] T P [a,z]-
            T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q P 0*
            (K (T.splitIndex a z)*
              ((scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0)^2)) := by ring
    _ = _ := by rw [←HC,HD];ring

theorem native_signed_double_sum_sub {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (F G : ∀ p : ClockTree.MarkedPlacement T,
      ClockTree.MarkedPlacement p.tree→ℝ) (c : ℝ) :
    ((T.markedAttach 0).map (fun p=>p.coeff*
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*(F p r-c*G p r))).sum)).sum=
    ((T.markedAttach 0).map (fun p=>p.coeff*
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*F p r)).sum)).sum-
    c*((T.markedAttach 0).map (fun p=>p.coeff*
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*G p r)).sum)).sum := by
  have hi (p : ClockTree.MarkedPlacement T) :
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*(F p r-c*G p r))).sum=
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*F p r)).sum-
        c*((p.tree.markedAttach 0).map (fun r=>r.coeff*G p r)).sum := by
    have he (r : ClockTree.MarkedPlacement p.tree) :
        r.coeff*(F p r-c*G p r)=r.coeff*F p r-c*(r.coeff*G p r) := by ring
    simp_rw [he]
    rw [sum_map_sub_explicit,List.sum_map_mul_left]
  simp_rw [hi]
  have he (p : ClockTree.MarkedPlacement T) (x y : ℝ) :
      p.coeff*(x-c*y)=p.coeff*x-c*(p.coeff*y) := by ring
  simp_rw [he]
  rw [sum_map_sub_explicit,List.sum_map_mul_left]

def nativeErrorFirstConnectedLedger (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) : ℝ :=
  ((T.markedAttach 0).map (fun p=>p.coeff*
    ((p.tree.markedAttach 0).map (fun r=>r.coeff*
      nativeLowHighConnectedCoefficient n q U b h K r.tree
        (insertedRestTest P (restHighKernel n U b h K) p r)
        (r.embed (p.embed a)) (r.embed (p.embed z)) (r.embed p.mark) r.mark)).sum)).sum/2

theorem native_error_first_ledger_eq_centered_high_low (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) :
    nativeErrorFirstConnectedLedger n q U b h K T P a z=
      retainedSignedJets n q U b h K [restHighKernel n U b h K,restLowKernel n U b h] T P [a,z]-
      K (T.splitIndex a z)*
        ((scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0)^2*
        retainedSignedJets n q U b h K [restHighKernel n U b h K] T P [] := by
  let c:=K (T.splitIndex a z)*
    ((scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0)^2
  let F:=fun (p : ClockTree.MarkedPlacement T) (r : ClockTree.MarkedPlacement p.tree)=>
    retainedSignedJets n q U b h K [restLowKernel n U b h] r.tree
      (insertedRestTest P (restHighKernel n U b h K) p r)
      [r.embed (p.embed a),r.embed (p.embed z),r.embed p.mark,r.mark]
  let G:=fun (p : ClockTree.MarkedPlacement T) (r : ClockTree.MarkedPlacement p.tree)=>
    r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (insertedRestTest P (restHighKernel n U b h K) p r) 0*
      fullScalarCutGamma r.tree U K (r.embed p.mark) r.mark
  have HE : (T.markedAttach 0).map (fun p=>p.coeff*
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*
        nativeLowHighConnectedCoefficient n q U b h K r.tree
          (insertedRestTest P (restHighKernel n U b h K) p r)
          (r.embed (p.embed a)) (r.embed (p.embed z)) (r.embed p.mark) r.mark)).sum)=
    (T.markedAttach 0).map (fun p=>p.coeff*
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*(F p r-c*G p r))).sum) := by
    apply List.map_congr_left
    intro p hp
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro r hr
    have hs : r.tree.splitIndex (r.embed (p.embed a)) (r.embed (p.embed z))=T.splitIndex a z := by
      rw [(p.tree.markedAttach_embed_preserves 0 r hr).2,
        (T.markedAttach_embed_preserves 0 p hp).2]
    unfold nativeLowHighConnectedCoefficient
    rw [hs]
    dsimp only [F,G,c]
    ring
  unfold nativeErrorFirstConnectedLedger
  rw [HE,native_signed_double_sum_sub]
  dsimp only [F,G,c]
  simp only [retainedSignedJets,insertedSiteSlots,List.map_cons,List.map_nil,
    List.cons_append,List.nil_append,fullScalarCutGamma,mul_assoc]
  ring

theorem actual_first_low_high_centered_eq_error_first_ledger (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (hq0 : ∀ j i,0 ≤ q j i) (hq : ∀ i,Monotone (fun j=>q j i))
    (hb : ∀ j,0 ≤ b j) (hh : ∀ j,0 ≤ h j) (hK : ∀ j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    (hU : U ≤ as.length) (haz : T.splitIndex a z < U) :
    cutFrozenCenteredJet n q U b h K T P (sitePair T a z) 0 1 1 0=
      nativeErrorFirstConnectedLedger n q U b h K T P a z := by
  rw [←nativeScalarTest_pair,actual_frozen_centered_coefficient_eq_native_retained n q U b h K T ho
    P [a,z] hq0 hq hb hh hK hbm hhm hKm]
  have HZ : retainedSignedJets n q U b h K [] T (fun _=>1) [a,z]=0 := by
    simp only [retainedSignedJets]
    have hgamma : fullScalarCutMoment T U K [a,z]=0 := fullScalarCutGamma_cross_zero T ho U K a z hU haz
    rw [hgamma,mul_zero]
  simp only [nativeRetainedCenteredCoefficient,productJet3,Fin.val_one,Fin.val_zero,
    List.replicate_one,List.replicate_zero,List.nil_append,List.append_nil,List.cons_append]
  rw [HZ,native_scalar_first_retained_eq_K_hessian_sq n q U b h K T ho a z hU haz]
  simp only [zero_mul,zero_add]
  rw [native_retained_low_high_eq_high_low n q U b h K T ho P [a,z] hq0 hq hb hh hK hbm hhm hKm,
    ←native_error_first_ledger_eq_centered_high_low n q U b h K T ho P a z]

end OAI.SKFluctuations.Cavity
