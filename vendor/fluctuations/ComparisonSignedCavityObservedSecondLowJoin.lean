module

public import ComparisonSignedCavityFrozenAssembly

@[expose] public section

noncomputable section
set_option maxHeartbeats 4000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy

theorem fullScalarCutGamma_symm {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (U : ℕ) (K : ℕ→ℝ) (a c : T.Slot) :
    fullScalarCutGamma T U K a c=fullScalarCutGamma T U K c a := by
  unfold fullScalarCutGamma fullScalarCutMoment scalarCutMoment
  congr 1
  funext σ
  simp only [List.map_cons,List.map_nil,ClockTree.slotProduct]
  ring

theorem fullScalarCutMoment_second_low_path {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (hU0 : 0<U) (hU : U≤as.length) (K : ℕ→ℝ)
    (a z f c e d : T.Slot)
    (hA : ∀ s∈[a,f],∀ t∈[c,e,z,d],T.splitIndex s t<U)
    (hD : ∀ s∈[c,e],∀ t∈[z,d],T.splitIndex s t<U) :
    fullScalarCutMoment T U K [a,z,f,c,e,d]=
      fullScalarCutGamma T U K a f*fullScalarCutGamma T U K c e*
        fullScalarCutGamma T U K d z := by
  have he : fullScalarCutMoment T U K [a,z,f,c,e,d]=
      fullScalarCutMoment T U K [a,f,c,e,z,d] := by
    unfold fullScalarCutMoment scalarCutMoment
    congr 1
    funext σ
    simp only [List.map_cons,List.map_nil,ClockTree.slotProduct]
    ring
  have h₁ := fullScalarCutMoment_factor T ho U hU0 hU K [a,f] [c,e,z,d] hA
  have h₂ := fullScalarCutMoment_factor T ho U hU0 hU K [c,e] [z,d] hD
  simp only [List.cons_append,List.nil_append] at h₁ h₂
  rw [he,h₁,h₂]
  change fullScalarCutGamma T U K a f*
      (fullScalarCutGamma T U K c e*fullScalarCutGamma T U K z d)=_
  rw [fullScalarCutGamma_symm T U K z d]
  ring

theorem actual_second_low_path_joint_expectation (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (hU0 : 0<U) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (hU : U≤as.length)
    (P : T.cavityLeft.Assignment→ℝ) (a z f c e d : T.Slot)
    (hA : ∀ s∈[a,f],∀ t∈[c,e,z,d],T.splitIndex s t<U)
    (hD : ∀ s∈[c,e],∀ t∈[z,d],T.splitIndex s t<U) :
    T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cutFullVariance n q U 0 0 b h K)
      (fun σ=>P (T.cavityAssignment σ).1*siteMonomial T σ [a,z,f,c,e,d]) 0=
      fullScalarCutGamma T U K a f*fullScalarCutGamma T U K c e*
        fullScalarCutGamma T U K d z*
        T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q P 0 := by
  rw [cut_full_monomial_eq_retained n q U b h K T ho,
    fullScalarCutMoment_second_low_path T ho U hU0 hU K a z f c e d hA hD]
  ring

theorem retained_one_low_no_site_zero (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (hU : U≤as.length)
    (P : T.cavityLeft.Assignment→ℝ) :
    retainedSignedJets n q U b h K [restLowKernel n U b h] T P []=0 := by
  simp only [retainedSignedJets]
  have hplacement (p : ClockTree.MarkedPlacement T) (hp : p∈T.markedAttach 0)
      (r : ClockTree.MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0) :
      r.coeff*r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
        (insertedRestTest P (restLowKernel n U b h) p r) 0*
        fullScalarCutMoment r.tree U K (insertedSiteSlots [] p r)=0 := by
    by_cases hj : r.tree.splitIndex (r.embed p.mark) r.mark<U
    · have hz := fullScalarCutGamma_cross_zero r.tree ho U K (r.embed p.mark) r.mark hU hj
      change _*fullScalarCutGamma r.tree U K (r.embed p.mark) r.mark=0
      rw [hz,mul_zero]
    · have hz : insertedRestTest P (restLowKernel n U b h) p r=fun _=>0 := by
        funext σ
        simp [insertedRestTest,restLowKernel,hj]
      rw [hz]
      simp [ClockTree.disorderExpect]
  have hm (p : ClockTree.MarkedPlacement T) (hp : p∈T.markedAttach 0) :
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*
        r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (insertedRestTest P (restLowKernel n U b h) p r) 0*
        fullScalarCutMoment r.tree U K (insertedSiteSlots [] p r))).sum=0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨r,hr,rfl⟩:=List.mem_map.mp hx
    exact hplacement p hp r hr
  have hz : ((T.markedAttach 0).map (fun p=>p.coeff*
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*
        r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (insertedRestTest P (restLowKernel n U b h) p r) 0*
        fullScalarCutMoment r.tree U K (insertedSiteSlots [] p r))).sum)).sum=0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hx
    rw [hm p hp,mul_zero]
  simpa only [mul_assoc,zero_div] using congrArg (fun x : ℝ=>x/2) hz

theorem native_second_low_centered_eq_scalar_subtraction (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (P : T.cavityLeft.Assignment→ℝ)
    (a z : T.Slot) (hU : U≤as.length) (haz : T.splitIndex a z<U) :
    nativeRetainedCenteredCoefficient n q U b h K T P [a,z] 2 0=
      retainedSignedJets n q U b h K [restLowKernel n U b h,restLowKernel n U b h]
        T P [a,z]-
      T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q P 0*
        retainedSignedJets n q U b h K [restLowKernel n U 0 K,restLowKernel n U 0 K]
          T (fun _=>1) [a,z] := by
  have h₀ : retainedSignedJets n q U b h K [] T (fun _=>1) [a,z]=0 := by
    simp only [retainedSignedJets]
    change _*fullScalarCutGamma T U K a z=0
    rw [fullScalarCutGamma_cross_zero T ho U K a z hU haz,mul_zero]
  have h₁ := retained_one_low_no_site_zero n q U b h K T ho hU P
  simp only [nativeRetainedCenteredCoefficient,productJet3,Fin.val_zero,
    Fin.val_one,show (2 : Fin 4).val=2 from rfl,List.replicate_zero,
    List.replicate_succ,List.append_nil]
  rw [h₀,h₁]
  simp only [zero_mul,mul_zero,zero_add,add_zero,retainedSignedJets,
    fullScalarCutMoment_nil T ho,mul_one]
  ring

theorem actual_second_low_centered_eq_scalar_subtraction (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (P : T.cavityLeft.Assignment→ℝ)
    (a z : T.Slot)
    (hq0 : ∀ j i,0≤q j i) (hq : ∀ i,Monotone (fun j=>q j i))
    (hb : ∀ j,0≤b j) (hh : ∀ j,0≤h j) (hK : ∀ j,0≤K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    (hU : U≤as.length) (haz : T.splitIndex a z<U) :
    cutFrozenCenteredJet n q U b h K T P (sitePair T a z) 0 2 0 0=
      retainedSignedJets n q U b h K [restLowKernel n U b h,restLowKernel n U b h]
        T P [a,z]-
      T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q P 0*
        retainedSignedJets n q U b h K [restLowKernel n U 0 K,restLowKernel n U 0 K]
          T (fun _=>1) [a,z] := by
  rw [←nativeScalarTest_pair,
    actual_frozen_centered_coefficient_eq_native_retained n q U b h K T ho P [a,z]
      hq0 hq hb hh hK hbm hhm hKm,
    native_second_low_centered_eq_scalar_subtraction n q U b h K T ho P a z hU haz]

def nativeSecondLowScalarValue (U : ℕ) (K : ℕ→ℝ) (j : ℕ) : ℝ :=
  if j<U then K j else 0

theorem restLowKernel_scalar_value (n U : ℕ) (K : ℕ→ℝ)
    (j : ℕ) (σ τ : Spin n) :
    restLowKernel n U 0 K j σ τ=nativeSecondLowScalarValue U K j := by
  simp [restLowKernel,nativeSecondLowScalarValue]

def nativeSecondLowJointRestTest (n U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (P : T.cavityLeft.Assignment→ℝ)
    (p : ClockTree.MarkedPlacement T) (r : ClockTree.MarkedPlacement p.tree)
    (s : ClockTree.MarkedPlacement r.tree) (t : ClockTree.MarkedPlacement s.tree)
    (τ : t.tree.cavityLeft.Assignment) : ℝ :=
  insertedRestTest (insertedRestTest P (restLowKernel n U b h) p r)
      (restLowKernel n U b h) s t τ-
    nativeSecondLowScalarValue U K (r.tree.splitIndex (r.embed p.mark) r.mark)*
      nativeSecondLowScalarValue U K (t.tree.splitIndex (t.embed s.mark) t.mark)*
      P (p.restRestrict (r.restRestrict (s.restRestrict (t.restRestrict τ))))

theorem native_second_low_joint_rest_test_product (n U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (P : T.cavityLeft.Assignment→ℝ)
    (p : ClockTree.MarkedPlacement T) (r : ClockTree.MarkedPlacement p.tree)
    (s : ClockTree.MarkedPlacement r.tree) (t : ClockTree.MarkedPlacement s.tree)
    (τ : t.tree.cavityLeft.Assignment) :
    nativeSecondLowJointRestTest n U b h K P p r s t τ=
      P (p.restRestrict (r.restRestrict (s.restRestrict (t.restRestrict τ))))*
      (restLowKernel n U b h (r.tree.splitIndex (r.embed p.mark) r.mark)
          (p.restSpin (r.restRestrict (s.restRestrict (t.restRestrict τ))))
          (r.restSpin (s.restRestrict (t.restRestrict τ)))*
        restLowKernel n U b h (t.tree.splitIndex (t.embed s.mark) t.mark)
          (s.restSpin (t.restRestrict τ)) (t.restSpin τ)-
        nativeSecondLowScalarValue U K (r.tree.splitIndex (r.embed p.mark) r.mark)*
          nativeSecondLowScalarValue U K (t.tree.splitIndex (t.embed s.mark) t.mark)) := by
  unfold nativeSecondLowJointRestTest insertedRestTest
  ring

theorem native_second_low_joint_rest_expectation (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (P : T.cavityLeft.Assignment→ℝ)
    (p : ClockTree.MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (r : ClockTree.MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
    (s : ClockTree.MarkedPlacement r.tree) (hs : s∈r.tree.markedAttach 0)
    (t : ClockTree.MarkedPlacement s.tree) (ht : t∈s.tree.markedAttach 0) :
    t.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (nativeSecondLowJointRestTest n U b h K P p r s t) 0=
    t.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (insertedRestTest (insertedRestTest P (restLowKernel n U b h) p r)
        (restLowKernel n U b h) s t) 0-
      T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q P 0*
      t.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
        (insertedRestTest (insertedRestTest (fun _=>1) (restLowKernel n U 0 K) p r)
          (restLowKernel n U 0 K) s t) 0 := by
  let P₀ := fun τ=>P (p.restRestrict (r.restRestrict (s.restRestrict (t.restRestrict τ))))
  let k := nativeSecondLowScalarValue U K (r.tree.splitIndex (r.embed p.mark) r.mark)*
    nativeSecondLowScalarValue U K (t.tree.splitIndex (t.embed s.mark) t.mark)
  have hpres : t.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q P₀ 0=
      T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q P 0 := by
    exact (native_rest_marked_restrict_preserves n q U b h K s.tree ho
      (fun τ=>P (p.restRestrict (r.restRestrict (s.restRestrict τ)))) t ht).trans
      ((native_rest_marked_restrict_preserves n q U b h K r.tree ho
        (fun τ=>P (p.restRestrict (r.restRestrict τ))) s hs).trans
      ((native_rest_marked_restrict_preserves n q U b h K p.tree ho
        (fun τ=>P (p.restRestrict τ)) r hr).trans
        (native_rest_marked_restrict_preserves n q U b h K T ho P p hp)))
  have hscalar : insertedRestTest
      (insertedRestTest (fun _=>1) (restLowKernel n U 0 K) p r)
      (restLowKernel n U 0 K) s t=fun _=>k := by
    funext τ
    simp only [insertedRestTest,restLowKernel_scalar_value,one_mul]
    rfl
  have hconst : t.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (fun _=>k) 0=k := by
    simpa only [mul_one,t.tree.cavityLeft.disorderExpect_one (restWeight_pos n)
      (restFeature n) ho] using
      t.tree.cavityLeft.disorderExpect_const_mul (restWeight_pos n) (restFeature n)
        ho 0 q (fun _=>1) k 0
  have hdiff : t.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (nativeSecondLowJointRestTest n U b h K P p r s t) 0=
      t.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
        (insertedRestTest (insertedRestTest P (restLowKernel n U b h) p r)
          (restLowKernel n U b h) s t) 0-
        k*t.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q P₀ 0 := by
    unfold nativeSecondLowJointRestTest ClockTree.disorderExpect
    simp only [mul_sub,Finset.sum_sub_distrib]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro τ _
    dsimp only [P₀,k]
    ring
  rw [hdiff,hscalar,hconst,hpres]
  ring

def nativeSecondLowDoubleAverage {S : Type*} {as : List PositiveMass}
    (T : ClockTree S as) (F : ∀ p : ClockTree.MarkedPlacement T,
      ClockTree.MarkedPlacement p.tree→ℝ) : ℝ :=
  ((T.markedAttach 0).map (fun p=>p.coeff*
    ((p.tree.markedAttach 0).map (fun r=>r.coeff*F p r)).sum)).sum/2

theorem native_second_low_double_average_congr {S : Type*} {as : List PositiveMass}
    (T : ClockTree S as) (F G : ∀ p : ClockTree.MarkedPlacement T,
      ClockTree.MarkedPlacement p.tree→ℝ)
    (h : ∀ p∈T.markedAttach 0,∀ r∈p.tree.markedAttach 0,F p r=G p r) :
    nativeSecondLowDoubleAverage T F=nativeSecondLowDoubleAverage T G := by
  unfold nativeSecondLowDoubleAverage
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro r hr
  rw [h p hp r hr]

theorem native_second_low_double_average_sub {S : Type*} {as : List PositiveMass}
    (T : ClockTree S as) (F G : ∀ p : ClockTree.MarkedPlacement T,
      ClockTree.MarkedPlacement p.tree→ℝ) (c : ℝ) :
    nativeSecondLowDoubleAverage T (fun p r=>F p r-c*G p r)=
      nativeSecondLowDoubleAverage T F-c*nativeSecondLowDoubleAverage T G := by
  have he (x y z : ℝ) : x*(y-c*z)=x*y-c*(x*z) := by ring
  have hi (p : ClockTree.MarkedPlacement T) :
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*(F p r-c*G p r))).sum=
        ((p.tree.markedAttach 0).map (fun r=>r.coeff*F p r)).sum-
          c*((p.tree.markedAttach 0).map (fun r=>r.coeff*G p r)).sum := by
    simp_rw [he]
    rw [sum_map_sub_explicit,List.sum_map_mul_left]
  unfold nativeSecondLowDoubleAverage
  simp_rw [hi,he]
  rw [sum_map_sub_explicit,List.sum_map_mul_left]
  ring

def nativeSecondLowJointLedger (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (es : List T.Slot) : ℝ :=
  nativeSecondLowDoubleAverage T (fun p r=>
    nativeSecondLowDoubleAverage r.tree (fun s t=>
      t.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
        (nativeSecondLowJointRestTest n U b h K P p r s t) 0*
        fullScalarCutMoment t.tree U K
          (insertedSiteSlots (insertedSiteSlots es p r) s t)))

theorem native_second_low_joint_ledger_eq_scalar_subtraction (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (P : T.cavityLeft.Assignment→ℝ) (es : List T.Slot) :
    nativeSecondLowJointLedger n q U b h K T P es=
      retainedSignedJets n q U b h K [restLowKernel n U b h,restLowKernel n U b h]
        T P es-
      T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q P 0*
        retainedSignedJets n q U b h K [restLowKernel n U 0 K,restLowKernel n U 0 K]
          T (fun _=>1) es := by
  let C:=T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q P 0
  let F:=fun (p : ClockTree.MarkedPlacement T) (r : ClockTree.MarkedPlacement p.tree)=>
    retainedSignedJets n q U b h K [restLowKernel n U b h] r.tree
      (insertedRestTest P (restLowKernel n U b h) p r) (insertedSiteSlots es p r)
  let G:=fun (p : ClockTree.MarkedPlacement T) (r : ClockTree.MarkedPlacement p.tree)=>
    retainedSignedJets n q U b h K [restLowKernel n U 0 K] r.tree
      (insertedRestTest (fun _=>1) (restLowKernel n U 0 K) p r) (insertedSiteSlots es p r)
  have hi (p : ClockTree.MarkedPlacement T) (hp : p∈T.markedAttach 0)
      (r : ClockTree.MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0) :
      nativeSecondLowDoubleAverage r.tree (fun s t=>
        t.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (nativeSecondLowJointRestTest n U b h K P p r s t) 0*
          fullScalarCutMoment t.tree U K
            (insertedSiteSlots (insertedSiteSlots es p r) s t))=F p r-C*G p r := by
    let f:=fun (s : ClockTree.MarkedPlacement r.tree)
      (t : ClockTree.MarkedPlacement s.tree)=>
      t.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
        (insertedRestTest (insertedRestTest P (restLowKernel n U b h) p r)
          (restLowKernel n U b h) s t) 0*
        fullScalarCutMoment t.tree U K (insertedSiteSlots (insertedSiteSlots es p r) s t)
    let g:=fun (s : ClockTree.MarkedPlacement r.tree)
      (t : ClockTree.MarkedPlacement s.tree)=>
      t.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
        (insertedRestTest (insertedRestTest (fun _=>1) (restLowKernel n U 0 K) p r)
          (restLowKernel n U 0 K) s t) 0*
        fullScalarCutMoment t.tree U K (insertedSiteSlots (insertedSiteSlots es p r) s t)
    calc
      _=nativeSecondLowDoubleAverage r.tree (fun s t=>f s t-C*g s t) := by
        apply native_second_low_double_average_congr
        intro s hs t ht
        rw [native_second_low_joint_rest_expectation n q U b h K T ho P p hp r hr s hs t ht]
        dsimp only [f,g,C]
        ring
      _=F p r-C*G p r := by
        rw [native_second_low_double_average_sub]
        rfl
  unfold nativeSecondLowJointLedger
  rw [native_second_low_double_average_congr T _ (fun p r=>F p r-C*G p r) hi,
    native_second_low_double_average_sub]
  rfl

theorem actual_second_low_centered_eq_joint_ledger (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (hq0 : ∀ j i,0≤q j i) (hq : ∀ i,Monotone (fun j=>q j i))
    (hb : ∀ j,0≤b j) (hh : ∀ j,0≤h j) (hK : ∀ j,0≤K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    (hU : U≤as.length) (haz : T.splitIndex a z<U) :
    cutFrozenCenteredJet n q U b h K T P (sitePair T a z) 0 2 0 0=
      nativeSecondLowJointLedger n q U b h K T P [a,z] := by
  rw [actual_second_low_centered_eq_scalar_subtraction n q U b h K T ho P a z
    hq0 hq hb hh hK hbm hhm hKm hU haz,
    native_second_low_joint_ledger_eq_scalar_subtraction n q U b h K T ho P [a,z]]

theorem native_second_low_joint_placement_path (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (hU0 : 0<U) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (hU : U≤as.length) (P : T.cavityLeft.Assignment→ℝ)
    (a z : T.Slot)
    (p : ClockTree.MarkedPlacement T) (r : ClockTree.MarkedPlacement p.tree)
    (s : ClockTree.MarkedPlacement r.tree) (t : ClockTree.MarkedPlacement s.tree) :
    let a':=t.embed (s.embed (r.embed (p.embed a)))
    let z':=t.embed (s.embed (r.embed (p.embed z)))
    let f':=t.embed (s.embed (r.embed p.mark))
    let c':=t.embed (s.embed r.mark)
    let e':=t.embed s.mark
    let d':=t.mark
    (∀ u∈[a',f'],∀ v∈[c',e',z',d'],t.tree.splitIndex u v<U)→
    (∀ u∈[c',e'],∀ v∈[z',d'],t.tree.splitIndex u v<U)→
    t.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
        (nativeSecondLowJointRestTest n U b h K P p r s t) 0*
        fullScalarCutMoment t.tree U K (insertedSiteSlots (insertedSiteSlots [a,z] p r) s t)=
      fullScalarCutGamma t.tree U K a' f'*fullScalarCutGamma t.tree U K c' e'*
        fullScalarCutGamma t.tree U K d' z'*
        t.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (nativeSecondLowJointRestTest n U b h K P p r s t) 0 := by
  dsimp only
  intro hA hD
  change _*fullScalarCutMoment t.tree U K
    [t.embed (s.embed (r.embed (p.embed a))),t.embed (s.embed (r.embed (p.embed z))),
      t.embed (s.embed (r.embed p.mark)),t.embed (s.embed r.mark),t.embed s.mark,t.mark]=_
  rw [fullScalarCutMoment_second_low_path t.tree ho U hU0 hU K _ _ _ _ _ _ hA hD]
  ring

end OAI.SKFluctuations.Cavity
