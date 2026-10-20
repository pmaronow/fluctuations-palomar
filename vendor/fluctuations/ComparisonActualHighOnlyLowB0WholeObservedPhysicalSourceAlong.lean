module

public import ComparisonSignedCavitySecondLowInheritedFreshAffineSource
public import ComparisonSignedCavitySecondLowInheritedActualResidualSavedRate
public import ComparisonSignedCavitySecondLowInheritedWholeObservedSavedRate
public import ComparisonActualHighOnlyLowB0ObservedAffinePhysicalSourceAlong

@[expose] public section
noncomputable section
set_option maxHeartbeats 80000000
set_option linter.unusedVariables false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal ENNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization ActualHighOnlyOverlapMinimum
attribute [local instance] Classical.propDecidable
attribute [local instance] nativeSecondLowSlotFintype
theorem eventually_actual_minimum_inherited_second_low_fresh_low_difference_saved_rate_high_only
    (a : ℕ) (Bclock Temp Cf Cmass Ccal : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcal : 1≤Ccal)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃Cp C : ℝ,0<Cp ∧ 0<C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf → M.xs≤1 →
        M.xs^2≤Ccal^2*laplaceComparisonStrength M.context.d M.lam M.xs →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
          (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
        let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))
        ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
          partitionPoint 0 as (pre.length+mid.length)≤Cmass*W →
        ∀(T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (c b fslot : T.Slot)
          (U : ℕ),0 < mid.length → pre.length+mid.length<U → U≤as.length →
          NativePersistentLowForks pre.length (pre.length+mid.length) U T →
          (T.splitIndex c b=pre.length ∨ T.splitIndex c b=pre.length+mid.length) →
          T.splitIndex c fslot≤pre.length+mid.length →
          W≤M.R (partitionPoint 0 as U) →
          M.R (partitionPoint 0 as (pre.length+mid.length))≤M.R (partitionPoint 0 as U)/2 →
          M.z≤M.R (partitionPoint 0 as U)/2 →
        ∀(G : ActualNaturalBoundaryShape n a T) (forms : Fin a→NativeSourceFactorForm)
          (initial : Finset (Fin a)) (x : ℝ),M.xs≤x → x≤W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e) →
          |nativeSecondLowCanonicalObservedFreshLowDifferenceRow_high_only n a M T (pre.length+mid.length) U c b fslot
            G forms q (nativeSecondLowInheritedSavedMixedClock n M.bf M.hf as)|≤
            (2*(T.leaves:ℝ))*C*(n:ℝ)^(-eta)*(W*M.xs^2*(Cp^a*sourceMonomialScale x W initial)) := by
  obtain ⟨Cp,C,hCp,hC,H⟩:=eventually_actual_minimum_inherited_second_low_observed_affine_saved_rate_high_only
    (D:=D) a Bclock Temp Cf Cmass Ccal hTemp hCf hCmass hCcal
    hm hdelta hroom hgap hcl hcu hAz hC0 hCt
  refine ⟨Cp,C,hCp,hC,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs HS hxs hcompare L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs HS hxs hcompare L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro pre mid tail hcut hmass T c b fslot U hmid hU hlen hT hcb hcf hWU hstar hz
    G forms initial x hxsx hxW hmassG
  rw [native_second_low_canonical_observed_fresh_low_difference_eq_negative_affine_row_high_only n a M T
    (pre.length+mid.length) U c b fslot hU (by omega) G forms,abs_neg]
  exact hk pre mid tail hcut hmass T c b fslot false U hmid hU hlen hT hcb hcf hWU hstar hz
    G forms initial x hxsx hxW hmassG

private theorem low_b0_second_low_residual_weight_abs_le {α : Type} (L : List α)
    (w F : α→ℝ) {B : ℝ} (hF : ∀x∈L,|F x|≤B) :
    |(L.map (fun x=>w x*F x)).sum|≤(L.map (fun x=>|w x|)).sum*B := by
  induction L with
  | nil=>simp
  | cons x L ih=>
    simp only [List.map_cons,List.sum_cons,add_mul]
    exact (abs_add_le _ _).trans (add_le_add
      (by rw [abs_mul];exact mul_le_mul_of_nonneg_left (hF x List.mem_cons_self) (abs_nonneg _))
      (ih (fun y hy=>hF y (List.mem_cons_of_mem _ hy))))

private theorem low_b0_second_low_residual_nonnegative_filtered_sum_le {α : Type} (L : List α)
    (P : α→Bool) (F : α→ℝ) (hF : ∀x∈L,0≤F x) :
    ((L.filter P).map F).sum≤(L.map F).sum := by
  induction L with
  | nil=>simp
  | cons x L ih=>
    have H:=ih (fun y hy=>hF y (List.mem_cons_of_mem x hy))
    cases HP : P x with
    | true=>simpa only [List.filter_cons,HP,ite_true,List.map_cons,List.sum_cons]
        using add_le_add (le_refl (F x)) H
    | false=>
      simp only [List.filter_cons,HP,Bool.false_eq_true,ite_false,List.map_cons,List.sum_cons]
      exact H.trans (le_add_of_nonneg_left (hF x List.mem_cons_self))

private theorem low_b0_second_low_residual_high_attach_variation {S : Type} {as : List PositiveMass}
    (T : ClockTree S as) (ho : MassOrdered 0 as) (c : T.Slot) (U : ℕ)
    {rBound : ℕ} (hT : T.leaves≤rBound) :
    ((nativeHighMarkedRows T c (U-1) 0).attach.map (fun p=>|p.val.coeff|)).sum≤2*(rBound:ℝ) := by
  have HE : ((nativeHighMarkedRows T c (U-1) 0).attach.map (fun p=>|p.val.coeff|)).sum=
      ((nativeHighMarkedRows T c (U-1) 0).map (fun p=>|p.coeff|)).sum := by
    conv_rhs=>rw [←List.attach_map_val]
  rw [HE,nativeHighMarkedRows_eq_filter]
  apply (low_b0_second_low_residual_nonnegative_filtered_sum_le (T.markedAttach 0)
    (fun p=>decide (U-1<p.tree.splitIndex (p.embed c) p.mark)) _
    (fun p _=>abs_nonneg p.coeff)).trans
  rw [T.markedAttach_variation ho,sub_zero]
  exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hT) (by norm_num)

theorem eventually_actual_minimum_inherited_second_low_actual_fresh_residual_saved_rate_high_only
    (degree rBound : ℕ) (Bclock Temp Cf Cmass Ccal : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcal : 1≤Ccal)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0<C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf → M.xs≤1 →
        M.xs^2≤Ccal^2*laplaceComparisonStrength M.context.d M.lam M.xs →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
          (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=nativeSecondLowInheritedSavedMixedClock n M.bf M.hf as
        let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))
        ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
          partitionPoint 0 as (pre.length+mid.length)≤Cmass*W →
        ∀(T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (a v z : T.Slot)
          (U : ℕ),0 < mid.length → pre.length+mid.length<U → U≤as.length →
          T.leaves≤rBound → NativePersistentLowForks pre.length (pre.length+mid.length) U T →
          (T.splitIndex v z=pre.length ∨ T.splitIndex v z=pre.length+mid.length) →
          T.splitIndex a v≤pre.length+mid.length →
          W≤M.R (partitionPoint 0 as U) →
          M.R (partitionPoint 0 as (pre.length+mid.length))≤M.R (partitionPoint 0 as U)/2 →
          M.z≤M.R (partitionPoint 0 as U)/2 →
        ∀(G : ActualNaturalBoundaryShape n degree T) (forms : Fin degree→NativeSourceFactorForm)
          (initial : Finset (Fin degree)) (x : ℝ),M.xs≤x → x≤W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e) →
          let g:=nativeFreshAtSlot T 0 z (pre.length+mid.length)
          |nativeSecondLowCanonicalObservedResidualSource n q U b h K g.tree
            (fun old=>(G.canonicalHighOnlySource M forms).restProduct (g.restRestrict old))
            (g.embed a) (g.embed v) g.mark|≤
            C*(n:ℝ)^(-eta)*(W*M.xs^2*sourceMonomialScale x W initial) := by
  obtain ⟨Cp,C,hCp,hC,H⟩:=eventually_actual_minimum_inherited_second_low_fresh_low_difference_saved_rate_high_only
    (D:=D) degree Bclock Temp Cf Cmass Ccal hTemp hCf hCmass hCcal
    hm hdelta hroom hgap hcl hcu hAz hC0 hCt
  let Cglobal:=(8*((rBound+1:ℕ):ℝ)*(rBound+2)*(rBound+3))*C*Cp^degree
  refine ⟨Cglobal,by dsimp [Cglobal];positivity,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs HS hxs hcompare L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs HS hxs hcompare L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro pre mid tail hcut hmass T a v z U hmid hU hlen hleaves hT hvz hav hWU hstar hz
    G forms initial x hxsx hxW hmassG
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus k
  have hlen' : U≤(pre++(mid++tail)).length:=by simpa only [hcut] using hlen
  let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
    (fun _=>(M.bf (partitionPoint 0 (finiteCutMasses us k) j):ℝ))
    (fun _=>(M.hf (partitionPoint 0 (finiteCutMasses us k) j):ℝ))
  let K:=nativeSecondLowInheritedSavedMixedClock n M.bf M.hf (finiteCutMasses us k)
  let B:=C*(n:ℝ)^(-eta)*(W*M.xs^2*(Cp^degree*sourceMonomialScale x W initial))
  have hB : 0≤B:=by
    have hxpos : 0<x:=M.hxs.trans_le hxsx
    have hWpos : 0<W:=M.hxs.trans_le (le_max_left _ _)
    unfold B sourceMonomialScale
    positivity
  have Hlocal (p : {p // p∈nativeHighMarkedRows T a (U-1) 0})
      (r : {r // r∈nativeHighMarkedRows p.val.tree (p.val.embed v) (U-1) 0}) :
      |nativeSecondLowCanonicalObservedFreshLowDifferenceRow_high_only n degree M r.val.tree (pre.length+mid.length) U
        r.val.mark (r.val.embed (p.val.embed z)) (r.val.embed p.val.mark)
        ((G.retainOnMarked 0 p.val ((mem_nativeHighMarkedRows T a (U-1) 0 p.val).mp p.property).1).retainOnMarked
          0 r.val ((mem_nativeHighMarkedRows p.val.tree (p.val.embed v) (U-1) 0 r.val).mp r.property).1)
        forms q K|≤2*((rBound+2:ℕ):ℝ)*B := by
    obtain ⟨hp,Hp⟩:=(mem_nativeHighMarkedRows T a (U-1) 0 p.val).mp p.property
    obtain ⟨hr,Hr⟩:=(mem_nativeHighMarkedRows p.val.tree (p.val.embed v) (U-1) 0 r.val).mp r.property
    have HpU : U ≤ p.val.tree.splitIndex p.val.mark (p.val.embed a):=by rw [p.val.tree.splitIndex_symm];omega
    have HrU : U ≤ r.val.tree.splitIndex r.val.mark (r.val.embed (p.val.embed v)):=by
      rw [r.val.tree.splitIndex_symm];omega
    have HpT:=hT.observedHigh (by omega) hU 0 p.val hp a HpU
    have HrT:=HpT.observedHigh (by omega) hU 0 r.val hr (p.val.embed v) HrU
    have Hpv : p.val.tree.splitIndex p.val.mark (p.val.embed v)=T.splitIndex a v:=by
      rw [p.val.tree.splitIndex_symm]
      exact (native_second_low_high_mark_low_split T U v a p.val hp (by omega)
        (by rw [T.splitIndex_symm];omega)).trans (T.splitIndex_symm _ _)
    have Hcf : r.val.tree.splitIndex r.val.mark (r.val.embed p.val.mark)=T.splitIndex a v:=by
      rw [r.val.tree.splitIndex_symm,native_second_low_high_mark_low_split p.val.tree U p.val.mark
        (p.val.embed v) r.val hr (by omega) (by rw [Hpv];omega),Hpv]
    have Hvzlow : T.splitIndex v z<U:=by rcases hvz with hvz|hvz <;> omega
    have Hcz : r.val.tree.splitIndex r.val.mark (r.val.embed (p.val.embed z))=T.splitIndex v z:=by
      rw [r.val.tree.splitIndex_symm,native_second_low_high_mark_low_split p.val.tree U (p.val.embed z)
        (p.val.embed v) r.val hr (by omega)]
      · rw [(T.markedAttach_embed_preserves 0 p.val hp).2,T.splitIndex_symm]
      · rw [(T.markedAttach_embed_preserves 0 p.val hp).2,T.splitIndex_symm];exact Hvzlow
    have Hrate:=hk pre mid tail hcut hmass r.val.tree r.val.mark (r.val.embed (p.val.embed z))
      (r.val.embed p.val.mark) U hmid hU hlen HrT (by rw [Hcz];exact hvz) (by rw [Hcf];exact hav)
      hWU hstar hz ((G.retainOnMarked 0 p.val hp).retainOnMarked 0 r.val hr) forms initial x hxsx hxW
      (by intro e;rw [ActualNaturalBoundaryShape.retained_source_mass,ActualNaturalBoundaryShape.retained_source_mass];exact hmassG e)
    have HRleaves : r.val.tree.leaves≤rBound+2:=by
      have HLp:=T.markedAttach_leaves 0 p.val hp
      have HLr:=p.val.tree.markedAttach_leaves 0 r.val hr
      omega
    change |nativeSecondLowCanonicalObservedFreshLowDifferenceRow_high_only n degree M r.val.tree (pre.length+mid.length) U
      r.val.mark (r.val.embed (p.val.embed z)) (r.val.embed p.val.mark)
      ((G.retainOnMarked 0 p.val hp).retainOnMarked 0 r.val hr) forms q K|≤_
    apply Hrate.trans
    have HSCALE:=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr HRleaves) (by norm_num : (0:ℝ)≤2)) hB
    simpa only [B,W,mul_assoc] using HSCALE
  have Hsource:=native_second_low_actual_canonical_fresh_residual_eq_retained_low_difference_source_high_only n degree M T ho
    (pre.length+mid.length) U hU hlen' a v z G forms q K
  simp only [hcut] at Hsource
  rw [Hsource]
  change |nativeSecondLowCanonicalRetainedFreshLowDifferenceHighSource_high_only n degree M T
    (pre.length+mid.length) U a v z G forms q K|≤_
  unfold nativeSecondLowCanonicalRetainedFreshLowDifferenceHighSource_high_only
  let inner:=fun p : {p // p∈nativeHighMarkedRows T a (U-1) 0}=>
    ((nativeHighMarkedRows p.val.tree (p.val.embed v) (U-1) 0).attach.map (fun r=>r.val.coeff*
      nativeSecondLowCanonicalObservedFreshLowDifferenceRow_high_only n degree M r.val.tree (pre.length+mid.length) U
        r.val.mark (r.val.embed (p.val.embed z)) (r.val.embed p.val.mark)
        ((G.retainOnMarked 0 p.val ((mem_nativeHighMarkedRows T a (U-1) 0 p.val).mp p.property).1).retainOnMarked
          0 r.val ((mem_nativeHighMarkedRows p.val.tree (p.val.embed v) (U-1) 0 r.val).mp r.property).1)
        forms q K)).sum
  have Hinner (p : {p // p∈nativeHighMarkedRows T a (U-1) 0}) :
      |inner p|≤(2*((rBound+1:ℕ):ℝ))*(2*((rBound+2:ℕ):ℝ)*B) := by
    have Hp : p.val.tree.leaves≤rBound+1:=
      (T.markedAttach_leaves 0 p.val ((mem_nativeHighMarkedRows T a (U-1) 0 p.val).mp p.property).1).trans
        (Nat.add_le_add_right hleaves 1)
    have HH:=low_b0_second_low_residual_weight_abs_le
      (nativeHighMarkedRows p.val.tree (p.val.embed v) (U-1) 0).attach
      (fun r=>r.val.coeff) _ (fun r _=>Hlocal p r)
    exact HH.trans (mul_le_mul_of_nonneg_right
      (low_b0_second_low_residual_high_attach_variation p.val.tree ho (p.val.embed v) U Hp) (by positivity))
  have Houter:=low_b0_second_low_residual_weight_abs_le (nativeHighMarkedRows T a (U-1) 0).attach
    (fun p=>p.val.coeff) (fun p=>fullScalarCutGamma p.val.tree U K (p.val.embed a) p.val.mark*inner p)
    (fun p _=>by
      rw [abs_mul]
      have HG:=native_full_scalar_cut_moment_abs_le_one p.val.tree ho U K [p.val.embed a,p.val.mark]
      change |fullScalarCutGamma p.val.tree U K (p.val.embed a) p.val.mark|≤1 at HG
      exact (mul_le_mul_of_nonneg_right HG (abs_nonneg _)).trans (by simpa only [one_mul] using Hinner p))
  have HTV:=low_b0_second_low_residual_high_attach_variation T ho a U hleaves
  have Hbound:=Houter.trans (mul_le_mul_of_nonneg_right HTV (by positivity))
  change |((nativeHighMarkedRows T a (U-1) 0).attach.map
    (fun p=>p.val.coeff*fullScalarCutGamma p.val.tree U K (p.val.embed a) p.val.mark*inner p)).sum|≤_
  simp only [←mul_assoc] at Hbound
  apply Hbound.trans
  have HP1 : (rBound:ℝ)≤(rBound+1:ℕ):=by exact_mod_cast Nat.le_succ rBound
  have HP2 : ((rBound+1:ℕ):ℝ)≤(rBound+2:ℕ):=by exact_mod_cast Nat.le_succ (rBound+1)
  have HP3 : ((rBound+2:ℕ):ℝ)≤(rBound+3:ℕ):=by exact_mod_cast Nat.le_succ (rBound+2)
  have Hpoly : 8*(rBound:ℝ)*(rBound+1)*(rBound+2)≤8*((rBound+1:ℕ):ℝ)*(rBound+2)*(rBound+3):=by
    push_cast at HP1 HP2 HP3 ⊢
    nlinarith
  have HE:=mul_le_mul_of_nonneg_right Hpoly hB
  dsimp only [B,Cglobal,W] at HE ⊢
  convert HE using 1 <;> push_cast <;> ring

theorem eventually_actual_minimum_inherited_second_low_whole_observed_saved_rate_high_only
    (degree rBound : ℕ) (Bclock Temp Cf Cmass Ccal : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcal : 1≤Ccal)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0<C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf → M.xs≤1 →
        M.xs^2≤Ccal^2*laplaceComparisonStrength M.context.d M.lam M.xs →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
          (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=nativeSecondLowInheritedSavedMixedClock n M.bf M.hf as
        let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))
        ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
          partitionPoint 0 as (pre.length+mid.length)≤Cmass*W →
        ∀(T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (s : T.Slot) (U : ℕ)
          (hU : U≤(pre++(mid++tail)).length),0 < mid.length → pre.length+mid.length<U →
          T.leaves≤rBound → NativePersistentLowForks pre.length (pre.length+mid.length) U T →
          W≤M.R (partitionPoint 0 as U) →
          M.R (partitionPoint 0 as (pre.length+mid.length))≤M.R (partitionPoint 0 as U)/2 →
          M.z≤M.R (partitionPoint 0 as U)/2 →
        ∀(G : ActualNaturalBoundaryShape n degree T) (forms : Fin degree→NativeSourceFactorForm)
          (initial : Finset (Fin degree)) (x : ℝ),M.xs≤x → x≤W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e) →
          let g:=nativeFreshAtSlot T 0 s (pre.length+mid.length)
          let P:=(G.canonicalHighOnlySource M forms).restProduct
          let Pg:=fun old=>P (g.restRestrict old)
          let χ:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
          |(∑j : Fin 8,nativeSecondLowClassLedger n q U b h K g.tree hU Pg (g.embed s) g.mark j true/2)-
            χ^2*nativeSecondLowFreshOccupiedUnweightedCSource n q U b h K T s (pre.length+mid.length) hU P|≤
            C*(n:ℝ)^(-eta)*(W*M.xs^2*sourceMonomialScale x W initial) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_second_low_actual_fresh_residual_saved_rate_high_only
    (D:=D) degree rBound Bclock Temp Cf Cmass Ccal hTemp hCf hCmass hCcal
    hm hdelta hroom hgap hcl hcu hAz hC0 hCt
  refine ⟨((rBound+1:ℕ):ℝ)*C,mul_pos (by positivity) hC,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs HS hxs hcompare L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs HS hxs hcompare L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro pre mid tail hcut hmass T s U hU hmid hstar hleaves hT hWU hRstar hz
    G forms initial x hxsx hxW hmassG
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus k
  have hlen : U≤(finiteCutMasses us k).length:=by simpa only [hcut] using hU
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
    (fun _=>(M.bf (partitionPoint 0 (finiteCutMasses us k) j):ℝ))
    (fun _=>(M.hf (partitionPoint 0 (finiteCutMasses us k) j):ℝ))
  let b:=fun j=>(M.bf (partitionPoint 0 (finiteCutMasses us k) j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 (finiteCutMasses us k) j):ℝ)
  let K:=nativeSecondLowInheritedSavedMixedClock n M.bf M.hf (finiteCutMasses us k)
  let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))
  let P:=(G.canonicalHighOnlySource M forms).restProduct
  let χ:=(scalarTerminal.schedule (scalarBoundaryClocks (finiteCutMasses us k) (relocatedClock U 0 K))).H 0 0
  let A:=C*(n:ℝ)^(-eta)*(W*M.xs^2*sourceMonomialScale x W initial)
  have hA : 0≤A:=by
    have hxpos : 0<x:=M.hxs.trans_le hxsx
    have hWpos : 0<W:=M.hxs.trans_le (le_max_left _ _)
    unfold A sourceMonomialScale
    positivity
  have Hpoint (B : NativeSecondLowFreshOccupiedMiddleBlock T s (pre.length+mid.length) U hU) :
      |nativeSecondLowCanonicalObservedResidualSource n q U b h K
        (nativeFreshAtSlot T 0 s (pre.length+mid.length)).tree
        (fun old=>P ((nativeFreshAtSlot T 0 s (pre.length+mid.length)).restRestrict old))
        ((nativeFreshAtSlot T 0 s (pre.length+mid.length)).embed s)
        (nativeSecondLowOccupiedBlockRepresentative (nativeFreshAtSlot T 0 s (pre.length+mid.length)).tree U hU B.val)
        (nativeFreshAtSlot T 0 s (pre.length+mid.length)).mark|≤A := by
    have Hfork:=native_second_low_fresh_occupied_old_slot_low_forks T s pre.length (pre.length+mid.length) U hU
      (by omega) hT B
    dsimp only at Hfork
    have Hrate:=hk pre mid tail hcut hmass T s
      (nativeSecondLowFreshOccupiedOldSlot T s (pre.length+mid.length) U hU B) s U hmid hstar hlen
      hleaves hT Hfork.1 Hfork.2 hWU hRstar hz G forms initial x hxsx hxW hmassG
    rw [←native_second_low_fresh_occupied_old_slot_exact T s (pre.length+mid.length) U hU B] at Hrate
    exact Hrate
  have Hgroup : |nativeSecondLowFreshOccupiedResidualSource n q U b h K T s (pre.length+mid.length) hU P|≤
      ((rBound+1:ℕ):ℝ)*A := by
    unfold nativeSecondLowFreshOccupiedResidualSource
    dsimp only
    calc
      _≤∑B : NativeSecondLowFreshOccupiedMiddleBlock T s (pre.length+mid.length) U hU,
        |nativeSecondLowCanonicalObservedResidualSource n q U b h K
          (nativeFreshAtSlot T 0 s (pre.length+mid.length)).tree
          (fun old=>P ((nativeFreshAtSlot T 0 s (pre.length+mid.length)).restRestrict old))
          ((nativeFreshAtSlot T 0 s (pre.length+mid.length)).embed s)
          (nativeSecondLowOccupiedBlockRepresentative (nativeFreshAtSlot T 0 s (pre.length+mid.length)).tree U hU B.val)
          (nativeFreshAtSlot T 0 s (pre.length+mid.length)).mark|:=Finset.abs_sum_le_sum_abs _ _
      _≤∑_B : NativeSecondLowFreshOccupiedMiddleBlock T s (pre.length+mid.length) U hU,A:=
        Finset.sum_le_sum (fun B _=>Hpoint B)
      _=(Fintype.card (NativeSecondLowFreshOccupiedMiddleBlock T s (pre.length+mid.length) U hU):ℝ)*A:=by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      _≤((rBound+1:ℕ):ℝ)*A:=by
        apply mul_le_mul_of_nonneg_right _ hA
        exact Nat.cast_le.mpr ((native_second_low_fresh_occupied_middle_block_count T s (pre.length+mid.length) U hU).trans
          (hleaves.trans (Nat.le_succ rBound)))
  have Hchi : |χ|≤1:=native_second_low_original_chi_abs_le_one (finiteCutMasses_ordered us hus k) U K
  have Hsaved : |χ*nativeSecondLowFreshOccupiedResidualSource n q U b h K T s (pre.length+mid.length) hU P|≤
      ((rBound+1:ℕ):ℝ)*A := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right Hchi (abs_nonneg _)).trans (by simpa only [one_mul] using Hgroup)
  have Hwhole:=native_second_low_actual_fresh_observed_half_eq_grouped_unweighted_add_residual n q U
    (pre.length+mid.length) b h K T ho s hstar hU P
  dsimp only at Hwhole
  simp only [hcut] at Hwhole
  rw [Hwhole]
  change |χ^2*nativeSecondLowFreshOccupiedUnweightedCSource n q U b h K T s (pre.length+mid.length) hU P+
    χ*nativeSecondLowFreshOccupiedResidualSource n q U b h K T s (pre.length+mid.length) hU P-
    χ^2*nativeSecondLowFreshOccupiedUnweightedCSource n q U b h K T s (pre.length+mid.length) hU P|≤_
  rw [add_sub_cancel_left]
  simpa only [A,W,mul_assoc] using Hsaved

end OAI.SKFluctuations.Cavity
