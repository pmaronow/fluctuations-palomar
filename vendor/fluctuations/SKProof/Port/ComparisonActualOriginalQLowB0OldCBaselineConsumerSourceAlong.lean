module

public import ComparisonSignedCavitySecondLowActualOldCBaselinePointBudgetAlong
public import ComparisonSignedCavitySecondLowActualOccupiedOldCBaselineBudgetAlong
public import SKProof.Port.ComparisonActualOriginalQLowB0InitialPhysicalConsumerSourceAlong
public import SKProof.Port.ComparisonActualOriginalQLowB0StarUnobservedCompatibleSourceAlong

@[expose] public section
noncomputable section
set_option maxHeartbeats 600000
set_option linter.unusedVariables false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal ENNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization ActualThetaZeroOverlapMinimum
open NativeOverlapMinimum (ActualSlowWindowChoice)
attribute [local instance] Classical.propDecidable
attribute [local instance] nativeSecondLowSlotFintype
theorem actual_second_low_old_c_baseline_point_budget_along_original_q
    {m delta cl cu Az C0 Ct D Bclock Temp Cf Tstar Lwin Cs : ℝ}
    (degree rBound : ℕ) (Cmass Ccut Couter : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCm : 0≤Cmass) (hCcut : 0≤Ccut) (hCouter : 0≤Couter)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (hWlim : Tendsto W atTop (𝓝 0)) (w : ℕ→ActualSlowWindowChoice)
    (HS : ∀ᶠn in atTop,ActualOriginalQSmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow_original_q (M n) (W n) Tstar Lwin Cs (w n)) :
    ∃C : ℝ,0<C ∧ ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val≤1)→(w n).star∈us→
      (∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹≤(M n).xs→
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        let b:=fun j=>((M n).sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>((M n).sweepHf (partitionPoint 0 as j):ℝ)
        let K:=fun j=>h j+b j*orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf (partitionPoint 0 as j)
        let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(i V U : ℕ) (T : ClockTree (Spin (dim n)×Bool) as),
          U≤as.length→i<V→V ≤ star→star<U→T.leaves≤rBound→
          partitionPoint 0 as V≤Ccut*(M n).xs→partitionPoint 0 as U≤Couter*W n→
        ∀(G : ActualNaturalBoundaryShape (dim n) degree T) (forms : Fin degree→NativeSourceFactorForm)
          (initial : Finset (Fin degree)) (x : ℝ),(M n).xs≤x→x≤W n→
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x (W n) initial e)→
        ∀(f c z : T.Slot),f≠z→
          ((T.splitIndex f c=i ∧ T.splitIndex c z=i) ∨
            (T.splitIndex f c=star ∧ T.splitIndex c z=star))→
          let p0:=sourceMonomialScale x (W n) initial
          let d:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
            (nativeOriginalCutLowErrorRadius (dim n) (M n).sweepBf (M n).sweepHf as i+1/(dim n+1:ℕ))
          |T.cavityLeft.disorderExpect (restWeight (dim n)) (restFeature (dim n)) 0 q
            (nativeSecondLowUnweightedCOldPayload (dim n) U b h K T f c z
              (G.canonicalOriginalQSource (M n) forms).restProduct) 0|≤
            C*(M n).xs*d*p0+
            2*((dim n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/32))*(M n).xs^2*p0 := by
  obtain ⟨Craw,hCraw,Hraw⟩:=eventually_actual_minimum_inherited_second_low_old_c_error_atom_budget_original_q
    (D:=D) degree rBound Bclock Temp Cf Cmass hTemp hCf hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  have Hstar:=actual_second_low_star_error_atom_saving_along_original_q degree rBound Cmass Couter 1
    hTemp hCf hCm hCouter zero_le_one hm hdelta hroom hcl hcu hAz hC0 hCt
    dim hdim M W hcanonical hWlim w HS Hcutoff hw
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  refine ⟨2*Craw*(1+Ccut),by positivity,?_⟩
  filter_upwards [hdim.eventually Hraw,Hstar,HS,HW1,Hcutoff] with n hnRaw hnStar hnHS hnW hnCutoff
  have hxsW:(M n).xs≤W n:=(M n).canonical_direct_test_band_ge_scale.trans_eq (hcanonical n).symm
  intro L us hus hstar hret hmesh
  filter_upwards [hnRaw (M n) hnCutoff.1 hnCutoff.2 hnHS (hxsW.trans hnW) L us hus hret hmesh,
    hnStar L us hus hstar hret hmesh] with jGrid hgridRaw hgridStar
  dsimp only at hgridRaw hgridStar ⊢
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let b:=fun j=>((M n).sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>((M n).sweepHf (partitionPoint 0 as j):ℝ)
  let K:=fun j=>h j+b j*orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf (partitionPoint 0 as j)
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  intro i V U T hU hiV hVstar hstarU hT hcut houter G forms initial x hxsx hxW hmass f c z Hfz Hcuts
  let p0:=sourceMonomialScale x (W n) initial
  let d:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
    (nativeOriginalCutLowErrorRadius (dim n) (M n).sweepBf (M n).sweepHf as i+1/(dim n+1:ℕ))
  let rate:=((dim n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/32))*(M n).xs^2*p0
  have hp0:0≤p0:=by
    dsimp [p0]
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>
      (source_factor_scale_pos ((M n).hxs.trans_le hxsx) ((M n).hxs.trans_le hxsW) initial e).le
  have hd:0≤d:=mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp)
    (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hrate:0≤rate:=by dsimp [rate];positivity
  have ho:MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  rw [native_second_low_old_c_baseline_expect_eq_error_atoms (dim n) q U b h K T ho]
  apply (abs_add_le _ _).trans
  rcases Hcuts with ⟨Hfc,Hcz⟩|⟨Hfc,Hcz⟩
  · have Hfi:T.splitIndex f c<U:=Hfc ▸ lt_of_lt_of_le hiV (hVstar.trans hstarU.le)
    have Hci:T.splitIndex c z<U:=Hcz ▸ lt_of_lt_of_le hiV (hVstar.trans hstarU.le)
    have B1:=hgridRaw U T hU hT G forms initial x (W n) hxsx hxW hmass f c z Hfi Hci Hfz true
    have B2:=hgridRaw U T hU hT G forms initial x (W n) hxsx hxW hmass f c z Hfi Hci Hfz false
    simp only [ite_true,Bool.false_eq_true,ite_false,Hfc,Hcz] at B1 B2
    have Hmass:partitionPoint 0 as i≤Ccut*(M n).xs:=
      (partitionPoint_mono as ho hiV.le).trans hcut
    have Hsum:2*(Craw*d*((M n).xs+partitionPoint 0 as i)*p0)≤2*Craw*(1+Ccut)*(M n).xs*d*p0:=by
      have H:=mul_le_mul_of_nonneg_left (add_le_add_left Hmass (M n).xs)
        (mul_nonneg (mul_nonneg hCraw.le hd) hp0)
      convert mul_le_mul_of_nonneg_left H (by norm_num : (0:ℝ)≤2) using 1 <;> ring
    apply (add_le_add B1 B2).trans
    change Craw*d*((M n).xs+partitionPoint 0 as i)*p0+Craw*d*((M n).xs+partitionPoint 0 as i)*p0≤_
    linarith only [Hsum,hrate]
  · have Hfs:T.splitIndex f c<U:=Hfc ▸ hstarU
    have Hcs:T.splitIndex c z<U:=Hcz ▸ hstarU
    have Hfn:f≠c:=native_second_low_low_slots_ne T U hU f c Hfs
    have Hcn:c≠z:=native_second_low_low_slots_ne T U hU c z Hcs
    have hzero:(0:ℝ)∈Icc (0:ℝ) 1:=⟨le_rfl,zero_le_one⟩
    have hone:(1:ℝ)∈Icc (0:ℝ) 1:=⟨zero_le_one,le_rfl⟩
    have B1:=hgridStar U T 0 0 hU hstarU houter hzero hzero hT G forms initial x hxsx hxW hmass
      f c c z f z 1 Hfc Hcs Hcn Hfz hone
    have B2:=hgridStar U T 0 0 hU hstarU houter hzero hzero hT G forms initial x hxsx hxW hmass
      c z f c f z 0 Hcz Hfs Hfn Hfz hzero
    simp only [one_mul] at B1 B2
    have hx:0 < (M n).xs:=(M n).hxs
    have Hinitial:0≤2*Craw*(1+Ccut)*(M n).xs*d*p0:=by positivity
    apply (add_le_add B1 B2).trans
    change rate+rate≤_
    linarith only [Hinitial]

private theorem low_b0_initial_old_c_weight_abs_le {α : Type} (L : List α) (w F : α→ℝ)
    {B : ℝ} (H : ∀x∈L,|F x|≤B) :
    |(L.map (fun x=>w x*F x)).sum|≤(L.map (fun x=>|w x|)).sum*B := by
  induction L with
  | nil=>simp
  | cons x L ih=>
    simp only [List.map_cons,List.sum_cons,add_mul]
    exact (abs_add_le _ _).trans (add_le_add
      (by rw [abs_mul];exact mul_le_mul_of_nonneg_left (H x List.mem_cons_self) (abs_nonneg _))
      (ih (fun y hy=>H y (List.mem_cons_of_mem _ hy))))

private theorem low_b0_initial_old_c_filtered_nonneg_sum_le {α : Type} (L : List α) (P : α→Bool)
    (F : α→ℝ) (H : ∀x∈L,0≤F x) :
    ((L.filter P).map F).sum≤(L.map F).sum := by
  induction L with
  | nil=>simp
  | cons x L ih=>
    have HH:=ih (fun y hy=>H y (List.mem_cons_of_mem x hy))
    cases HP : P x with
    | true=>simpa only [List.filter_cons,HP,ite_true,List.map_cons,List.sum_cons]
        using add_le_add (le_refl (F x)) HH
    | false=>
      simp only [List.filter_cons,HP,Bool.false_eq_true,ite_false,List.map_cons,List.sum_cons]
      exact HH.trans (le_add_of_nonneg_left (H x List.mem_cons_self))

private theorem low_b0_initial_old_c_HIGH_variation {S : Type} {as : List PositiveMass}
    (T : ClockTree S as) (ho : MassOrdered 0 as) (a : T.Slot) (U rBound : ℕ) (hT : T.leaves≤rBound) :
    ((nativeHighMarkedRows T a (U-1) 0).map (fun p=>|p.coeff|)).sum≤2*(rBound:ℝ) := by
  rw [nativeHighMarkedRows_eq_filter]
  apply (low_b0_initial_old_c_filtered_nonneg_sum_le (T.markedAttach 0)
    (fun p=>decide (U-1<p.tree.splitIndex (p.embed a) p.mark)) _ (fun p _=>abs_nonneg p.coeff)).trans
  rw [T.markedAttach_variation ho,sub_zero]
  exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hT) (by norm_num)

theorem actual_second_low_occupied_old_c_baseline_budget_along_original_q
    {m delta cl cu Az C0 Ct D Bclock Temp Cf Tstar Lwin Cs : ℝ}
    (degree rBound : ℕ) (Cmass Ccut Couter : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCm : 0≤Cmass) (hCcut : 0≤Ccut) (hCouter : 0≤Couter)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (hWlim : Tendsto W atTop (𝓝 0)) (w : ℕ→ActualSlowWindowChoice)
    (HS : ∀ᶠn in atTop,ActualOriginalQSmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow_original_q (M n) (W n) Tstar Lwin Cs (w n)) :
    ∃Ci Cstar : ℝ,0<Ci ∧ 0<Cstar ∧ ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val≤1)→(w n).star∈us→
      (∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹≤(M n).xs→
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        let b:=fun j=>((M n).sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>((M n).sweepHf (partitionPoint 0 as j):ℝ)
        let K:=fun j=>h j+b j*orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf (partitionPoint 0 as j)
        let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(i V U : ℕ) (T : ClockTree (Spin (dim n)×Bool) as) (hU : U≤as.length),
          i<V→V ≤ star→star<U→T.leaves≤rBound→NativePersistentLowForks i star U T→
          partitionPoint 0 as V≤Ccut*(M n).xs→partitionPoint 0 as U≤Couter*W n→
        ∀(G : ActualNaturalBoundaryShape (dim n) degree T) (forms : Fin degree→NativeSourceFactorForm)
          (initial : Finset (Fin degree)) (x : ℝ),(M n).xs≤x→x≤W n→
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x (W n) initial e)→∀s:T.Slot,
          let p0:=sourceMonomialScale x (W n) initial
          let d:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
            (nativeOriginalCutLowErrorRadius (dim n) (M n).sweepBf (M n).sweepHf as i+1/(dim n+1:ℕ))
          |nativeSecondLowFreshOccupiedOldCBaselineSource (dim n) q U b h K T s star hU
            (G.canonicalOriginalQSource (M n) forms).restProduct|≤
            Ci*partitionPoint 0 as U*(M n).xs*d*p0+
            Cstar*((dim n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/32))*W n*(M n).xs^2*p0 := by
  obtain ⟨C,hC,H⟩:=actual_second_low_old_c_baseline_point_budget_along_original_q degree (rBound+2) Cmass Ccut Couter
    hTemp hCf hCm hCcut hCouter hm hdelta hroom hcl hcu hAz hC0 hCt
    dim hdim M W hcanonical hWlim w HS Hcutoff hw
  let Poly:ℝ:=2*(rBound+1)^2
  have hPoly:0<Poly:=by dsimp [Poly];positivity
  refine ⟨Poly*C,2*Poly*(1+Couter),mul_pos hPoly hC,by positivity,?_⟩
  filter_upwards [H] with n hn
  intro L us hus hstar hret hmesh
  filter_upwards [hn L us hus hstar hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let b:=fun j=>((M n).sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>((M n).sweepHf (partitionPoint 0 as j):ℝ)
  let K:=fun j=>h j+b j*orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf (partitionPoint 0 as j)
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  intro i V U T hU hiV hVstar hstarU hT hpersistent hcut houter G forms initial x hxsx hxW hmass s
  let g:=nativeFreshAtSlot T 0 s star
  have hgMem:g∈T.markedAttach 0:=nativeFreshAtSlot_mem T 0 s star
  let Gg:=G.retainOnMarked 0 g hgMem
  let P:=(G.canonicalOriginalQSource (M n) forms).restProduct
  let Pg:=fun old=>P (g.restRestrict old)
  have hgLeaves:g.tree.leaves≤rBound+1:=
    (T.markedAttach_leaves 0 g hgMem).trans (Nat.add_le_add_right hT 1)
  let p0:=sourceMonomialScale x (W n) initial
  let d:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
    (nativeOriginalCutLowErrorRadius (dim n) (M n).sweepBf (M n).sweepHf as i+1/(dim n+1:ℕ))
  let rate:=((dim n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/32))*(M n).xs^2*p0
  let B:=C*(M n).xs*d*p0+2*rate
  have hW:0<W n:=(M n).hxs.trans_le (hxsx.trans hxW)
  have hp0:0≤p0:=by
    dsimp [p0]
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>
      (source_factor_scale_pos ((M n).hxs.trans_le hxsx) hW initial e).le
  have hd:0≤d:=mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp)
    (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hrate:0≤rate:=by dsimp [rate];positivity
  have hx:0 < (M n).xs:=(M n).hxs
  have hB:0≤B:=by dsimp [B];positivity
  have ho:MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hUmas:0≤partitionPoint 0 as U:=(partitionPoint_mem as ho U).1
  have Hpoint (block : NativeSecondLowFreshOccupiedMiddleBlock T s star U hU)
      (p : MarkedPlacement g.tree) (hp : p∈nativeHighMarkedRows g.tree (g.embed s) (U-1) 0) :
      |p.tree.cavityLeft.disorderExpect (restWeight (dim n)) (restFeature (dim n)) 0 q
        (nativeSecondLowUnweightedCOldPayload (dim n) U b h K p.tree p.mark
          (p.embed (nativeSecondLowOccupiedBlockRepresentative g.tree U hU block.val)) (p.embed g.mark)
          (fun old=>Pg (p.restRestrict old))) 0|≤B := by
    have hpMem:=((mem_nativeHighMarkedRows g.tree (g.embed s) (U-1) 0 p).mp hp).1
    let Gp:=Gg.retainOnMarked 0 p hpMem
    have hpLeaves:p.tree.leaves≤rBound+2:=
      (g.tree.markedAttach_leaves 0 p hpMem).trans (by omega)
    have HP:(Gp.canonicalOriginalQSource (M n) forms).restProduct=(fun old=>Pg (p.restRestrict old)):=by
      funext τ
      exact (Gg.retained_canonical_restProduct_original_q (M n) forms 0 p hpMem τ).trans
        (G.retained_canonical_restProduct_original_q (M n) forms 0 g hgMem (p.restRestrict τ))
    have Hmass:∀e,Gp.sourceLowMass e≤Cmass*sourceFactorScale x (W n) initial e:=by
      intro e
      rw [ActualNaturalBoundaryShape.retained_source_mass,ActualNaturalBoundaryShape.retained_source_mass]
      exact hmass e
    have Hcuts:=native_second_low_fresh_occupied_old_c_equal_LOW_cuts T s i star U hU
      (hiV.le.trans hVstar) hstarU hpersistent block p hp
    have Hfz:p.mark≠p.embed g.mark:=native_second_low_low_slots_ne p.tree U hU _ _
      ((native_second_low_fresh_HIGH_mark_tooth_split_eq_star T s star U hU hstarU p hp).trans_lt hstarU)
    have HH:=hgrid i V U p.tree hU hiV hVstar hstarU hpLeaves hcut houter Gp forms initial x
      hxsx hxW Hmass p.mark (p.embed (nativeSecondLowOccupiedBlockRepresentative g.tree U hU block.val))
      (p.embed g.mark) Hfz Hcuts
    rw [HP] at HH
    simpa only [B,rate,p0,d,q,b,h,K,as,mul_assoc] using HH
  have Hblock (block : NativeSecondLowFreshOccupiedMiddleBlock T s star U hU) :
      |nativeSecondLowCanonicalOldCBaselineSource (dim n) q U b h K g.tree Pg
        (g.embed s) (nativeSecondLowOccupiedBlockRepresentative g.tree U hU block.val) g.mark|≤
        2*(rBound+1)*partitionPoint 0 as U*B := by
    unfold nativeSecondLowCanonicalOldCBaselineSource
    have Hnorm (p : MarkedPlacement g.tree) (hp : p∈nativeHighMarkedRows g.tree (g.embed s) (U-1) 0) :
        |fullScalarCutGamma p.tree U K (p.embed (g.embed s)) p.mark*partitionPoint 0 as U*
          p.tree.cavityLeft.disorderExpect (restWeight (dim n)) (restFeature (dim n)) 0 q
            (nativeSecondLowUnweightedCOldPayload (dim n) U b h K p.tree p.mark
              (p.embed (nativeSecondLowOccupiedBlockRepresentative g.tree U hU block.val)) (p.embed g.mark)
              (fun old=>Pg (p.restRestrict old))) 0|≤partitionPoint 0 as U*B := by
      rw [abs_mul,abs_mul,abs_of_nonneg hUmas]
      have HG:=native_full_scalar_cut_moment_abs_le_one p.tree ho U K [p.embed (g.embed s),p.mark]
      change |fullScalarCutGamma p.tree U K (p.embed (g.embed s)) p.mark|≤1 at HG
      apply (mul_le_mul (mul_le_mul_of_nonneg_right HG hUmas) (Hpoint block p hp)
        (abs_nonneg _) (mul_nonneg zero_le_one hUmas)).trans_eq
      ring
    have HH:=low_b0_initial_old_c_weight_abs_le (nativeHighMarkedRows g.tree (g.embed s) (U-1) 0)
      (fun p=>p.coeff) _ Hnorm
    simp_rw [mul_assoc] at HH ⊢
    apply HH.trans
    convert mul_le_mul_of_nonneg_right (low_b0_initial_old_c_HIGH_variation g.tree ho (g.embed s) U (rBound+1) hgLeaves)
      (mul_nonneg hUmas hB) using 1; push_cast; ring
  unfold nativeSecondLowFreshOccupiedOldCBaselineSource
  dsimp only
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply (Finset.sum_le_sum (fun block _=>Hblock block)).trans
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have Hcount:=native_second_low_fresh_occupied_middle_block_count T s star U hU
  have HcountR:(Fintype.card (NativeSecondLowFreshOccupiedMiddleBlock T s star U hU):ℝ)≤rBound:=
    Nat.cast_le.mpr (Hcount.trans hT)
  have Hpoly:(Fintype.card (NativeSecondLowFreshOccupiedMiddleBlock T s star U hU):ℝ)*
      (2*(rBound+1))≤Poly:=by
    dsimp [Poly]
    have Hr:0≤(rBound:ℝ):=Nat.cast_nonneg _
    nlinarith only [HcountR,Hr]
  have Htotal:=mul_le_mul_of_nonneg_right Hpoly (mul_nonneg hUmas hB)
  have Hstar:Poly*partitionPoint 0 as U*(2*rate)≤2*Poly*(1+Couter)*W n*rate:=by
    have HH:=mul_le_mul_of_nonneg_left houter (mul_nonneg hPoly.le hrate)
    have HC:=mul_nonneg (mul_nonneg hPoly.le hW.le) hrate
    nlinarith only [HH,HC]
  have Hstep:(Fintype.card (NativeSecondLowFreshOccupiedMiddleBlock T s star U hU):ℝ)*
      (2*(rBound+1)*partitionPoint 0 as U*B)≤Poly*partitionPoint 0 as U*B:=by
    convert Htotal using 1 <;> ring
  apply Hstep.trans
  dsimp only [B]
  have HE:Poly*partitionPoint 0 as U*(C*(M n).xs*d*p0+2*rate)=
      (Poly*C)*partitionPoint 0 as U*(M n).xs*d*p0+Poly*partitionPoint 0 as U*(2*rate):=by ring
  rw [HE]
  apply add_le_add le_rfl
  convert Hstar using 1; dsimp [rate]; ring

end OAI.SKFluctuations.Cavity
