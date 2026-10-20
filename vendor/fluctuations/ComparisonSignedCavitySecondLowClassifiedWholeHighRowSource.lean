module

public import ComparisonSignedCavitySecondLowClassifiedHighJointRowLaw

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

theorem native_star_arm_classification_with_whole_retained_clone_and_high_rows
    (mid tail : List PositiveMass) (T : ClockTree S (mid++tail)) (s : T.Slot) {U : ℕ}
    (hmid : 0 < mid.length) (hU : mid.length < U)
    (hT : NativePersistentLowForks 0 mid.length U T)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a (mid++tail)) :
    ∃(E : ClockTree S (mid++tail)) (D : ClockTree S tail)
      (R : E.Assignment→D.Assignment→T.Assignment) (target : D.Slot) (embedD : D.Slot→T.Slot),
      NativePersistentLowForks 0 mid.length U E ∧
      (∀η δ,T.atSlot (R η δ) s=D.atSlot δ target) ∧
      (∀c,T.splitIndex s c=0 → ∃e : E.Slot,∀η δ,T.atSlot (R η δ) c=E.atSlot η e) ∧
      (∀c,mid.length ≤ T.splitIndex s c → ∃d : D.Slot,
        (∀η δ,T.atSlot (R η δ) c=D.atSlot δ d) ∧
        mid.length+D.splitIndex target d=T.splitIndex s c) ∧
      embedD target=s ∧ Function.Injective embedD ∧
      (∀η δ d,T.atSlot (R η δ) (embedD d)=D.atSlot δ d) ∧
      (∀d e,T.splitIndex (embedD d) (embedD e)=mid.length+D.splitIndex d e) ∧
      (∀(q : ℕ→ι→ℝ≥0) (Q : T.Assignment→ℝ) (x : ι→ℝ),
        T.expect w φ q Q x=(E.fork (exteriorPrepend mid D)).expect w φ q
          (fun σ=>Q (R σ.1 (exteriorPrependAssignmentEquiv mid D σ.2))) x) ∧
      (∀(d : D.Slot) (cut : ℕ),mid.length < cut →
        ∀(q : ℕ→ι→ℝ≥0) (Q : T.Assignment→T.Assignment→ℝ) (x : ι→ℝ),
          nativeRetainedCloneCutMean w φ T (embedD d) cut q Q x=
            nativeRetainedCloneCutMean w φ (E.fork (exteriorPrepend mid D))
              (.inr ((exteriorPrependSlotEquiv mid D).symm d)) cut q
              (fun σ σ'=>Q (R σ.1 (exteriorPrependAssignmentEquiv mid D σ.2))
                (R σ'.1 (exteriorPrependAssignmentEquiv mid D σ'.2))) x) ∧
      (∀(d : D.Slot) (cut : ℕ),mid.length < cut →
        ∀(a : ℝ) (q : ℕ→ι→ℝ≥0) (H : T.Assignment→S→ℝ) (x : ι→ℝ),
          nativeJointAttachmentRow w φ q (nativeHighMarkedRows T (embedD d) (cut-1) a) H x=
            nativeJointAttachmentRow w φ q
              (nativeHighMarkedRows (E.fork (exteriorPrepend mid D))
                (.inr ((exteriorPrependSlotEquiv mid D).symm d)) (cut-1) a)
              (fun σ new=>H (R σ.1 (exteriorPrependAssignmentEquiv mid D σ.2)) new) x) := by
  have Hmiddle:=native_group_occupied_shares_middle mid T s hU hT
  have hE:=nativeGroupRootForest_exterior_lowForks T s hT
  have hLaw:=fun q Q x=>nativeGroupRootForest_expect T s hw φ ho q Q x
  have hTarget:=fun η δ=>(nativeGroupRootForest T s).read_target η δ
  have hHigh:=fun c hc=>(nativeGroupRootForest T s).read_high_relative c hc
  have has : mid++tail≠[]:=by
    intro H
    have HM:=congrArg List.length (List.append_eq_nil_iff.mp H).1
    simp only [List.length_nil] at HM
    omega
  have hOutside:=fun c hc=>(nativeGroupRootForest T s).read_exterior_relative has c hc
  have hClone:=fun d cut hc q Q x=>native_group_root_forest_retained_clone_all_occupied
    T s d cut hc hw φ ho q Q x
  have hRow:=fun d cut a q H x=>native_group_root_forest_high_joint_rows T s d cut a hw φ ho q H x
  generalize hg:nativeGroupRootForest T s=g at Hmiddle hE hLaw hTarget hHigh hOutside hClone hRow
  rcases g with ⟨E,Di,ti,readi,ei,oi,hti,hoi,hri,hsi,hio,hfree⟩
  obtain ⟨D,hD⟩:=native_exists_prepend_of_trunk_split mid Di ti Hmiddle
  subst Di
  let target:=exteriorPrependSlotEquiv mid D ti
  let R:=fun η δ=>readi η ((exteriorPrependAssignmentEquiv mid D).symm δ)
  let embedD:=fun d=>oi ((exteriorPrependSlotEquiv mid D).symm d)
  refine ⟨E,D,R,target,embedD,hE,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro η δ
    rw [hTarget,exteriorPrepend_atSlot]
    simp only [Equiv.apply_symm_apply]
    rfl
  · intro c hc
    obtain ⟨e,he⟩:=hOutside c hc
    exact ⟨e,fun η δ=>he η _⟩
  · intro c hc
    obtain ⟨d,hr,hs⟩:=hHigh c (by omega)
    refine ⟨exteriorPrependSlotEquiv mid D d,?_,?_⟩
    · intro η δ
      rw [hr,exteriorPrepend_atSlot]
      simp only [Equiv.apply_symm_apply]
    · simpa only [exteriorPrepend_splitIndex] using hs
  · dsimp only [embedD,target]
    rw [Equiv.symm_apply_apply]
    exact hti
  · intro d e H
    have HH:=congrArg ei H
    dsimp only [embedD] at HH
    rw [hoi,hoi] at HH
    exact (exteriorPrependSlotEquiv mid D).symm.injective (Sum.inr.inj HH)
  · intro η δ d
    dsimp only [R,embedD]
    rw [hri,hoi]
    change (exteriorPrepend mid D).atSlot ((exteriorPrependAssignmentEquiv mid D).symm δ)
      ((exteriorPrependSlotEquiv mid D).symm d)=D.atSlot δ d
    rw [exteriorPrepend_atSlot]
    simp only [Equiv.apply_symm_apply]
  · intro d e
    dsimp only [embedD]
    rw [hio,exteriorPrepend_splitIndex]
    simp only [Equiv.apply_symm_apply]
  · intro q Q x
    simpa only [R,Equiv.symm_apply_apply] using hLaw q Q x
  · intro d cut hc q Q x
    have HC:=hClone ((exteriorPrependSlotEquiv mid D).symm d) cut (by omega) q Q x
    obtain ⟨j,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : cut≠0)
    change _=E.expect w φ q (fun η=>nativeRetainedCloneCutMean w φ (exteriorPrepend mid D)
      ((exteriorPrependSlotEquiv mid D).symm d) (j+1) q
      (fun δ δ'=>Q (R η (exteriorPrependAssignmentEquiv mid D δ))
        (R η (exteriorPrependAssignmentEquiv mid D δ'))) x) x
    simpa only [embedD,R,Equiv.symm_apply_apply] using HC

  · intro d cut _ a q H x
    have HR:=hRow ((exteriorPrependSlotEquiv mid D).symm d) cut a q H x
    change _=nativeJointAttachmentRow w φ q
      ((nativeHighMarkedRows (exteriorPrepend mid D) ((exteriorPrependSlotEquiv mid D).symm d)
        (cut-1) a).map (fun p=>p.right E))
      (fun (σ : (E.fork (exteriorPrepend mid D)).Assignment) new=>
        H (R σ.1 (exteriorPrependAssignmentEquiv mid D σ.2)) new) x
    rw [native_second_low_c_joint_rows_right]
    simpa only [embedD,R,Equiv.symm_apply_apply] using HR

structure NativeClassifiedWholeHighRowSource
    (pre mid tail : List PositiveMass) (T : ClockTree S (pre++(mid++tail))) (s : T.Slot)
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) where
  core : NativeClassifiedWholeRetainedSource pre mid tail T s w φ
  high_joint_row_expect : ∀(d : core.D.Slot) (cut : ℕ),pre.length+mid.length < cut →
    ∀(a : ℝ) (q : ℕ→ι→ℝ≥0) (H : T.Assignment→S→ℝ) (x : ι→ℝ),
      nativeJointAttachmentRow w φ q (nativeHighMarkedRows T (core.embedD d) (cut-1) a) H x=
        nativeJointAttachmentRow w φ q
          (nativeHighMarkedRows (nativeExteriorForestTree pre mid core.Ei core.Es core.D)
            (nativeClassifiedForestOccupiedSlot pre mid core.Ei core.Es core.D d) (cut-1) a)
          (fun σ new=>H (nativeClassifiedSourceRead pre mid core.Ei core.Es core.D core.read σ) new) x

theorem native_classified_whole_high_row_source
    (pre mid tail : List PositiveMass) (T : ClockTree S (pre++(mid++tail))) (s : T.Slot)
    {U : ℕ} (hmid : 0 < mid.length) (hU : pre.length+mid.length < U)
    (hlen : U ≤ pre.length+mid.length+tail.length)
    (hT : NativePersistentLowForks pre.length (pre.length+mid.length) U T)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a (pre++(mid++tail))) :
    Nonempty (NativeClassifiedWholeHighRowSource pre mid tail T s w φ) := by
  have Hpre : ∀c,pre.length ≤ T.splitIndex s c:=by
    intro c
    rcases hT s c with H|H|H <;> omega
  obtain ⟨Ti,hpre⟩:=native_exists_prepend_of_trunk_split pre T s Hpre
  subst T
  let si:=exteriorPrependSlotEquiv pre Ti s
  have hTi:=NativePersistentLowForks.strip_prefix pre mid Ti hU hT
  obtain ⟨Ei,Ts,Ri,ts,embedI,hEi,htI,hOutI,hHighI,hembI,hinjI,hreadI,hsplitI,hLawI,hCloneI,hRowI⟩:=
    native_star_arm_classification_with_whole_retained_clone_and_high_rows mid tail Ti si hmid (by omega)
      hTi hw φ ho.suffix_end
  have htail : tail≠[]:=by
    intro H
    have HL:=congrArg List.length H
    simp only [List.length_nil] at HL
    omega
  have hLawS:=fun q Q x=>nativeGroupRootForest_expect Ts ts hw φ ho.suffix_end.suffix_end q Q x
  have hTarget:=fun ζ δ=>(nativeGroupRootForest Ts ts).read_target ζ δ
  have hOutside:=fun c hc=>(nativeGroupRootForest Ts ts).read_exterior_relative htail c hc
  have hHigh:=fun c hc=>(nativeGroupRootForest Ts ts).read_high_relative c hc
  have hCloneS:=fun d cut hc q Q x=>native_group_root_forest_retained_clone_all_occupied
    Ts ts d cut hc hw φ ho.suffix_end.suffix_end q Q x
  have hRowS:=fun d cut a q H x=>native_group_root_forest_high_joint_rows Ts ts d cut a hw φ
    ho.suffix_end.suffix_end q H x
  generalize hg:nativeGroupRootForest Ts ts=g at hLawS hTarget hOutside hHigh hCloneS hRowS
  rcases g with ⟨Es,D,td,Rs,es,os,hts,hos,hrs,hss,hso,hfree⟩
  let R:=fun η ζ δ=>(exteriorPrependAssignmentEquiv pre Ti).symm (Ri η (Rs ζ δ))
  let embedD:=fun d=>(exteriorPrependSlotEquiv pre Ti).symm (embedI (os d))
  let Rsv : (Es.fork D).Assignment→Ts.Assignment:=fun σ=>Rs σ.1 σ.2
  let V:=Ei.fork (exteriorPrepend mid (Es.fork D))
  let Rv : V.Assignment→Ti.Assignment:=fun σ=>Ri σ.1
    (exteriorPrependAssignmentEquiv mid Ts
      (exteriorPrependRead mid Ts (Es.fork D) Rsv σ.2))
  have hCore : ∀(q' : ℕ→ι→ℝ≥0) (P : Ti.Assignment→ℝ) (y : ι→ℝ),
      Ti.expect w φ q' P y=V.expect w φ q' (fun σ=>P (Rv σ)) y:=by
    intro q' P y
    rw [hLawI,expect_fork]
    rw [expect_fork]
    apply congrArg (fun F=>Ei.expect w φ q' F y)
    funext η
    exact exteriorPrepend_expect_map_congr mid Ts (Es.fork D) Rsv hw φ ho.suffix_end
      hLawS q' (fun σ=>P (Ri η (exteriorPrependAssignmentEquiv mid Ts σ))) y
  have hCloneCore : ∀(d : D.Slot) (cut : ℕ),mid.length < cut →
      ∀(q' : ℕ→ι→ℝ≥0) (P : Ti.Assignment→Ti.Assignment→ℝ) (y : ι→ℝ),
        nativeRetainedCloneCutMean w φ Ti (embedI (os d)) cut q' P y=
          nativeRetainedCloneCutMean w φ V
            (.inr ((exteriorPrependSlotEquiv mid (Es.fork D)).symm (.inr d))) cut q'
            (fun σ σ'=>P (Rv σ) (Rv σ')) y:=by
    intro d cut hc q' P y
    rw [hCloneI (os d) cut hc]
    obtain ⟨j,hj⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : cut≠0)
    conv_lhs=>rw [hj]
    conv_rhs=>rw [hj]
    change Ei.expect w φ q' (fun η=>nativeRetainedCloneCutMean w φ (exteriorPrepend mid Ts)
      ((exteriorPrependSlotEquiv mid Ts).symm (os d)) (j+1) q'
      (fun δ δ'=>P (Ri η (exteriorPrependAssignmentEquiv mid Ts δ))
        (Ri η (exteriorPrependAssignmentEquiv mid Ts δ'))) y) y=
      Ei.expect w φ q' (fun η=>nativeRetainedCloneCutMean w φ (exteriorPrepend mid (Es.fork D))
        ((exteriorPrependSlotEquiv mid (Es.fork D)).symm (.inr d)) (j+1) q'
        (fun δ δ'=>P (Rv (η,δ)) (Rv (η,δ'))) y) y
    apply congrArg (fun F=>Ei.expect w φ q' F y)
    funext η
    have Hlaw : ∀(q'' : ℕ→ι→ℝ≥0) (Q : Ts.Assignment→Ts.Assignment→ℝ) (x : ι→ℝ),
        nativeRetainedCloneCutMean w φ Ts (os d) (cut-mid.length) q'' Q x=
          nativeRetainedCloneCutMean w φ (Es.fork D) (.inr d) (cut-mid.length) q''
            (fun σ σ'=>Q (Rsv σ) (Rsv σ')) x:=by
      intro q'' Q x
      have HC:=hCloneS d (cut-mid.length) (by omega) q'' Q x
      obtain ⟨l,hl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : cut-mid.length≠0)
      rw [hl] at HC ⊢
      exact HC
    have HH:=exteriorPrepend_retained_clone_map_congr mid Ts (Es.fork D) (os d) (.inr d) Rsv
      (cut-mid.length) w φ Hlaw q'
      (fun δ δ'=>P (Ri η (exteriorPrependAssignmentEquiv mid Ts δ))
        (Ri η (exteriorPrependAssignmentEquiv mid Ts δ'))) y
    rw [show mid.length+(cut-mid.length)=j+1 by omega] at HH
    exact HH
  have hRowCore : ∀(d : D.Slot) (cut : ℕ),mid.length < cut →
      ∀(a : ℝ) (q' : ℕ→ι→ℝ≥0) (H : Ti.Assignment→S→ℝ) (y : ι→ℝ),
        nativeJointAttachmentRow w φ q'
          (nativeHighMarkedRows Ti (embedI (os d)) (cut-1) a) H y=
          nativeJointAttachmentRow w φ q'
            (nativeHighMarkedRows V (.inr ((exteriorPrependSlotEquiv mid (Es.fork D)).symm (.inr d)))
              (cut-1) a) (fun σ new=>H (Rv σ) new) y:=by
    intro d cut hc a q' H y
    rw [hRowI (os d) cut hc]
    change nativeJointAttachmentRow w φ q'
      ((nativeHighMarkedRows (exteriorPrepend mid Ts) ((exteriorPrependSlotEquiv mid Ts).symm (os d))
        (cut-1) a).map (fun p=>p.right Ei))
      (fun (σ : (Ei.fork (exteriorPrepend mid Ts)).Assignment) new=>
        H (Ri σ.1 (exteriorPrependAssignmentEquiv mid Ts σ.2)) new) y=
      nativeJointAttachmentRow w φ q'
        ((nativeHighMarkedRows (exteriorPrepend mid (Es.fork D))
          ((exteriorPrependSlotEquiv mid (Es.fork D)).symm (.inr d)) (cut-1) a).map (fun p=>p.right Ei))
        (fun σ new=>H (Rv σ) new) y
    rw [native_second_low_c_joint_rows_right,native_second_low_c_joint_rows_right]
    apply congrArg (fun F=>Ei.expect w φ q' F y)
    funext η
    have Hlaw : ∀(a' : ℝ) (q'' : ℕ→ι→ℝ≥0) (P : Ts.Assignment→S→ℝ) (x : ι→ℝ),
        nativeJointAttachmentRow w φ q''
          (nativeHighMarkedRows Ts (os d) ((cut-mid.length)-1) a') P x=
          nativeJointAttachmentRow w φ q''
            (nativeHighMarkedRows (Es.fork D) (.inr d) ((cut-mid.length)-1) a')
            (fun σ new=>P (Rsv σ) new) x:=by
      intro a' q'' P x
      change _=nativeJointAttachmentRow w φ q''
        ((nativeHighMarkedRows D d ((cut-mid.length)-1) a').map (fun p=>p.right Es))
        (fun σ new=>P (Rsv σ) new) x
      rw [native_second_low_c_joint_rows_right]
      exact hRowS d (cut-mid.length) a' q'' P x
    have HH:=exteriorPrepend_high_joint_rows_map_congr mid Ts (Es.fork D) (os d) (.inr d) Rsv
      (cut-mid.length) (by omega) hw φ ho.suffix_end Hlaw a q'
      (fun δ new=>H (Ri η (exteriorPrependAssignmentEquiv mid Ts δ)) new) y
    rw [show mid.length+(cut-mid.length)=cut by omega] at HH
    exact HH
  refine ⟨⟨⟨Ei,Es,D,R,td,embedD,hfree,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩,?_⟩⟩
  · dsimp only [embedD]
    rw [hts,hembI]
    exact (exteriorPrependSlotEquiv pre Ti).symm_apply_apply s
  · intro d e H
    have HH:=congrArg (exteriorPrependSlotEquiv pre Ti) H
    dsimp only [embedD] at HH
    simp only [Equiv.apply_symm_apply] at HH
    have HI:=hinjI HH
    have HS:=congrArg es HI
    rw [hos,hos] at HS
    exact Sum.inr.inj HS
  · intro η ζ δ d
    rw [exteriorPrepend_atSlot]
    simp only [R,embedD,Equiv.apply_symm_apply]
    rw [hreadI,hrs,hos]
    rfl
  · intro d e
    rw [exteriorPrepend_splitIndex]
    simp only [embedD,Equiv.apply_symm_apply]
    rw [hsplitI,hso]
    omega
  · intro η ζ δ
    rw [exteriorPrepend_atSlot]
    simp only [R,Equiv.apply_symm_apply]
    rw [htI]
    exact hTarget ζ δ
  · intro c hc
    let ci:=exteriorPrependSlotEquiv pre Ti c
    have hci : Ti.splitIndex si ci=0:=by
      have HS:=exteriorPrepend_splitIndex pre Ti s c
      dsimp only [si,ci] at *
      omega
    obtain ⟨e,he⟩:=hOutI ci hci
    refine ⟨e,?_⟩
    intro η ζ δ
    rw [exteriorPrepend_atSlot]
    simp only [R,Equiv.apply_symm_apply]
    exact he η (Rs ζ δ)
  · intro c hc
    let ci:=exteriorPrependSlotEquiv pre Ti c
    have hci : Ti.splitIndex si ci=mid.length:=by
      have HS:=exteriorPrepend_splitIndex pre Ti s c
      dsimp only [si,ci] at *
      omega
    obtain ⟨cs,hr,hs⟩:=hHighI ci hci.ge
    have hcs : Ts.splitIndex ts cs=0:=by omega
    obtain ⟨e,he⟩:=hOutside cs hcs
    refine ⟨e,?_⟩
    intro η ζ δ
    rw [exteriorPrepend_atSlot]
    simp only [R,Equiv.apply_symm_apply]
    rw [hr]
    exact he ζ δ
  · intro c hc
    have HS:=exteriorPrepend_splitIndex pre Ti s c
    let ci:=exteriorPrependSlotEquiv pre Ti c
    have hci : mid.length < Ti.splitIndex si ci:=by dsimp only [si,ci] at *;omega
    obtain ⟨cs,hr,hs⟩:=hHighI ci hci.le
    have hcs : 0 < Ts.splitIndex ts cs:=by omega
    obtain ⟨d,hr',hs'⟩:=hHigh cs hcs
    refine ⟨d,?_,?_⟩
    · intro η ζ δ
      rw [exteriorPrepend_atSlot]
      simp only [R,Equiv.apply_symm_apply]
      rw [hr]
      exact hr' ζ δ
    · dsimp only [si,ci] at *
      omega
  · intro q Q x
    have H:=exteriorPrepend_expect_map_congr pre Ti V Rv hw φ ho hCore q Q x
    unfold nativeExteriorForestRead
    simpa only [nativeExteriorForestTree,exteriorPrependRead,Rv,Rsv,R,V,Equiv.apply_symm_apply] using H
  · intro d cut hc q Q x
    have H:=exteriorPrepend_retained_clone_map_congr pre Ti V (embedI (os d))
      (.inr ((exteriorPrependSlotEquiv mid (Es.fork D)).symm (.inr d))) Rv (cut-pre.length)
      w φ (hCloneCore d (cut-pre.length) (by omega)) q Q x
    rw [show pre.length+(cut-pre.length)=cut by omega] at H
    simpa only [nativeExteriorForestTree,nativeClassifiedForestOccupiedSlot,nativeClassifiedSourceRead,
      exteriorPrependRead,Rv,Rsv,R,V,embedD,Equiv.apply_symm_apply] using H

  · intro d cut hc a q H x
    have HH:=exteriorPrepend_high_joint_rows_map_congr pre Ti V (embedI (os d))
      (.inr ((exteriorPrependSlotEquiv mid (Es.fork D)).symm (.inr d))) Rv (cut-pre.length)
      (by omega) hw φ ho (hRowCore d (cut-pre.length) (by omega)) a q H x
    rw [show pre.length+(cut-pre.length)=cut by omega] at HH
    simpa only [nativeExteriorForestTree,nativeClassifiedForestOccupiedSlot,nativeClassifiedSourceRead,
      exteriorPrependRead,Rv,Rsv,R,V,embedD,Equiv.apply_symm_apply] using HH

end OAI.SKFluctuations.Cavity
