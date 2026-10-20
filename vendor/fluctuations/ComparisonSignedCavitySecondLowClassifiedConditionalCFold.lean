module

public import ComparisonSignedCavitySecondLowClassifiedHighRowPrefix

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 26000000
set_option backward.isDefEq.respectTransparency false
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

theorem native_classified_prefixTest_sub_mul
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (pre tail : List (GaussianStep ι)) {a : ℝ} (ho : OrderedSteps a (pre++tail))
    (F G : (ι→ℝ)→ℝ) (hF : BddSmooth 0 F) (hG : BddSmooth 0 G) (c : ℝ) (x : ι→ℝ) :
    prefixTest pre (gaussianHierarchy w φ tail) (fun y=>F y-c*G y) x=
      prefixTest pre (gaussianHierarchy w φ tail) F x-
        c*prefixTest pre (gaussianHierarchy w φ tail) G x := by
  let B : Bool→(ι→ℝ)→ℝ:=fun b=>if b then F else fun y=>-c*G y
  have hb : ∀b,BddSmooth 0 (B b):=by
    intro b
    cases b
    · exact hG.const_mul (-c)
    · exact hF
  have HH:=prefixTest_fintype_sum hw φ pre tail ho B hb x
  simp only [Fintype.sum_bool,B,Bool.false_eq_true,ite_false,ite_true] at HH
  have HE : (fun y=>F y+-c*G y)=fun y=>F y-c*G y:=by funext y;ring
  rw [HE,prefixTest_scalar_mul] at HH
  convert HH using 1
  ring

omit [Nonempty S] in
private theorem classified_expect_sub_mul
    {as : List PositiveMass} (T : ClockTree S as)
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (q : ℕ→ι→ℝ≥0)
    (P R : T.Assignment→ℝ) (c : ℝ) (x : ι→ℝ) :
    T.expect w φ q (fun σ=>P σ-c*R σ) x=T.expect w φ q P x-c*T.expect w φ q R x := by
  unfold ClockTree.expect
  simp only [mul_sub,Finset.sum_sub_distrib]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  ring

def nativeClassifiedConditionalCFold
    {ias sas : List PositiveMass} (Ei : ClockTree S ias) (Es D : ClockTree S sas)
    (d : D.Slot) (U : ℕ) (a : ℝ) (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (qi qs : ℕ→ι→ℝ≥0) (P : Ei.Assignment→Es.Assignment→D.Assignment→ℝ)
    (outsideF outsideZ : Ei.Assignment→Es.Assignment→S) (Q : S→S→S→ℝ)
    (xi xs : ι→ℝ) : ℝ:=
  Ei.expect w φ qi (fun η=>Es.expect w φ qs (fun ζ=>nativeSecondLowCCouplingFold w φ D d U a qs
    (P η ζ) (.fixed (outsideF η ζ)) (.fixed (outsideZ η ζ)) Q xs) xs) xi

theorem native_classified_forest_c_replacement_eq_conditional_prefix
    (pre mid tail : List PositiveMass) (Ei : ClockTree S (mid++tail)) (Es D : ClockTree S tail)
    (d : D.Slot) (U : ℕ) (hstar : pre.length+mid.length < U)
    (hU : U ≤ (pre++(mid++tail)).length) (a : ℝ)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (ho : MassOrdered a (pre++(mid++tail))) (q : ℕ→ι→ℝ≥0)
    (P : Ei.Assignment→Es.Assignment→D.Assignment→ℝ)
    (outsideF outsideZ : Ei.Assignment→Es.Assignment→S) (Q : S→S→S→ℝ) (x : ι→ℝ) :
    nativeJointAttachmentRow w φ q
      (nativeHighMarkedRows (nativeExteriorForestTree pre mid Ei Es D)
        (nativeClassifiedForestOccupiedSlot pre mid Ei Es D d) (U-1) a)
      (fun σ new=>nativeClassifiedSourceRead pre mid Ei Es D
        (fun η ζ δ=>P η ζ δ*Q (outsideF η ζ) new (outsideZ η ζ)) σ) x-
      partitionPoint a (pre++(mid++tail)) U*
        (nativeExteriorForestTree pre mid Ei Es D).expect w φ q
          (nativeExteriorForestRead pre mid Ei Es D
            (fun η ζ δ=>P η ζ δ*Q (outsideF η ζ) (D.atSlot δ d) (outsideZ η ζ))) x=
      prefixTest (clockSteps pre q)
        (gaussianHierarchy w φ (clockSteps (mid++tail) (fun j=>q (pre.length+j))))
        (fun xi=>prefixTest (clockSteps mid (fun j=>q (pre.length+j)))
          (gaussianHierarchy w φ (clockSteps tail (fun j=>q (pre.length+(mid.length+j)))))
          (nativeClassifiedConditionalCFold Ei Es D d (U-(pre.length+mid.length))
            (partitionPoint a (pre++(mid++tail)) (pre.length+mid.length)) w φ
            (fun j=>q (pre.length+j)) (fun j=>q (pre.length+(mid.length+j))) P outsideF outsideZ Q xi) xi) x := by
  let qi:=fun j=>q (pre.length+j)
  let qs:=fun j=>q (pre.length+(mid.length+j))
  let astar:=partitionPoint a (pre++(mid++tail)) (pre.length+mid.length)
  let ai:=partitionPoint a pre pre.length
  let uD:=U-(pre.length+mid.length)
  let mU:=partitionPoint a (pre++(mid++tail)) U
  let ms:=clockSteps mid qi
  let ts:=clockSteps tail qs
  let H:=fun η ζ δ new=>P η ζ δ*Q (outsideF η ζ) new (outsideZ η ζ)
  let old:=fun η ζ δ=>H η ζ δ (D.atSlot δ d)
  let Bhi:=nativeClassifiedHighJointMean Ei Es D d uD astar w φ qi qs H
  let Blo:=nativeExteriorForestConditionalTest Ei Es D w φ qi qs old
  let Ahi:=fun xi=>prefixTest ms (gaussianHierarchy w φ ts) (Bhi xi) xi
  let Alo:=fun xi=>prefixTest ms (gaussianHierarchy w φ ts) (Blo xi) xi
  have huD : 0 < uD:=by dsimp only [uD];omega
  have huDlen : uD ≤ tail.length:=by simp only [List.length_append] at hU;dsimp only [uD];omega
  have has : astar=partitionEnd (partitionEnd a pre) mid:=by
    dsimp only [astar]
    rw [native_classified_star_mass_eq_nested_prefix,partitionPoint_eq_end_take,partitionPoint_eq_end_take]
    simp only [List.take_length]
  have hoD : MassOrdered astar tail:=by rw [has];exact ho.suffix_end.suffix_end
  have hmU : partitionPoint astar tail uD=mU:=by
    have HH:=native_classified_suffix_mass_readout a (pre++mid) tail U (by simp only [List.length_append];omega)
    simpa only [List.append_assoc,List.length_append,astar,uD,mU] using HH
  have hoG : OrderedSteps (partitionEnd a pre) (ms++ts):=by
    dsimp only [ms,ts,qs]
    rw [←clockSteps_append]
    exact clockSteps_ordered ho.suffix_end qi
  have hBhi (xi : ι→ℝ) : BddSmooth 0 (Bhi xi):=by
    have hB (η : Ei.Assignment) : BddSmooth 0 (fun xs=>Es.expect w φ qs (fun ζ=>
        nativeJointAttachmentRow w φ qs (nativeHighMarkedRows D d (uD-1) astar) (H η ζ) xs) xs):=by
      have HH:=native_joint_attachment_row_smooth (Es.fork D) hw φ hoD qs
        (nativeHighMarkedRows (Es.fork D) (.inr d) (uD-1) astar) (fun σ new=>H η σ.1 σ.2 new) 0
      have HE : (fun xs=>nativeJointAttachmentRow w φ qs
          (nativeHighMarkedRows (Es.fork D) (.inr d) (uD-1) astar) (fun σ new=>H η σ.1 σ.2 new) xs)=
          fun xs=>Es.expect w φ qs (fun ζ=>nativeJointAttachmentRow w φ qs
            (nativeHighMarkedRows D d (uD-1) astar) (H η ζ) xs) xs:=by
        funext xs
        exact native_second_low_c_joint_rows_right Es D w φ qs _ _ xs
      rw [HE] at HH
      exact HH
    change BddSmooth 0 (fun xs=>∑η,Ei.weight w φ qi η xi*Es.expect w φ qs
      (fun ζ=>nativeJointAttachmentRow w φ qs (nativeHighMarkedRows D d (uD-1) astar) (H η ζ) xs) xs)
    exact BddSmooth.sum Finset.univ (fun η _=>(hB η).const_mul _)
  have hBlo (xi : ι→ℝ) : BddSmooth 0 (Blo xi):=
    nativeExteriorForestConditionalTest_smooth_star hw φ Ei Es D hoD qi qs old xi 0
  have hAhi : BddSmooth 0 Ahi:=by
    let V:=Ei.fork (exteriorPrepend mid (Es.fork D))
    have HH:=native_joint_attachment_row_smooth V hw φ ho.suffix_end qi
      (nativeHighMarkedRows V (.inr ((exteriorPrependSlotEquiv mid (Es.fork D)).symm (.inr d)))
        ((U-pre.length)-1) ai)
      (fun σ new=>let u:=exteriorPrependAssignmentEquiv mid (Es.fork D) σ.2;H σ.1 u.1 u.2 new) 0
    have HE : (fun xi=>nativeJointAttachmentRow w φ qi
        (nativeHighMarkedRows V (.inr ((exteriorPrependSlotEquiv mid (Es.fork D)).symm (.inr d)))
          ((U-pre.length)-1) ai)
        (fun σ new=>let u:=exteriorPrependAssignmentEquiv mid (Es.fork D) σ.2;H σ.1 u.1 u.2 new) xi)=Ahi:=by
      funext xi
      have HT:=native_classified_forest_tail_high_joint_rows_eq_prefix mid tail Ei Es D d
        (U-pre.length) (by omega) ai hw φ ho.suffix_end qi H xi
      have Hmass : partitionPoint ai (mid++tail) mid.length=astar:=by
        dsimp only [ai,astar]
        rw [native_classified_star_mass_eq_nested_prefix]
        have HS:=native_classified_partitionPoint_append_shift (partitionPoint a pre pre.length) mid tail 0
        simp only [Nat.add_zero] at HS
        have HZ : partitionPoint (partitionEnd (partitionPoint a pre pre.length) mid) tail 0=
            partitionEnd (partitionPoint a pre pre.length) mid:=by
          simp only [partitionPoint,partitionValues_zero,id_eq]
        rw [HZ] at HS
        rw [HS]
        simp only [partitionPoint_eq_end_take,List.take_length]
      rw [Hmass,show (U-pre.length)-mid.length=uD by dsimp only [uD];omega] at HT
      exact HT
    rw [HE] at HH
    exact HH
  have hAlo : BddSmooth 0 Alo:=by
    have HH:=(Ei.fork (exteriorPrepend mid (Es.fork D))).nativeAnchor_expect_smooth hw φ
      ho.suffix_end qi (fun σ=>let u:=exteriorPrependAssignmentEquiv mid (Es.fork D) σ.2;old σ.1 u.1 u.2) 0
    have HE : (Ei.fork (exteriorPrepend mid (Es.fork D))).expect w φ qi
        (fun σ=>let u:=exteriorPrependAssignmentEquiv mid (Es.fork D) σ.2;old σ.1 u.1 u.2)=Alo:=
      funext fun xi=>nativeExteriorForestTail_expect_eq_prefix mid hw φ Ei Es D ho.suffix_end qi old xi
    rw [HE] at HH
    exact HH
  have Hmean (xi xs : ι→ℝ) :
      nativeClassifiedConditionalCFold Ei Es D d uD astar w φ qi qs P outsideF outsideZ Q xi xs=
        Bhi xi xs-mU*Blo xi xs:=by
    have HP (η : Ei.Assignment) (ζ : Es.Assignment) :
        nativeSecondLowCCouplingFold w φ D d uD astar qs (P η ζ)
          (.fixed (outsideF η ζ)) (.fixed (outsideZ η ζ)) Q xs=
          nativeJointAttachmentRow w φ qs (nativeHighMarkedRows D d (uD-1) astar) (H η ζ) xs-
            mU*D.expect w φ qs (old η ζ) xs:=by
      rw [native_second_low_c_coupling_fold_eq_original hw φ D d uD hoD huDlen (by omega)
        qs (P η ζ) (.fixed (outsideF η ζ)) (.fixed (outsideZ η ζ)) trivial trivial Q xs]
      unfold nativeSecondLowCReplacementValue
      simp only [nativeSecondLowCSourceRows,ne_of_gt huD,ite_false,NativeSecondLowCReader.read,hmU]
      rfl
    unfold nativeClassifiedConditionalCFold
    simp_rw [HP,classified_expect_sub_mul]
    have HE : Blo xi xs=Ei.expect w φ qi (fun η=>Es.expect w φ qs (fun ζ=>D.expect w φ qs (old η ζ) xs) xs) xi:=by
      dsimp only [Blo]
      rw [nativeExteriorForestConditionalTest_eq_joint]
      simp_rw [expect_fork]
    rw [HE]
    rfl
  rw [native_classified_forest_high_joint_rows_eq_prefix pre mid tail Ei Es D d U hstar a hw φ ho,
    nativeExteriorForestTree_expect_eq_prefix pre mid hw φ Ei Es D ho]
  change prefixTest (clockSteps pre q) (gaussianHierarchy w φ (clockSteps (mid++tail) qi)) Ahi x-
    mU*prefixTest (clockSteps pre q) (gaussianHierarchy w φ (clockSteps (mid++tail) qi)) Alo x=_
  have hoPre : OrderedSteps a (clockSteps pre q++clockSteps (mid++tail) qi):=by
    rw [←clockSteps_append]
    exact clockSteps_ordered ho q
  rw [←native_classified_prefixTest_sub_mul hw φ _ _ hoPre Ahi Alo hAhi hAlo]
  apply congrArg (fun F=>prefixTest (clockSteps pre q)
    (gaussianHierarchy w φ (clockSteps (mid++tail) qi)) F x)
  funext xi
  have HM:=native_classified_prefixTest_sub_mul hw φ ms ts hoG (Bhi xi) (Blo xi) (hBhi xi) (hBlo xi) mU xi
  rw [←HM]
  apply congrArg (fun F=>prefixTest ms (gaussianHierarchy w φ ts) F xi)
  funext xs
  exact (Hmean xi xs).symm

end OAI.SKFluctuations.Cavity
