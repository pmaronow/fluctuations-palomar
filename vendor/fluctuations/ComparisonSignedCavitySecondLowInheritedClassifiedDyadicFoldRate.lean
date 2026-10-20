module

public import ComparisonSignedCavitySecondLowClassifiedDyadicSource

@[expose] public section

noncomputable section
set_option maxHeartbeats 60000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_minimum_inherited_second_low_classified_dyadic_fold_rate
    (a : ℕ) (Bclock Temp Cf Cmass Ccal Rmacro F : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cmass)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
        M.xs^2 ≤ Ccal^2*laplaceComparisonStrength M.context.d M.lam M.xs →
      ∀(L : ℕ) (us : List PositiveMass) (_hus : ∀u∈us,u.val ≤ 1), (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
          (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
        let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))
        ∀(pre mid tail : List PositiveMass) (_hparts : as=pre++(mid++tail))
          (T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (G : ActualNaturalBoundaryShape n a T)
          (forms : Fin a→NativeSourceFactorForm) (initial : Finset (Fin a))
          (f c z : T.Slot) (U : ℕ) (x sourceMass : ℝ) (hsourceMass : 0 < sourceMass)
          (E : NativeSecondLowClassifiedRetainedWholeCSource n pre mid tail T f c z 0 q 0),
          pre.length+mid.length < U → U ≤ (pre++(mid++tail)).length →
          NativePersistentLowForks pre.length (pre.length+mid.length) U T →
          T.splitIndex f c < U → T.splitIndex c z < U →
          M.xs ≤ x → x ≤ W → W ≤ Rmacro/2 →
          (∀(d : E.source.D.Slot) e,T.splitIndex (E.originalSlot d) (G.i e) < U) →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
          4*W ≤ M.R (partitionPoint 0 as U) →
          M.z ≤ min (M.R (partitionPoint 0 as U)/8) (Rmacro/4) →
          (∀(d : E.source.D.Slot) e,U ≤ T.splitIndex (E.originalSlot d) (G.j e) →
            M.R (G.sourceLowMass e) ≤ min (M.R (partitionPoint 0 as U)/8) (Rmacro/4)) →
          partitionPoint 0 as (T.splitIndex f c) ≤ Cmass*W →
          partitionPoint 0 as (T.splitIndex z c) ≤ Cmass*W →
          M.R (partitionPoint 0 as (T.splitIndex f c)) ≤
            min (M.R (partitionPoint 0 as U)/8) (Rmacro/4) →
          M.R (partitionPoint 0 as (T.splitIndex z c)) ≤
            min (M.R (partitionPoint 0 as U)/8) (Rmacro/4) →
          NativeDyadicRetainedReadout sourceMass hsourceMass (pre++(mid++tail)) U →
        |nativeSecondLowClassifiedCompleteCFold E U q
          (fun j=>(M.bf (partitionPoint 0 as j):ℝ))
          (fun j=>(M.hf (partitionPoint 0 as j):ℝ))
          (fun j=>(M.hf (partitionPoint 0 as j):ℝ)+
            (M.bf (partitionPoint 0 as j):ℝ)*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j))
          (G.canonicalMinimumSource M forms).restProduct| ≤
          C*((nativeDyadicCutDepth sourceMass:ℝ)+1)*(E.source.D.leaves:ℝ)^2*
            ((n:ℝ)^(-eta))^2*W*M.xs^2*sourceMonomialScale x W initial := by
  obtain ⟨Cl,hCl,HL⟩:=eventually_actual_minimum_inherited_second_low_classified_indexed_layer_rate
    (D:=D) a Bclock Temp Cf Cmass Ccal Rmacro F hTemp hCf hCm hm hdelta hroom hgap
    hcl hcu hAz hC0 hCt hCcal hmacro hRhalf hFmass hFradius
  obtain ⟨Cc,hCc,HC⟩:=eventually_actual_minimum_inherited_second_low_classified_covariance_rate
    (D:=D) a Bclock Temp Cf Cmass Ccal Rmacro F hTemp hCf hCm hm hdelta hroom hgap
    hcl hcu hAz hC0 hCt hCcal hmacro hRhalf hFmass hFradius
  refine ⟨Cl+Cc+1,by positivity,?_⟩
  filter_upwards [HL,HC] with n hnL hnC
  intro M HS hxs hcompare L us hus hret hmesh
  filter_upwards [hnL M HS hxs hcompare L us hus hret hmesh,
    hnC M HS hxs hcompare L us hus hret hmesh] with k hkL hkC
  dsimp only at hkL hkC ⊢
  intro pre mid tail hparts T G forms initial f c z U x sourceMass hsourceMass E
    hstar hU hT Hfc Hcz hxsx hxW hWmacro hout hmass hhigh hz hlow Hmf Hmz Hrf Hrz Hchain
  let as:=finiteCutMasses us k
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
    (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
  let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=fun j=>h j+b j*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let P:=(G.canonicalMinimumSource M forms).restProduct
  let p0:=sourceMonomialScale x W initial
  let ell:=(E.source.D.leaves:ℝ)
  let base:=((n:ℝ)^(-eta))^2*W*M.xs^2*p0
  let count:=nativeDyadicCutDepth sourceMass
  let cut:=nativeDyadicSourceRetainedIndex sourceMass hsourceMass (pre++(mid++tail)) U
  let cuts:=fun j=>(nativeDyadicMassCut sourceMass hsourceMass j).val
  have ho : MassOrdered 0 (pre++(mid++tail)):=hparts ▸ finiteCutMasses_ordered us hus k
  have hoas : MassOrdered 0 as:=finiteCutMasses_ordered us hus k
  have HD:=Hchain.shifted_two_level ho pre mid tail rfl hstar hU (cumulativeIncrements (q 0) (fun j=>q (j+1)))
  have huas : U ≤ as.length:=by simpa only [as,hparts] using hU
  have hbase : 0 ≤ base:=by
    have hx:=M.hxs.trans_le hxsx
    have hW:=hx.trans_le hxW
    dsimp [base,p0,W]
    unfold sourceMonomialScale
    positivity
  have hell : 1 ≤ ell:=by dsimp only [ell];exact_mod_cast (show 1 ≤ E.source.D.leaves by have HH:=indexed_native_leaves_pos E.source.D;omega)
  have HR (j : ℕ) (hj : j < count) : M.R (partitionPoint 0 as U) ≤ M.R (partitionPoint 0 as (cut j)) := by
    have HU:=HD.original_source_le j (Nat.le_of_lt hj)
    exact comparisonSweepQuantile_monotone M.context.hc M.context.hk M.context.hkc M.context.hm
      M.context.hM M.alpha (partitionPoint_mono as hoas HU)
  have Hbounds (j : ℕ) (hj : j < count) :
      |nativeSecondLowClassifiedIndexedLayer E ho U (cut j) (cuts j) (cuts (j+1)) q b h K P| ≤ Cl*ell^2*base := by
    have huj:=HD.original_source_le j (Nat.le_of_lt hj)
    have hkj:cut j ≤ as.length:=by simpa only [cut,as,hparts] using HD.original_index_le j (Nat.le_of_lt hj)
    have hrj:=HR j hj
    have Hmin : min (M.R (partitionPoint 0 as U)/8) (Rmacro/4) ≤
        min (M.R (partitionPoint 0 as (cut j))/8) (Rmacro/4) := min_le_min (by linarith) le_rfl
    have HLj:=hkL pre mid tail hparts T G forms initial f c z U (cut j) x (cuts j) (cuts (j+1)) E
      hstar hU hT Hfc Hcz huj (HD.cut_monotone (Nat.le_succ j)) (HD.comparable j hj)
      hxsx hxW (nativeDyadicMassCut sourceMass hsourceMass j).property hWmacro hkj
      (fun d e=>(hout d e).trans_le huj) hmass (hhigh.trans hrj) (hz.trans Hmin)
      (fun d e he=>(hlow d e (huj.trans he)).trans Hmin) Hmf Hmz (Hrf.trans Hmin) (Hrz.trans Hmin)
      (by simpa only [cut,cuts,hparts,as] using HD.lower_mass j (Nat.le_of_lt hj))
    convert HLj using 1
    dsimp only [ell,base,p0,W]
    ring
  have HCv : |(sourceMass/2)*nativeSecondLowClassifiedRetainedCovariance E U U q b h K P| ≤ Cc*base := by
    have Hv : sourceMass/2 ≤ partitionPoint 0 as U := by
      change sourceMass/2 ≤ partitionPoint 0 (finiteCutMasses us k) U
      rw [hparts,Hchain.literal_source_mass]
      linarith
    have HCo:=hkC pre mid tail hparts T G forms initial f c z U U x (sourceMass/2) E
      hstar le_rfl Hfc Hcz hxsx hxW (by linarith) hWmacro huas
      (fun e=>by have HH:=hout E.source.target e;rw [E.originalSlot_target] at HH;exact HH)
      hmass Hmf Hmz hhigh hz
      (fun e he=>by have HH:=hlow E.source.target e;rw [E.originalSlot_target] at HH;exact HH he)
      Hrf Hrz Hv
    convert HCo using 1
    dsimp only [base,p0,W]
    ring
  have HT:=native_second_low_classified_complete_c_fold_eq_dyadic_layers_sub_covariance
    E ho U hstar hU hT q b h K P sourceMass hsourceMass Hchain
  rw [HT]
  have Hsum : |∑j∈Finset.range count,nativeSecondLowClassifiedIndexedLayer E ho U (cut j) (cuts j) (cuts (j+1)) q b h K P| ≤
      (count:ℝ)*(Cl*ell^2*base) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply (Finset.sum_le_sum (fun j hj=>Hbounds j (Finset.mem_range.mp hj))).trans
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,le_refl]
  apply (abs_sub _ _).trans
  apply (add_le_add Hsum HCv).trans
  have hell2 : 1 ≤ ell^2:=by nlinarith only [hell]
  have hcount : 0 ≤ (count:ℝ):=Nat.cast_nonneg _
  have Hnum : (count:ℝ)*(Cl*ell^2)+Cc ≤ (Cl+Cc+1)*((count:ℝ)+1)*ell^2 := by
    nlinarith only [hCl,hCc,hell2,hcount,
      mul_nonneg hcount (sub_nonneg.mpr hell2)]
  convert mul_le_mul_of_nonneg_right Hnum hbase using 1 <;>
    dsimp only [ell,base,p0,W,count] <;> ring

end OAI.SKFluctuations.Cavity
