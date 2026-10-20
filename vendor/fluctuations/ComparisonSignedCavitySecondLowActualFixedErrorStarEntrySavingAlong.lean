module

public import ComparisonSignedCavitySecondLowUnobservedErrorEntrySource
public import ComparisonSignedCavitySecondLowActualStarAtomSavingAlong
public import ComparisonSignedCavitySecondLowOriginalCanonicalTransport

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
set_option maxHeartbeats 30000000

def ActualSecondLowUnobservedFixedErrorStarEntrySavingOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (aDegree rBound : ℕ) (saving Cmass Couter : ℝ)
    (dim : ℕ→ℕ)
    (M : (n:ℕ)→NativeOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
    ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val≤1)→(w n).star∈us→
      (∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹≤(M n).xs→
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS ((dim n)+1) (M n).bf (M n).hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (T : ClockTree (Spin (dim n)×Bool) as) (hU : U≤as.length),
          T.leaves≤rBound→star < U→partitionPoint 0 as U≤Couter*W n→
        ∀(G : ActualNaturalBoundaryShape (dim n) aDegree T)
          (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x : ℝ),(M n).xs≤x→x≤W n→
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x (W n) initial e)→
        ∀(a z : T.Slot),T.splitIndex a z < U→∀(j : Fin 8) (firstError : Bool),
          |nativeSecondLowFixedErrorUnobservedClassLedger (dim n) q star U b h K T
            hU (G.canonicalMinimumSource (M n) forms).restProduct a z j firstError/2|≤
            (((dim n)+1:ℕ):ℝ)^(-saving)*W n*(M n).xs^2*
              sourceMonomialScale x (W n) initial

theorem actual_second_low_unobserved_fixed_error_star_entry_saving_along
    {m delta cl cu Az C0 Ct D Bclock Temp Tstar Lwin Cs Cf : ℝ}
    (aDegree rBound : ℕ) (Cmass Couter : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCm : 0≤Cmass) (hCouter : 0≤Couter)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0)) (w : ℕ→ActualSlowWindowChoice)
    (Hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cs (w n)) :
    ActualSecondLowUnobservedFixedErrorStarEntrySavingOnEveryFinalNetAlong aDegree rBound
      (actualMassSavingExponent m delta/32) Cmass Couter dim M W w := by
  let Prow:ℝ:=4*(rBound+1)*(rBound+2)*(rBound+3)*(rBound+4)
  have hProw:0 < Prow:=by dsimp [Prow];positivity
  let Cpay:=Prow*(1+Couter)
  have hpay:0 < Cpay:=mul_pos hProw (by linarith)
  have HA:=actual_second_low_star_error_atom_saving_along aDegree (rBound+4) Cmass Couter Cpay
    hTemp hCf hCm hCouter hpay.le hm hdelta hroom hcl hcu hAz hC0 hCt
    dim hdim M W hcanonical hWlim w Hsource hw
  filter_upwards [HA] with n hn
  intro L us hus hstar hret hmesh
  filter_upwards [hn L us hus hstar hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS ((dim n)+1) (M n).bf (M n).hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  intro U T hU hT hstarU houter G forms initial x hxsx hxW hmass a z haz j firstError
  let p0:=sourceMonomialScale x (W n) initial
  let rate:=(((dim n)+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/32))*(M n).xs^2*p0
  let Bd:=rate/Cpay
  let F:=nativeSecondLowFixedErrorUnobservedWord (dim n) q star U b h K hU
    (G.canonicalMinimumSource (M n) forms).restProduct a z j firstError
  have hW:0 < W n:=(M n).hxs.trans_le (hxsx.trans hxW)
  have hp0:0≤p0:=by
    dsimp [p0]
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>
      (source_factor_scale_pos ((M n).hxs.trans_le hxsx) hW initial e).le
  have hrate:0≤rate:=by dsimp [rate];positivity
  have hBd:0≤Bd:=div_nonneg hrate hpay.le
  have ho:MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have HF:∀p∈T.markedAttach 0,∀r∈p.tree.markedAttach 0,
      ∀s∈r.tree.markedAttach 0,∀t∈s.tree.markedAttach 0,|F p r s t|≤Bd:=by
    intro p hp r hr s hs t ht
    dsimp only [F,nativeSecondLowFixedErrorUnobservedWord,nativeSecondLowUnobservedErrorWord]
    split_ifs with Hindex _Hsource
    · by_cases Hfirst:r.tree.splitIndex (r.embed p.mark) r.mark < U
      · by_cases Hsecond:t.tree.splitIndex (t.embed s.mark) t.mark < U
        · let Gfinal:=nativeSecondLowCanonicalOldShape G p hp r hr s hs t ht
          let af:=t.embed (s.embed (r.embed (p.embed a)))
          let zf:=t.embed (s.embed (r.embed (p.embed z)))
          let f:=t.embed (s.embed (r.embed p.mark))
          let c:=t.embed (s.embed r.mark)
          let e:=t.embed s.mark
          let d:=t.mark
          have hfinal:t.tree.leaves≤rBound+4:=
            (native_second_low_four_mark_leaves_le p hp r hr s hs t ht).trans (by omega)
          have hfinalmass:∀i,Gfinal.sourceLowMass i≤Cmass*sourceFactorScale x (W n) initial i:=by
            intro i
            rw [native_second_low_canonical_old_shape_source_mass]
            exact hmass i
          have Hfc:t.tree.splitIndex f c=r.tree.splitIndex (r.embed p.mark) r.mark:=by
            dsimp only [f,c]
            rw [(s.tree.markedAttach_embed_preserves 0 t ht).2,
              (r.tree.markedAttach_embed_preserves 0 s hs).2]
          have Hf:t.tree.splitIndex f c < U:=by rw [Hfc];exact Hfirst
          have He:t.tree.splitIndex e d < U:=Hsecond
          have Ha:t.tree.splitIndex af zf < U:=by
            dsimp only [af,zf]
            rw [(s.tree.markedAttach_embed_preserves 0 t ht).2,
              (r.tree.markedAttach_embed_preserves 0 s hs).2,
              (p.tree.markedAttach_embed_preserves 0 r hr).2,
              (T.markedAttach_embed_preserves 0 p hp).2]
            exact haz
          have Hne(u v:t.tree.Slot)(H:t.tree.splitIndex u v < U):u≠v:=by
            intro HH
            rw [HH,t.tree.splitIndex_self] at H
            omega
          have Hfn:f≠c:=Hne f c Hf
          have Hen:e≠d:=Hne e d He
          have Han:af≠zf:=Hne af zf Ha
          have hzero:(0:ℝ)∈Icc (0:ℝ) 1:=⟨le_rfl,zero_le_one⟩
          have hone:(1:ℝ)∈Icc (0:ℝ) 1:=⟨zero_le_one,le_rfl⟩
          have HP:(Gfinal.canonicalMinimumSource (M n) forms).restProduct=
              nativeSecondLowOldTest (G.canonicalMinimumSource (M n) forms).restProduct p r s t:=by
            funext τ
            exact native_second_low_canonical_old_shape_rest_product (M n) G forms p hp r hr s hs t ht τ
          have HB:Cpay*|nativeSecondLowErrorWord (dim n) q U b h K
              (G.canonicalMinimumSource (M n) forms).restProduct a z firstError p r s t|≤rate:=by
            cases firstError
            · simp only [nativeSecondLowErrorCut,Bool.false_eq_true,ite_false] at Hindex
              have Bsecond:=hgrid U t.tree 0 0 hU hstarU houter hzero hzero hfinal
                Gfinal forms initial x hxsx hxW hfinalmass e d f c af zf 0 Hindex Hf Hfn Han hzero
              rw [HP] at Bsecond
              exact Bsecond
            · simp only [nativeSecondLowErrorCut,ite_true] at Hindex
              have Hfixed:t.tree.splitIndex f c=star:=Hfc.trans Hindex
              have Bfirst:=hgrid U t.tree 0 0 hU hstarU houter hzero hzero hfinal
                Gfinal forms initial x hxsx hxW hfinalmass f c e d af zf 1 Hfixed He Hen Han hone
              rw [HP] at Bfirst
              exact Bfirst
          apply (le_div_iff₀ hpay).mpr
          exact (mul_comm _ Cpay).le.trans HB
        · rw [native_second_low_error_word_zero_second_high (dim n) q U b h K
            (G.canonicalMinimumSource (M n) forms).restProduct a z firstError p r s t (not_lt.mp Hsecond)]
          simpa only [abs_zero] using hBd
      · rw [native_second_low_error_word_zero_first_high (dim n) q U b h K
          (G.canonicalMinimumSource (M n) forms).restProduct a z firstError p r s hs t ht (not_lt.mp Hfirst)]
        simpa only [abs_zero] using hBd
    · simpa only [abs_zero] using hBd
    · simpa only [abs_zero] using hBd
  have Hentry:=native_second_low_entry_four_average_abs_le T U hU ho hT
    (nativeSecondLowFirstMiddleIsFirst j) F hBd HF
  rw [←native_second_low_fixed_error_unobserved_class_eq_entry (dim n) q star U b h K T hU
    (G.canonicalMinimumSource (M n) forms).restProduct a z j firstError] at Hentry
  have Hmass:0≤partitionPoint 0 as U:=(partitionPoint_mem as ho U).1
  have Hpoly:(4*(rBound:ℝ)*(rBound+1)*(rBound+2)*(rBound+3))≤Prow:=by
    dsimp [Prow]
    gcongr <;> linarith
  have Hcp:Prow*Couter≤Cpay:=by dsimp [Cpay];nlinarith only [hProw]
  have Hnonneg:0≤(4*(rBound:ℝ)*(rBound+1)*(rBound+2)*(rBound+3))*
      partitionPoint 0 as U*Bd:=by positivity
  rw [abs_div,abs_of_pos (by norm_num:(0:ℝ) < 2)]
  calc
    _≤((4*(rBound:ℝ)*(rBound+1)*(rBound+2)*(rBound+3))*partitionPoint 0 as U*Bd)/2:=
      div_le_div_of_nonneg_right Hentry (by norm_num)
    _≤(4*(rBound:ℝ)*(rBound+1)*(rBound+2)*(rBound+3))*partitionPoint 0 as U*Bd:=by
      nlinarith only [Hnonneg]
    _≤Prow*partitionPoint 0 as U*Bd:=by gcongr
    _≤Prow*(Couter*W n)*Bd:=by gcongr
    _≤Cpay*W n*Bd:=by
      convert mul_le_mul_of_nonneg_right Hcp (mul_nonneg hW.le hBd) using 1 <;> ring
    _=W n*rate:=by dsimp [Bd];field_simp [hpay.ne']
    _=_:=by dsimp [rate];ring

end OAI.SKFluctuations.Cavity
