module

public import ComparisonSignedCavitySecondLowActualStarAtomSavingAlong
public import ComparisonSignedCavitySecondLowActualFixedErrorStarEntrySavingAlong
public import ComparisonSignedCavitySecondLowStarOnlyUnobservedBudgetAlong
public import ComparisonSignedCavitySecondLowActualStarOldCBaselinePointBudgetAlong
public import ComparisonSignedCavitySecondLowActualStarOccupiedOldCBaselineBudgetAlong
public import ComparisonActualHighOnlyLowB0UnobservedPhysicalSourceAlong
public import ComparisonActualHighOnlyLowSharpRadiusCompatibleSourceAlong

@[expose] public section
noncomputable section
set_option maxHeartbeats 70000000
set_option linter.unusedVariables false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal ENNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization ActualHighOnlyOverlapMinimum
open NativeOverlapMinimum (ActualSlowWindowChoice)
attribute [local instance] nativeSecondLowSlotFintype
attribute [local instance] Classical.propDecidable

theorem actual_second_low_star_error_atom_saving_along_high_only
    {m delta cl cu Az C0 Ct D Bclock Temp Tstar Lwin Cs Cf : ℝ}
    (aDegree rBound : ℕ) (Cmass Couter Cpay : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cmass)
    (hCouter : 0 ≤ Couter) (hCpay : 0 ≤ Cpay)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0)) (w : ℕ→ActualSlowWindowChoice)
    (Hsource : ∀ᶠn in atTop,ActualHighOnlySmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow_high_only (M n) (W n) Tstar Lwin Cs (w n)) :
    ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val ≤ 1)→(w n).star∈us→
      (∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs→
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS ((dim n)+1) (M n).bf (M n).hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (T : ClockTree (Spin (dim n)×Bool) as) (l t : ℝ),
          U ≤ as.length→star < U→partitionPoint 0 as U ≤ Couter*W n→
          l∈Icc (0:ℝ) 1→t∈Icc (0:ℝ) 1→T.leaves ≤ rBound→
        ∀(G : ActualNaturalBoundaryShape (dim n) aDegree T)
          (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x : ℝ),(M n).xs ≤ x→x ≤ W n→
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x (W n) initial e)→
        ∀(u z s0 w0 s1 w1 : T.Slot) (vOrd : ℝ),
          T.splitIndex u z=star→T.splitIndex s0 w0 < U→
          s0≠w0→s1≠w1→vOrd∈Icc (0:ℝ) 1→
          Cpay*|T.disorderExpect (fullWeight (dim n)) (fullFeature (dim n)) 0 (cutFullVariance (dim n) q U l t b h K)
            (nativeOldInitialRowProduct (dim n) T (G.canonicalHighOnlySource (M n) forms).restProduct
              (nativeSmallCutOldErrorRestKernel (dim n) U b h K) u z
              (fun i : Fin 2=>nativeSmallCutOrdinaryRestKernel (dim n) U b h K (![false,true] i) (![vOrd,0] i))
              ![s0,s1] ![w0,w1]) 0| ≤
            (((dim n)+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/32))*(M n).xs^2*
              sourceMonomialScale x (W n) initial := by
  obtain ⟨C,hC,HC⟩:=eventually_actual_minimum_inherited_second_low_actual_raw_atom_budget_high_only
    (D:=D) aDegree rBound Bclock Temp Cf Cmass hTemp hCf hCm
    hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cerr:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp
  have hCerr : 0 ≤ Cerr:=actualLowErrorComparisonConstant_nonneg _ hTemp
  let R:=Cpay*C*(1+Couter)*Cerr
  have hR : 0 ≤ R:=by dsimp [R];positivity
  have HR:=eventually_actual_sharp_star_original_low_radius_saving_along_high_only hm hdelta hC0
    R hR dim hdim M W hcanonical hWlim w hw
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hdim.eventually HC,HR,Hsource,HW,Hcutoff] with n hn hc hs hw1 hnCutoff
  have hxsW : (M n).xs ≤ W n:=by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have hW : 0 < W n:=(M n).hxs.trans_le hxsW
  intro L us hus hstar hret hmesh
  filter_upwards [hn (M n) hnCutoff.1 hnCutoff.2 hs (hxsW.trans hw1) L us hus hret hmesh,
    hc us hus hstar] with jGrid hgrid hsave
  dsimp only at hgrid hsave ⊢
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let rho:=nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as star+1/((dim n)+1:ℕ)
  have hrho : 0 ≤ rho:=add_nonneg (Real.sqrt_nonneg _) (by positivity)
  intro U T l t hU hstarU houter hl ht hT G forms initial x hxsx hxW hmass
    u z s0 w0 s1 w1 vOrd heq hOrd hne0 hne1 hv
  have Hraw:=hgrid U T l t hU hl ht hT G forms initial x (W n) hxsx hxW hmass
    u z (heq ▸ hstarU) s0 w0 s1 w1 vOrd hOrd hne0 hne1 hv
  rw [heq] at Hraw
  let p0:=sourceMonomialScale x (W n) initial
  have hp0 : 0 ≤ p0:=by
    dsimp [p0]
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>
      (source_factor_scale_pos ((M n).hxs.trans_le hxsx) hW initial e).le
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hnatural : 0 ≤ (M n).xs+partitionPoint 0 as (T.splitIndex s0 w0):=
    add_nonneg (M n).hxs.le (partitionPoint_mem as ho _).1
  have hsmall : (M n).xs+partitionPoint 0 as (T.splitIndex s0 w0) ≤ (1+Couter)*W n:=by
    have Hmass:=(partitionPoint_mono as ho hOrd.le).trans houter
    nlinarith only [hxsW,Hmass]
  change R*rho ≤ (((dim n)+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/32))*((M n).xs^2/W n) at hsave
  apply (mul_le_mul_of_nonneg_left Hraw hCpay).trans
  calc
    Cpay*(C*(Cerr*rho)*((M n).xs+partitionPoint 0 as (T.splitIndex s0 w0))*p0) ≤
        Cpay*(C*(Cerr*rho)*((1+Couter)*W n)*p0) := by gcongr
    _= (R*rho)*W n*p0 := by dsimp [R];ring
    _≤ ((((dim n)+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/32))*((M n).xs^2/W n))*W n*p0 := by gcongr
    _= _ := by dsimp [p0];field_simp [hW.ne']

def ActualSecondLowUnobservedFixedErrorStarEntrySavingOnEveryFinalNetAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (aDegree rBound : ℕ) (saving Cmass Couter : ℝ)
    (dim : ℕ→ℕ)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
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
            hU (G.canonicalHighOnlySource (M n) forms).restProduct a z j firstError/2|≤
            (((dim n)+1:ℕ):ℝ)^(-saving)*W n*(M n).xs^2*
              sourceMonomialScale x (W n) initial

theorem actual_second_low_unobserved_fixed_error_star_entry_saving_along_high_only
    {m delta cl cu Az C0 Ct D Bclock Temp Tstar Lwin Cs Cf : ℝ}
    (aDegree rBound : ℕ) (Cmass Couter : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCm : 0≤Cmass) (hCouter : 0≤Couter)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0)) (w : ℕ→ActualSlowWindowChoice)
    (Hsource : ∀ᶠn in atTop,ActualHighOnlySmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow_high_only (M n) (W n) Tstar Lwin Cs (w n)) :
    ActualSecondLowUnobservedFixedErrorStarEntrySavingOnEveryFinalNetAlong_high_only aDegree rBound
      (actualMassSavingExponent m delta/32) Cmass Couter dim M W w := by
  let Prow:ℝ:=4*(rBound+1)*(rBound+2)*(rBound+3)*(rBound+4)
  have hProw:0 < Prow:=by dsimp [Prow];positivity
  let Cpay:=Prow*(1+Couter)
  have hpay:0 < Cpay:=mul_pos hProw (by linarith)
  have HA:=actual_second_low_star_error_atom_saving_along_high_only aDegree (rBound+4) Cmass Couter Cpay
    hTemp hCf hCm hCouter hpay.le hm hdelta hroom hcl hcu hAz hC0 hCt
    dim hdim M W hcanonical hWlim w Hsource Hcutoff hw
  filter_upwards [HA,Hcutoff] with n hn hnCutoff
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
    (G.canonicalHighOnlySource (M n) forms).restProduct a z j firstError
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
          have HP:(Gfinal.canonicalHighOnlySource (M n) forms).restProduct=
              nativeSecondLowOldTest (G.canonicalHighOnlySource (M n) forms).restProduct p r s t:=by
            funext τ
            exact native_second_low_canonical_old_shape_rest_product_high_only (M n) G forms p hp r hr s hs t ht τ
          have HB:Cpay*|nativeSecondLowErrorWord (dim n) q U b h K
              (G.canonicalHighOnlySource (M n) forms).restProduct a z firstError p r s t|≤rate:=by
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
            (G.canonicalHighOnlySource (M n) forms).restProduct a z firstError p r s t (not_lt.mp Hsecond)]
          simpa only [abs_zero] using hBd
      · rw [native_second_low_error_word_zero_first_high (dim n) q U b h K
          (G.canonicalHighOnlySource (M n) forms).restProduct a z firstError p r s hs t ht (not_lt.mp Hfirst)]
        simpa only [abs_zero] using hBd
    · simpa only [abs_zero] using hBd
    · simpa only [abs_zero] using hBd
  have Hentry:=native_second_low_entry_four_average_abs_le T U hU ho hT
    (nativeSecondLowFirstMiddleIsFirst j) F hBd HF
  rw [←native_second_low_fixed_error_unobserved_class_eq_entry (dim n) q star U b h K T hU
    (G.canonicalHighOnlySource (M n) forms).restProduct a z j firstError] at Hentry
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

def ActualSecondLowStarOnlyUnobservedBudgetOnEveryFinalNetAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (aDegree rBound : ℕ) (saving Cmass Couter Cerr Cmoving : ℝ)
    (dim : ℕ→ℕ)
    (M : (n:ℕ) → ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ → ℝ) (w : ℕ → ActualSlowWindowChoice) : Prop :=
    ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val ≤ 1) → (w n).star∈us →
      (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (dim n+1) (M n).bf (M n).hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ → RestCoordinate (dim n) → ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (T : ClockTree (Spin (dim n)×Bool) as) (hU : U ≤ as.length),
          star<U → NativePersistentLowForks star star U T → T.leaves ≤ rBound →
          partitionPoint 0 as U ≤ Couter*W n →
        ∀(G : ActualNaturalBoundaryShape (dim n) aDegree T)
          (forms : Fin aDegree → NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x : ℝ),(M n).xs ≤ x → x ≤ W n →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x (W n) initial e) →
        ∀(a z : T.Slot),T.splitIndex a z=star →
          let p0:=sourceMonomialScale x (W n) initial
          let rho:=(M n).actualOriginalLowErrorDensitySaving (Couter+1)*(M n).xs^2+
            partitionPoint 0 as U/(dim n+1:ℕ)
          |∑j : Fin 8,nativeSecondLowClassLedger (dim n) q U b h K T hU
            (G.canonicalHighOnlySource (M n) forms).restProduct a z j false/2| ≤
            16*((dim n+1:ℕ):ℝ)^(-saving)*W n*(M n).xs^2*p0+
            Cmoving*W n*Cerr*rho*p0

theorem actual_second_low_star_only_unobserved_budget_along_high_only
    {m delta cl cu Az C0 Ct D Bclock Temp Tstar Lwin Cs Cf : ℝ}
    (aDegree rBound : ℕ) (Cmass Couter : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cmass) (hCouter : 0 ≤ Couter)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ) → ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0)) (w : ℕ → ActualSlowWindowChoice)
    (Hsource : ∀ᶠn in atTop,ActualHighOnlySmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow_high_only (M n) (W n) Tstar Lwin Cs (w n)) :
    ∃Cmoving : ℝ,0<Cmoving ∧
      ActualSecondLowStarOnlyUnobservedBudgetOnEveryFinalNetAlong_high_only aDegree rBound
        (actualMassSavingExponent m delta/32) Cmass Couter
        (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp) Cmoving dim M W w := by
  obtain ⟨Cm,hCmRate,HM⟩:=eventually_actual_minimum_inherited_second_low_unobserved_moving_entry_budget_high_only
    (D:=D) aDegree rBound Bclock Temp Cf Cmass Couter (Couter+1) hTemp hCf hCm hCouter (by linarith)
    hm hdelta hroom hcl hcu hAz hC0 hCt
  have HS:=actual_second_low_unobserved_fixed_error_star_entry_saving_along_high_only aDegree rBound Cmass Couter
    hTemp hCf hCm hCouter hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M W hcanonical hWlim w Hsource Hcutoff hw
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  refine ⟨16*Cm,mul_pos (by norm_num) hCmRate,?_⟩
  filter_upwards [hdim.eventually HM,HS,Hsource,HW1,Hcutoff] with n hnM hnS hnSource hnW hnCutoff
  have hxs:(M n).xs≤1:=((M n).canonical_direct_test_band_ge_scale.trans_eq (hcanonical n).symm).trans hnW
  intro L us hus hstar hret hmesh
  filter_upwards [hnM (M n) hnCutoff.1 hnCutoff.2 hnSource hxs L us hus hret hmesh,
    hnS L us hus hstar hret hmesh] with jGrid hgridM hgridS
  dsimp only at hgridM hgridS ⊢
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
  let K:=fun j=>h j+b j*orderedPathS (dim n+1) (M n).bf (M n).hf (partitionPoint 0 as j)
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  intro U T hU hstarU hpersistent hT houter G forms initial x hxsx hxW hmass a z hsplit
  have ho:MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have haz:T.splitIndex a z<U:=hsplit ▸ hstarU
  have hW:0<W n:=(M n).hxs.trans_le (hxsx.trans hxW)
  have hdensity:partitionPoint 0 as U≤ min ((Couter+1)*(M n).canonicalDirectTestBandScale) 1:=by
    apply le_min
    · rw [←hcanonical n];nlinarith only [houter,hW]
    · exact (partitionPoint_mem as ho U).2
  let P:=(G.canonicalHighOnlySource (M n) forms).restProduct
  let p0:=sourceMonomialScale x (W n) initial
  let starRate:=((dim n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/32))*W n*(M n).xs^2*p0
  let rho:=(M n).actualOriginalLowErrorDensitySaving (Couter+1)*(M n).xs^2+partitionPoint 0 as U/(dim n+1:ℕ)
  let movingRate:=Cm*W n*actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*rho*p0
  have Hpoint (j : Fin 8):|nativeSecondLowClassLedger (dim n) q U b h K T hU P a z j false/2|≤
      2*starRate+2*movingRate:=by
    have BS1:=hgridS U T hU hT hstarU houter G forms initial x hxsx hxW hmass a z haz j true
    have BS2:=hgridS U T hU hT hstarU houter G forms initial x hxsx hxW hmass a z haz j false
    have BM1:=hgridM star star U T hU le_rfl hstarU hpersistent hT G forms initial x (W n)
      hxsx hxW hmass houter hdensity a z haz j true
    have BM2:=hgridM star star U T hU le_rfl hstarU hpersistent hT G forms initial x (W n)
      hxsx hxW hmass houter hdensity a z haz j false
    rw [native_second_low_original_unobserved_class_eq_star_moving (dim n) q star U b h K T ho hU P a z j]
    simp only [add_div]
    apply (abs_add_le _ _).trans
    apply (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
      (add_le_add BS1 BS2)) BM1)) BM2).trans_eq
    dsimp [starRate,movingRate,rho,P,p0,K,q,b,h,as]
    ring
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply (Finset.sum_le_sum (fun j _=>Hpoint j)).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  dsimp [starRate,movingRate,rho,P,p0,K,q,b,h,as]
  ring

theorem actual_second_low_star_old_c_baseline_point_budget_along_high_only
    {m delta cl cu Az C0 Ct D Bclock Temp Cf Tstar Lwin Cs : ℝ}
    (degree rBound : ℕ) (Cmass Couter : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCm : 0≤Cmass) (hCouter : 0≤Couter)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0)) (w : ℕ→ActualSlowWindowChoice)
    (HS : ∀ᶠn in atTop,ActualHighOnlySmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow_high_only (M n) (W n) Tstar Lwin Cs (w n)) :
    ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val≤1)→(w n).star∈us→
      (∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹≤(M n).xs→
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
        let K:=fun j=>h j+b j*orderedPathS (dim n+1) (M n).bf (M n).hf (partitionPoint 0 as j)
        let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (T : ClockTree (Spin (dim n)×Bool) as),
          U≤as.length→star<U→T.leaves≤rBound→
          partitionPoint 0 as U≤Couter*W n→
        ∀(G : ActualNaturalBoundaryShape (dim n) degree T) (forms : Fin degree→NativeSourceFactorForm)
          (initial : Finset (Fin degree)) (x : ℝ),(M n).xs≤x→x≤W n→
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x (W n) initial e)→
        ∀(f c z : T.Slot),f≠z→
          T.splitIndex f c=star→T.splitIndex c z=star→
          let p0:=sourceMonomialScale x (W n) initial
          |T.cavityLeft.disorderExpect (restWeight (dim n)) (restFeature (dim n)) 0 q
            (nativeSecondLowUnweightedCOldPayload (dim n) U b h K T f c z
              (G.canonicalHighOnlySource (M n) forms).restProduct) 0|≤
            2*((dim n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/32))*(M n).xs^2*p0 := by
  have Hstar:=actual_second_low_star_error_atom_saving_along_high_only degree rBound Cmass Couter 1
    hTemp hCf hCm hCouter zero_le_one hm hdelta hroom hcl hcu hAz hC0 hCt
    dim hdim M W hcanonical hWlim w HS Hcutoff hw
  filter_upwards [Hstar,Hcutoff] with n hnStar hnCutoff
  intro L us hus hstar hret hmesh
  filter_upwards [hnStar L us hus hstar hret hmesh] with jGrid hgridStar
  dsimp only at hgridStar ⊢
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
  let K:=fun j=>h j+b j*orderedPathS (dim n+1) (M n).bf (M n).hf (partitionPoint 0 as j)
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  intro U T hU hstarU hT houter G forms initial x hxsx hxW hmass f c z Hfz Hfc Hcz
  have ho:MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have Hfs:T.splitIndex f c<U:=Hfc ▸ hstarU
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
  rw [native_second_low_old_c_baseline_expect_eq_error_atoms (dim n) q U b h K T ho]
  apply (abs_add_le _ _).trans
  simpa only [nativeSecondLowOldCBaselineErrorAtom,ite_true,Bool.false_eq_true,ite_false,two_mul,add_mul]
    using add_le_add B1 B2

private theorem old_c_weight_abs_le {α : Type} (L : List α) (w F : α→ℝ)
    {B : ℝ} (H : ∀x∈L,|F x|≤B) :
    |(L.map (fun x=>w x*F x)).sum|≤(L.map (fun x=>|w x|)).sum*B := by
  induction L with
  | nil=>simp
  | cons x L ih=>
    simp only [List.map_cons,List.sum_cons,add_mul]
    exact (abs_add_le _ _).trans (add_le_add
      (by rw [abs_mul];exact mul_le_mul_of_nonneg_left (H x List.mem_cons_self) (abs_nonneg _))
      (ih (fun y hy=>H y (List.mem_cons_of_mem _ hy))))

private theorem old_c_filtered_nonneg_sum_le {α : Type} (L : List α) (P : α→Bool)
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

private theorem old_c_HIGH_variation {S : Type} {as : List PositiveMass}
    (T : ClockTree S as) (ho : MassOrdered 0 as) (a : T.Slot) (U rBound : ℕ) (hT : T.leaves≤rBound) :
    ((nativeHighMarkedRows T a (U-1) 0).map (fun p=>|p.coeff|)).sum≤2*(rBound:ℝ) := by
  rw [nativeHighMarkedRows_eq_filter]
  apply (old_c_filtered_nonneg_sum_le (T.markedAttach 0)
    (fun p=>decide (U-1<p.tree.splitIndex (p.embed a) p.mark)) _ (fun p _=>abs_nonneg p.coeff)).trans
  rw [T.markedAttach_variation ho,sub_zero]
  exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hT) (by norm_num)

theorem actual_second_low_star_occupied_old_c_baseline_budget_along_high_only
    {m delta cl cu Az C0 Ct D Bclock Temp Cf Tstar Lwin Cs : ℝ}
    (degree rBound : ℕ) (Cmass Couter : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCm : 0≤Cmass) (hCouter : 0≤Couter)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0)) (w : ℕ→ActualSlowWindowChoice)
    (HS : ∀ᶠn in atTop,ActualHighOnlySmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow_high_only (M n) (W n) Tstar Lwin Cs (w n)) :
    ∃Cstar : ℝ,0<Cstar ∧ ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val≤1)→(w n).star∈us→
      (∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹≤(M n).xs→
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
        let K:=fun j=>h j+b j*orderedPathS (dim n+1) (M n).bf (M n).hf (partitionPoint 0 as j)
        let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (T : ClockTree (Spin (dim n)×Bool) as) (hU : U≤as.length),
          star<U→T.leaves≤rBound→NativePersistentLowForks star star U T→
          partitionPoint 0 as U≤Couter*W n→
        ∀(G : ActualNaturalBoundaryShape (dim n) degree T) (forms : Fin degree→NativeSourceFactorForm)
          (initial : Finset (Fin degree)) (x : ℝ),(M n).xs≤x→x≤W n→
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x (W n) initial e)→∀s:T.Slot,
          let p0:=sourceMonomialScale x (W n) initial
          |nativeSecondLowFreshOccupiedOldCBaselineSource (dim n) q U b h K T s star hU
            (G.canonicalHighOnlySource (M n) forms).restProduct|≤
            Cstar*((dim n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/32))*W n*(M n).xs^2*p0 := by
  have H:=actual_second_low_star_old_c_baseline_point_budget_along_high_only degree (rBound+2) Cmass Couter
    hTemp hCf hCm hCouter hm hdelta hroom hcl hcu hAz hC0 hCt
    dim hdim M W hcanonical hWlim w HS Hcutoff hw
  let Poly:ℝ:=2*(rBound+1)^2
  have hPoly:0<Poly:=by dsimp [Poly];positivity
  refine ⟨2*Poly*(1+Couter),by positivity,?_⟩
  filter_upwards [H,Hcutoff] with n hn hnCutoff
  intro L us hus hstar hret hmesh
  filter_upwards [hn L us hus hstar hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
  let K:=fun j=>h j+b j*orderedPathS (dim n+1) (M n).bf (M n).hf (partitionPoint 0 as j)
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  intro U T hU hstarU hT hpersistent houter G forms initial x hxsx hxW hmass s
  let g:=nativeFreshAtSlot T 0 s star
  have hgMem:g∈T.markedAttach 0:=nativeFreshAtSlot_mem T 0 s star
  let Gg:=G.retainOnMarked 0 g hgMem
  let P:=(G.canonicalHighOnlySource (M n) forms).restProduct
  let Pg:=fun old=>P (g.restRestrict old)
  have hgLeaves:g.tree.leaves≤rBound+1:=
    (T.markedAttach_leaves 0 g hgMem).trans (Nat.add_le_add_right hT 1)
  let p0:=sourceMonomialScale x (W n) initial
  let rate:=((dim n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/32))*(M n).xs^2*p0
  let B:=2*rate
  have hW:0<W n:=(M n).hxs.trans_le (hxsx.trans hxW)
  have hp0:0≤p0:=by
    dsimp [p0]
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>
      (source_factor_scale_pos ((M n).hxs.trans_le hxsx) hW initial e).le
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
    have HP:(Gp.canonicalHighOnlySource (M n) forms).restProduct=(fun old=>Pg (p.restRestrict old)):=by
      funext τ
      exact (Gg.retained_canonical_restProduct_high_only (M n) forms 0 p hpMem τ).trans
        (G.retained_canonical_restProduct_high_only (M n) forms 0 g hgMem (p.restRestrict τ))
    have Hmass:∀e,Gp.sourceLowMass e≤Cmass*sourceFactorScale x (W n) initial e:=by
      intro e
      rw [ActualNaturalBoundaryShape.retained_source_mass,ActualNaturalBoundaryShape.retained_source_mass]
      exact hmass e
    have Hcuts:=native_second_low_fresh_occupied_old_c_equal_LOW_cuts T s star star U hU
      le_rfl hstarU hpersistent block p hp
    have Hfz:p.mark≠p.embed g.mark:=native_second_low_low_slots_ne p.tree U hU _ _
      ((native_second_low_fresh_HIGH_mark_tooth_split_eq_star T s star U hU hstarU p hp).trans_lt hstarU)
    have Hboth:p.tree.splitIndex p.mark (p.embed (nativeSecondLowOccupiedBlockRepresentative g.tree U hU block.val))=star ∧
        p.tree.splitIndex (p.embed (nativeSecondLowOccupiedBlockRepresentative g.tree U hU block.val)) (p.embed g.mark)=star:=by
      rcases Hcuts with H|H <;> exact H
    have HH:=hgrid U p.tree hU hstarU hpLeaves houter Gp forms initial x
      hxsx hxW Hmass p.mark (p.embed (nativeSecondLowOccupiedBlockRepresentative g.tree U hU block.val))
      (p.embed g.mark) Hfz Hboth.1 Hboth.2
    rw [HP] at HH
    simpa only [B,rate,p0,q,b,h,K,as,mul_assoc] using HH
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
    have HH:=old_c_weight_abs_le (nativeHighMarkedRows g.tree (g.embed s) (U-1) 0)
      (fun p=>p.coeff) _ Hnorm
    simp_rw [mul_assoc] at HH ⊢
    apply HH.trans
    convert mul_le_mul_of_nonneg_right (old_c_HIGH_variation g.tree ho (g.embed s) U (rBound+1) hgLeaves)
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
  convert Hstar using 1; dsimp only [B,rate,p0,q,b,h,K,as]; ring

end OAI.SKFluctuations.Cavity
