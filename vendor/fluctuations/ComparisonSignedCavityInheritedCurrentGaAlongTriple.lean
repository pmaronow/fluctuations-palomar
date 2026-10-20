module

public import ComparisonSignedCavityActualPairedIncomingSourceErrorRate
public import ComparisonSignedCavityActualPairedStarIncomingSourceErrorRate
public import ComparisonSignedCavityActualTripleIncomingRate
public import ComparisonSignedCavityActualTriplePowerRate
public import ComparisonSignedCavityActualTripleStarIncomingRate
public import ComparisonSignedCavityEventuallyInheritedTripleAllRates
public import ComparisonSignedCavityInheritedCurrentGaAlongProducts

@[expose] public section

noncomputable section
set_option maxHeartbeats 30000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity LaplaceWindowFormalization NativeOverlapMinimum
variable {dim : ℕ→ℕ}

theorem actual_canonical_paired_incoming_source_error_from_products_along
    {m delta cl cu Az C0 Ct D Bclock eta saving Cmass Cp Ch : ℝ} {a b d : ℕ}
    {Cpower Cbase : ℕ→ℝ}
    {M : (n:ℕ)→NativeOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice}
    (HI : ActualCanonicalIncomingSourceErrorProductOnEveryFinalNetAlong a 0 d eta saving Cmass Cp Ch M W w)
    (HP : ∀j,ActualCanonicalPowerSourceErrorProductOnEveryFinalNetAlong b j (d-1-j) eta saving Cmass
      (Cpower j) (Cbase j) M W w) :
    ActualCanonicalPairedIncomingSourceErrorOnEveryFinalNetAlong a b d eta saving Cmass Cp Ch Cpower Cbase M W w := by
  have HPfin:=Filter.eventually_all.mpr (fun j : Fin d=>HP j.val)
  filter_upwards [HI,HPfin] with n hnI hnP
  intro L us hus hret hmesh hstar
  have HPgrid:=Filter.eventually_all.mpr (fun j : Fin d=>hnP j L us hus hret hmesh hstar)
  filter_upwards [hnI L us hus hret hmesh hstar,HPgrid] with r hrI hrP
  dsimp only at hrI hrP ⊢
  intro pre mid tail hcut hindex hmass T G forms initial x hxsx hxW hG G₀ forms₀ initial₀ hG₀
    s E e t hst c e₀ hc he B hdiff v hWv hvr hlow hz e₁ e₂ hef error herror F hF
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus r
  have H:=E.paired_incoming_i_error_allocation ho c e₀ t e hc he
    (G₀.canonicalMinimumSource (M n) forms₀).restProduct B F error hF hdiff d
    (orderedPathS ((dim n)+1) (M n).bf (M n).hf (w n).star.val)
  rw [add_mul,Finset.sum_mul]
  apply (congrArg abs H).le.trans
  apply (abs_add_le _ _).trans
  apply add_le_add
  · have HIn:=hrI pre mid tail hcut hindex hmass T G forms initial x
      hxsx hxW hG s E.toNativeCanonicalExteriorSource e t hst v hWv hvr hlow hz e₁ e₂ hef error herror
    simp only [Nat.zero_add] at HIn
    convert HIn using 1
    congr 3
  · apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro j hj
    have hJ : j<d:=Finset.mem_range.mp hj
    have HJ:=hrP ⟨j,hJ⟩ pre mid tail hcut hindex hmass T G₀ forms₀ initial₀ x hxsx hxW hG₀
      a (G.canonicalMinimumSource (M n) forms) s E.toNativeCanonicalExteriorSource t hst v hWv hvr hlow hz e₁ e₂ hef error herror
    have hpow : j+(d-1-j)=d-1 := by omega
    rw [hpow] at HJ
    convert HJ using 1
    congr 3

theorem actual_canonical_paired_star_incoming_source_error_from_products_along
    {m delta cl cu Az C0 Ct D Bclock eta saving Cmass Cp Ch : ℝ} {a b d : ℕ}
    {Cpower Cbase : ℕ→ℝ}
    {M : (n:ℕ)→NativeOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice}
    (HI : ActualCanonicalStarIncomingSourceErrorProductOnEveryFinalNetAlong a 0 d eta saving Cmass Cp Ch M W w)
    (HP : ∀j,ActualCanonicalPowerSourceErrorProductOnEveryFinalNetAlong b j (d-1-j) eta saving Cmass
      (Cpower j) (Cbase j) M W w) :
    ActualCanonicalPairedStarIncomingSourceErrorOnEveryFinalNetAlong a b d eta saving Cmass Cp Ch Cpower Cbase M W w := by
  have HPfin:=Filter.eventually_all.mpr (fun j : Fin d=>HP j.val)
  filter_upwards [HI,HPfin] with n hnI hnP
  intro L us hus hret hmesh hstar
  have HPgrid:=Filter.eventually_all.mpr (fun j : Fin d=>hnP j L us hus hret hmesh hstar)
  filter_upwards [hnI L us hus hret hmesh hstar,HPgrid] with r hrI hrP
  dsimp only at hrI hrP ⊢
  intro pre mid tail hcut hindex hmass T G forms initial x hxsx hxW hG G₀ forms₀ initial₀ hG₀
    s E e t hst c e₀ hc he B hdiff v hWv hvr hlow hz e₁ e₂ hef error herror F hF
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus r
  have H:=E.paired_incoming_star_error_allocation ho c e₀ t e hc he
    (G₀.canonicalMinimumSource (M n) forms₀).restProduct B F error hF hdiff d
    (orderedPathS ((dim n)+1) (M n).bf (M n).hf (w n).star.val)
  rw [add_mul,Finset.sum_mul]
  apply (congrArg abs H).le.trans
  apply (abs_add_le _ _).trans
  apply add_le_add
  · have HIn:=hrI pre mid tail hcut hindex hmass T G forms initial x
      hxsx hxW hG s E.toNativeCanonicalExteriorSource e t hst v hWv hvr hlow hz e₁ e₂ hef error herror
    simp only [Nat.zero_add] at HIn
    convert HIn using 1
    congr 3
  · apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro j hj
    have hJ : j<d:=Finset.mem_range.mp hj
    have HJ:=hrP ⟨j,hJ⟩ pre mid tail hcut hindex hmass T G₀ forms₀ initial₀ x hxsx hxW hG₀
      a (G.canonicalMinimumSource (M n) forms) s E.toNativeCanonicalExteriorSource t hst v hWv hvr hlow hz e₁ e₂ hef error herror
    have hpow : j+(d-1-j)=d-1 := by omega
    rw [hpow] at HJ
    convert HJ using 1
    congr 3

theorem actual_generated_triple_incoming_error_from_canonical_along
    {m delta cl cu Az C0 Ct D Bclock eta saving Cmass Cp Ch : ℝ} {a b d : ℕ}
    {Cpower Cbase : ℕ→ℝ}
    {M : (n:ℕ)→NativeOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice}
    (hCp : 0 ≤ Cp) (hCh : 0 ≤ Ch) (hC : ∀j,0 ≤ Cpower j ∧ 0 ≤ Cbase j)
    (H : ActualCanonicalPairedIncomingSourceErrorOnEveryFinalNetAlong a b d eta saving Cmass Cp Ch Cpower Cbase M W w) :
    ActualGeneratedTripleIncomingErrorOnEveryFinalNetAlong a b d eta saving Cmass Cp Ch Cpower Cbase M W w := by
  filter_upwards [H] with n hn
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar] with r hr
  dsimp only at hr ⊢
  intro pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht ha hb e₀ hIn hi x hxsx hxW hmi
    p hp rr hrr zz hzz hpH hrH hzH hef v hWv hvr hlow hz
  subst a
  subst b
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus r
  have hlen : pre.length+mid.length<(pre++(mid++tail)).length:=
    hU.trans_le (hpH.trans (p.tree.splitIndex_le_clockLength _ _))
  let G:=(((nativeGeneratedExteriorShape (dim n) P.live.test P.live.ancestry (by omega) hlen).retainOnMarked 0 p hp).retainOnMarked 0 rr hrr).retainOnMarked 0 zz hzz
  let G₀:=(((nativeGeneratedCompleteShape (dim n) P.live.test P.live.ancestry (by omega) hlen).retainOnMarked 0 p hp).retainOnMarked 0 rr hrr).retainOnMarked 0 zz hzz
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim
    (fun _=>((M n).bf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
    (fun _=>((M n).hf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
  let center:=orderedPathS ((dim n)+1) (M n).bf (M n).hf (w n).star.val
  obtain ⟨E,t,e,f,i₀,htRead,heRead,hfRead,hiRead,hsplit,Hlaw⟩:=
    native_actual_triple_reset_incoming_i_error_source (dim n) pre mid tail hP hmid hU ht e₀ hIn hi
      p hp rr hrr zz hzz hpH hrH hzH ho (M n) 0 q 0 d center
  have hG (j) : G.sourceLowMass j ≤ Cmass*sourceFactorScale x (W n)
      (nativeGeneratedExteriorInitial P.live.test pre.length) j := by
    simp only [G,ActualNaturalBoundaryShape.retained_source_mass]
    exact native_generated_exterior_source_mass (dim n) P.live.test P.live.ancestry (by omega) hlen Cmass x (W n)
      (by simpa only [hcut] using hmi) (by simpa only [hcut] using hmass) j
  have hG₀ (j) : G₀.sourceLowMass j ≤ Cmass*sourceFactorScale x (W n)
      (nativeGeneratedCompleteInitial P.live.test pre.length) j := by
    simp only [G₀,ActualNaturalBoundaryShape.retained_source_mass]
    exact native_generated_complete_source_mass (dim n) P.live.test P.live.ancestry (by omega) hlen
      Cmass x (W n) (by simpa only [hcut] using hmi) (by simpa only [hcut] using hmass) j
  have hraw : 0 ≤ (M n).xs+partitionPoint 0 (finiteCutMasses us r)
      (zz.tree.splitIndex (zz.embed rr.mark) zz.mark) :=
    add_nonneg (M n).hxs.le (partitionPoint_mem _ (finiteCutMasses_ordered us hus r) _).1
  by_cases hst : E.target=t
  · rw [←hst] at Hlaw
    simp only [native_two_level_incoming_error_product_self,native_two_level_power_error_product_self,
      integral_zero,Finset.sum_const_zero,add_zero] at Hlaw
    have hzero : nativeTripleResetPairedErrorValue (dim n) T P.live.test (M n) p rr zz q d center=0 := by
      simp only [native_generated_triple_canonical_rest_product] at Hlaw
      unfold nativeTripleResetPairedErrorValue nativeStarSuffixClock
      simpa only [MarkedPlacement.restRestrict_at,MarkedPlacement.restSpin] using Hlaw
    rw [hzero,abs_zero]
    apply mul_nonneg _ hraw
    have hx:0 ≤ x:=(M n).hxs.le.trans hxsx
    have hW:0 ≤ W n:=hx.trans hxW
    have hs : 0 ≤ (M n).xs+partitionPoint 0 (finiteCutMasses us r) pre.length :=
      add_nonneg (M n).hxs.le (partitionPoint_mem _ (finiteCutMasses_ordered us hus r) _).1
    apply native_reset_paired_budget_nonneg (dim n) _ _ d eta saving hCp hCh hC (M n).hxs.le hW
      (hW.trans hWv) hs <;> unfold sourceMonomialScale <;> positivity
  · have had:=comparisonVariableEndpoint_clocks_admissible (M n).context.hc (M n).context.hk (M n).context.hkc
      (M n).context.hm (M n).context.hM (M n).b (M n).h (M n).context.hd.ne' (M n).hlam.le
      (M n).hlb (M n).hb (M n).hh (M n).hh0 (M n).alpha
    have Hcenter:=native_ordered_source_center_eq_completed (dim n) (M n).bf (M n).hf
      (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1)
      (partitionPoint_mem (pre++(mid++tail)) ho (zz.tree.splitIndex (zz.embed rr.mark) zz.mark))
    have Hbound:=hr pre mid tail hcut hindex hmass zz.tree G (fun _=>NativeSourceFactorForm.centered)
      (nativeGeneratedExteriorInitial P.live.test pre.length) x hxsx hxW hG
      G₀ (fun _=>NativeSourceFactorForm.centered) (nativeGeneratedCompleteInitial P.live.test pre.length) hG₀
      (zz.tree.cavityLeftSlot (zz.embed (rr.embed (p.embed P.live.test.target)))) E i₀ t hst
      (zz.tree.cavityLeftSlot (zz.embed (rr.embed p.mark)))
      (zz.tree.cavityLeftSlot (zz.embed (rr.embed (p.embed e₀)))) htRead hiRead _
      (fun σ=>native_generated_triple_reset_change (dim n) P.live.test P.live.ancestry ht (by omega) hlen
        e₀ hIn (M n) p hp rr hrr zz hzz σ) v hWv
      (by simpa only [hsplit,(rr.tree.markedAttach_embed_preserves 0 zz hzz).2,
        (p.tree.markedAttach_embed_preserves 0 rr hrr).2] using hvr) hlow hz
      (zz.tree.cavityLeftSlot (zz.embed rr.mark)) (zz.tree.cavityLeftSlot zz.mark)
      (fun H=>hef (zz.tree.cavityLeftSlot.injective H))
      (fun δ=>deletedOverlap (dim n) (joinSpin (E.D.atSlot δ e,false)) (joinSpin (E.D.atSlot δ f,false))-
        pathPairMoment (uniformWeight ((dim n)+1)) (finiteFeature ((dim n)+1))
          (completedPathClock ((dim n)+1) (M n).bf (M n).hf) (orderedOverlap ((dim n)+1))
          (partitionPoint 0 (pre++(mid++tail)) (zz.tree.splitIndex (zz.embed rr.mark) zz.mark)))
      (fun η ζ δ=>by simp only [heRead,hfRead,cavityLeft_splitIndex,←hcut,Hcenter])
      (fun σ=>deletedOverlap (dim n)
        (joinSpin (zz.tree.cavityLeft.atSlot σ (zz.tree.cavityLeftSlot (zz.embed rr.mark)),false))
        (joinSpin (zz.restSpin σ,false))-
        pathPairMoment (uniformWeight ((dim n)+1)) (finiteFeature ((dim n)+1))
          (completedPathClock ((dim n)+1) (M n).bf (M n).hf) (orderedOverlap ((dim n)+1))
          (partitionPoint 0 (pre++(mid++tail)) (zz.tree.splitIndex (zz.embed rr.mark) zz.mark)))
      (fun η ζ δ=>by simp only [MarkedPlacement.restSpin,heRead,hfRead])
    dsimp only [G₀] at Hbound
    unfold nativeStarSuffixClock at Hbound
    unfold nativeTripleResetPairedErrorValue nativeResetPairedBudget nativeStarSuffixClock
    simpa only [
      native_generated_triple_canonical_rest_product,MarkedPlacement.restRestrict_at,
      MarkedPlacement.restSpin,cavityLeft_splitIndex] using Hbound

theorem actual_generated_triple_star_incoming_error_from_canonical_along
    {m delta cl cu Az C0 Ct D Bclock eta saving Cmass Cp Ch : ℝ} {a b d : ℕ}
    {Cpower Cbase : ℕ→ℝ}
    {M : (n:ℕ)→NativeOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice}
    (hCp : 0 ≤ Cp) (hCh : 0 ≤ Ch) (hC : ∀j,0 ≤ Cpower j ∧ 0 ≤ Cbase j)
    (H : ActualCanonicalPairedStarIncomingSourceErrorOnEveryFinalNetAlong a b d eta saving Cmass Cp Ch Cpower Cbase M W w) :
    ActualGeneratedTripleStarIncomingErrorOnEveryFinalNetAlong a b d eta saving Cmass Cp Ch Cpower Cbase M W w := by
  filter_upwards [H] with n hn
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar] with r hr
  dsimp only at hr ⊢
  intro pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht ha hb e₀ hIn hi x hxsx hxW hmi
    p hp rr hrr zz hzz hpH hrH hzH hef v hWv hvr hlow hz
  subst a
  subst b
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus r
  have hlen : pre.length+mid.length<(pre++(mid++tail)).length:=
    hU.trans_le (hpH.trans (p.tree.splitIndex_le_clockLength _ _))
  let G:=(((nativeGeneratedExteriorShape (dim n) P.live.test P.live.ancestry (by omega) hlen).retainOnMarked 0 p hp).retainOnMarked 0 rr hrr).retainOnMarked 0 zz hzz
  let G₀:=(((nativeGeneratedCompleteShape (dim n) P.live.test P.live.ancestry (by omega) hlen).retainOnMarked 0 p hp).retainOnMarked 0 rr hrr).retainOnMarked 0 zz hzz
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim
    (fun _=>((M n).bf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
    (fun _=>((M n).hf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
  let center:=orderedPathS ((dim n)+1) (M n).bf (M n).hf (w n).star.val
  obtain ⟨E,t,e,f,i₀,htRead,heRead,hfRead,hiRead,hsplit,Hlaw⟩:=
    native_actual_triple_reset_incoming_star_error_source (dim n) pre mid tail hP hmid hU ht e₀ hIn hi
      p hp rr hrr zz hzz hpH hrH hzH ho (M n) 0 q 0 d center
  have hG (j) : G.sourceLowMass j ≤ Cmass*sourceFactorScale x (W n)
      (nativeGeneratedExteriorInitial P.live.test pre.length) j := by
    simp only [G,ActualNaturalBoundaryShape.retained_source_mass]
    exact native_generated_exterior_source_mass (dim n) P.live.test P.live.ancestry (by omega) hlen Cmass x (W n)
      (by simpa only [hcut] using hmi) (by simpa only [hcut] using hmass) j
  have hG₀ (j) : G₀.sourceLowMass j ≤ Cmass*sourceFactorScale x (W n)
      (nativeGeneratedCompleteInitial P.live.test pre.length) j := by
    simp only [G₀,ActualNaturalBoundaryShape.retained_source_mass]
    exact native_generated_complete_source_mass (dim n) P.live.test P.live.ancestry (by omega) hlen
      Cmass x (W n) (by simpa only [hcut] using hmi) (by simpa only [hcut] using hmass) j
  have hraw : 0 ≤ (M n).xs+partitionPoint 0 (finiteCutMasses us r)
      (zz.tree.splitIndex (zz.embed rr.mark) zz.mark) :=
    add_nonneg (M n).hxs.le (partitionPoint_mem _ (finiteCutMasses_ordered us hus r) _).1
  by_cases hst : E.target=t
  · rw [←hst] at Hlaw
    simp only [native_two_level_star_incoming_error_product_self,native_two_level_power_error_product_self,
      integral_zero,Finset.sum_const_zero,add_zero] at Hlaw
    have hzero : nativeTripleResetPairedErrorValue (dim n) T P.live.test (M n) p rr zz q d center=0 := by
      simp only [native_generated_triple_canonical_rest_product] at Hlaw
      unfold nativeTripleResetPairedErrorValue nativeStarSuffixClock
      simpa only [MarkedPlacement.restRestrict_at,MarkedPlacement.restSpin] using Hlaw
    rw [hzero,abs_zero]
    apply mul_nonneg _ hraw
    have hx:0 ≤ x:=(M n).hxs.le.trans hxsx
    have hW:0 ≤ W n:=hx.trans hxW
    have hs : 0 ≤ (M n).xs+partitionPoint 0 (finiteCutMasses us r) (pre.length+mid.length) :=
      add_nonneg (M n).hxs.le (partitionPoint_mem _ (finiteCutMasses_ordered us hus r) _).1
    apply native_reset_paired_budget_nonneg (dim n) _ _ d eta saving hCp hCh hC (M n).hxs.le hW
      (hW.trans hWv) hs <;> unfold sourceMonomialScale <;> positivity
  · have had:=comparisonVariableEndpoint_clocks_admissible (M n).context.hc (M n).context.hk (M n).context.hkc
      (M n).context.hm (M n).context.hM (M n).b (M n).h (M n).context.hd.ne' (M n).hlam.le
      (M n).hlb (M n).hb (M n).hh (M n).hh0 (M n).alpha
    have Hcenter:=native_ordered_source_center_eq_completed (dim n) (M n).bf (M n).hf
      (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1)
      (partitionPoint_mem (pre++(mid++tail)) ho (zz.tree.splitIndex (zz.embed rr.mark) zz.mark))
    have Hbound:=hr pre mid tail hcut hindex hmass zz.tree G (fun _=>NativeSourceFactorForm.centered)
      (nativeGeneratedExteriorInitial P.live.test pre.length) x hxsx hxW hG
      G₀ (fun _=>NativeSourceFactorForm.centered) (nativeGeneratedCompleteInitial P.live.test pre.length) hG₀
      (zz.tree.cavityLeftSlot (zz.embed (rr.embed (p.embed P.live.test.target)))) E i₀ t hst
      (zz.tree.cavityLeftSlot (zz.embed (rr.embed p.mark)))
      (zz.tree.cavityLeftSlot (zz.embed (rr.embed (p.embed e₀)))) htRead hiRead _
      (fun σ=>native_generated_triple_reset_change (dim n) P.live.test P.live.ancestry ht (by omega) hlen
        e₀ hIn (M n) p hp rr hrr zz hzz σ) v hWv
      (by simpa only [hsplit,(rr.tree.markedAttach_embed_preserves 0 zz hzz).2,
        (p.tree.markedAttach_embed_preserves 0 rr hrr).2] using hvr) hlow hz
      (zz.tree.cavityLeftSlot (zz.embed rr.mark)) (zz.tree.cavityLeftSlot zz.mark)
      (fun H=>hef (zz.tree.cavityLeftSlot.injective H))
      (fun δ=>deletedOverlap (dim n) (joinSpin (E.D.atSlot δ e,false)) (joinSpin (E.D.atSlot δ f,false))-
        pathPairMoment (uniformWeight ((dim n)+1)) (finiteFeature ((dim n)+1))
          (completedPathClock ((dim n)+1) (M n).bf (M n).hf) (orderedOverlap ((dim n)+1))
          (partitionPoint 0 (pre++(mid++tail)) (zz.tree.splitIndex (zz.embed rr.mark) zz.mark)))
      (fun η ζ δ=>by simp only [heRead,hfRead,cavityLeft_splitIndex,←hcut,Hcenter])
      (fun σ=>deletedOverlap (dim n)
        (joinSpin (zz.tree.cavityLeft.atSlot σ (zz.tree.cavityLeftSlot (zz.embed rr.mark)),false))
        (joinSpin (zz.restSpin σ,false))-
        pathPairMoment (uniformWeight ((dim n)+1)) (finiteFeature ((dim n)+1))
          (completedPathClock ((dim n)+1) (M n).bf (M n).hf) (orderedOverlap ((dim n)+1))
          (partitionPoint 0 (pre++(mid++tail)) (zz.tree.splitIndex (zz.embed rr.mark) zz.mark)))
      (fun η ζ δ=>by simp only [MarkedPlacement.restSpin,heRead,hfRead])
    dsimp only [G₀] at Hbound
    unfold nativeStarSuffixClock at Hbound
    unfold nativeTripleResetPairedErrorValue nativeResetPairedBudget nativeStarSuffixClock
    simpa only [
      native_generated_triple_canonical_rest_product,MarkedPlacement.restRestrict_at,
      MarkedPlacement.restSpin,cavityLeft_splitIndex] using Hbound

theorem actual_generated_triple_power_error_from_canonical_along
    {m delta cl cu Az C0 Ct D Bclock eta saving Cmass : ℝ} {b d : ℕ}
    {Cpower Cbase : ℕ→ℝ}
    {M : (n:ℕ)→NativeOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice}
    (hC : ∀j,0 ≤ Cpower j ∧ 0 ≤ Cbase j)
    (H : ∀j,ActualCanonicalPowerSourceErrorProductOnEveryFinalNetAlong b j (d-1-j) eta saving Cmass
      (Cpower j) (Cbase j) M W w) :
    ActualGeneratedTriplePowerErrorOnEveryFinalNetAlong b d eta saving Cmass Cpower Cbase M W w := by
  have Hfin:=Filter.eventually_all.mpr (fun j : Fin d=>H j.val)
  filter_upwards [Hfin] with n hn
  intro L us hus hret hmesh hstar
  have Hgrid:=Filter.eventually_all.mpr (fun j : Fin d=>hn j L us hus hret hmesh hstar)
  filter_upwards [Hgrid] with r hr
  dsimp only at hr ⊢
  intro pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht hb hIn x hxsx hxW hmi
    p hp rr hrr zz hzz hpH hrH hzH hef v hWv hvr hlow hz
  subst b
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus r
  have hlen : pre.length+mid.length < (pre++(mid++tail)).length:=
    hU.trans_le (hpH.trans (p.tree.splitIndex_le_clockLength _ _))
  let G₀:=(((nativeGeneratedCompleteShape (dim n) P.live.test P.live.ancestry (by omega) hlen).retainOnMarked 0 p hp).retainOnMarked 0 rr hrr).retainOnMarked 0 zz hzz
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim
    (fun _=>((M n).bf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
    (fun _=>((M n).hf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
  let center:=orderedPathS ((dim n)+1) (M n).bf (M n).hf (w n).star.val
  obtain ⟨E,t,e,f,htRead,heRead,hfRead,hsplit,Hlaw⟩:=native_actual_triple_reset_power_error_source
    (dim n) pre mid tail hP hmid hU ht hIn p hp rr hrr zz hzz hpH hrH hzH ho (M n) 0 q 0 d center
  have hG₀ (j) : G₀.sourceLowMass j ≤ Cmass*sourceFactorScale x (W n)
      (nativeGeneratedCompleteInitial P.live.test pre.length) j := by
    simp only [G₀,ActualNaturalBoundaryShape.retained_source_mass]
    exact native_generated_complete_source_mass (dim n) P.live.test P.live.ancestry (by omega) hlen
      Cmass x (W n) (by simpa only [hcut] using hmi) (by simpa only [hcut] using hmass) j
  let error:=fun δ=>deletedOverlap (dim n) (joinSpin (E.D.atSlot δ e,false)) (joinSpin (E.D.atSlot δ f,false))-
    pathPairMoment (uniformWeight ((dim n)+1)) (finiteFeature ((dim n)+1))
      (completedPathClock ((dim n)+1) (M n).bf (M n).hf) (orderedOverlap ((dim n)+1))
      (partitionPoint 0 (pre++(mid++tail)) (zz.tree.splitIndex (zz.embed rr.mark) zz.mark))
  have HE : nativeTripleResetPairedErrorValue (dim n) T P.live.test (M n) p rr zz q d center=
      ∑j∈Finset.range d,∫z,nativeTwoLevelPowerErrorProduct (dim n) j (d-1-j) E.Ei E.Es E.D
        (fun η ζ δ=>(G₀.canonicalMinimumSource (M n) (fun _=>NativeSourceFactorForm.centered)).restProduct
          (E.read η ζ δ)) E.target t
        (fun l=>cumulativeIncrements (q 0) (fun l=>q (l+1)) (pre.length+l))
        (nativeStarSuffixClock (dim n) pre mid q) center error (exteriorForestIRoot z) (exteriorForestStarRoot z)
        ∂nativeExteriorForestDisorderRootLaw (restWeight (dim n)) (restFeature (dim n)) pre mid tail 0 q 0 := by
    simp only [native_generated_triple_canonical_rest_product] at Hlaw
    dsimp only [G₀]
    simp only [native_generated_triple_canonical_rest_product]
    unfold nativeTripleResetPairedErrorValue nativeStarSuffixClock
    simpa only [MarkedPlacement.restRestrict_at,MarkedPlacement.restSpin,error] using Hlaw
  rw [HE,Finset.sum_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  by_cases hst : E.target=t
  · rw [←hst]
    simp only [native_two_level_power_error_product_self,integral_zero,abs_zero]
    have h1:0 ≤ Cpower j:=(hC j).1
    have h2:0 ≤ Cbase j:=(hC j).2
    have hx:0 ≤ x:=(M n).hxs.le.trans hxsx
    have hW:0 ≤ W n:=hx.trans hxW
    have hu:0 ≤ partitionPoint 0 (finiteCutMasses us r) (zz.tree.splitIndex (zz.embed rr.mark) zz.mark):=
      (partitionPoint_mem _ (finiteCutMasses_ordered us hus r) _).1
    have hxs:0 ≤ (M n).xs:=(M n).hxs.le
    unfold sourceMonomialScale
    positivity
  · have had:=comparisonVariableEndpoint_clocks_admissible (M n).context.hc (M n).context.hk (M n).context.hkc
      (M n).context.hm (M n).context.hM (M n).b (M n).h (M n).context.hd.ne' (M n).hlam.le
      (M n).hlb (M n).hb (M n).hh (M n).hh0 (M n).alpha
    have Hcenter:=native_ordered_source_center_eq_completed (dim n) (M n).bf (M n).hf
      (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1)
      (partitionPoint_mem (pre++(mid++tail)) ho (zz.tree.splitIndex (zz.embed rr.mark) zz.mark))
    have HJ:=hr ⟨j,Finset.mem_range.mp hj⟩ pre mid tail hcut hindex hmass zz.tree G₀
      (fun _=>NativeSourceFactorForm.centered) (nativeGeneratedCompleteInitial P.live.test pre.length)
      x hxsx hxW hG₀ _ _ (zz.tree.cavityLeftSlot (zz.embed (rr.embed (p.embed P.live.test.target))))
      E.toNativeCanonicalExteriorSource t hst v hWv
      (by simpa only [hsplit,(rr.tree.markedAttach_embed_preserves 0 zz hzz).2,
        (p.tree.markedAttach_embed_preserves 0 rr hrr).2] using hvr) hlow hz
      (zz.tree.cavityLeftSlot (zz.embed rr.mark)) (zz.tree.cavityLeftSlot zz.mark)
      (fun H=>hef (zz.tree.cavityLeftSlot.injective H)) error
      (fun η ζ δ=>by simp only [error,heRead,hfRead,cavityLeft_splitIndex,←hcut,Hcenter])
    have hpow:j+(d-1-j)=d-1:=by have:=Finset.mem_range.mp hj;omega
    rw [hpow] at HJ
    simpa only [cavityLeft_splitIndex] using HJ

theorem eventually_inherited_same_star_triple_error_bounds_along (hdim : Tendsto dim atTop atTop)
    {m delta eta cl cu Az C0 Ct D Bclock Temp Cf Ccal : ℝ}
    (Cmass : ℝ) (hCm : 0 ≤ Cmass)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcal : 1 ≤ Ccal)
    (M : (n:ℕ)→NativeOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hsource : ∀ᶠn : ℕ in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (saving : ℝ) (w : ℕ→ActualSlowWindowChoice)
    (Hmixed : ∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) :
      (∀a b d : ℕ,∃Cp : ℝ,0 < Cp ∧ ∃Ch : ℝ,0 < Ch ∧
        ∃Cpower Cbase : ℕ→ℝ,(∀j,0 < Cpower j ∧ 0 < Cbase j) ∧
        ActualGeneratedTripleIncomingErrorOnEveryFinalNetAlong a b d eta saving Cmass Cp Ch Cpower Cbase M W w) ∧
      (∀a b d : ℕ,∃Cp : ℝ,0 < Cp ∧ ∃Ch : ℝ,0 < Ch ∧
        ∃Cpower Cbase : ℕ→ℝ,(∀j,0 < Cpower j ∧ 0 < Cbase j) ∧
        ActualGeneratedTripleStarIncomingErrorOnEveryFinalNetAlong a b d eta saving Cmass Cp Ch Cpower Cbase M W w) ∧
      ∀b d : ℕ,∃Cpower Cbase : ℕ→ℝ,(∀j,0 < Cpower j ∧ 0 < Cbase j) ∧
        ActualGeneratedTriplePowerErrorOnEveryFinalNetAlong b d eta saving Cmass Cpower Cbase M W w := by
  have HI (a j k : ℕ) :=
    eventually_inherited_canonical_incoming_source_error_product_from_same_star_along hdim a j k Bclock Temp Cf Cmass Ccal
      hTemp hCf hCm hCcal hm hdelta hroom hgap hcl hcu hAz hC0 hCt M W hcanonical hWlim
      hcompare hsource w (Hmixed (2*j) (2*k))
  have HS (a j k : ℕ) :=
    eventually_inherited_canonical_star_incoming_source_error_product_from_same_star_along hdim a j k Bclock Temp Cf Cmass Ccal
      hTemp hCf hCm hCcal hm hdelta hroom hgap hcl hcu hAz hC0 hCt M W hcanonical hWlim
      hcompare hsource w (Hmixed (2*j) (2*k))
  have HP (a j k : ℕ) :=
    eventually_inherited_canonical_power_source_error_product_from_same_star_along hdim a j k Bclock Temp Cf Cmass Ccal
      hTemp hCf hCm hCcal hm hdelta hroom hgap hcl hcu hAz hC0 hCt M W hcanonical hWlim
      hcompare hsource w (Hmixed (2*j) (2*k))
  refine ⟨?_,?_,?_⟩
  · intro a b d
    obtain ⟨Cp,hCp,Ch,hCh,Hin⟩:=HI a 0 d
    choose Cpower hCpower Cbase hCbase Hpower using fun j=>HP b j (d-1-j)
    exact ⟨Cp,hCp,Ch,hCh,Cpower,Cbase,fun j=>⟨hCpower j,hCbase j⟩,
      actual_generated_triple_incoming_error_from_canonical_along hCp.le hCh.le
        (fun j=>⟨(hCpower j).le,(hCbase j).le⟩)
        (actual_canonical_paired_incoming_source_error_from_products_along Hin Hpower)⟩
  · intro a b d
    obtain ⟨Cp,hCp,Ch,hCh,Hin⟩:=HS a 0 d
    choose Cpower hCpower Cbase hCbase Hpower using fun j=>HP b j (d-1-j)
    exact ⟨Cp,hCp,Ch,hCh,Cpower,Cbase,fun j=>⟨hCpower j,hCbase j⟩,
      actual_generated_triple_star_incoming_error_from_canonical_along hCp.le hCh.le
        (fun j=>⟨(hCpower j).le,(hCbase j).le⟩)
        (actual_canonical_paired_star_incoming_source_error_from_products_along Hin Hpower)⟩
  · intro b d
    choose Cpower hCpower Cbase hCbase Hpower using fun j=>HP b j (d-1-j)
    exact ⟨Cpower,Cbase,fun j=>⟨hCpower j,hCbase j⟩,
      actual_generated_triple_power_error_from_canonical_along
        (fun j=>⟨(hCpower j).le,(hCbase j).le⟩) Hpower⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
