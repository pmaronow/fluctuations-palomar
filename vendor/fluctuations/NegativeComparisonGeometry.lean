module

public import SKFluctuationsOAI.Probability.SKFluctuations.ComparisonCapTravel

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

theorem potential_negative_comparison_mismatch
    {H J p S B α M : ℝ → ℝ} {C : ℝ≥0} {r W : ℝ}
    (hW : 0<W) (hr : r∈Ioc (0:ℝ) 1)
    (hH : AbsolutelyContinuousOnInterval H 0 1)
    (hJ : ∀ t∈Icc (0:ℝ) 1,0<J t)
    (hd : ∀ᵐ t,t∈Icc (0:ℝ) 1→HasDerivAt H
      (J t*comparisonBracket (p t) t (S t) (B t)) t)
    (hcap : ∀ᵐ t,t∈Icc (0:ℝ) 1→H t<0→deriv α t=M (α t))
    (hneg : H r<0)
    (hp : MonotoneOn p (Ioc (0:ℝ) 1))
    (hpb : ∀ t∈Ioc (0:ℝ) 1,p t∈Icc (0:ℝ) 1)
    (hS : MonotoneOn S (Ioc (0:ℝ) 1))
    (hBm : MonotoneOn B (Ioc (0:ℝ) 1))
    (hSb : ∀ t∈Ioc (0:ℝ) 1,S t∈Icc (0:ℝ) 1)
    (hB : ∀ t∈Ioc (0:ℝ) 1,(S t)^2≤B t)
    (hα : LipschitzOnWith C α (Icc (0:ℝ) 1))
    (hm : StrictMonoOn α (Icc (0:ℝ) 1))
    (hαr : ∀ t∈Icc (0:ℝ) 1,α t∈Icc (0:ℝ) 1)
    (hMc : ContinuousOn M (Icc (0:ℝ) 1))
    (hM : ∀ u∈Icc (0:ℝ) 1,0<M u)
    (htravel : (∫u in (0:ℝ)..1,1/M u)≤W) :
    (S r-r)^2≤64*W^2+2*(B r-(S r)^2) := by
  have hD : 0≤B r-(S r)^2 := sub_nonneg.mpr (hB r hr)
  by_cases hSr : S r≤r
  · by_cases hrW : r≤2*W
    · have hdiff : |S r-r|≤2*W := abs_le.mpr
        ⟨by linarith [(hSb r hr).1],by linarith⟩
      have hs := (sq_le_sq₀ (abs_nonneg _) (by linarith : 0≤2*W)).mpr hdiff
      simp only [sq_abs] at hs
      nlinarith [sq_nonneg W]
    · let a := r-2*W
      have ha : 0<a := by dsimp [a];linarith
      have har : a<r := by dsimp [a];linarith
      have hasub : Icc a r⊆Icc (0:ℝ) 1 := Icc_subset_Icc ha.le hr.2
      have hex : ∃ t∈Icc a r,0≤H t := by
        by_contra hno
        push Not at hno
        have ht := cap_travel_le_total har.le (hα.mono hasub) (hm.mono hasub)
          (fun t ht=>hαr t (hasub ht)) hMc hM
          (hcap.mono (fun t ht hti=>ht (hasub hti) (hno t hti)))
        dsimp [a] at ht
        linarith
      obtain ⟨t,hti,htH⟩ := hex
      have htr : t<r := lt_of_le_of_ne hti.2 (by intro he;rw [he] at htH;linarith)
      have htsub : Icc t r⊆Icc (0:ℝ) 1 :=
        Icc_subset_Icc (ha.le.trans hti.1) hr.2
      obtain ⟨l,hli,hgl⟩ := potential_negative_left_witness htr
        (hH.mono (by simpa only [uIcc_of_le zero_le_one,uIcc_of_le htr.le] using htsub))
        (fun l hl=>hJ l (htsub hl)) (hd.mono (fun l hl hli=>hl (htsub hli)))
        (show H r<H t by linarith)
      have hl : l∈Ioc (0:ℝ) 1 :=
        ⟨ha.trans_le hti.1 |>.trans hli.1, hli.2.le.trans hr.2⟩
      have hleft : comparisonBracket (p r) l (S r) (B r)≤0 :=
        (comparisonBracket_mono_moments hl.1 (hpb r hr)
          (hS hl hr hli.2.le) (hBm hl hr hli.2.le)).trans
          ((comparisonBracket_antitone hl.1 (hB l hl) (hp hl hr hli.2.le)).trans hgl.le)
      have hbnd := comparisonBracket_left_mismatch hl.1 hli.2.le
        (hpb r hr) (hSb r hr).1 hSr (hB r hr) hleft
      have hlen : 0≤r-l := sub_nonneg.mpr hli.2.le
      have hlen' : r-l≤2*W := by dsimp [a] at hti;linarith [hli.1,hti.1]
      have hs := (sq_le_sq₀ hlen (by linarith : 0≤2*W)).mpr hlen'
      nlinarith [hbnd]
  · have hbnd := potential_negative_center_bound le_rfl hr hH hJ hd hcap hneg
      (fun t ht=>(hpb t ht).1) hS (hSb r hr).2 hB hα hm hαr hMc hM
    have hdiff : 0≤S r-r := by linarith
    have hdiff' : S r-r≤W := by linarith
    have hs := (sq_le_sq₀ hdiff hW.le).mpr hdiff'
    nlinarith [sq_nonneg W]

end OAI.SKFluctuations.LaplaceWindowFormalization
