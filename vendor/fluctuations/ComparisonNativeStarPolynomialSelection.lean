module

public import ComparisonNativeStarContinuumSelection

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 5000000
namespace NativeStarBuffer

theorem eventually_native_star_block_count {A B c1:ℝ} (hA:0 < A) (hc1:0 < c1) :
    ∀ᶠn:ℕ in atTop,
      0 < Nat.floor (A*(n:ℝ)^c1) ∧
      (Nat.floor (A*(n:ℝ)^c1):ℝ) ≤ A*(n:ℝ)^c1 ∧
      B*(n:ℝ)^(c1/2) ≤ (Nat.floor (A*(n:ℝ)^c1):ℝ) := by
  have ht:Tendsto (fun n:ℕ=>(n:ℝ)^(c1/2)) atTop atTop:=
    (tendsto_rpow_atTop (by linarith : 0 < c1/2)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (eventually_ge_atTop (2/A)),
    ht.eventually (eventually_ge_atTop (2*B/A)),ht.eventually (eventually_ge_atTop (1:ℝ)),
    eventually_gt_atTop (0:ℕ)] with n h2 hB h1 hn
  have hn0:0 < (n:ℝ):=by exact_mod_cast hn
  have hp:0 < (n:ℝ)^(c1/2):=Real.rpow_pos_of_pos hn0 _
  have hs:((n:ℝ)^(c1/2))^2=(n:ℝ)^c1:=by
    rw [pow_two,←Real.rpow_add hn0]
    congr 1
    ring
  have hAq2:2 ≤ A*(n:ℝ)^(c1/2):=by simpa only [mul_comm] using (div_le_iff₀ hA).mp h2
  have hAqB:2*B ≤ A*(n:ℝ)^(c1/2):=by simpa only [mul_comm] using (div_le_iff₀ hA).mp hB
  have hqq:(n:ℝ)^(c1/2) ≤ ((n:ℝ)^(c1/2))^2:=by nlinarith
  have hxx:2 ≤ A*(n:ℝ)^c1:=by
    have hh:=mul_le_mul_of_nonneg_left hqq hA.le
    rw [hs] at hh
    exact hAq2.trans hh
  have hl:=Nat.lt_floor_add_one (A*(n:ℝ)^c1)
  have hhalf:A*(n:ℝ)^c1/2 ≤ (Nat.floor (A*(n:ℝ)^c1):ℝ):=by linarith
  have hNpos:0 < Nat.floor (A*(n:ℝ)^c1):=by
    have hh:0 < (Nat.floor (A*(n:ℝ)^c1):ℝ):=by linarith
    exact_mod_cast hh
  refine ⟨hNpos,Nat.floor_le (by positivity),?_⟩
  have hh:=mul_le_mul_of_nonneg_right hAqB hp.le
  have hh':2*B*(n:ℝ)^(c1/2) ≤ A*(n:ℝ)^c1:=by
    apply hh.trans_eq
    rw [mul_assoc,←pow_two,hs]
  linarith

theorem eventually_exists_native_continuum_star {A B c1:ℝ}
    (hA:0 < A) (hc1:0 < c1) :
    ∀ᶠn:ℕ in atTop,∀(S:ℝ → ℝ) (start v:ℝ),
      MonotoneOn S (Icc (0:ℝ) 1) → 0 ≤ start → 0 < v → start+4*A*v ≤ 1 →
      S (start+4*A*v)-S start ≤ B*v →
      ∃N:ℕ,∃quarter:ℝ,∃i<N,
        0 < N ∧ 0 < quarter ∧
        (n:ℝ)^(-c1)*v ≤ quarter ∧ 4*(N:ℝ)*quarter=4*A*v ∧
        ∀u∈Icc (massNode start quarter (4*i)) (massNode start quarter (4*(i+1))),
          ∀w∈Icc (massNode start quarter (4*i)) (massNode start quarter (4*(i+1))),
            |S u-S w| ≤ (n:ℝ)^(-c1/2)*v := by
  filter_upwards [eventually_native_star_block_count (B:=B) hA hc1,
    eventually_gt_atTop (0:ℕ)] with n hcount hn
  intro S start v hS hstart hv hend hvariation
  let N:=Nat.floor (A*(n:ℝ)^c1)
  let quarter:=A*v/(N:ℝ)
  have hN:0 < N:=hcount.1
  have hNr:0 < (N:ℝ):=by exact_mod_cast hN
  have hn0:0 < (n:ℝ):=by exact_mod_cast hn
  have hq:0 < quarter:=by dsimp [quarter];positivity
  have htotal:4*(N:ℝ)*quarter=4*A*v:=by dsimp [quarter];field_simp
  have hNupper:(N:ℝ) ≤ A*(n:ℝ)^c1:=hcount.2.1
  have hNl:B*(n:ℝ)^(c1/2) ≤ (N:ℝ):=hcount.2.2
  have hthetaN:(n:ℝ)^(-c1)*(N:ℝ) ≤ A:=by
    rw [Real.rpow_neg hn0.le]
    have hh:(N:ℝ)/(n:ℝ)^c1 ≤ A:=
      (div_le_iff₀ (Real.rpow_pos_of_pos hn0 c1)).mpr (by nlinarith)
    simpa only [div_eq_mul_inv,mul_comm] using hh
  have hquarter:(n:ℝ)^(-c1)*v ≤ quarter:=by
    apply (le_div_iff₀ hNr).mpr
    have hh:=mul_le_mul_of_nonneg_right hthetaN hv.le
    nlinarith
  have hnv:B*v ≤ (N:ℝ)*((n:ℝ)^(-c1/2)*v):=by
    have hh:=mul_le_mul_of_nonneg_right hNl
      (mul_nonneg (Real.rpow_nonneg hn0.le (-c1/2)) hv.le)
    have he:(n:ℝ)^(c1/2)*((n:ℝ)^(-c1/2)*v)=v:=by
      rw [←mul_assoc,←Real.rpow_add hn0,show c1/2+-c1/2=0 by ring,Real.rpow_zero,one_mul]
    simpa only [mul_assoc,he] using hh
  have hnode:massNode start quarter (4*N)=start+4*A*v:=by
    unfold massNode
    rw [Nat.cast_mul,Nat.cast_ofNat]
    linarith [htotal]
  have hvar:S (massNode start quarter (4*N))-S start ≤ (N:ℝ)*((n:ℝ)^(-c1/2)*v):=by
    rw [hnode]
    exact hvariation.trans hnv
  obtain ⟨i,hi,hosc⟩:=exists_continuum_profile_block S hS hstart hq (hnode ▸ hend) hN hvar
  exact ⟨N,quarter,i,hi,hN,hq,hquarter,htotal,hosc⟩

end NativeStarBuffer
end OAI.SKFluctuations
