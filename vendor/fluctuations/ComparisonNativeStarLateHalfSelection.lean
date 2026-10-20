module

public import ComparisonNativeStarPolynomialSelection

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 6000000
namespace NativeStarBuffer

theorem massNode_later_half_reindex {start A v quarter : ℝ} {N j : ℕ}
    (htotal : 4*(N:ℝ)*quarter=2*A*v) :
    massNode start quarter (4*N+j)=massNode (start+2*A*v) quarter j := by
  unfold massNode
  push_cast
  nlinarith only [htotal]

theorem eventually_exists_native_continuum_star_later_half {A B c1 : ℝ}
    (hA : 0 < A) (hc1 : 0 < c1) :
    ∀ᶠn : ℕ in atTop,∀(S : ℝ→ℝ) (start v : ℝ),
      MonotoneOn S (Icc (0:ℝ) 1) → 0 ≤ start → 0 < v → start+4*A*v ≤ 1 →
      S (start+4*A*v)-S start ≤ B*v →
      ∃N : ℕ,∃quarter : ℝ,∃i<N,
        0 < N ∧ 0 < quarter ∧
        (n:ℝ)^(-c1)*v ≤ quarter ∧ 4*(N:ℝ)*quarter=4*A*v ∧
        start+2*A*v ≤ massNode start quarter (4*i) ∧
        ∀u∈Icc (massNode start quarter (4*i)) (massNode start quarter (4*(i+1))),
          ∀w∈Icc (massNode start quarter (4*i)) (massNode start quarter (4*(i+1))),
            |S u-S w| ≤ (n:ℝ)^(-c1/2)*v := by
  filter_upwards [eventually_exists_native_continuum_star (A:=A/2) (B:=B)
    (half_pos hA) hc1] with n hn
  intro S start v hS hstart hv hend hvariation
  have hAv : 0 < A*v:=mul_pos hA hv
  have hstart' : 0 ≤ start+2*A*v:=by nlinarith
  have hle : start ≤ start+2*A*v:=by nlinarith
  have hmid : start+2*A*v ≤ start+4*A*v:=by nlinarith
  have hmono:=hS ⟨hstart,hle.trans (hmid.trans hend)⟩ ⟨hstart',hmid.trans hend⟩ hle
  have hend' : start+2*A*v+4*(A/2)*v ≤ 1:=by nlinarith only [hend]
  have hvariation' : S (start+2*A*v+4*(A/2)*v)-S (start+2*A*v) ≤ B*v:=by
    rw [show start+2*A*v+4*(A/2)*v=start+4*A*v by ring]
    linarith only [hmono,hvariation]
  obtain ⟨N,q,i,hi,hN,hq,hql,htotal,hosc⟩:=hn S (start+2*A*v) v hS hstart' hv hend' hvariation'
  have htotal' : 4*(N:ℝ)*q=2*A*v:=by nlinarith only [htotal]
  have hshift (j : ℕ) : massNode start q (4*N+j)=massNode (start+2*A*v) q j:=
    massNode_later_half_reindex htotal'
  have hlo : massNode start q (4*(N+i))=massNode (start+2*A*v) q (4*i):=by
    rw [Nat.mul_add,hshift]
  have hhi : massNode start q (4*(N+i+1))=massNode (start+2*A*v) q (4*(i+1)):=by
    rw [show 4*(N+i+1)=4*N+4*(i+1) by omega,hshift]
  refine ⟨2*N,q,N+i,by omega,by omega,hq,hql,?_,?_,?_⟩
  · push_cast
    nlinarith only [htotal']
  · rw [hlo]
    unfold massNode
    have H : 0 ≤ ((4*i:ℕ):ℝ)*q:=mul_nonneg (Nat.cast_nonneg _) hq.le
    linarith only [H]
  · simpa only [hlo,hhi] using hosc

end NativeStarBuffer
end OAI.SKFluctuations
