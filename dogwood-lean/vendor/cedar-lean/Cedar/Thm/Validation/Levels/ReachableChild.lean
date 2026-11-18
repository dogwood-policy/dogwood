import Cedar.Thm.Validation.Slice.Reachable

namespace Cedar.Thm

open Cedar.Data Cedar.Spec Cedar.Validation

/--
Weakening: if `uid` is reachable at level `n`, it's reachable at any level `m ≥ n`.
-/
theorem reachable_of_le {entities : Entities} {start : Set EntityUID}
    {uid : EntityUID} {n m : Nat}
    (hr : ReachableIn entities start uid n)
    (hle : n ≤ m) :
    ReachableIn entities start uid m := by
  induction hle with
  | refl => exact hr
  | step _ ih => exact reachable_succ ih

/--
If `uid` is reachable at level `n+1`, `entities.find? uid = some ed`, and
`uid2 ∈ ed.sliceEUIDs`, then `uid2` is reachable at level `n+2`.
-/
theorem reachable_child {entities : Entities} {start : Set EntityUID}
    {uid uid2 : EntityUID} {ed : EntityData} {n : Nat}
    (hr : ReachableIn entities start uid (n + 1))
    (hf : entities.find? uid = some ed)
    (hm : uid2 ∈ ed.sliceEUIDs) :
    ReachableIn entities start uid2 (n + 2) := by
  cases hr with
  | in_start hs =>
    -- uid ∈ start, so use step with uid as the intermediate
    exact ReachableIn.step uid hs hf (ReachableIn.in_start hm)
  | step i hi he hr' =>
    -- i ∈ start, find? i = some ed_i, hr' : ReachableIn entities ed_i.sliceEUIDs uid n'
    -- where n' + 1 = n + 1, so n' = n. Wait, the step case has (level+1) in conclusion.
    -- ReachableIn.step produces at level (level + 1).
    -- So if hr : ReachableIn ... uid (n+1) comes from step, then
    -- hr' : ReachableIn ... uid level where level + 1 = n + 1, so level = n.
    -- No wait: the step constructor is:
    --   step (i) (hi) (he) (hr : ReachableIn es ed.sliceEUIDs finish level) : ReachableIn es start finish (level + 1)
    -- So if the conclusion is at (n+1), then hr' is at level where level+1 = n+1, i.e., level = n.
    -- But n might be 0!
    -- If n = 0: hr' : ReachableIn ... uid 0, which is uninhabited!
    -- Actually ReachableIn at level 0 is impossible (both constructors produce level+1).
    -- So if step produces (n+1), hr' is at n. If n=0, hr' is at 0 which is impossible.
    -- But wait: the input hr is at (n+1). The step case decomposes it as:
    -- step i hi he (hr' : ReachableIn ... uid n)
    -- This only applies if n+1 matches the pattern level+1, so level = n.
    -- If n = 0 then hr' : ReachableIn ... uid 0 which can't be constructed, contradiction.
    -- For n ≥ 1: hr' is at level n (≥ 1). We recurse.
    rename_i ed_i
    -- hr' : ReachableIn entities ed_i.sliceEUIDs uid n
    -- We want: ReachableIn entities ed_i.sliceEUIDs uid2 (n + 1)
    -- By reachable_child on hr' (which is at level n = (n-1)+1 for n ≥ 1):
    -- Wait, reachable_child needs input at level (n'+1). hr' is at level n.
    -- So we need n ≥ 1, i.e., n = m+1 for some m. Then hr' is at m+1.
    -- reachable_child hr' hf hm : ReachableIn ... uid2 (m + 2) = (n + 1). ✓
    cases n with
    | zero =>
      -- hr' : ReachableIn ... uid 0, which is impossible
      exact absurd hr' (by intro h; cases h)
    | succ m =>
      -- hr' : ReachableIn entities ed_i.sliceEUIDs uid (m + 1)
      have := reachable_child hr' hf hm
      -- this : ReachableIn entities ed_i.sliceEUIDs uid2 (m + 2)
      exact ReachableIn.step i hi he this

end Cedar.Thm
