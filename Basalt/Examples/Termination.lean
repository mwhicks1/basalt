import Basalt
import Basalt.Examples.NatList
import Basalt.Examples.BST

open RandomChoice

namespace NatListExample

theorem Nat.SPMF.IsPMF_arbitrary : SPMF.IsPMF Nat.arbitrary := by
  apply SPMF.IsPMF_pick_pure_of_mass_eq
  . rw [Nat.arbitrary]
  . exact SPMF.mass_bind_pure

theorem List.SPMF.IsPMF_arbitrary : SPMF.IsPMF List.arbitrary := by
  apply SPMF.IsPMF_pick_pure_of_mass_eq
  . rw [List.arbitrary]
  . apply SPMF.mass_bind_of_const_mass
    . exact Nat.SPMF.IsPMF_arbitrary
    . exact fun _ => SPMF.mass_bind_pure

theorem List.not_SPMF.IsPMF_diverge : ¬SPMF.IsPMF List.diverge := by
  have : (List.diverge : SPMF (List Nat)).mass = 0 := by
    apply SPMF.mass_eq_zero_of_support_empty
    ext xs
    induction xs <;> rw [List.diverge] <;> simp
    grind
  rw [SPMF.IsPMF, this]
  simp

theorem List.not_SPMF.IsPMF_pick_pure_nil_diverge :
    ¬SPMF.IsPMF (pick (fun () => pure []) (fun () => List.diverge)) := by
  have : (List.diverge : SPMF (List Nat)).mass = 0 := by
    apply SPMF.mass_eq_zero_of_support_empty
    ext xs
    induction xs <;> rw [List.diverge] <;> simp
    grind
  rw [SPMF.IsPMF, SPMF.mass_pick, this, SPMF.mass_pure]
  simp

/-
## Proving IsPMF (genSorted m)

The key challenge: genSorted m calls genSorted (m + delta) recursively with a different
parameter. The standard IsPMF_pick_pure_of_mass_eq requires body.mass = full.mass,
but here the body involves genSorted at different indices.

### Mathematical Approach

Let μ(m) = (genSorted m).mass. The recurrence gives:
  μ(m) = 1/2 + 1/2 * ∑_d p(d) * μ(m + d)

where p is the distribution of Nat.arbitrary (a PMF with ∑_d p(d) = 1).

Key insight: The infimum of μ must be 1.

Proof: Let c = iInf μ. For any m:
  μ(m) = 1/2 + 1/2 * ∑_d p(d) * μ(m+d) ≥ 1/2 + 1/2 * c

Taking infimum over m: c ≥ 1/2 + 1/2 * c, which gives c ≥ 1.
Since μ(m) ≤ 1 for all m (SPMF property), we have c ≤ 1.
Therefore c = 1, and μ(m) ≥ 1 for all m. Combined with μ(m) ≤ 1: μ(m) = 1.

### Proof Structure

We add a general lemma to SPMF that captures this pattern: if a family of SPMFs
satisfies a recurrence of the form μ(i) = 1/2 + 1/2 * (weighted avg of μ) where
the weights sum to 1, then μ(i) = 1 for all i.
-/

-- First establish the recurrence for genSorted's mass
theorem List.mass_genSorted_recurrence (m : Nat) :
    (List.genSorted m : SPMF (List Nat)).mass =
      1/2 + 1/2 * (Nat.arbitrary >>= fun d =>
        List.genSorted (m + d) >>= fun xs =>
          pure ((m + d) :: xs) : SPMF (List Nat)).mass := by
  conv_lhs => rw [List.genSorted]
  rw [SPMF.mass_pick, SPMF.mass_pure]
  ring

-- Lemma: the body mass of genSorted n is at least the infimum of all genSorted masses
theorem List.mass_genSorted_body_ge_iInf (n : Nat) :
    (Nat.arbitrary >>= fun d =>
      List.genSorted (n + d) >>= fun xs =>
        pure ((n + d) :: xs) : SPMF (List Nat)).mass ≥
          ⨅ k, (List.genSorted k : SPMF (List Nat)).mass := by
  -- Strategy:
  -- 1. First show that binding with `fun xs => pure ((n+d) :: xs)` preserves mass
  -- 2. Then use mass_bind_ge_of_ge to show the outer bind's mass ≥ infimum

  -- Step 1: Mass of inner bind equals mass of genSorted (n+d)
  have h_inner_mass : ∀ d, (List.genSorted (n + d) >>= fun xs =>
      pure ((n + d) :: xs) : SPMF (List Nat)).mass = (List.genSorted (n + d) : SPMF (List Nat)).mass :=
    fun d => SPMF.mass_bind_pure

  -- Step 2: Each inner bind's mass ≥ infimum
  have h_ge_iInf : ∀ d, (List.genSorted (n + d) >>= fun xs =>
      pure ((n + d) :: xs) : SPMF (List Nat)).mass ≥ ⨅ k, (List.genSorted k : SPMF (List Nat)).mass := by
    intro d
    rw [h_inner_mass]
    exact iInf_le _ (n + d)

  -- Step 3: Apply mass_bind_ge_of_ge with Nat.arbitrary (which is a PMF)
  exact SPMF.mass_bind_ge_of_ge Nat.SPMF.IsPMF_arbitrary h_ge_iInf

-- Main theorem: genSorted m is a PMF for any m
theorem List.IsPMF_genSorted (m : Nat) : SPMF.IsPMF (List.genSorted m) := by
  have h := SPMF.IsPMF_of_half_plus_half_weighted_avg
    (g := fun n => (List.genSorted n : SPMF (List Nat)))
    (body_mass := fun n => (Nat.arbitrary >>= fun d =>
        List.genSorted (n + d) >>= fun xs =>
          pure ((n + d) :: xs) : SPMF (List Nat)).mass)
    List.mass_genSorted_body_ge_iInf
    List.mass_genSorted_recurrence
  exact h m

end NatListExample

namespace TreeExample

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
theorem Tree.IsPMF_isBST (lo hi : Nat) : SPMF.IsPMF (Tree.genBST lo hi) := by
  sorry

end TreeExample
