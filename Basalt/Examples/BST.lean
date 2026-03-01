import Basalt

open RandomChoice

namespace TreeExample

inductive Tree (α : Type) where
  | leaf : Tree α
  | node : Tree α → α → Tree α → Tree α
deriving Repr

def Tree.size : Tree α → Nat
  | leaf => 0
  | node l _ r => l.size + r.size + 1

def Tree.isBST (lo hi : Nat) : Tree Nat → Prop
  | leaf => true
  | node l x r =>
    lo ≤ x ∧ x ≤ hi ∧
    isBST lo (x - 1) l ∧
    isBST (x + 1) hi r

def Tree.genBST (lo hi : Nat) : Gen (Tree Nat) := do
  if h : lo > hi then
    return leaf
  else
    pick
      (fun () => pure leaf)
      (fun () => do
        let x ← choose lo hi (by omega)
        let l ← Tree.genBST lo (x - 1)
        let r ← Tree.genBST (x + 1) hi
        return node l x r)
partial_fixpoint

theorem Tree.genBST_support :
    SPMF.support (Tree.genBST lo hi) = {t | Tree.isBST lo hi t} := by
  refine (Set.ext ?_)
  intro t
  simp
  fun_induction Tree.isBST
    <;> rw [Tree.genBST]
    <;> split
    <;> simp
    <;> grind

#guard_msgs(drop info) in
#eval (for _ in [0:20] do
  IO.println <| repr (← Gen.runIO (Tree.genBST 0 10)) : IO Unit)

private lemma mass_bind_ge_mul {x : SPMF α} {f : α → SPMF β} {c : ENNReal}
    (hf : ∀ a, (f a).mass ≥ c) : (x >>= f).mass ≥ x.mass * c := by
  simp only [SPMF.mass, Bind.bind, SPMF.bind, DFunLike.coe]
  rw [ENNReal.tsum_comm]
  simp [ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
  gcongr with a
  exact hf a

private lemma ennreal_one_of_ge_half_add_half_sq {c : ENNReal}
    (hc_le : c ≤ 1) (h : c ≥ 1 / 2 + 1 / 2 * c ^ 2) : c = 1 := by
  have hc_ne  : c ≠ ⊤     := ne_top_of_le_ne_top ENNReal.one_ne_top hc_le
  have hc2_ne : c ^ 2 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (pow_le_one₀ (zero_le _) hc_le)
  have hle : c.toReal ≤ 1 := by simpa using (ENNReal.toReal_le_toReal hc_ne ENNReal.one_ne_top).mpr hc_le
  have hge : c.toReal ≥ 1 / 2 + 1 / 2 * c.toReal ^ 2 := by
    have h2ne : (1 / 2 + 1 / 2 * c ^ 2 : ENNReal) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨by norm_num, ENNReal.mul_ne_top (by norm_num) hc2_ne⟩
    have hmono := (ENNReal.toReal_le_toReal h2ne hc_ne).mpr h
    rw [ENNReal.toReal_add (by norm_num) (ENNReal.mul_ne_top (by norm_num) hc2_ne),
        ENNReal.toReal_mul, ENNReal.toReal_pow] at hmono
    norm_num at hmono
    linarith
  have hone : c.toReal = 1 := by nlinarith
  rw [← ENNReal.ofReal_toReal hc_ne, hone, ENNReal.ofReal_one]

theorem Tree.genBST_terminates : SPMF.IsPMF (Tree.genBST lo hi) := by
  -- We work with c = ⨅ (lo', hi'), mass(genBST lo' hi') over all parameter pairs.
  -- Strategy:
  --   1. Show ∀ (lo', hi'), mass(genBST lo' hi') ≥ 1/2 + 1/2 * c².
  --   2. Taking infimum gives c ≥ 1/2 + 1/2 * c².
  --   3. The algebraic lemma forces c = 1.
  --   4. Since 1 = c ≤ mass(genBST lo hi) ≤ 1, we get mass = 1.
  haveI : Nonempty (Nat × Nat) := ⟨(0, 0)⟩
  unfold SPMF.IsPMF
  apply le_antisymm (Tree.genBST lo hi : SPMF _).tsum_coe
  let c := ⨅ p : Nat × Nat, (Tree.genBST p.1 p.2 : SPMF (Tree Nat)).mass
  -- c ≤ 1 because every mass is ≤ 1
  have hc_le_one : c ≤ 1 :=
    iInf_le_of_le (lo, hi) (Tree.genBST lo hi : SPMF _).tsum_coe
  -- ∀ (lo', hi'), mass(genBST lo' hi') ≥ 1/2 + 1/2 * c²
  have hge : ∀ p : Nat × Nat,
      1 / 2 + 1 / 2 * c ^ 2 ≤ (Tree.genBST p.1 p.2 : SPMF (Tree Nat)).mass := by
    intro ⟨lo', hi'⟩
    by_cases hlt : lo' > hi'
    · -- Base case: genBST lo' hi' = pure leaf, mass = 1
      have heq : (Tree.genBST lo' hi' : SPMF (Tree Nat)) = Pure.pure Tree.leaf := by grind [= genBST]
      rw [heq, SPMF.mass_pure]
      have hcsq : c ^ 2 ≤ 1 := Right.pow_le_one_of_le hc_le_one
      calc 1 / 2 + 1 / 2 * c ^ 2
          ≤ 1 / 2 + 1 / 2 * 1 := by gcongr
        _ = 1 := by rw [mul_one]; exact ENNReal.add_halves 1
    · -- Recursive case: genBST lo' hi' = pick (pure leaf) body, mass = 1/2 + 1/2 * body.mass
      push_neg at hlt
      -- Unfold genBST to the pick form
      have heq : (Tree.genBST lo' hi' : SPMF (Tree Nat)) =
          pick (fun () => Pure.pure Tree.leaf)
            (fun () => choose lo' hi' hlt >>= fun x =>
              Tree.genBST lo' (x - 1) >>= fun l =>
              Tree.genBST (x + 1) hi' >>= fun r =>
              Pure.pure (Tree.node l x r)) := by
        conv_lhs => rw [Tree.genBST]
        rw [dif_neg (by omega : ¬lo' > hi')]
      rw [heq, SPMF.mass_pick, SPMF.mass_pure]
      -- Goal: 1/2 + 1/2 * c² ≤ 1/2 * 1 + 1/2 * body.mass
      -- It suffices to show body.mass ≥ c²
      suffices h_body : (choose lo' hi' hlt >>= fun x =>
            Tree.genBST lo' (x - 1) >>= fun l =>
            Tree.genBST (x + 1) hi' >>= fun r =>
            Pure.pure (Tree.node l x r) : SPMF (Tree Nat)).mass ≥ c ^ 2 by
        calc 1 / 2 + 1 / 2 * c ^ 2
            ≤ 1 / 2 + 1 / 2 * (choose lo' hi' hlt >>= fun x =>
                Tree.genBST lo' (x - 1) >>= fun l =>
                Tree.genBST (x + 1) hi' >>= fun r =>
                Pure.pure (Tree.node l x r) : SPMF (Tree Nat)).mass := by
              gcongr
          _ = 1 / 2 * 1 + 1 / 2 * _ := by ring
      -- Body mass ≥ c² using mass_bind_ge_of_ge on choose (which is a PMF)
      apply SPMF.mass_bind_ge_of_ge (SPMF.IsPMF_choose lo' hi' hlt)
      intro x
      -- For each x, bound the inner double-bind mass by c²
      -- The inner mass = mass(genBST lo' (x-1)) * mass(genBST (x+1) hi') ≥ c * c = c²
      calc (Tree.genBST lo' (x - 1) >>= fun l =>
              Tree.genBST (x + 1) hi' >>= fun r =>
              Pure.pure (Tree.node l x r) : SPMF (Tree Nat)).mass
          _ ≥ (Tree.genBST lo' (x - 1) : SPMF (Tree Nat)).mass * c := by
              apply mass_bind_ge_mul
              intro l
              -- For fixed l, mass of [genBST (x+1) hi' >>= λ r, pure ...] = mass(genBST (x+1) hi')
              calc (Tree.genBST (x + 1) hi' >>= fun r =>
                      Pure.pure (Tree.node l x r) : SPMF (Tree Nat)).mass
                  _ = (Tree.genBST (x + 1) hi' : SPMF (Tree Nat)).mass := SPMF.mass_bind_pure
                  _ ≥ c := iInf_le _ (x + 1, hi')
          _ ≥ c * c := by gcongr; exact iInf_le _ (lo', x - 1)
          _ = c ^ 2 := by ring
  -- Taking infimum: c ≥ 1/2 + 1/2 * c²
  have hc_ge : c ≥ 1 / 2 + 1 / 2 * c ^ 2 := le_iInf hge
  -- The algebraic lemma gives c = 1
  have hc_one : c = 1 := ennreal_one_of_ge_half_add_half_sq hc_le_one hc_ge
  -- mass(genBST lo hi) ≥ c = 1
  calc (1 : ENNReal) = c := hc_one.symm
    _ ≤ (Tree.genBST lo hi : SPMF (Tree Nat)).mass := iInf_le _ (lo, hi)

namespace Counter

def ProducesWithCount (g : Counter α) (P : α → Nat → Prop) : Prop :=
  ∀ a count, (a, count) ∈ g.support → P a count

theorem count_pure :
    ProducesWithCount (pure a) (fun _ count => count = 0) := by
  unfold ProducesWithCount
  simp [pure, Counter.pure, SPMF.pure, SPMF.support, DFunLike.coe]

theorem count_bind
    {P : α → Nat → Prop}
    {Q : α → β → Nat → Prop}
    (hx : ProducesWithCount x P)
    (hf : (a : α) → ProducesWithCount (f a) (Q a)) :
    ProducesWithCount
      (x >>= f)
      (fun b count => ∃ a countX countF, P a countX ∧ Q a b countF ∧ count = countX + countF) := by
  unfold ProducesWithCount at *
  intro b count h
  simp [bind, Counter.bind, SPMF.support, SPMF.bind, DFunLike.coe, SPMF.pure] at *
  grind

theorem count_choose :
    ProducesWithCount (choose lo hi pf) (fun _ count => count = 1) := by
  unfold ProducesWithCount at *
  simp [choose, SPMF.support, SPMF.bind, DFunLike.coe, SPMF.pure] at *

theorem count_strengthen
    {P Q : α → Nat → Prop}
    (hP : ProducesWithCount g P)
    (h : ∀ a count, P a count → Q a count) :
    ProducesWithCount g Q := by
  unfold ProducesWithCount at *
  grind

end Counter

set_option maxHeartbeats 2000000 in
private lemma Tree.genBST_linear_fixed :
    (t, count) ∈ (Tree.genBST lo hi : Counter _).support →
    count ≤ 3 * t.size + 1 := by
  induction t generalizing lo hi count with
  | leaf =>
    intro h
    rw [Tree.genBST] at h
    split at h
    · simp [SPMF.support, pure, Counter.pure, SPMF.pure, DFunLike.coe] at h
      omega
    · simp [SPMF.support, pure, Counter.pure, SPMF.pure, DFunLike.coe, pick, bind, choose, Counter.bind, SPMF.bind] at h
      aesop
  | node l x r ihl ihr =>
    intro h
    rw [Tree.genBST] at h
    split at h
    · simp [SPMF.support, pure, Counter.pure, SPMF.pure, DFunLike.coe] at h
    · simp +arith [SPMF.support, pure, Counter.pure, SPMF.pure, DFunLike.coe, pick, bind, choose, Counter.bind, SPMF.bind, size] at *
      replace ⟨x1, ⟨h1, ⟨x2, ⟨h2, h⟩⟩⟩⟩ := h
      have : x2 ≤ (3 * l.size + 1) + (3 * r.size + 1) + 1 := by
        aesop (config := {warnOnNonterminal := false})
        have := @ihl lo (x - 1) w left_2
        have := @ihr (x + 1) hi w_1 right
        grind
      grind

theorem Tree.genBST_linear :
    (t, count) ∈ (Tree.genBST lo hi : Counter _).support →
    ∃ m b, count ≤ m * t.size + b := by
  intro h
  exists 3
  exists 1
  exact Tree.genBST_linear_fixed h

end TreeExample
