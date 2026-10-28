/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
module

public import Basalt.Fuzz.Basic
public import SplitMix.Lemmas

/-!
# The `RecordGen` interpretation

`RecordGen` makes each choice uniformly at random, as `IO` does, and records a `FuzzGen` buffer that
decodes to the same choices: a random run that `FuzzGen` replays exactly, and so can seed a
libFuzzer corpus. `readNat_recordDraw` proves it per draw; a whole run's agreement is a free theorem
of the generator's polymorphism, so it is pinned by `BasaltTest/Fuzz.lean` instead.
-/

public section

namespace Basalt.Fuzz

open Basalt.PBT

/-- A `RecordGen` run's state: the PRNG it draws from and the bytes recorded so far. -/
structure RecordState where
  rng : SplitMix
  bytes : ByteArray

/-- A random interpretation of `Gen` that records, for every `choose`, bytes `FuzzGen` decodes back
to the same value. The `Option` base is `FuzzGen`'s, for the same reason. -/
abbrev RecordGen (α : Type) := StateT RecordState Option α

instance : Inhabited (RecordGen α) :=
  ⟨fun _ => none⟩

/-- `raw`'s low `n` bytes, big-endian, appended to `b`: what `readNat _ n` reads back. -/
def pushBE (b : ByteArray) : Nat → Nat → ByteArray
  | 0, _ => b
  | n + 1, raw => pushBE (b.push (raw / 256 ^ n % 256).toUInt8) n raw

/-! The bytes `pushBE` writes are the ones `readNat` reads back. -/

private theorem get!_eq (b : ByteArray) (i : Nat) (h : i < b.size) : b.get! i = b.data[i]'h := by
  cases b with | mk bs =>
  show bs[i]! = bs[i]
  exact getElem!_pos bs i h

private theorem get!_push_lt (b : ByteArray) (x : UInt8) (i : Nat) (h : i < b.size) :
    (b.push x).get! i = b.get! i := by
  rw [get!_eq _ _ (by simp [ByteArray.size_push]; omega), get!_eq _ _ h]
  simp [ByteArray.push, Array.getElem_push, h]

private theorem get!_push_size (b : ByteArray) (x : UInt8) : (b.push x).get! b.size = x := by
  rw [get!_eq _ _ (by simp [ByteArray.size_push])]
  simp [ByteArray.push, Array.getElem_push]

private theorem get!_append_lt (a c : ByteArray) (i : Nat) (h : i < a.size) :
    (a ++ c).get! i = a.get! i := by
  rw [get!_eq _ _ (by simp [ByteArray.size_append]; omega), get!_eq _ _ h]
  have := @ByteArray.getElem_append_left i a c (by simp [ByteArray.size_append]; omega) h
  simpa [ByteArray.getElem_eq_getElem_data] using this

private theorem size_pushBE (b : ByteArray) (n raw : Nat) : (pushBE b n raw).size = b.size + n := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih => simp only [pushBE, ih, ByteArray.size_push]; omega

private theorem get!_pushBE_lt (b : ByteArray) (n raw i : Nat) (h : i < b.size) :
    (pushBE b n raw).get! i = b.get! i := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    simp only [pushBE]
    rw [ih _ (by simp [ByteArray.size_push]; omega), get!_push_lt _ _ _ h]

private theorem get!_pushBE (b : ByteArray) (n raw i : Nat) (h : i < n) :
    (pushBE b n raw).get! (b.size + i) = (raw / 256 ^ (n - 1 - i) % 256).toUInt8 := by
  induction n generalizing b i with
  | zero => omega
  | succ n ih =>
    simp only [pushBE]
    cases i with
    | zero =>
      rw [get!_pushBE_lt _ _ _ _ (by simp [ByteArray.size_push]), Nat.add_zero, get!_push_size]
      simp
    | succ i =>
      have := ih (b.push (raw / 256 ^ n % 256).toUInt8) i (by omega)
      rw [ByteArray.size_push] at this
      rw [show b.size + (i + 1) = b.size + 1 + i by omega, this,
        show n + 1 - 1 - (i + 1) = n - 1 - i by omega]

private theorem readNatFrom_digits (raw : Nat) : ∀ (n acc : Nat) (s : FuzzState),
    s.cursor + n ≤ s.buffer.size →
    (∀ i < n, s.buffer.get! (s.cursor + i) = (raw / 256 ^ (n - 1 - i) % 256).toUInt8) →
    readNatFrom acc s n = (acc * 256 ^ n + raw % 256 ^ n, { s with cursor := s.cursor + n })
  | 0, acc, s, _, _ => by simp [readNatFrom, Nat.mod_one]
  | n + 1, acc, s, hn, hd => by
    have h0 := hd 0 (by omega)
    simp only [Nat.add_zero, Nat.add_sub_cancel, Nat.sub_zero] at h0
    have ih := readNatFrom_digits raw n (acc * 256 + raw / 256 ^ n % 256)
      { s with cursor := s.cursor + 1 } (by simp; omega)
      (fun i hi => by
        have := hd (i + 1) (by omega)
        simp only at this ⊢
        rw [show s.cursor + 1 + i = s.cursor + (i + 1) by omega, this,
          show n + 1 - 1 - (i + 1) = n - 1 - i by omega])
    simp only [readNatFrom, readByte, show s.cursor < s.buffer.size by omega, ite_true, h0]
    have hb : ((raw / 256 ^ n % 256).toUInt8).toNat = raw / 256 ^ n % 256 := by
      simp
    rw [hb, ih]
    have : (acc * 256 + raw / 256 ^ n % 256) * 256 ^ n + raw % 256 ^ n
        = acc * 256 ^ (n + 1) + raw % 256 ^ (n + 1) := by
      rw [Nat.mod_pow_succ, Nat.pow_succ, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm 256 (256 ^ n),
        Nat.mul_comm (raw / 256 ^ n % 256) (256 ^ n)]
      omega
    rw [this, show s.cursor + 1 + n = s.cursor + (n + 1) by omega]

/-- One draw: the value `d ∈ [0, range)` comes from the PRNG, as at `IO`, and the bytes encode
`raw = d + range * k` for a random `k` among those that fit in `bytesFor range` bytes. Every such
`raw` decodes to `d` under `FuzzGen`'s modulo reduction; drawing `k` rather than fixing `0` keeps
the high bytes as varied as a mutated input's, so a recorded seed is not a corner of byte space. -/
def recordDraw (s : RecordState) (range : Nat) : Nat × RecordState :=
  let n := bytesFor range
  let (d, g) := s.rng.randNat 0 (range - 1)
  let (k, g) := g.randNat 0 ((256 ^ n - 1 - d) / range)
  let raw := d + range * k
  (raw, { rng := g, bytes := pushBE s.bytes n raw })

/-- `choose` returns exactly what `FuzzGen`'s `choose` computes from the recorded `raw`. -/
instance : RandomChoice RecordGen where
  choose lo hi h := do
    let s ← get
    let range := hi - lo + 1
    let (raw, s') := recordDraw s range
    set s'
    have := Nat.mod_lt raw (show range > 0 by omega)
    pure (ULift.up ⟨lo + raw % range, by omega⟩)

/-- `RecordGen` has everything a generator needs. -/
example : Gen RecordGen := inferInstance

/-- Run a property once at `RecordGen` from PRNG state `g`: its outcome, the `FuzzGen` buffer that
replays it, and the PRNG state for the next run. The `none` case is `runOne`'s. -/
def runRecord (T : PropM RecordGen Unit) (g : SplitMix) : TestOutcome × ByteArray × SplitMix :=
  match (runProp T).run { rng := g, bytes := ByteArray.emptyWithCapacity 64 } with
  | some (outcome, s) => (outcome, s.bytes, s.rng)
  | none              => (Except.error .discard, ByteArray.empty, g.split.2)

/-- `range` outcomes fit in `bytesFor range` bytes. -/
private theorem le_pow_bytesFor (range : Nat) : range ≤ 256 ^ bytesFor range := by
  unfold bytesFor bitsFor
  split
  · simp; omega
  · have h1 := @Nat.lt_log2_self (range - 1)
    have h2 : 2 ^ ((range - 1).log2 + 1) ≤ 256 ^ (((range - 1).log2 + 1 + 7) / 8) := by
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
      exact Nat.pow_le_pow_right (by omega) (by omega)
    omega

/-- **The decode contract, per draw.** The bytes one `RecordGen` draw appends, followed by anything,
are read back by `FuzzGen`'s `readNat` as the `raw` it drew — so `FuzzGen`'s `choose` makes that
same choice and leaves its cursor where the next draw's bytes begin. The bytes are in the buffer,
so nothing past it is read. -/
theorem readNat_recordDraw (s : RecordState) (range : Nat) (hr : 0 < range) (post : ByteArray)
    (trace : Option ByteArray) :
    readNat ⟨(recordDraw s range).2.bytes ++ post, s.bytes.size, trace⟩ (bytesFor range) =
      ((recordDraw s range).1,
       ⟨(recordDraw s range).2.bytes ++ post, s.bytes.size + bytesFor range, trace⟩) := by
  have hpow := le_pow_bytesFor range
  have hd := SplitMix.randNat_mem s.rng (Nat.zero_le (range - 1))
  generalize hdg : s.rng.randNat 0 (range - 1) = dg at hd
  obtain ⟨d, g⟩ := dg
  have hk := SplitMix.randNat_mem g (Nat.zero_le ((256 ^ bytesFor range - 1 - d) / range))
  generalize hkg : g.randNat 0 ((256 ^ bytesFor range - 1 - d) / range) = kg at hk
  obtain ⟨k, g'⟩ := kg
  simp only at hd hk
  have hraw : d + range * k < 256 ^ bytesFor range := by
    have h1 := Nat.mul_le_mul_left range hk.2
    have h2 : range * ((256 ^ bytesFor range - 1 - d) / range) ≤ 256 ^ bytesFor range - 1 - d := by
      -- `Nat.div_mul_le_self`, with the factors in the order `omega` needs below.
      rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _
    omega
  simp only [recordDraw, hdg, hkg]
  unfold readNat
  rw [readNatFrom_digits (d + range * k) (bytesFor range) 0 _
    (by simp [ByteArray.size_append, size_pushBE])
    (fun i hi => by
      simp only
      rw [get!_append_lt _ _ _ (by rw [size_pushBE]; omega), get!_pushBE _ _ _ _ hi])]
  simp [Nat.mod_eq_of_lt hraw]

end Basalt.Fuzz
