import Basalt

open RandomChoice

def assert (b : Bool) (f : b = true → Gen α) : Gen α :=
  if h : b then f h else default

example : (assert false (fun _ => pure 2) : SPMF _).mass = 0 := by
  simp [assert, default]

def sampleUntilOne : Gen Unit := do
  if (← choose 0 1 (by simp)) == 1 then
    return ()
  else
    sampleUntilOne
partial_fixpoint
