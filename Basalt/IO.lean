import Basalt.RandomChoice
import Basalt.Gen

open RandomChoice

instance : RandomChoice IO where
  choose lo hi _ := IO.rand lo hi

-- FIXME: Once Lean updates, this shouldn't need to be unsafe.
unsafe abbrev Gen.runIO (g : Gen α) : IO α := @g _ _ (unsafeCast ()) _ (unsafeCast ()) _
