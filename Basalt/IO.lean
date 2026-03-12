import Basalt.RandomChoice
import Basalt.Gen

open RandomChoice

instance : RandomChoice IO where
  choose lo hi _ := IO.rand lo hi
