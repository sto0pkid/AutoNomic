```
open import lc-essentials


open import IO

open import Data.String.Base using (String)

show : Bool → String
show true  = "true"
show false = "false"
          


main = run(IO.putStrLn (show (Nat-eq (suc z) (max (suc z) (suc (suc z))))))
```
hecks yeah
hmmmmmmmm
If you then want to compile your program, make sure you have agda-lib-ffi installed (run cabal install in ffi directory of Agda stdlib). You can then use Emacs command C-c C-x C-c to actually compile the module you're working with. -SO, for accessing haskell fns it looks like.
alright i can try installing that, but i think this should still compile? i mean, when we get it right.
it compiles on my machine.
i see
alright im not sure how to go about installing it, because i set agda up with stack
what is ffi directory of Agda stdlib, in sources? Couldn't tell you. Maybe this is a problem better solved by stoop? maaaybe. we can try though.
