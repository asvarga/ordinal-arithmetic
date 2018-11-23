
import Language.Haskell.Liquid.ProofCombinators

{-@ LIQUID "--reflection" @-}

--------

--{-@ type PlusComm = x:Int -> y:Int -> {x + y == y + x} @-} 
--{-@ propPlusComm :: PlusComm @-} 
--type PlusComm = Int -> Int -> ()
--propPlusComm :: PlusComm

{-@ propPlusComm :: x:Int -> y:Int -> {x + y == y + x} @-} 
propPlusComm :: Int -> Int -> ()
propPlusComm _ _ = trivial *** QED


{-@ reflect fib @-}
{-@ fib :: i:Nat -> Nat / [i] @-}
fib :: Int -> Int
fib i | i == 0    = 0 
      | i == 1    = 1 
      | otherwise = fib (i-1) + fib (i-2)

{-@ fibTwo :: _ -> { fib 2 == 1 } @-}
fibTwo :: () -> ()
fibTwo _ = [fib 0, fib 1, fib 2] *** QED






