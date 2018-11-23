
{-@ LIQUID "--reflection" @-}

import Language.Haskell.Liquid.ProofCombinators

--------

-- (Ord a n b) = a^n + b
{-@ data Ordinal [size] @-}
{-@ type NFOrd = {v:Ordinal | normal v} @-}
data Ordinal = Ord Ordinal Integer Ordinal
             | Zero
             deriving (Eq, Show)

{-@ measure size @-}
{-@ size :: Ordinal -> Nat @-}
size :: Ordinal -> Integer
size Zero = 1
size (Ord a n b) = (size a) + 1 + (size b)

{-@ reflect normal @-}
normal :: Ordinal -> Bool
normal Zero = True
normal (Ord a n b) = (normal a) && (n >= 0) && (normal b) && (case b of
    Zero -> True
    (Ord c _ _) -> ordLT c a)

{-@ reflect ordLT @-}
ordLT :: Ordinal -> Ordinal -> Bool
ordLT _ Zero = False
ordLT Zero _ = True
ordLT (Ord a0 n0 b0) (Ord a1 n1 b1) =
    (ordLT a0 a1) || 
    (a0 == a1 && n0 < n1) || 
    (a0 == a1 && n0 == n1 && ordLT b0 b1)

{-@ reflect one @-}
one = (Ord Zero 1 Zero)     -- 1
{-@ normal_one :: _ -> { normal one } @-}
normal_one _ = [normal Zero, normal one] *** QED

{-@ reflect ok @-}
ok = (Ord one 1 Zero)      -- 1 + 1
{-@ normal_ok :: _ -> { normal ok } @-}
normal_ok _ = [normal Zero, normal one, normal ok] *** QED

{-@ reflect err @-}
err = (Ord Zero 1 one)      -- 1 + 1
{-@ normal_err :: _ -> { normal err } @-}
normal_err _ = [normal Zero, normal one, normal err] *** QED





--w   = (Ord one 1 Zero)      -- omega
main = print "hi"              -- Ord (Ord Zero 1 Zero) 1 Zero







