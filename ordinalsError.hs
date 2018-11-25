
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--higherorder"     @-}

import Language.Haskell.Liquid.ProofCombinators

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

{-@ reflect ordLT @-}
ordLT :: Ordinal -> Ordinal -> Bool
ordLT _ Zero = False
ordLT Zero _ = True
ordLT (Ord a0 n0 b0) (Ord a1 n1 b1) =
    (ordLT a0 a1) || 
    (a0 == a1 && n0 < n1) || 
    (a0 == a1 && n0 == n1 && ordLT b0 b1)

{-@ reflect normal @-}
normal :: Ordinal -> Bool
normal Zero = True
normal (Ord a n b) = (normal a) && (n > 0) && (normal b) && (case b of
    Zero -> True
    (Ord c _ _) -> ordLT c a)


{-@ zero :: NFOrd @-}
zero = let zero' = Zero in castWithTheorem [normal Zero] zero'
{-@ one :: NFOrd @-}
one = let one' = Ord Zero 1 Zero in castWithTheorem [normal Zero, normal one'] one'
{-@ w :: NFOrd @-}
w = let w' = Ord one 1 Zero in castWithTheorem [normal Zero, normal w'] w'

{-@ ordId :: NFOrd -> NFOrd @-}
ordId :: Ordinal -> Ordinal
ordId a = a

main = print $ ordId w












-- {-@ reflect w @-}
-- w = (Ord one 1 Zero)      -- 1 + 1
-- {-@ normal_w :: _ -> { normal w } @-}
-- normal_w _ = [normal Zero, normal one, normal w] *** QED


-- {-@ err :: NFOrd @-}

-- {-@ reflect err @-}
-- err = (Ord Zero 1 one)      -- 1 + 1
-- {-@ normal_err :: _ -> { normal err } @-}
-- normal_err _ = [normal Zero, normal one, normal err] *** QED





