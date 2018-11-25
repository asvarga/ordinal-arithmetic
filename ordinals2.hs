
-- {-@ LIQUID "--reflection" @-}
{-@ LIQUID "--exact-data-cons" @-}
-- {-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder"     @-}

import Language.Haskell.Liquid.ProofCombinators

----------------------------------------------------------------

-- (Ord a n b) = a^n + b
-- require Cantor Normal Form and use the measure "size" to check termination
{-@ data Ordinal [size] @-}
{-@ type NFOrd = {v:Ordinal | normal v} @-}
data Ordinal = Ord Ordinal Int Ordinal
             | Zero
             deriving (Eq, Show)

{-@ type Pos = {v:Int | v > 0} @-}

{-@ measure size @-}
{-@ size :: Ordinal -> Nat @-}
size :: Ordinal -> Int
size Zero = 0
size (Ord a n b) = (size a) + 1 + (size b)

{-@ reflect normal @-}
normal :: Ordinal -> Bool
normal Zero = True
normal (Ord a n b) = (normal a) && (n > 0) && (normal b) && (case b of
    Zero -> True
    (Ord c _ _) -> (compOrd c a == LT))

{-@ reflect compInt @-}
compInt :: Int -> Int -> Ordering
compInt x y = if x < y then LT else if x == y then EQ else GT

{-@ reflect compOrd @-}
compOrd :: Ordinal -> Ordinal -> Ordering
compOrd Zero Zero = EQ
compOrd Zero (Ord a n b) = LT
compOrd (Ord a n b) Zero = GT
compOrd (Ord a0 n0 b0) (Ord a1 n1 b1) =
    case (compOrd a0 a1) of
        LT -> LT
        GT -> GT
        EQ -> case (compInt n0 n1) of
            LT -> LT
            GT -> GT
            EQ -> (compOrd b0 b1)
instance Ord Ordinal where compare = compOrd

-- {-@ zero :: NFOrd @-}
-- zero = let zero' = Zero in castWithTheorem [normal Zero] zero'
-- {-@ one :: NFOrd @-}
-- one = let one' = Ord Zero 1 Zero in castWithTheorem [normal Zero, normal one'] one'
-- {-@ w :: NFOrd @-}
-- w = let w' = Ord one 1 Zero in castWithTheorem [normal Zero, normal w'] w'




{-@ reflect nat2ord' @-}
nat2ord' :: Int -> Ordinal
nat2ord' 0 = Zero
nat2ord' p = Ord Zero p Zero

{-@ normal_nat :: n:Nat -> {normal (nat2ord' n)} @-}
normal_nat :: Int -> ()
normal_nat n = [normal Zero, normal (nat2ord' n)] *** QED 

{-@ nat2ord :: Nat -> NFOrd @-}
nat2ord :: Int -> Ordinal
nat2ord n = castWithTheorem (normal_nat n) (nat2ord' n) where


{-@ zero :: NFOrd @-}
zero = nat2ord 0
{-@ one :: NFOrd @-}
one = nat2ord 1
{-@ w :: NFOrd @-}
w = let w = (Ord one 1 Zero) in castWithTheorem [normal Zero, normal w] w



-- {-@ addOrd :: Ordinal -> Ordinal -> Ordinal @-}
-- addOrd :: Ordinal -> Ordinal -> Ordinal
-- addOrd x Zero = x
-- addOrd Zero y = y
-- addOrd (Ord a0 n0 b0) (Ord a1 n1 b1) = case (compOrd a0 a1) of
--     LT -> (Ord a1 n1 b1)
--     GT -> (Ord a0 n0 (addOrd b0 (Ord a1 n1 b1)))
--     EQ -> (Ord a0 (n0+n1) (addOrd b0 b1))




-- err = (Ord Zero 1 w)

main = do
    print $ "start"
    -- print $ normal x
    -- print $ degree one
    -- print $ w
    -- print $ compOrd (degree one) w






