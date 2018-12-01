
module O where

{-@ LIQUID "--reflection" @-}
-- {-@ LIQUID "--ple" @-}

-- import Language.Haskell.Liquid.NewProofCombinators
import NewProofCombinators

----------------------------------------------------------------

-- (Ord a n b) = a^n + b
-- require Cantor Normal Form and use the measure "size" to check termination
{-@ data Ordinal [size] @-}
data Ordinal = Ord Ordinal Int Ordinal
             | Zero
             deriving (Eq, Show)

{-@ measure size @-}
{-@ size :: Ordinal -> Nat @-}
size :: Ordinal -> Int
size Zero = 0
size (Ord a n b) = (size a) + 1 + (size b)

{-@ type NFOrd = {v:Ordinal | normal v} @-}
{-@ reflect normal @-}
normal :: Ordinal -> Bool
normal Zero = True
normal (Ord a n b) = (normal a) && (n > 0) && (normal b) && (case b of
    Zero -> True
    (Ord c _ _) -> (compOrd c a == LT))

{-@ type Pos = {v:Int | v > 0} @-}

----------------------------------------------------------------

-- instance Show Ordinal where
--     show Zero = "0"
--     show (Ord Zero n Zero) = (show n)
--     show (Ord a n b) = (f a) ++ (g n) ++ (h b)
--         where
--             f (Ord Zero 1 Zero) = "ω"
--             f (Ord Zero x Zero) = "ω^" ++ (show x)
--             f a = "ω^(" ++ (show a) ++ ")"
--             g 1 = ""
--             g n = "*" ++ (show n)
--             h Zero = ""
--             h b = " + " ++ (show b)

----------------------------------------------------------------

instance Ord Ordinal where compare = compOrd

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

{-@ reflect maxOrd @-}
maxOrd :: Ordinal -> Ordinal -> Ordinal
maxOrd a b = case (compOrd a b) of
    LT -> b
    GT -> a
    EQ -> a

{-@ reflect op @-}
op :: Ordering -> Ordering
op LT = GT
op GT = LT
op EQ = EQ

{-@ eq_is_eq :: x:Ordinal -> y:Ordinal -> {(compOrd x y == EQ) <=> (x == y)} @-}
eq_is_eq :: Ordinal -> Ordinal -> ()
eq_is_eq x@Zero y@Zero = (compOrd x y == EQ) *** QED
eq_is_eq x@Zero y@(Ord a1 n1 b1) = ((compOrd x y == EQ) == False) *** QED
eq_is_eq x@(Ord a0 n0 b0) y@Zero = ((compOrd x y == EQ) == False) *** QED
eq_is_eq x@(Ord a0 n0 b0) y@(Ord a1 n1 b1) = ((compOrd x y == EQ) == (x == y))
    === (case (compOrd a0 a1) of
            LT -> (False == (x == y))
            GT -> (False == (x == y))
            EQ -> case (compInt n0 n1) of
                LT -> (False == (x == y))
                GT -> (False == (x == y))
                EQ -> ((compOrd x y == EQ) == (x == y)))
    ==? True ? (eq_is_eq a0 a1 &&& eq_is_eq b0 b1) *** QED


-- TODO: LEMMA: compOrd x y == op (compOrd y x) 

----------------------------------------------------------------

instance Num Ordinal where
    (+) x y = Zero -- addOrd (norm x) (norm y) ???
    (-) _ _ = Zero
    (*) _ _ = Zero
    abs x = x
    signum x = (Ord Zero 1 Zero)
    fromInteger = fromInteger' -- nat2ord . abs' . fromIntegral

----

{-@ reflect nat2ord' @-}
nat2ord' 0 = Zero
nat2ord' p = Ord Zero p Zero
{-@ normal_nat :: n:Nat -> {normal (nat2ord' n)} @-}
normal_nat :: Int -> ()
normal_nat 0 =   normal (nat2ord' 0)
             === normal Zero
             *** QED
normal_nat p =   normal (nat2ord' p)
             === normal Zero
             *** QED
{-@ nat2ord :: Nat -> NFOrd @-}
nat2ord n = (nat2ord' n) `withProof` (normal_nat n)
{-@ abs' :: Int -> Nat @-}
abs' :: Int -> Int
abs' n
  | 0 < n     = n
  | otherwise = 0 - n
{-@ fromInteger' :: Integer -> NFOrd @-}
fromInteger' = nat2ord . abs' . fromIntegral

----

{-@ reflect addOrd' @-}
addOrd' :: Ordinal -> Ordinal -> Ordinal
addOrd' x Zero = x
addOrd' Zero y = y
addOrd' x@(Ord a0 n0 b0) y@(Ord a1 n1 b1) = case (compOrd a1 a0) of
    GT -> y
    LT -> (Ord a0 n0 (addOrd' b0 y))
    EQ -> (Ord a0 (n0+n1) (addOrd' b0 b1))
{-@ normal_add :: x:NFOrd -> y:NFOrd -> {normal (addOrd' x y)} / [(size x), (size y)] @-}
normal_add :: Ordinal -> Ordinal -> ()
normal_add x y@Zero = normal (addOrd' x y) *** QED
normal_add x@Zero y = normal (addOrd' x y) *** QED
normal_add x@(Ord a0 n0 b0) y@(Ord a1 n1 b1) = normal (addOrd' x y) 
    === (case (compOrd a1 a0) of
            GT -> (normal y)
            LT -> (normal (Ord a0 n0 (addOrd' b0 y)))
            EQ -> (normal (Ord (a1 ==? a0 ? eq_is_eq a1 a0) (n0+n1) (addOrd' b0 b1))))
    ==? True ? ((normal x == True *** QED)
                 &&& (normal y == True *** QED)
                 &&& normal_add b0 b1
                 &&& normal_add b0 y) *** QED
{-@ addOrd :: NFOrd -> NFOrd -> NFOrd @-}
addOrd x y = (addOrd' x y) `withProof` (normal_add x y)

----------------------------------------------------------------

{-@ zero :: NFOrd @-}
zero = nat2ord 0
{-@ one :: NFOrd @-}
one = nat2ord 1
{-@ w :: NFOrd @-}
w = let w = (Ord one 1 Zero) in w `withProof` [normal Zero, normal w]

main = do
    print $ "start"
    print $ compOrd w (nat2ord 3)
    print $ one `addOrd` one `addOrd` one
    -- print $ addOrd (nat2ord 2) (nat2ord 3)

    -- print $ normal x
    -- print $ degree one
    -- print $ w
    -- print $ compOrd (degree one) w






