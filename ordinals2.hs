
-- {-@ LIQUID "--reflection" @-}
{-@ LIQUID "--exact-data-cons" @-}
-- {-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder"     @-}

-- import Language.Haskell.Liquid.NewProofCombinators
import NewProofCombinators

-- {-@ die :: {v:String | false} -> a @-}
-- die :: String -> a
-- die msg = error msg
-- {-@ lAssert  :: {v:Bool | v == True} -> a -> a @-}
-- lAssert True  x = x
-- lAssert False _ = die "yikes, assertion fails!"
-- yes = lAssert (1 + 1 == 2) ()
-- -- no  = lAssert (1 + 1 == 3) ()

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

----------------------------------------------------------------

instance Num Ordinal where
    (+) _ _ = Zero
    (-) _ _ = Zero
    (*) _ _ = Zero
    abs x = x
    signum x = (Ord Zero 1 Zero)
    fromInteger = fromInteger'

{-@ reflect nat2ord' @-}
nat2ord' 0 = Zero
nat2ord' p = Ord Zero p Zero
{-@ normal_nat :: n:Nat -> {normal (nat2ord' n)} @-}
normal_nat 0 =   normal (nat2ord' 0)
             === normal Zero
             === True
             *** QED
normal_nat p =   normal (nat2ord' p)
             === normal (Ord Zero p Zero)
             === normal Zero
             === True
             *** QED
-- normal_nat n = [normal Zero, normal (nat2ord' n)] *** QED 
{-@ nat2ord :: Nat -> NFOrd @-}
nat2ord n = (nat2ord' n) `withProof` (normal_nat n)
{-@ abs' :: Int -> Nat @-}
abs' :: Int -> Int
abs' n
  | 0 < n     = n
  | otherwise = 0 - n
{-@ fromInteger' :: Integer -> NFOrd @-}
fromInteger' = nat2ord . abs' . fromIntegral





{-@ reflect addOrd' @-}
addOrd' :: Ordinal -> Ordinal -> Ordinal
addOrd' x Zero = x
addOrd' Zero y = y
addOrd' x@(Ord a0 n0 b0) y@(Ord a1 n1 b1) = case (compOrd a0 a1) of
    LT -> y
    GT -> (Ord a0 n0 (addOrd' b0 y))
    EQ -> (Ord a0 (n0+n1) (addOrd' b0 b1))


-- READ THIS: https://arxiv.org/pdf/1806.03541.pdf

-- {-@ normal_add :: x:NFOrd -> y:NFOrd -> {normal (addOrd' x y)} / [(size x) + (size y)] @-}
-- normal_add x Zero = normal (addOrd' x Zero) *** QED
-- normal_add Zero y = normal (addOrd' Zero y) *** QED
-- normal_add x@(Ord a0 n0 b0) y@(Ord a1 n1 b1) = case (compOrd a0 a1) of
--     LT -> [addOrd' x y == y] *** QED
--     GT -> [addOrd' x y == (Ord a0 n0 (addOrd' b0 y))] *** QED
--     EQ -> [addOrd' x y == (Ord a0 (n0+n1) (addOrd' b0 b1))] *** QED

            -- [ normal a0,
            --         n0 > 0,
            --         n1 > 0,
            --         n0+n1 > 0, 
            --         normal b0, 
            --         normal b1, 
            --         normal (addOrd' b0 b1), 
            --         case (addOrd' b0 b1) of
            --             Zero -> True
            --             (Ord c _ _) -> (compOrd c a0 == LT),
            --         addOrd' x y == (Ord a0 (n0+n1) (addOrd' b0 b1)),
            --         normal (addOrd' x y)]
            --     *** QED




 -- normal a0
 --                ==> n0+n1 > 0
 --                ==> 


-- ∵



--{-@ addOrd :: NFOrd -> NFOrd -> NFOrd @-}





----------------------------------------------------------------

{-@ zero :: NFOrd @-}
zero = nat2ord 0
{-@ one :: NFOrd @-}
one = nat2ord 1
{-@ w :: NFOrd @-}
w = let w = (Ord one 1 Zero) in w `withProof` [normal Zero, normal w]

five :: Ordinal
five = 2+3

main = do
    print $ "start"
    print $ compOrd w (nat2ord 3)
    -- print $ addOrd (nat2ord 2) (nat2ord 3)

    -- print $ normal x
    -- print $ degree one
    -- print $ w
    -- print $ compOrd (degree one) w






