
-- {-@ LIQUID "--reflection" @-}
{-@ LIQUID "--exact-data-cons" @-}
-- {-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder"     @-}

-- import Language.Haskell.Liquid.ProofCombinators
import ProofCombinators

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
normal_nat n = [normal Zero, normal (nat2ord' n)] *** QED 
{-@ nat2ord :: Nat -> NFOrd @-}
nat2ord n = castWithTheorem (normal_nat n) (nat2ord' n)
{-@ abs' :: Int -> Nat @-}
abs' :: Int -> Int
abs' n
  | 0 < n     = n
  | otherwise = 0 - n
{-@ fromInteger' :: Integer -> NFOrd @-}
fromInteger' = nat2ord . abs' . fromIntegral









-- {-@ addOrd :: Ordinal -> Ordinal -> Ordinal @-}
-- addOrd :: Ordinal -> Ordinal -> Ordinal
-- addOrd x Zero = x
-- addOrd Zero y = y
-- addOrd (Ord a0 n0 b0) (Ord a1 n1 b1) = case (compOrd a0 a1) of
--     LT -> (Ord a1 n1 b1)
--     GT -> (Ord a0 n0 (addOrd b0 (Ord a1 n1 b1)))
--     EQ -> (Ord a0 (n0+n1) (addOrd b0 b1))






----------------------------------------------------------------

{-@ zero :: NFOrd @-}
zero = nat2ord 0
{-@ one :: NFOrd @-}
one = nat2ord 1
{-@ w :: NFOrd @-}
w = let w = (Ord one 1 Zero) in castWithTheorem [normal Zero, normal w] w

five :: Ordinal
five = 2+3

main = do
    print $ "start"
    print $ compOrd w (nat2ord 3)
    print $ five
    -- print $ normal x
    -- print $ degree one
    -- print $ w
    -- print $ compOrd (degree one) w






