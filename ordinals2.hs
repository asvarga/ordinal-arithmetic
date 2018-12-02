
-- An implementation of ordinal arithmetic
-- Liquid Haskell is used to require all Ordinals to be in Cantor Normal Form
    -- Comments like {-@ ... @-} are for LH
    -- To type-check with LH, run: liquid ordinals.hs

----------------------------------------------------------------  

module O where

{-@ LIQUID "--reflection" @-}

-- import Language.Haskell.Liquid.NewProofCombinators
import NewProofCombinators

----------------------------------------------------------------

-- (Ord a n b) = a^n + b
-- require Cantor Normal Form and use the measure "size" to check termination
{-@ data Ordinal [size] @-}
data Ordinal = Ord Ordinal Int Ordinal
             | Zero
             deriving (Eq)

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
    (Ord c _ _) -> (comp c a == LT))

----------------------------------------------------------------

-- to distinguish from Ints:
natStyle x = "[" ++ x ++ "]"

instance Show Ordinal where
    show Zero = natStyle "0"
    show (Ord Zero n Zero) = natStyle (show n)
    show (Ord a n b) = (f a) ++ (g n) ++ (h b)
        where
            f (Ord Zero 1 Zero) = "ω"
            f (Ord Zero x Zero) = "ω^" ++ (show x)
            f a = "ω^(" ++ (show a) ++ ")"
            g 1 = ""
            g n = "*" ++ (show n)
            h Zero = ""
            h b = " + " ++ (show b)

----------------------------------------------------------------

instance Ord Ordinal where compare = comp

{-@ reflect compInt @-}
compInt :: Int -> Int -> Ordering
compInt x y = if x < y then LT else if x == y then EQ else GT

{-@ reflect comp @-}
comp :: Ordinal -> Ordinal -> Ordering
comp Zero Zero = EQ
comp Zero (Ord a n b) = LT
comp (Ord a n b) Zero = GT
comp (Ord a0 n0 b0) (Ord a1 n1 b1) =
    case (a0 `comp` a1) of
        LT -> LT
        GT -> GT
        EQ -> case (n0 `compInt` n1) of
            LT -> LT
            GT -> GT
            EQ -> (b0 `comp` b1)

{-@ reflect maxOrd @-}
maxOrd :: Ordinal -> Ordinal -> Ordinal
maxOrd a b = case (a `comp` b) of
    LT -> b
    GT -> a
    EQ -> a

{-@ reflect op @-}
op :: Ordering -> Ordering
op LT = GT
op GT = LT
op EQ = EQ

{-@ eq_is_eq :: x:Ordinal -> y:Ordinal -> {(comp x y == EQ) <=> (x == y)} @-}
eq_is_eq :: Ordinal -> Ordinal -> ()
eq_is_eq x@Zero y@Zero = (x `comp` y == EQ) *** QED
eq_is_eq x@Zero y@(Ord a1 n1 b1) = ((x `comp` y == EQ) == False) *** QED
eq_is_eq x@(Ord a0 n0 b0) y@Zero = ((x `comp` y == EQ) == False) *** QED
eq_is_eq x@(Ord a0 n0 b0) y@(Ord a1 n1 b1) = ((x `comp` y == EQ) == (x == y))
    === (case (a0 `comp` a1) of
            LT -> (False == (x == y))
            GT -> (False == (x == y))
            EQ -> case (n0 `compInt` n1) of
                LT -> (False == (x == y))
                GT -> (False == (x == y))
                EQ -> ((x `comp` y == EQ) == (x == y)))
    ==? True ? (eq_is_eq a0 a1 &&& eq_is_eq b0 b1) *** QED

{-@ op_op :: x:Ordering -> {op (op x) == x} @-}
op_op x = op (op x) == x *** QED

{-@ op_compInt :: x:Int -> y:Int -> {compInt x y == op (compInt y x)} @-}
op_compInt x y = compInt x y == op (compInt y x) *** QED

{-@ op_comp :: x:Ordinal -> y:Ordinal -> {comp x y == op (comp y x)} @-}
op_comp x@Zero y = (x `comp` y == op (y `comp` x)) *** QED
op_comp x y@Zero = (x `comp` y == op (y `comp` x)) *** QED
op_comp x@(Ord a0 n0 b0) y@(Ord a1 n1 b1) = (x `comp` y == op (y `comp` x)) 
    === (case (a0 `comp` a1 ==? op (a1 `comp` a0) ? op_comp a0 a1) of
            LT -> (LT == op GT)
            GT -> (GT == op LT)
            EQ -> case (n0 `compInt` n1 ==? op (n1 `compInt` n0) ? op_compInt n0 n1) of
                LT -> (LT == op GT)
                GT -> (GT == op LT)
                EQ -> (x `comp` y == op (y `comp` x)))
    ==? True ? (op_comp b0 b1) *** QED

----------------------------------------------------------------

-- Based On: https://en.wikipedia.org/wiki/Ordinal_arithmetic#Cantor_normal_form
instance Num Ordinal where
    (+) x y = Zero -- add (norm x) (norm y) ???
    (-) x y = Zero -- sub (norm x) (norm y) ???
    (*) x y = Zero -- mul (norm x) (norm y) ???
    abs x = x
    signum x = (Ord Zero 1 Zero)
    fromInteger = fromInteger' -- nat2ord . abs' . fromIntegral

----

{-@ reflect nat2ord' @-}
nat2ord' 0 = Zero
nat2ord' p = Ord Zero p Zero
{-@ normal_nat :: n:Nat -> {normal (nat2ord' n)} @-}
normal_nat :: Int -> ()
normal_nat p = normal (nat2ord' p) === normal Zero *** QED
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

{-@ reflect add' @-}
add' :: Ordinal -> Ordinal -> Ordinal
add' x Zero = x
add' Zero y = y
add' x@(Ord a0 n0 b0) y@(Ord a1 n1 b1) = case (a1 `comp` a0) of
    GT -> y
    LT -> (Ord a0 n0 (add' b0 y))
    EQ -> (Ord a0 (n0+n1) (add' b0 b1))
{-@ normal_add :: x:NFOrd -> y:NFOrd -> {normal (add' x y)} @-}
normal_add :: Ordinal -> Ordinal -> ()
normal_add x y@Zero = normal (add' x y) *** QED
normal_add x@Zero y = normal (add' x y) *** QED
normal_add x@(Ord a0 n0 b0) y@(Ord a1 n1 b1) = normal (add' x y) 
    === (case (a1 `comp` a0) of
            GT -> (normal y)
            LT -> (normal (Ord a0 n0 (add' b0 y)))
            EQ -> (normal (Ord a0 (n0+n1) (add' b0 b1))))
    ==? True ? ((normal x *** QED)
                 &&& (normal y *** QED)
                 &&& eq_is_eq a1 a0
                 &&& normal_add b0 b1
                 &&& normal_add b0 y) *** QED
{-@ add :: NFOrd -> NFOrd -> NFOrd @-}
add x y = (add' x y) `withProof` (normal_add x y)

----

{-@ reflect sub' @-}
sub' :: Ordinal -> Ordinal -> Ordinal
sub' x Zero = x
sub' Zero y = Zero
sub' x@(Ord a0 n0 b0) y@(Ord a1 n1 b1) = case (a0 `comp` a1) of
    LT -> Zero
    GT -> x
    EQ -> case (n0 `compInt` n1) of
        LT -> Zero
        GT -> (Ord a0 (n0-n1) b0)
        EQ -> (sub' b0 b1)
{-@ normal_sub :: x:NFOrd -> y:NFOrd -> {normal (sub' x y)} @-}
normal_sub :: Ordinal -> Ordinal -> ()
normal_sub x y@Zero = normal (sub' x y) *** QED
normal_sub x@Zero y = normal (sub' x y) *** QED
normal_sub x@(Ord a0 n0 b0) y@(Ord a1 n1 b1) = normal (sub' x y) 
    === (case (a0 `comp` a1) of
            LT -> normal Zero
            GT -> normal x
            EQ -> case (n0 `compInt` n1) of
                LT -> normal Zero
                GT -> normal (Ord a0 (n0-n1) b0)
                EQ -> normal (sub' b0 b1))
    ==? True ? ((normal x *** QED)
                 &&& (normal y *** QED)
                 &&& normal_sub b0 b1) *** QED
{-@ sub :: NFOrd -> NFOrd -> NFOrd @-}
sub x y = (sub' x y) `withProof` (normal_sub x y)

----

{-@ reflect mul' @-}
{-@ mul' :: x:Ordinal -> y:Ordinal -> Ordinal / [(size x), (size y)] @-}
mul' :: Ordinal -> Ordinal -> Ordinal
mul' x Zero = Zero
mul' Zero x = Zero
mul' (Ord a0 n0 b0) (Ord Zero n1 Zero) = (Ord a0 (n0*n1) b0)
mul' (Ord a0 n0 b0) (Ord a1 n1 Zero) = (Ord (add' a0 a1) n1 Zero)
mul' x (Ord a1 n1 b1) = (add' (mul' x (Ord a1 n1 Zero)) (mul' x b1))
{-@ normal_mul :: x:NFOrd -> y:NFOrd -> {normal (mul' x y)} / [(size x), (size y)] @-}
normal_mul :: Ordinal -> Ordinal -> ()
normal_mul x y@Zero = normal (mul' x y) *** QED
normal_mul x@Zero y = normal (mul' x y) *** QED
normal_mul x@(Ord a0 n0 b0) y@(Ord Zero n1 Zero) = normal (mul' x y) 
    === normal (Ord a0 (n0*n1) b0)
    ==? True ? ((normal x *** QED) &&& (normal y *** QED)) *** QED
normal_mul x@(Ord a0 n0 b0) y@(Ord a1 n1 Zero) = normal (mul' x y) 
    === normal (Ord (add' a0 a1) n1 Zero)
    ==? True ? ((normal x *** QED) &&& (normal y *** QED) &&& normal_add a0 a1) 
    *** QED 
normal_mul x y@(Ord a1 n1 b1) = normal (mul' x y) 
    === normal (add' (mul' x (Ord a1 n1 Zero)) (mul' x b1))
    ==? True ? ((normal x *** QED) 
            &&& (normal y *** QED)
            &&& (normal Zero *** QED)
            &&& (normal (Ord a1 n1 Zero) *** QED)
            &&& normal_mul x (Ord a1 n1 Zero)
            &&& normal_mul x b1
            &&& normal_add (mul' x (Ord a1 n1 Zero)) (mul' x b1))
    *** QED
{-@ mul :: NFOrd -> NFOrd -> NFOrd @-}
mul x y = (mul' x y) `withProof` (normal_mul x y)

----------------------------------------------------------------

{-@ zero :: NFOrd @-}
zero = nat2ord 0
{-@ one :: NFOrd @-}
one = nat2ord 1
{-@ w :: NFOrd @-}
w = let w = (Ord one 1 Zero) in w `withProof` [normal Zero, normal w]

main = do
    print $ "start"
    print $ comp w (nat2ord 3)
    print $ one `add` one `add` one
    -- print $ add (nat2ord 2) (nat2ord 3)

    -- print $ normal x
    -- print $ degree one
    -- print $ w
    -- print $ comp (degree one) w






