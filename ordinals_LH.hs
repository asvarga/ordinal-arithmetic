
-- An implementation of ordinal arithmetic
-- Liquid Haskell is used to require all Ordinals (NFO) to be in Cantor Normal Form
    -- Comments like {-@ ... @-} are for LH
    -- To type-check with LH, run: liquid ordinals_LH.hs

----------------------------------------------------------------  

{-@ LIQUID "--reflection" @-}

module O where      -- keeps LH error messages legible

import NewProofCombinators

----------------------------------------------------------------

-- (Ord a n b) = ω^a * n + b
{-@ data Ordinal [size] @-}
data Ordinal = Ord Ordinal Int Ordinal
             | Zero
             deriving (Eq, Show)

{-@ measure size @-}
{-@ size :: Ordinal -> Nat @-}
size :: Ordinal -> Int
size Zero = 0
size (Ord a n b) = 1 + (size a) + n*n + (size b)

{-@ reflect normal @-}
normal :: Ordinal -> Bool
normal Zero = True
normal (Ord a n b) = (normal a) && (n > 0) && (normal b) && (case b of
    Zero -> True
    (Ord c _ _) -> (comp c a == LT))

----------------------------------------------------------------

-- Ordinals in Cantor Normal Form:
{-@ type NFOrd = {v:Ordinal | normal v} @-}

-- Until LH supports typeclasses with directly refined types, need this wrapper:
{-@ data NFO = NFO { nfo :: NFOrd } @-}
data NFO = NFO Ordinal deriving (Eq)

zero    = NFO zero'
one     = NFO one'
w       = NFO w'
ω       = w
ww      = NFO ww'

instance Ord NFO where compare (NFO x) (NFO y) = comp x y

instance Num NFO where
    (+) (NFO x) (NFO y) = NFO $ add x y 
    (-) (NFO x) (NFO y) = NFO $ sub x y
    (*) (NFO x) (NFO y) = NFO $ mul x y
    abs = id
    signum = const one
    fromInteger i = NFO $ n2o . abs' . fromIntegral $ i

instance Show NFO where show (NFO x) = str x

----------------------------------------------------------------

---- INSTANCE ORD ----

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

{-@ total :: x:Ordinal -> y:Ordinal -> {(comp x y == EQ) <=> (x == y)} @-}
total :: Ordinal -> Ordinal -> ()
total x@Zero y@Zero = (x `comp` y == EQ) *** QED
total x@Zero y@(Ord a1 n1 b1) = ((x `comp` y == EQ) == False) *** QED
total x@(Ord a0 n0 b0) y@Zero = ((x `comp` y == EQ) == False) *** QED
total x@(Ord a0 n0 b0) y@(Ord a1 n1 b1) = ((x `comp` y == EQ) == (x == y))
    === (case (a0 `comp` a1) of
            LT -> (False == (x == y))
            GT -> (False == (x == y))
            EQ -> case (n0 `compInt` n1) of
                LT -> (False == (x == y))
                GT -> (False == (x == y))
                EQ -> ((x `comp` y == EQ) == (x == y)))
    ==? True ? (total a0 a1 &&& total b0 b1) *** QED

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

---- INSTANCE NUM ---- 

{-@ reflect n2o' @-}
n2o' 0 = Zero
n2o' p = Ord Zero p Zero
{-@ normal_nat :: n:Nat -> {normal (n2o' n)} @-}
normal_nat :: Int -> ()
normal_nat p = normal (n2o' p) === normal Zero *** QED
{-@ n2o :: Nat -> NFOrd @-}
n2o n = (n2o' n) `withProof` (normal_nat n)
{-@ abs' :: Int -> Nat @-}
abs' :: Int -> Int
abs' n
  | 0 < n     = n
  | otherwise = 0 - n


{-@ zero' :: NFOrd @-}
zero'   = n2o 0
{-@ one' :: NFOrd @-}
one'    = n2o 1
{-@ w' :: NFOrd @-}
w'      = let w' = (Ord one' 1 Zero) in w' `withProof` [normal Zero, normal w']
{-@ ww' :: NFOrd @-}
ww'     = let ww' = (Ord w' 1 Zero) in ww' `withProof` [normal Zero, normal ww']

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
                 &&& total a1 a0
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
{-@ mul' :: x:_ -> y:_ -> _ / [(size x), (size y)] @-}
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

---- INSTANCE SHOW ---- 

str :: Ordinal -> String
str Zero = "0"
str (Ord Zero n Zero) = (show n)
str (Ord a n b) = (f a) ++ (g n) ++ (h b) where
    f (Ord Zero 1 Zero) = "ω"
    f (Ord Zero n Zero) = "ω^" ++ (show n)
    f a = "ω^(" ++ (str a) ++ ")"
    g 1 = ""
    g n = "*" ++ (show n)
    h Zero = ""
    h b = " + " ++ (str b)

----------------------------------------------------------------

main = do
    print $ w + 1
    print $ 1 + w
    print $ ww * w
    print $ w * ww
    print $ w * 5
    print $ w + ww*3 + w*w*5 + w + 2
    print $ compare one w
    print $ abs w * signum w
    






