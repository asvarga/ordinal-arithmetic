
-- {-@ LIQUID "--reflection" @-}
{-@ LIQUID "--exact-data-cons" @-}
-- {-@ LIQUID "--ple" @-}

import Language.Haskell.Liquid.ProofCombinators

----------------------------------------------------------------

-- (Ord a n b) = a^n + b
-- require Cantor Normal Form and use the measure "size" to check termination
-- the "v == Zero" is because degree is truncated to be >= Zero
-- {-@ data Ordinal [size] 
--     = Ord { a :: Ordinal, 
--             n :: {v:Nat | v > 0},  
--             b :: {v:Ordinal | degLT v a} }
--     | Zero {} @-}
{-@ data Ordinal [size] @-}
{-@ type NFOrd = {v:Ordinal | normal v} @-}
data Ordinal = Ord Ordinal Integer Ordinal
             | Zero
             deriving (Eq, Show)

-- (compOrd (degree v) a == LT) || v == Zero

-- {-@ reflect degLT @-}
-- {-@ degLT :: Ordinal -> Ordinal -> Bool @-}
-- degLT :: Ordinal -> Ordinal -> Bool
-- degLT Zero _ = True
-- degLT (Ord a _ _) x = (compOrd a x == LT)


{-@ reflect normal @-}
{-@ normal :: Ordinal -> Bool @-}
normal :: Ordinal -> Bool
normal Zero = True
normal (Ord a n b) = (normal a) && (n >= 0) && (normal b) && (case b of
    Zero -> True
    (Ord c _ _) -> (compOrd c a == LT))


{-@ measure size @-}
{-@ size :: Ordinal -> Nat @-}
size :: Ordinal -> Integer
size Zero = 0
size (Ord a n b) = (size a) + 1 + (size b)

{-@ reflect degree @-}
degree :: Ordinal -> Ordinal
degree Zero = Zero              -- truncated
degree (Ord a n b) = a

{-@ reflect compInt @-}
compInt :: Integer -> Integer -> Ordering
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

-- {-@ addOrd :: Ordinal -> Ordinal -> Ordinal @-}
-- addOrd :: Ordinal -> Ordinal -> Ordinal
-- addOrd x Zero = x
-- addOrd Zero y = y
-- addOrd (Ord a0 n0 b0) (Ord a1 n1 b1) = case (compOrd a0 a1) of
--     LT -> (Ord a1 n1 b1)
--     GT -> (Ord a0 n0 (addOrd b0 (Ord a1 n1 b1)))
--     EQ -> (Ord a0 (n0+n1) (addOrd b0 b1))


-- instance Ord Ordinal where compare = compOrd

-- {-@ one :: NFOrd @-}



-- {-@ degLT_Zero_Zero :: _ -> { degLT Zero Zero } @-}
-- degLT_Zero_Zero :: () -> ()
-- degLT_Zero_Zero _ = degLT Zero Zero *** QED
-- 
-- {-@ reflect one @-}


{-@ reflect one @-}     
{-@ one :: NFOrd @-}
one = (Ord Zero 1 Zero)
{-@ reflect w @-}       
{-@ w   :: NFOrd @-}
w   = (Ord one 1 Zero)  -- omega




-- {-@ reflect x @-}       
-- {-@ x   :: NFOrd @-}
-- x   = (Ord w 1 one)


{-@ reflect err @-}       
{-@ err   :: NFOrd @-}
err   = (Ord Zero 1 w)


-- {-@ normal_one :: _ -> { normal one } @-}
-- normal_one :: () -> ()
-- normal_one _ = [normal one] *** QED


-- {-@ normal_x :: _ -> { normal x } @-}
-- normal_x :: () -> ()
-- normal_x _ = [normal x] *** QED


-- err = (Ord Zero 1 w)

main = do
    print $ "start"
    -- print $ normal x
    -- print $ degree one
    -- print $ w
    -- print $ compOrd (degree one) w








--------------------


{-
{-@ data Ordinal [size] @-}
data Ordinal = Ord Ordinal Integer Ordinal
             | Zero
             deriving (Eq, Show)
{-@ type NFOrd = { v:Ordinal | normal v } @-}


{-@ measure normal @-}
normal :: Ordinal -> Bool
normal _ = True
-- normal Zero = True
-- normal (Ord a n b) = (normal a) && (normal b) && case b of
-- 	Zero -> True
-- 	(Ord c _ _) -> ordLT c a

-- {-@ type DegreeLT D = {v:Ordinal | (ordLT (degree v) D) || v == Zero} @-}
-- -- the "v == Zero" is because degree is truncated to be >= Zero
-- {-@ measure degree @-}
-- degree :: Ordinal -> Ordinal
-- degree Zero = Zero         -- truncated     
-- degree (Ord a n b) = a

{-@ inline ordLT @-}
ordLT :: Ordinal -> Ordinal -> Bool
ordLT _ Zero = False
ordLT Zero _ = True
ordLT (Ord a0 n0 b0) (Ord a1 n1 b1) =
    (ordLT a0 a1) || 
    (a0 == a1 && n0 < n1) || 
    (a0 == a1 && n0 == n1 && ordLT b0 b1)
    
{-@ measure size @-}
{-@ size :: Ordinal -> Nat @-}
size :: Ordinal -> Integer
size Zero = 1
size (Ord a n b) = (size a) + 1 + (size b)

--------

one = (Ord Zero 1 Zero)
w   = (Ord one 1 Zero)  -- omega

main = print w          -- Ord (Ord Zero 1 Zero) 1 Zero
-}





------------------------------


{-
-- (Ord a n b) = a^n + b
{-@ data Ordinal [size] = Ord { a :: Ordinal, n :: Nat,  b :: Ordinal }
                        | Zero {} @-}
data Ordinal = Ord Ordinal Integer Ordinal
             | Zero
             deriving (Eq, Show)

{-@ measure size @-}
{-@ size :: Ordinal -> Nat @-}
size :: Ordinal -> Integer
size Zero = 1
size (Ord a n b) = (size a) + 1 + (size b)

{-@ inline ordLT @-}
ordLT :: Ordinal -> Ordinal -> Bool
ordLT _ Zero = False
ordLT Zero _ = True
ordLT (Ord a0 n0 b0) (Ord a1 n1 b1) =
    (ordLT a0 a1) || 
    (a0 == a1 && n0 < n1) || 
    (a0 == a1 && n0 == n1 && ordLT b0 b1)
    
one = (Ord Zero 1 Zero)     -- 1
w   = (Ord one 1 Zero)      -- omega
main = print w              -- Ord (Ord Zero 1 Zero) 1 Zero
-}





