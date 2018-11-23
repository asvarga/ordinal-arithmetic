
-- An implementation of ordinal arithmetic
-- Liquid Haskell is used to require all Ordinals to be in Cantor Normal Form
    -- Comments like {-@ ... @-} are for LH
    -- To type-check with LH, run: liquid ordinals.hs

----------------------------------------------------------------

{-@ LIQUID "--reflection" @-}

--import Prelude hiding ((^))
--import qualified Prelude as P ((^))









--  TODO:
--    LH isn't using < on Ordinals at all
--    fix and use fromInteger









----------------------------------------------------------------

-- (Ord a n b) = a^n + b
-- require Cantor Normal Form and use the measure "size" to check termination
-- the "v == Zero" is because degree is truncated to be >= Zero
{-@ data Ordinal [size] 
    = Ord { a :: Ordinal, 
            n :: Nat,  
            b :: {v:Ordinal | (compOrd (degree v) a == LT) || v == Zero } }
    | Zero {} @-}
data Ordinal = Ord Ordinal Integer Ordinal
             | Zero
             deriving Eq

{-@ measure size @-}
{-@ size :: Ordinal -> Nat @-}
size :: Ordinal -> Integer
size Zero = 1
size (Ord a n b) = (size a) + 1 + (size b)

{-@ measure degree @-}
degree :: Ordinal -> Ordinal
degree Zero = Zero              -- truncated
degree (Ord a n b) = a

{-@ reflect compInt @-}
{-@ compInt :: Integer -> Integer -> Ordering @-}
compInt :: Integer -> Integer -> Ordering
compInt x y = if x < y  then LT else if x == y then EQ else GT

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

instance Show Ordinal where
    show Zero = "0"
    show (Ord Zero n Zero) = (show n)
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


one = (Ord Zero 1 Zero) -- 1
w   = (Ord one 1 Zero)  -- omega
ω   = w








-- Based On: https://en.wikipedia.org/wiki/Ordinal_arithmetic#Cantor_normal_form
instance Num Ordinal where
    (+) _ _ = 0
    (-) _ _ = 0
    (*) _ _ = 0
    -- (+) x Zero = x
    -- (+) Zero y = y
    -- (+) (Ord a0 n0 b0) (Ord a1 n1 b1) = case (compare a0 a1) of
    --     LT -> (Ord a1 n1 b1)
    --     GT -> (Ord a0 n0 (b0+(Ord a1 n1 b1)))
    --     EQ -> (Ord a0 (n0+n1) (b0+b1))
    -- (-) x Zero = x
    -- (-) Zero y = Zero
    -- (-) (Ord a0 n0 b0) (Ord a1 n1 b1) = case (compare a0 a1) of
    --     LT -> Zero
    --     GT -> (Ord a0 n0 b0)
    --     EQ -> case (compare n0 n1) of
    --         LT -> Zero
    --         GT -> (Ord a0 (n0-n1) b0)
    --         EQ -> b0 - b1
    -- (*) x Zero = Zero
    -- (*) Zero x = Zero
    -- (*) (Ord a0 n0 b0) (Ord Zero n1 Zero) = (Ord a0 (n0*n1) b0)
    -- (*) (Ord a0 n0 b0) (Ord a1 n1 Zero) = (Ord (a0+a1) n1 Zero)
    -- (*) x (Ord a1 n1 b1) = x*(Ord a1 n1 Zero) + x*b1
    abs x = x
    signum x = 1
    fromInteger 0 = Zero
    fromInteger n = Ord Zero n Zero

-- (^) :: Ordinal -> Ordinal -> Ordinal                -- let 1 < n < ω:
-- (^) x Zero = one                                    -- x^0 = 1
-- (^) x (Ord Zero n Zero) = x P.^ n                   -- x^n uses Prelude's ^
-- (^) (Ord Zero 1 Zero) y = one                       -- 1^y = 1
-- (^) (Ord Zero n Zero) (Ord y 1 Zero) =              -- n^(ω^y) = ω^(ω^(y-1)) 
--     (Ord (Ord (y-one) 1 Zero) 1 Zero)               --   ex: 2^(ω^4) = ω^(ω^3)
-- (^) (Ord (Ord a n c) _ b) y =                       -- (ω^x)^y = ω^(x*y)
--     (Ord ((Ord a n c)*y) 1 Zero)                    --   ex: (ω^ω)^3 = ω^(ω*3)
-- (^) x (Ord y n Zero) = (x^(Ord y 1 Zero)) P.^ n     -- x^(y*n) = (x^y)^n
-- (^) x (Ord y n z) = x^(Ord y n Zero) * x^z          -- x^(y+z) = x^y * x^z

-- --------

-- a = w^2*12 + w*3 + 5
-- b = w^2*12 + w*4 + 5
-- c = w^a*12 + w^2 + w*7 + 3
-- d = w^b*12 + w^2 + w*7 + 3
-- e = w^3 + w
-- f = w^5 + w^3

main = do
    print $ w
    print $ degree one
    -- print $ (degree one) < w
    print $ Ord w 2 one

--     print $ (ω^3 + ω)^5
--     print $ (ω^5 + ω^3)^3
--     print $ "----"
--     print $ 1 + w
--     print $ c
--     print $ d
--     print $ c + d
--     print $ "----"
--     print $ a
--     print $ b
--     print $ b - a
--     print $ "----"
--     print $ (w^4*3 + w^3*2 + w^2 + w^1*10 + 100)^5
--     print $ (w^w + w^3*2 + w^2)^2
--     print $ (w+2)^0
--     print $ (w+2)^1
--     print $ (w+2)^2
--     print $ (w+2)^3
--     print $ (w+2)^4
--     print $ (w+2)^5
--     print $ "----"
--     print $ 2^0
--     print $ 2^w
--     print $ 2^(w*3 + 3)
--     print $ 2^(w^4 + w^3 + 5
--     print $ 2^(w^w)
--     print $ "----"
--     print $ w^(w^w)
--     print $ (w^w)^2
--     print $ (w^w)^w
--     print $ ((w^w)*3)^2
--     print $ (w^w)^(w^w)
--     print $ "----"
--     print $ (w*w+2)^w
--     print $ w*(w^2)


-- main = do
--     print $ "hello"







