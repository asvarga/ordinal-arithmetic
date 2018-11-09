
-- An implementation of ordinal arithmetic
-- Comments like {-@ ... @-} are for Liquid Haskell

----------------------------------------------------------------

import Prelude hiding ((^))
import qualified Prelude as P ((^))

{-@ data Ordinal [size] @-}     -- use 'size' to prove termination
data Ordinal = Ord [(Ordinal, Integer)] -- (Ord (a, n):b) = a^n + b
             deriving Eq

{-@ measure size @-}            -- size is a measure
{-@ size :: Ordinal -> Nat @-}  -- LH provides Nat `subset` Integer
size :: Ordinal -> Integer
size (Ord []) = 0
size (Ord ((a, n):b)) = (size a) + 1 + (size (Ord b))

-- {-@ type NFOrd ::  @-}


-- build Ordinals from lists
-- ord :: [(Ordinal, Integer)] -> Ordinal
-- ord = foldr (\(a, n) (Ord b) -> (Ord ((a, n):b))) (Ord [])

-- zero = fromInteger 0
-- one = fromInteger 1
-- two = fromInteger 2
-- three = fromInteger 3
-- four = fromInteger 4
-- five = fromInteger 5
-- w = (Ord [(one, 1)])
-- ω = w

instance Show Ordinal where
    show (Ord []) = "0"
    show (Ord [(Ord [], n)]) = (show n)
    show (Ord ((a, n):b)) = (f a) ++ (g n) ++ (h b)
        where
            f (Ord [(Ord [], 1)]) = "ω"
            f (Ord [(Ord [], x)]) = "ω^" ++ (show x)
            f a = "ω^(" ++ (show a) ++ ")"
            g 1 = ""
            g n = "*" ++ (show n)
            h [] = ""
            h b = " + " ++ (show b)

instance Ord Ordinal where
    compare (Ord []) (Ord []) = EQ
    compare (Ord []) (Ord ((a, n):b)) = LT
    compare (Ord ((a, n):b)) (Ord []) = GT
    compare (Ord ((a0, n0):b0)) (Ord ((a1, n1):b1)) = 
        case (compare a0 a1) of
            LT -> LT
            GT -> GT
            EQ -> case (compare n0 n1) of
                LT -> LT
                GT -> GT
                EQ -> compare b0 b1

-- Based On: https://en.wikipedia.org/wiki/Ordinal_arithmetic#Cantor_normal_form
-- instance Num Ordinal where
--     (+) x (Ord []) = x
--     (+) (Ord []) y = y
--     (+) (Ord ((a0, n0):b0)) (Ord ((a1, n1):b1)) = case (compare a0 a1) of
--         LT -> (Ord ((a1, n1):b1))
--         GT -> (Ord a0 n0 (b0+(Ord ((a1, n1):b1))))
--         EQ -> (Ord a0 (n0+n1) (b0+b1))
--     -- (-) x (Ord []) = x
--     -- (-) (Ord []) y = (Ord [])
--     -- (-) (Ord ((a0, n0):b0)) (Ord ((a1, n1):b1)) = case (compare a0 a1) of
--     --     LT -> (Ord [])
--     --     GT -> (Ord ((a0, n0):b0))
--     --     EQ -> case (compare n0 n1) of
--     --         LT -> (Ord [])
--     --         GT -> (Ord a0 (n0-n1) b0)
--     --         EQ -> b0 - b1
--     -- (*) x (Ord []) = (Ord [])
--     -- (*) (Ord []) x = (Ord [])
--     -- (*) (Ord ((a0, n0):b0)) (Ord Zero n1 Zero) = (Ord a0 (n0*n1) b0)
--     -- (*) (Ord ((a0, n0):b0)) (Ord a1 n1 Zero) = (Ord (a0+a1) n1 Zero)
--     -- (*) x (Ord ((a1, n1):b1)) = x*(Ord a1 n1 Zero) + x*b1
--     abs x = x
--     signum x = one
--     fromInteger 0 = (Ord [])
--     fromInteger n = (Ord [(zero, n)])

-- (^) :: Ordinal -> Ordinal -> Ordinal                -- let 1 < n < ω:
-- (^) x Zero = one                                    -- x^0 = 1
-- (^) x (Ord Zero n Zero) = x P.^ n                   -- x^n uses Prelude's ^
-- (^) (Ord Zero 1 Zero) y = one                       -- 1^y = 1
-- (^) (Ord Zero n Zero) (Ord y 1 Zero) =              -- n^(ω^y) = ω^(ω^(y-1)) 
--     (Ord (Ord (y-one) 1 Zero) 1 Zero)               --   ex: 2^(ω^4) = ω^(ω^3)
-- (^) (Ord (Ord a b c) n rest) y =                    -- (ω^x)^y = ω^(x*y)
--     (Ord ((Ord a b c)*y) 1 Zero)                    --   ex: (ω^ω)^3 = ω^(ω*3)
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
    print $ "hello"
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
--     print $ 2^(w^4 + w^3 + 5)    
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










