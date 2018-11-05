
import Prelude hiding ((^))
import qualified Prelude as P ((^))

-- (Ord a n b) = a^n + b
data Ordinal  = Ord  Ordinal Integer Ordinal -- In Cantor Normal Form
              | Ord' Ordinal Integer Ordinal -- Arbitrary Ordinal
              | Zero
              deriving Eq

-- build Ordinals from lists
ord :: [(Ordinal, Integer)] -> Ordinal
ord = norm . (foldr (\(b, n) acc -> (Ord' b n acc)) Zero)

zero = fromInteger 0
one = fromInteger 1
two = fromInteger 2
three = fromInteger 3
four = fromInteger 4
five = fromInteger 5
w = ord [(one, 1)]

norm :: Ordinal -> Ordinal
norm (Ord' ord' n Zero) = (Ord (norm ord') n Zero)
norm (Ord' ord0' n0 rest') = 
    let ord0 = norm ord0'
        (Ord ord1 n1 rest) = norm rest'
        in case (compare ord0 ord1) of
            LT -> (Ord ord1 n1 rest)
            EQ -> (Ord ord1 (n0+n1) rest)
            GT -> (Ord ord0 n0 (Ord ord1 n1 rest))
norm x = x

instance Show Ordinal where
    show Zero = "0"
    show (Ord Zero n Zero) = (show n)
    show (Ord ord n rest) = (f ord) ++ (g n) ++ (h rest)
        where
            f (Ord Zero 1 Zero) = "ω"
            f (Ord Zero x Zero) = "ω^" ++ (show x)
            -- f (Ord (Ord Zero 1 Zero) 1 Zero) = "ω^ω"
            f ord = "ω^(" ++ (show ord) ++ ")"
            g 1 = ""
            g n = "*" ++ (show n)
            h Zero = ""
            h rest = " + " ++ (show rest)
    show x = "!{" ++ show (norm x) ++ "}"

instance Ord Ordinal where
    compare Zero Zero = EQ
    compare Zero (Ord x y z) = LT
    compare (Ord x y z) Zero = GT
    compare (Ord ord0 n0 rest0) (Ord ord1 n1 rest1) = 
        case (compare ord0 ord1) of
            LT -> LT
            GT -> GT
            EQ -> case (compare n0 n1) of
                LT -> LT
                GT -> GT
                EQ -> compare rest0 rest1
    compare x y = compare (norm x) (norm y)

instance Semigroup Ordinal where
    (<>) Zero x = x
    (<>) (Ord ord n rest) x = (Ord' ord n (rest <> x))
instance Monoid Ordinal where
    mempty = Zero

-- Based On: https://en.wikipedia.org/wiki/Ordinal_arithmetic#Cantor_normal_form
instance Num Ordinal where
    (+) x y = norm (x <> y)
    (-) x Zero = x
    (-) Zero y = Zero
    (-) (Ord ord0 n0 rest0) (Ord ord1 n1 rest1) = case (compare ord0 ord1) of
        LT -> Zero
        GT -> (Ord ord0 n0 rest0)
        EQ -> case (compare n0 n1) of
            LT -> Zero
            GT -> (Ord ord0 (n0-n1) rest0)
            EQ -> rest0 - rest1
    (*) x Zero = Zero
    (*) Zero x = Zero
    (*) (Ord ord0 n0 rest0) (Ord Zero n1 Zero) = (Ord ord0 (n0*n1) rest0)
    (*) (Ord ord0 n0 rest0) (Ord ord1 n1 Zero) = (Ord (ord0+ord1) n1 Zero)
    (*) x (Ord ord1 n1 rest0) = x*(Ord ord1 n1 Zero) + x*rest0
    abs x = x
    signum x = one
    fromInteger 0 = Zero
    fromInteger n = Ord Zero n Zero

(^) :: Ordinal -> Ordinal -> Ordinal                  -- let 1 < n < ω:
(^) x Zero = one                                      -- x^0 = 1
(^) x (Ord Zero n Zero) = x P.^ n                         -- x^n uses repeated *
(^) (Ord Zero 1 Zero) y = one                         -- 1^y = 1
(^) (Ord Zero n Zero) (Ord y 1 Zero) =                -- n^(ω^y) = ω^(ω^(y-1)) 
    (Ord (Ord (y-one) 1 Zero) 1 Zero)                   --   ex: 2^(ω^4) = ω^(ω^3)
(^) (Ord (Ord a b c) n rest) y =                      -- (ω^x)^y = ω^(x*y)
    (Ord ((Ord a b c)*y) 1 Zero)                        --   ex: (ω^ω)^3 = ω^(ω*3)
(^) x (Ord y n Zero) = (x^(Ord y 1 Zero)) P.^ n         -- x^(y*n) = (x^y)^n
(^) x (Ord y n z) = x^(Ord y n Zero) * x^z        -- x^(y+z) = x^y * x^z


--------

a = ord [(two, 12), (one, 3), (zero, 5)]
b = ord [(two, 12), (one, 4), (zero, 5)]
c = ord [(a, 12), (two, 1), (one, 7), (zero, 3)]
d = ord [(b, 12), (two, 1), (one, 7), (zero, 3)]
e = ord [(three, 1), (one, 1)]
f = ord [(five, 1), (three, 1)]

main = do
    print $ one + w
    print $ ord [(one, 1), (three, 1)]
    print $ "----"
    print $ c
    print $ d
    print $ c + d
    print $ "----"
    print $ a
    print $ b
    print $ b - a
    print $ "----"
    print $ a * three
    print $ a * w
    print $ a * b
    print $ "----"
    print $ e
    print $ f
    print $ e P.^ 5
    print $ e P.^ 5 == f P.^ 3
    print $ "----"
    print $ e^five
    print $ (ord [(four, 3), (three, 2), (two, 1), (one, 10), (zero, 100)])^five
    print $ (ord [(w, 1), (three, 2), (two, 1)])^two
    print $ (w+two)^one
    print $ (w+two)^two
    print $ (w+two)^three
    print $ (w+two)^four
    print $ (w+two)^five
    print $ "----"
    print $ two^zero
    print $ two^w
    print $ two^(w*three + three)
    print $ two^(w^four + w^three + five)    
    print $ two^(w^w)
    print $ "----"
    print $ w^(w^w)
    print $ (w^w)^two
    print $ (w^w)^w
    print $ ((w^w)*three)^two
    print $ (w^w)^(w^w)
    print $ "----"
    print $ (w*w+two)^w









