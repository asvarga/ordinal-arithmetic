
{-@ LIQUID "--reflection" @-}
-- {-@ LIQUID "--exact-data-cons" @-}
-- {-@ LIQUID "--ple" @-}
-- {-@ LIQUID "--higherorder"     @-}

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

{-@ reflect maxOrd @-}
maxOrd :: Ordinal -> Ordinal -> Ordinal
maxOrd a b = case (compOrd a b) of
    LT -> b
    GT -> a
    EQ -> a

{-@ comp_i_i_EQ :: i:Int -> {(compInt i i == EQ)} @-}
comp_i_i_EQ :: Int -> ()
comp_i_i_EQ i = compInt i i === EQ *** QED

{-@ comp_x_x_EQ :: x:Ordinal -> {(compOrd x x == EQ)} @-}
comp_x_x_EQ :: Ordinal -> ()
comp_x_x_EQ Zero = compOrd Zero Zero === EQ *** QED
comp_x_x_EQ (Ord a n b) =   compOrd (Ord a n b) (Ord a n b)
                        ==? EQ ? (comp_x_x_EQ a &&& comp_i_i_EQ n &&& comp_x_x_EQ b) 
                        *** QED 

{-@ eq_is_eq :: x:Ordinal -> y:Ordinal -> {(compOrd x y == EQ) <=> (x == y)} @-}
eq_is_eq :: Ordinal -> Ordinal -> ()
eq_is_eq Zero Zero = ((compOrd Zero Zero == EQ) == (Zero == Zero)) *** QED
eq_is_eq Zero (Ord a1 n1 b1) = 
    ((compOrd Zero (Ord a1 n1 b1) == EQ) == (Zero == (Ord a1 n1 b1))) *** QED
eq_is_eq (Ord a0 n0 b0) Zero = 
    ((compOrd (Ord a0 n0 b0) Zero == EQ) == ((Ord a0 n0 b0) == Zero)) *** QED
eq_is_eq (Ord a0 n0 b0) (Ord a1 n1 b1) =  
    ((compOrd (Ord a0 n0 b0) (Ord a1 n1 b1) == EQ) == ((Ord a0 n0 b0) == (Ord a1 n1 b1)))
    === (case (compOrd a0 a1) of
            LT -> (False == ((Ord a0 n0 b0) == (Ord a1 n1 b1))) 
                   ==? True ? (comp_x_x_EQ a0)
            GT -> (False == ((Ord a0 n0 b0) == (Ord a1 n1 b1)))
                   ==? True ? (comp_x_x_EQ a0)
            EQ -> case (compInt n0 n1) of
                LT -> (False == ((Ord a0 n0 b0) == (Ord a1 n1 b1))) === True
                GT -> (False == ((Ord a0 n0 b0) == (Ord a1 n1 b1))) === True
                EQ -> ((compOrd (Ord a0 n0 b0) (Ord a1 n1 b1) == EQ) == ((Ord a0 n0 b0) == (Ord a1 n1 b1)))
                       === (((compOrd b0 b1) == EQ) == (b0 == b1))
                       ==? True ? (eq_is_eq b0 b1 &&& comp_x_x_EQ b0))
    *** QED


Try eq is eq with ints first, and then try ords



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
normal_nat :: Int -> ()
-- normal_nat 0 = ()
-- normal_nat p = normal_nat 0
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





{-@ reflect addOrd' @-}
addOrd' :: Ordinal -> Ordinal -> Ordinal
addOrd' x Zero = x
addOrd' Zero y = y
-- addOrd' x@(Ord a0 n0 b0) y@(Ord a1 n1 b1) = case (compOrd a0 a1) of
--     LT -> y
--     GT -> (Ord a0 n0 (addOrd' b0 y))
--     EQ -> (Ord a0 (n0+n1) (addOrd' b0 b1))
addOrd' x@(Ord a0 n0 b0) y@(Ord a1 n1 b1) = case (compOrd a1 a0) of
    GT -> y
    LT -> (Ord a0 n0 (addOrd' b0 y))
    EQ -> (Ord a1 (n0+n1) (addOrd' b0 b1))


-- READ THIS: https://arxiv.org/pdf/1806.03541.pdf

-- {-@ normal_add :: x:NFOrd -> y:NFOrd -> {normal (addOrd' x y)} / [(size x), (size y)] @-}
-- normal_add :: Ordinal -> Ordinal -> ()
-- normal_add x Zero = ()
-- normal_add Zero y = ()
-- normal_add x@(Ord a0 n0 b0) y@(Ord a1 n1 b1) = (normal_add b0 b1) &&& (normal_add b0 y)


-- LEMMA: compOrd x y == op (compOrd y x) where
--     op LT = GT
--     op EQ = EQ
--     op GT = LT
-- LEMMA: compOrd x y == EQ -> x == y



-- normal_add x Zero = normal (addOrd' x Zero) *** QED
-- normal_add Zero y = normal (addOrd' Zero y) *** QED
-- -- normal_add x@(Ord a0 n0 b0) y@(Ord a1 n1 b1) = 
-- --     let evidence = ((normal x == True *** QED)
-- --                  &&& (normal y == True *** QED)
-- --                  &&& normal_add b0 b1
-- --                  &&& normal_add b0 y)
-- --     in  (normal (addOrd' (Ord a0 n0 b0) (Ord a1 n1 b1)) 
-- --     === (case (compOrd a1 a0) of
-- --             GT -> (normal y === True)
-- --             LT -> (normal (Ord a0 n0 (addOrd' b0 y)) ==? True ? evidence)
-- --             EQ -> (normal (Ord a0 (n0+n1) (addOrd' b0 b1)) ==? True ? evidence))
-- --     *** QED)
-- normal_add x@(Ord a0 n0 b0) y@(Ord a1 n1 b1@Zero) = 
--     let evidence = ((normal x == True *** QED)
--                  &&& (normal y == True *** QED)
--                  &&& normal_add b0 b1
--                  &&& normal_add b0 y)
--     in  (normal (addOrd' (Ord a0 n0 b0) (Ord a1 n1 Zero)) 
--     === (case (compOrd a1 a0) of
--             GT -> (normal y === True)
--             LT -> (normal (Ord a0 n0 (addOrd' b0 y)) ==? True ? evidence)
--             EQ -> (normal (Ord a1 (n0+n1) (addOrd' b0 Zero)) ==? True ? evidence))
--     *** QED)
-- -- maybe change b0@Zero -> b0?
-- -- normal_add x@(Ord a0 n0 b0@Zero) y@(Ord a1 n1 b1@(Ord c1 m1 d1)) = 
-- --     let evidence = ((normal x == True *** QED)
-- --                  &&& (normal y == True *** QED)
-- --                  &&& (compOrd c1 a0 == LT *** QED)
-- --                  &&& (a0 == a1 *** QED)
-- --                  &&& (n0+n1 > 0 *** QED)
-- --                  &&& normal_add Zero b1
-- --                  &&& normal_add Zero y)
-- --     in  (normal (addOrd' (Ord a0 n0 Zero) (Ord a1 n1 (Ord c1 m1 d1))) 
-- --     === (case (compOrd a1 a0) of
-- --             GT -> (normal y === True)
-- --             LT -> (normal (Ord a0 n0 (addOrd' Zero y)) ==? True ? evidence)
-- --             EQ -> (normal (Ord a0 (n0+n1) (addOrd' Zero b1 === b1)) ==? True ? evidence))
-- --     *** QED)

    -- let evidence = ((normal x == True *** QED)
    --                  &&& (normal y == True *** QED)
    --                  &&& (addOrd' b0 b1 == Zero *** QED)
    --                  &&& normal_add b0 b1)
    -- in case (compOrd a0 a1) of
    --     LT -> normal (addOrd' x y) *** QED 
    --     GT -> normal (Ord a0 n0 (addOrd' b0 y)) *** QED
    --     EQ -> normal (Ord a0 (n0+n1) (addOrd' b0 b1))
    --           === ((normal a0 ==? True ? evidence)
    --                 && (n0+n1 > 0 ==? True ? evidence)
    --                 && (normal (addOrd' b0 b1) ==? True ? evidence)
    --                 && (((addOrd' b0 b1) == Zero) ==? True ? evidence) )
    --                     -- === (compOrd Zero a0 == LT) 
    --                     -- ==? True ? evidence))
    --                 -- (case (addOrd' b0 b1) of
    --                         -- Zero -> True
    --                         -- (Ord a2 _ _) -> ((compOrd a2 a0 == LT) ==? True ? evidence)))
    --           -- === (True && True && True && True)
    --           -- === True
    --           *** QED

-- a0 and a1 are allowed to be Zero! I've assumed they aren't



-- normal_add x@(Ord a0 n0 b0) y@(Ord a1 n1 b1) = 
--     let evidence = ((normal x == True *** QED)
--                      &&& (normal y == True *** QED)
--                      &&& ((case b0 of
--                             Zero -> True
--                             Ord a2 _ _ -> compOrd a2 a0 == LT) *** QED)
--                      &&& ((case b1 of
--                             Zero -> True
--                             Ord a2 _ _ -> compOrd a2 a0 == LT) *** QED)
--                      &&& normal_add b0 b1
--                      &&& normal_add b0 y)
--     in case (compOrd a1 a0) of
--         GT -> normal (addOrd' x y) *** QED 
--         LT -> normal (Ord a0 n0 (addOrd' b0 y)) *** QED
--         EQ -> normal (Ord a0 (n0+n1) (addOrd' b0 b1))
--               === ((normal a0 ==? True ? evidence)
--                     && (n0+n1 > 0 ==? True ? evidence)
--                     && (normal (addOrd' b0 b1) ==? True ? evidence)
--                     && (case (addOrd' b0 b1) of
--                             Zero -> True
--                             (Ord c _ _) -> ((compOrd c a0 == LT) ==? True ? (case (b0, b1) of
--                                 (Zero, Zero) -> trivial *** QED
--                                 (Ord a2 _ _, Zero) -> 
--                                     ((c === a2 *** QED) &&& (compOrd a2 a0 == LT *** QED))
--                                 (Zero, Ord a3 _ _) -> 
--                                     ((c === a3 *** QED) &&& (compOrd a3 a0 == LT *** QED))
--                                 (Ord a2 _ _, Ord a3 _ _) -> 
--                                     ((c === (maxOrd a2 a3) *** QED)
--                                         &&& (compOrd a2 a0 == LT *** QED)
--                                         &&& (compOrd a3 a0 == LT *** QED))))))
--               -- ==? True ? evidence
--               *** QED




              -- case (compOrd a2 a3) of 
              --     LT -> a3
              --     GT -> a2
              --     EQ -> a2

    -- EQ -> normal (Ord a0 (n0+n1) (addOrd' b0 b1)) 
    --       === (case (addOrd' b0 b1) of
    --               Zero -> True
    --               (Ord c _ _) -> (compOrd c a0 == LT)) *** QED

-- normal :: Ordinal -> Bool
-- normal Zero = True
-- normal (Ord a n b) = (normal a) && (n > 0) && (normal b) && (case b of
--     Zero -> True
--     (Ord c _ _) -> (compOrd c a == LT))


    -- LT -> [addOrd' x y == y] *** QED
    -- GT -> [addOrd' x y == (Ord a0 n0 (addOrd' b0 y))] *** QED
    -- EQ -> [addOrd' x y == (Ord a0 (n0+n1) (addOrd' b0 b1))] *** QED

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






