
{-@ LIQUID "--reflection" @-}

import NewProofCombinators

data Nat' = Z | S Nat' | T Nat' deriving Show

{-@ reflect double' @-}
double' :: Nat' -> Nat'
double' Z = Z
double' (S x) = (S (S (double' x)))
double' (T x) = (T (T (double' x)))

{-@ type Even' = {v:Nat' | even' v} @-}

{-@ reflect even' @-}
even' :: Nat' -> Bool
even' Z = True
even' (S Z) = False
even' (T Z) = False
even' (S (S x)) = even' x
even' (S (T x)) = even' x
even' (T (S x)) = even' x
even' (T (T x)) = even' x

{-@ even_double :: x:Nat' -> {even' (double' x)} @-}
even_double y = let explanation = (even_double x) in case y of
    Z     ->  even' (double' Z) 
          === even' Z   
          *** QED
    (S x) ->  even' (double' (S x))
          === even' (S (S (double' x)))
          === even' (double' x)
          ==? True ? explanation
          *** QED
    (T x) ->  even' (double' (T x))
          === even' (T (T (double' x)))
          === even' (double' x)
          ==? True ? explanation
          *** QED


-- even_double Z =     even' (double' Z) 
--               ===   even' Z   
--               ***   QED
-- even_double (S x) =     even' (double' (S x))
--                   ===   even' (S (S (double' x)))
--                   ===   even' (double' x)
--                   ==?   True ? (even_double x)
--                   ***   QED
-- even_double (T x) =     even' (double' (T x))
--                   ===   even' (T (T (double' x)))
--                   ===   even' (double' x)
--                   ==?   True ? (even_double x)
--                   ***   QED


-- even_double (S x) =     (even' (double' (S x))
--                   ===   even' (S (S (double' x)))
--                   ===   even' (double' x)
--                   ===   True
--                   ***   QED) `withProof` (even_double x)
-- even_double (S x) = let evidence = even_double x in
--                         even' (double' (S x))
--                   ===   even' (S (S (double' x)))
--                   ===   even' (double' x)
--                   ==?   True ? evidence
--                   ***   QED


{-@ double :: Nat' -> Even' @-}
double :: Nat' -> Nat'
double x = (double' x) `withProof` (even_double x)  

main = do
    print $ even' $ (S (S (S (S Z))))
    print $ even' $ (S (S (S (S (S Z)))))
    print $ even' $ double' $ (S (S (S Z)))









-- {-@ reflect add' @-}
-- add' :: Nat' -> Nat' -> Nat'
-- add' Z x = x
-- add' (S y) x = S (add' y x) 

-- {-@ even_closed :: x:Even' -> y:Even' -> {even' (add' x y)} @-}
-- even_closed Z x =    even' (add' Z x) 
--                ==.  even' x  
--                ==.  True 
--                ***  QED
-- even_closed (S (S y)) x =    even' (add' (S (S y)) x) 
--                        ==.  even' (S (add' (S y) x))
--                        ==.  even' (S (S (add' y x)))
--                        ==.  even' (add' y x) 
--                        ?    even_closed y x
--                        ==.  True
--                        ***  QED

-- {-@ add'' :: Even' -> Even' -> Even' @-}
-- add'' x y = castWithTheorem (even_closed x y) (add' x y)








-- Proof Combinator with Types Refined by Predicates
