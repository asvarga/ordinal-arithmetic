
{-@ LIQUID "--reflection" @-}

import NewProofCombinators

data Nat' = Z | S Nat' deriving Show

{-@ reflect double' @-}
double' :: Nat' -> Nat'
double' Z = Z
double' (S x) = (S (S (double' x)))

{-@ type Even' = {v:Nat' | even' v} @-}

{-@ reflect even' @-}
even' :: Nat' -> Bool
even' Z = True
even' (S Z) = False
even' (S (S x)) = even' x

{-@ even_double :: x:Nat' -> {even' (double' x)} @-}
even_double Z =     even' (double' Z) 
              ===   even' Z  
              ===   True 
              ***   QED
even_double (S x) =     even' (double' (S x))
                  ===   even' (S (S (double' x)))
                  ==?   even' (double' x)
                  ?     even_double x
                  ===   True
                  ***   QED

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
