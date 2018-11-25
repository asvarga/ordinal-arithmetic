
{-@ LIQUID "--reflection" @-}
import Language.Haskell.Liquid.ProofCombinators

{-@ type LT10 = {v:Nat | lt10 v} @-}

{-@ inline lt10 @-}
{-@ lt10 :: Nat -> Bool @-}
lt10 :: Int -> Bool
lt10 x = x < 10

{-@ id' :: LT10 -> LT10 @-}
id' :: Int -> Int
id' x = x

-- {-@ lt10_5 :: _ -> { lt10 5 } @-}
-- lt10_5 _ = lt10 5 *** QED


main = do 
	print $ id' 5
	-- print $ id' 15