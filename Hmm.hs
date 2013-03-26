{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables #-}
module Hmm where

import Coerce
import Data.Rank1Typeable
import Data.Dynamic
import Control.Applicative

replicate' :: G Int -> ANY -> G1 [] ANY
replicate' (GK i) a = GK (replicate i a)

hiddenReplicate :: Dynamic
hiddenReplicate = toDyn replicate'

mReplicate :: Maybe (Int -> a -> [a])
mReplicate = coerceAny <$> (fromDynamic hiddenReplicate :: Maybe (G Int -> ANY -> G1 [] ANY))

main :: IO ()
main = print $ do
         liftA2 (++)
               (show . ($ "Beat It") <$> ($ 1) <$> mReplicate)
               (show . ($ (4 :: Int)) <$> ($ 4) <$> mReplicate)
