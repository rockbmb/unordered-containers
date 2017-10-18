{-# LANGUAGE CPP, DeriveGeneric, GADTs, PackageImports, RecordWildCards #-}

module Main where

import Control.DeepSeq
import Control.DeepSeq.Generics (genericRnf)
import Criterion.Main (bench, bgroup, defaultMain, env, nf, whnf)
import Data.Bits ((.&.))
import Data.Hashable (Hashable)
import qualified Data.ByteString as BS
import qualified "hashmap" Data.HashMap as IHM
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import qualified Data.IntMap as IM
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Vector as V
import Data.List (foldl')
import Data.Maybe (fromMaybe)
import GHC.Generics (Generic)
import Prelude hiding (lookup)

import qualified Util.ByteString as UBS
import qualified Util.Int as UI
import qualified Util.String as US

#if !MIN_VERSION_bytestring(0,10,0)
instance NFData BS.ByteString
#endif

data B where
    B :: NFData a => a -> B

instance NFData B where
    rnf (B b) = rnf b

-- TODO: This a stopgap measure to keep the benchmark work with
-- Criterion 1.0.
data Env = Env {
    n :: !Int,

    csz :: !Int, -- container size

    elems   :: ![(String, Int)],
    keys    :: ![String],
    elemsBS :: ![(BS.ByteString, Int)],
    keysBS  :: ![BS.ByteString],
    elemsI  :: ![(Int, Int)],
    keysI   :: ![Int],
    elemsI2 :: ![(Int, Int)],  -- for union

    keys'    :: ![String],
    keysBS'  :: ![BS.ByteString],
    keysI'   :: ![Int],

    listOfHMs :: ![HM.HashMap Int Int],
    vecOfHMs  :: !(V.Vector (HM.HashMap Int Int)),
    hsetOfHMs :: !(HS.HashSet (HM.HashMap Int Int)),
    setOfHMs  :: !(S.Set (HM.HashMap Int Int)),

    keysDup    :: ![String],
    keysDupBS  :: ![BS.ByteString],
    keysDupI   :: ![Int],
    elemsDup   :: ![(String, Int)],
    elemsDupBS :: ![(BS.ByteString, Int)],
    elemsDupI  :: ![(Int, Int)],

    hm    :: !(HM.HashMap String Int),
    hmbs  :: !(HM.HashMap BS.ByteString Int),
    hmi   :: !(HM.HashMap Int Int),
    hmi2  :: !(HM.HashMap Int Int),
    m     :: !(M.Map String Int),
    mbs   :: !(M.Map BS.ByteString Int),
    im    :: !(IM.IntMap Int),
    ihm   :: !(IHM.Map String Int),
    ihmbs :: !(IHM.Map BS.ByteString Int)
    } deriving Generic

instance NFData Env where rnf = genericRnf

setupEnv :: IO Env
setupEnv = do
    let n = 2^(12 :: Int)

        -- When building a container of hashmaps, 'cn' will be the size of each.
        cn = n `div` 16
        -- 'csz' is the size of the container of hashmaps.
        csz = 2^(7 :: Int)

        values = [1..csz*cn]

        chop _ [] = []
        chop k l =
            let (taken, left) = splitAt k l
            in taken : chop k left

        vals = chop cn values

        elems   = zip keys [1..n]
        keys    = US.rnd 8 n
        elemsBS = zip keysBS [1..n]
        keysBS  = UBS.rnd 8 n
        elemsI  = zip keysI [1..n]
        keysI   = UI.rnd (n+n) n
        elemsI2 = zip [n `div` 2..n + (n `div` 2)] [1..n]  -- for union

        keys'    = US.rnd' 8 n
        keysBS'  = UBS.rnd' 8 n
        keysI'   = UI.rnd' (n+n) n

        listOfHMs = zipWith (\x y -> HM.fromList (zip x y)) (repeat keysI) vals
        vecOfHMs  = V.fromList listOfHMs
        hsetOfHMs = HS.fromList listOfHMs
        setOfHMs  = S.fromList listOfHMs

        keysDup    = US.rnd 2 n
        keysDupBS  = UBS.rnd 2 n
        keysDupI   = UI.rnd (n`div`4) n
        elemsDup   = zip keysDup [1..n]
        elemsDupBS = zip keysDupBS [1..n]
        elemsDupI  = zip keysDupI [1..n]

        hm   = HM.fromList elems
        hmbs = HM.fromList elemsBS
        hmi  = HM.fromList elemsI
        hmi2 = HM.fromList elemsI2
        m    = M.fromList elems
        mbs  = M.fromList elemsBS
        im   = IM.fromList elemsI
        ihm  = IHM.fromList elems
        ihmbs = IHM.fromList elemsBS
    return Env{..}

main :: IO ()
main = do
    defaultMain
        [
          env setupEnv $ \ ~(Env{..}) ->
          -- * Comparison to other data structures
          -- ** Map
          bgroup "Map"
          [ bgroup "lookup"
            [ bench "String" $ whnf (lookupM keys) m
            , bench "ByteString" $ whnf (lookupM keysBS) mbs
            ]
          , bgroup "lookup-miss"
            [ bench "String" $ whnf (lookupM keys') m
            , bench "ByteString" $ whnf (lookupM keysBS') mbs
            ]
          , bgroup "insert"
            [ bench "String" $ whnf (insertM elems) M.empty
            , bench "ByteStringString" $ whnf (insertM elemsBS) M.empty
            ]
          , bgroup "insert-dup"
            [ bench "String" $ whnf (insertM elems) m
            , bench "ByteStringString" $ whnf (insertM elemsBS) mbs
            ]
          , bgroup "delete"
            [ bench "String" $ whnf (deleteM keys) m
            , bench "ByteString" $ whnf (deleteM keysBS) mbs
            ]
          , bgroup "delete-miss"
            [ bench "String" $ whnf (deleteM keys') m
            , bench "ByteString" $ whnf (deleteM keysBS') mbs
            ]
          , bgroup "size"
            [ bench "String" $ whnf M.size m
            , bench "ByteString" $ whnf M.size mbs
            ]
          , bgroup "fromList"
            [ bench "String" $ whnf M.fromList elems
            , bench "ByteString" $ whnf M.fromList elemsBS
            ]
          ]

          -- ** Map from the hashmap package
        , env setupEnv $ \ ~(Env{..}) ->
          bgroup "hashmap/Map"
          [ bgroup "lookup"
            [ bench "String" $ whnf (lookupIHM keys) ihm
            , bench "ByteString" $ whnf (lookupIHM keysBS) ihmbs
            ]
          , bgroup "lookup-miss"
            [ bench "String" $ whnf (lookupIHM keys') ihm
            , bench "ByteString" $ whnf (lookupIHM keysBS') ihmbs
            ]
          , bgroup "insert"
            [ bench "String" $ whnf (insertIHM elems) IHM.empty
            , bench "ByteStringString" $ whnf (insertIHM elemsBS) IHM.empty
            ]
          , bgroup "insert-dup"
            [ bench "String" $ whnf (insertIHM elems) ihm
            , bench "ByteStringString" $ whnf (insertIHM elemsBS) ihmbs
            ]
          , bgroup "delete"
            [ bench "String" $ whnf (deleteIHM keys) ihm
            , bench "ByteString" $ whnf (deleteIHM keysBS) ihmbs
            ]
          , bgroup "delete-miss"
            [ bench "String" $ whnf (deleteIHM keys') ihm
            , bench "ByteString" $ whnf (deleteIHM keysBS') ihmbs
            ]
          , bgroup "size"
            [ bench "String" $ whnf IHM.size ihm
            , bench "ByteString" $ whnf IHM.size ihmbs
            ]
          , bgroup "fromList"
            [ bench "String" $ whnf IHM.fromList elems
            , bench "ByteString" $ whnf IHM.fromList elemsBS
            ]
          ]

          -- ** IntMap
        , env setupEnv $ \ ~(Env{..}) ->
          bgroup "IntMap"
          [ bench "lookup" $ whnf (lookupIM keysI) im
          , bench "lookup-miss" $ whnf (lookupIM keysI') im
          , bench "insert" $ whnf (insertIM elemsI) IM.empty
          , bench "insert-dup" $ whnf (insertIM elemsI) im
          , bench "delete" $ whnf (deleteIM keysI) im
          , bench "delete-miss" $ whnf (deleteIM keysI') im
          , bench "size" $ whnf IM.size im
          , bench "fromList" $ whnf IM.fromList elemsI
          ]

        , env setupEnv $ \ ~(Env{..}) ->
          bgroup "HashMap"
          [ -- * Basic interface
            bgroup "lookup"
            [ bench "String" $ whnf (lookup keys) hm
            , bench "ByteString" $ whnf (lookup keysBS) hmbs
            , bench "Int" $ whnf (lookup keysI) hmi
            ]
          , bgroup "lookup-miss"
            [ bench "String" $ whnf (lookup keys') hm
            , bench "ByteString" $ whnf (lookup keysBS') hmbs
            , bench "Int" $ whnf (lookup keysI') hmi
            ]
          , bgroup "insert"
            [ bench "String" $ whnf (insert elems) HM.empty
            , bench "ByteString" $ whnf (insert elemsBS) HM.empty
            , bench "Int" $ whnf (insert elemsI) HM.empty
            ]
          , bgroup "insert-dup"
            [ bench "String" $ whnf (insert elems) hm
            , bench "ByteString" $ whnf (insert elemsBS) hmbs
            , bench "Int" $ whnf (insert elemsI) hmi
            ]
          , bgroup "delete"
            [ bench "String" $ whnf (delete keys) hm
            , bench "ByteString" $ whnf (delete keysBS) hmbs
            , bench "Int" $ whnf (delete keysI) hmi
            ]
          , bgroup "delete-miss"
            [ bench "String" $ whnf (delete keys') hm
            , bench "ByteString" $ whnf (delete keysBS') hmbs
            , bench "Int" $ whnf (delete keysI') hmi
            ]

          , bgroup "containerized"
            [ bgroup "lookup"
              [ bench "List" $ nf (lookupC keysI) listOfHMs
              , bench "Vector" $ nf (lookupC keysI) vecOfHMs
              , bench "HashSet" $ nf (lookupHS keysI) hsetOfHMs
              , bench "Set" $ nf (lookupS keysI) setOfHMs
              ]
            , bgroup "insert"
              [ bench "List" $ nf (insertC elemsI) listOfHMs
              , bench "Vector" $ nf (insertC elemsI) vecOfHMs
              , bench "HashSet" $ nf (insertHS elemsI) hsetOfHMs
              , bench "Set" $ nf (insertS elemsI) setOfHMs
              ]
            , bgroup "delete"
              [ bench "List" $ nf (deleteC keysI) listOfHMs
              , bench "Vector" $ nf (deleteC keysI) vecOfHMs
              , bench "HashSet" $ nf (deleteHS keysI) hsetOfHMs
              , bench "Set" $ nf (deleteS keysI) setOfHMs
              ]
            , bgroup "union"
              [ bench "List" $ whnf unionC listOfHMs
              , bench "Vector" $ whnf unionC vecOfHMs
              , bench "HashSet" $ whnf unionC hsetOfHMs
              , bench "Set" $ whnf unionC setOfHMs
              ]
            , bgroup "map"
              [ bench "List" $ nf (mapC (\ v -> v + 1)) listOfHMs
              , bench "Vector" $ nf (mapC (\ v -> v + 1)) vecOfHMs
              , bench "HashSet" $ nf (mapHS (\ v -> v + 1)) hsetOfHMs
              , bench "Set" $ nf (mapS (\ v -> v + 1)) setOfHMs
              ]
            , bgroup "intersection"
              [ bench "List" $ whnf intersectionC listOfHMs
              , bench "Vector" $ whnf intersectionC vecOfHMs
              , bench "HashSet" $ whnf intersectionC hsetOfHMs
              , bench "Set" $ whnf intersectionC setOfHMs
              ]
            , bgroup "size"
              [ bench "List" $ nf sizeC listOfHMs
              , bench "Vector" $ nf sizeC vecOfHMs
              , bench "HashSet" $ nf sizeHS hsetOfHMs
              , bench "Set" $ nf sizeS setOfHMs
              ]
            ]

            -- Combine
          , bench "union" $ whnf (HM.union hmi) hmi2

            -- Transformations
          , bench "map" $ whnf (HM.map (\ v -> v + 1)) hmi

            -- * Difference and intersection
          , bench "difference" $ whnf (HM.difference hmi) hmi2
          , bench "intersection" $ whnf (HM.intersection hmi) hmi2

            -- Folds
          , bench "foldl'" $ whnf (HM.foldl' (+) 0) hmi
          , bench "foldr" $ nf (HM.foldr (:) []) hmi

            -- Filter
          , bench "filter" $ whnf (HM.filter (\ v -> v .&. 1 == 0)) hmi
          , bench "filterWithKey" $ whnf (HM.filterWithKey (\ k _ -> k .&. 1 == 0)) hmi

            -- Size
          , bgroup "size"
            [ bench "String" $ whnf HM.size hm
            , bench "ByteString" $ whnf HM.size hmbs
            , bench "Int" $ whnf HM.size hmi
            ]

            -- fromList
          , bgroup "fromList"
            [ bgroup "long"
              [ bench "String" $ whnf HM.fromList elems
              , bench "ByteString" $ whnf HM.fromList elemsBS
              , bench "Int" $ whnf HM.fromList elemsI
              ]
            , bgroup "short"
              [ bench "String" $ whnf HM.fromList elemsDup
              , bench "ByteString" $ whnf HM.fromList elemsDupBS
              , bench "Int" $ whnf HM.fromList elemsDupI
              ]
            ]
            -- fromListWith
          , bgroup "fromListWith"
            [ bgroup "long"
              [ bench "String" $ whnf (HM.fromListWith (+)) elems
              , bench "ByteString" $ whnf (HM.fromListWith (+)) elemsBS
              , bench "Int" $ whnf (HM.fromListWith (+)) elemsI
              ]
            , bgroup "short"
              [ bench "String" $ whnf (HM.fromListWith (+)) elemsDup
              , bench "ByteString" $ whnf (HM.fromListWith (+)) elemsDupBS
              , bench "Int" $ whnf (HM.fromListWith (+)) elemsDupI
              ]
            ]
          ]
        ]

------------------------------------------------------------------------
-- * HashMap

lookup :: (Eq k, Hashable k) => [k] -> HM.HashMap k Int -> Int
lookup xs m = foldl' (\z k -> fromMaybe z (HM.lookup k m)) 0 xs
{-# SPECIALIZE lookup :: [Int] -> HM.HashMap Int Int -> Int #-}
{-# SPECIALIZE lookup :: [String] -> HM.HashMap String Int -> Int #-}
{-# SPECIALIZE lookup :: [BS.ByteString] -> HM.HashMap BS.ByteString Int
                      -> Int #-}

lookupC :: (Eq k, Hashable k, Traversable f) => [k] -> f (HM.HashMap k Int) -> f Int
lookupC = fmap . lookup
{-# SPECIALIZE lookupC :: [Int] -> [HM.HashMap Int Int] -> [Int] #-}
{-# SPECIALIZE lookupC :: [Int] -> V.Vector (HM.HashMap Int Int)
                       -> V.Vector Int #-}

lookupHS :: [Int] -> HS.HashSet (HM.HashMap Int Int) -> HS.HashSet Int
lookupHS = HS.map . lookup

lookupS :: [Int] -> S.Set (HM.HashMap Int Int) -> S.Set Int
lookupS = S.map . lookup

insert :: (Eq k, Hashable k) => [(k, Int)] -> HM.HashMap k Int
       -> HM.HashMap k Int
insert xs m0 = foldl' (\m (k, v) -> HM.insert k v m) m0 xs
{-# SPECIALIZE insert :: [(Int, Int)] -> HM.HashMap Int Int
                      -> HM.HashMap Int Int #-}
{-# SPECIALIZE insert :: [(String, Int)] -> HM.HashMap String Int
                      -> HM.HashMap String Int #-}
{-# SPECIALIZE insert :: [(BS.ByteString, Int)] -> HM.HashMap BS.ByteString Int
                      -> HM.HashMap BS.ByteString Int #-}

insertC :: (Eq k, Hashable k, Traversable f) => [(k, Int)] -> f (HM.HashMap k Int)
        -> f (HM.HashMap k Int)
insertC l = fmap (insert l)
{-# SPECIALIZE insertC :: [(Int, Int)] -> [HM.HashMap Int Int]
                       -> [HM.HashMap Int Int] #-}
{-# SPECIALIZE insertC :: [(Int, Int)] -> V.Vector (HM.HashMap Int Int)
                       -> V.Vector (HM.HashMap Int Int) #-}

insertHS :: [(Int, Int)] -> HS.HashSet (HM.HashMap Int Int)
         -> HS.HashSet (HM.HashMap Int Int)
insertHS l = HS.map (insert l)

insertS :: [(Int, Int)] -> S.Set (HM.HashMap Int Int) -> S.Set (HM.HashMap Int Int)
insertS l = S.map (insert l)

delete :: (Eq k, Hashable k) => [k] -> HM.HashMap k Int -> HM.HashMap k Int
delete xs m0 = foldl' (\m k -> HM.delete k m) m0 xs
{-# SPECIALIZE delete :: [Int] -> HM.HashMap Int Int -> HM.HashMap Int Int #-}
{-# SPECIALIZE delete :: [String] -> HM.HashMap String Int
                      -> HM.HashMap String Int #-}
{-# SPECIALIZE delete :: [BS.ByteString] -> HM.HashMap BS.ByteString Int
                      -> HM.HashMap BS.ByteString Int #-}

deleteC :: (Eq k, Hashable k, Functor f) => [k] -> f (HM.HashMap k Int)
        -> f (HM.HashMap k Int)
deleteC = fmap . delete
{-# SPECIALIZE deleteC :: [Int] -> [HM.HashMap Int Int]
                       -> [HM.HashMap Int Int] #-}
{-# SPECIALIZE deleteC :: [Int] -> V.Vector (HM.HashMap Int Int)
                       -> V.Vector (HM.HashMap Int Int) #-}

deleteHS :: [Int] -> HS.HashSet (HM.HashMap Int Int)
         -> HS.HashSet (HM.HashMap Int Int)
deleteHS = HS.map . delete

deleteS :: [Int] -> S.Set (HM.HashMap Int Int) -> S.Set (HM.HashMap Int Int)
deleteS = S.map . delete

unionC :: (Eq k, Hashable k, Foldable f) => f (HM.HashMap k Int)
       -> HM.HashMap k Int
unionC = foldl' HM.union mempty
{-# SPECIALIZE unionC :: [HM.HashMap Int Int] -> HM.HashMap Int Int #-}
{-# SPECIALIZE unionC :: V.Vector (HM.HashMap Int Int) -> HM.HashMap Int Int #-}
{-# SPECIALIZE unionC :: HS.HashSet (HM.HashMap Int Int) -> HM.HashMap Int Int #-}
{-# SPECIALIZE unionC :: S.Set (HM.HashMap Int Int) -> HM.HashMap Int Int #-}

mapC :: (Eq k, Hashable k, Functor f) => (Int -> Int) -> f (HM.HashMap k Int)
       -> f (HM.HashMap k Int)
mapC f = fmap (HM.map f)
{-# SPECIALIZE mapC :: (Int -> Int) -> [HM.HashMap Int Int]
                    -> [HM.HashMap Int Int] #-}
{-# SPECIALIZE mapC :: (Int -> Int) -> V.Vector (HM.HashMap Int Int)
                    -> V.Vector (HM.HashMap Int Int) #-}

mapHS :: (Int -> Int) -> HS.HashSet (HM.HashMap Int Int)
      -> HS.HashSet (HM.HashMap Int Int)
mapHS f = HS.map (HM.map f)

mapS :: (Int -> Int) -> S.Set (HM.HashMap Int Int) -> S.Set (HM.HashMap Int Int)
mapS f = S.map (HM.map f)

intersectionC :: (Eq k, Hashable k, Foldable f) => f (HM.HashMap k Int)
            -> HM.HashMap k Int
intersectionC = foldl' HM.intersection mempty
{-# SPECIALIZE intersectionC :: [HM.HashMap Int Int]
                             -> HM.HashMap Int Int #-}
{-# SPECIALIZE intersectionC :: V.Vector (HM.HashMap Int Int)
                             -> HM.HashMap Int Int #-}
{-# SPECIALIZE intersectionC :: HS.HashSet (HM.HashMap Int Int)
                             -> HM.HashMap Int Int #-}
{-# SPECIALIZE intersectionC :: S.Set (HM.HashMap Int Int)
                             -> HM.HashMap Int Int #-}

sizeC :: (Eq k, Hashable k, Functor f) => f (HM.HashMap k Int) -> f Int
sizeC = fmap HM.size
{-# SPECIALIZE sizeC :: [HM.HashMap Int Int] -> [Int] #-}
{-# SPECIALIZE sizeC :: V.Vector (HM.HashMap Int Int) -> V.Vector Int #-}

sizeHS :: HS.HashSet (HM.HashMap Int Int) -> HS.HashSet Int
sizeHS = HS.map HM.size

sizeS :: S.Set (HM.HashMap Int Int) -> S.Set Int
sizeS = S.map HM.size
------------------------------------------------------------------------
-- * Map

lookupM :: Ord k => [k] -> M.Map k Int -> Int
lookupM xs m = foldl' (\z k -> fromMaybe z (M.lookup k m)) 0 xs
{-# SPECIALIZE lookupM :: [String] -> M.Map String Int -> Int #-}
{-# SPECIALIZE lookupM :: [BS.ByteString] -> M.Map BS.ByteString Int -> Int #-}

insertM :: Ord k => [(k, Int)] -> M.Map k Int -> M.Map k Int
insertM xs m0 = foldl' (\m (k, v) -> M.insert k v m) m0 xs
{-# SPECIALIZE insertM :: [(String, Int)] -> M.Map String Int
                       -> M.Map String Int #-}
{-# SPECIALIZE insertM :: [(BS.ByteString, Int)] -> M.Map BS.ByteString Int
                       -> M.Map BS.ByteString Int #-}

deleteM :: Ord k => [k] -> M.Map k Int -> M.Map k Int
deleteM xs m0 = foldl' (\m k -> M.delete k m) m0 xs
{-# SPECIALIZE deleteM :: [String] -> M.Map String Int -> M.Map String Int #-}
{-# SPECIALIZE deleteM :: [BS.ByteString] -> M.Map BS.ByteString Int
                       -> M.Map BS.ByteString Int #-}

------------------------------------------------------------------------
-- * Map from the hashmap package

lookupIHM :: (Eq k, Hashable k, Ord k) => [k] -> IHM.Map k Int -> Int
lookupIHM xs m = foldl' (\z k -> fromMaybe z (IHM.lookup k m)) 0 xs
{-# SPECIALIZE lookupIHM :: [String] -> IHM.Map String Int -> Int #-}
{-# SPECIALIZE lookupIHM :: [BS.ByteString] -> IHM.Map BS.ByteString Int
                         -> Int #-}

insertIHM :: (Eq k, Hashable k, Ord k) => [(k, Int)] -> IHM.Map k Int
          -> IHM.Map k Int
insertIHM xs m0 = foldl' (\m (k, v) -> IHM.insert k v m) m0 xs
{-# SPECIALIZE insertIHM :: [(String, Int)] -> IHM.Map String Int
                         -> IHM.Map String Int #-}
{-# SPECIALIZE insertIHM :: [(BS.ByteString, Int)] -> IHM.Map BS.ByteString Int
                         -> IHM.Map BS.ByteString Int #-}

deleteIHM :: (Eq k, Hashable k, Ord k) => [k] -> IHM.Map k Int -> IHM.Map k Int
deleteIHM xs m0 = foldl' (\m k -> IHM.delete k m) m0 xs
{-# SPECIALIZE deleteIHM :: [String] -> IHM.Map String Int
                         -> IHM.Map String Int #-}
{-# SPECIALIZE deleteIHM :: [BS.ByteString] -> IHM.Map BS.ByteString Int
                         -> IHM.Map BS.ByteString Int #-}

------------------------------------------------------------------------
-- * IntMap

lookupIM :: [Int] -> IM.IntMap Int -> Int
lookupIM xs m = foldl' (\z k -> fromMaybe z (IM.lookup k m)) 0 xs

insertIM :: [(Int, Int)] -> IM.IntMap Int -> IM.IntMap Int
insertIM xs m0 = foldl' (\m (k, v) -> IM.insert k v m) m0 xs

deleteIM :: [Int] -> IM.IntMap Int -> IM.IntMap Int
deleteIM xs m0 = foldl' (\m k -> IM.delete k m) m0 xs
