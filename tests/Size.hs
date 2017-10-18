{-# LANGUAGE CPP, GeneralizedNewtypeDeriving, FlexibleInstances #-}

-- | Tests for size field invariant in 'HashMap' wrapper introduced in GitHub
-- PR #170.

module Main (main) where

import Data.Hashable (Hashable(hashWithSalt))
#if defined(STRICT)
import qualified Data.HashMap.Strict as HM
#else
import qualified Data.HashMap.Lazy as HM
#endif
import qualified Data.Map as M
#if !MIN_VERSION_base(4,8,0)
import Control.Applicative (pure, (<*>))
import Data.Functor ((<$>))
import Data.Monoid (mempty)
#endif

import Test.QuickCheck (Arbitrary (..), Property, conjoin, frequency, (===))
import Test.Framework (Test, defaultMain, testGroup)
import Test.Framework.Providers.QuickCheck2 (testProperty)

-- Key type that generates more hash collisions.
newtype Key = K { unK :: Int }
            deriving (Arbitrary, Eq, Ord, Read, Show)

instance Hashable Key where
    hashWithSalt salt k = hashWithSalt salt (unK k) `mod` 20

-- Datatype representing the actions that can potentially change a hashmap's
-- size modulo repetition i.e. 'mapMaybe' and 'filter' are essentially
-- equivalent in how they modify a hashmap, so only one ('filter') is tested.
data HashMapAction
    = Insert Key Int
    -- 'InsertWith' should have a 'Int -> Int -> Int' argument, but (+) is used
    -- to simplify because of the 'Show instance'
    | InsertWith Key Int
    | Delete Key
    | Union (HM.HashMap Key Int)
    | Intersection (HM.HashMap Key Int)
    | Difference (HM.HashMap Key Int)
    -- 'Filter' should also have a 'Int -> Bool' argument, but 'even' is
    -- sufficient.
    | Filter
  deriving (Eq, Show)

instance Arbitrary (HM.HashMap Key Int) where
    arbitrary = HM.fromList <$> arbitrary

-- Here, higher weights are used for operations that increase the size of the
-- hashmap so that its size is more likely to grow instead of nearing and
-- staying 0, creating more interesting sequences of actions to be tested.
instance Arbitrary HashMapAction where
    arbitrary = frequency
        [ (2, Insert <$> arbitrary <*> arbitrary)
        , (2, InsertWith <$> arbitrary <*> arbitrary)
        , (1, Delete <$> arbitrary)
        , (2, Union <$> arbitrary)
        , (1, Intersection <$> arbitrary)
        , (1, Difference <$> arbitrary)
        , (1, pure Filter)
        ]

-- Simple way of representing a hashmap and its size without having to
-- use 'size', which is the function to be tested. As such, its use is
-- avoided and the 'Int' field of the tuple is used instead.
type HashMapSt = (Int, HM.HashMap Key Int)

-- | Applies a 'HashMapAction' to 'HashMapSt', updating the hashmap's
-- size after the operation.
applyActionToState :: HashMapSt -> HashMapAction -> HashMapSt
applyActionToState p@(sz, hm) (Insert k v)
    | HM.member k hm = p
    | otherwise      = (sz + 1, HM.insert k v hm)
applyActionToState p@(sz, hm) (InsertWith k v)
    | HM.member k hm = p
    | otherwise      = (sz + 1, HM.insertWith (+) k v hm)
applyActionToState p@(sz, hm) (Delete k)
    | HM.member k hm = (sz - 1, HM.delete k hm)
    | otherwise      = p
applyActionToState (sz, hm) (Union hm') =
    let sz'          = length $ HM.toList hm'
        lenIntersect = length [ k | k <- HM.keys hm, HM.member k hm' ]
        newLen       = sz + sz' - lenIntersect
    in (newLen, HM.union hm hm')
applyActionToState (_, hm) (Intersection hm') =
    let lenIntersect = length [ k | k <- HM.keys hm, HM.member k hm' ]
    in (lenIntersect, HM.intersection hm hm')
applyActionToState (_, hm) (Difference hm')=
    let lenDiff = length [ k | k <- HM.keys hm, not $ HM.member k hm' ]
    in (lenDiff, HM.difference hm hm')
applyActionToState (_, hm) Filter =
    let lenFilter = length [ (k, v) | (k, v) <- HM.toList hm, even v ]
    in (lenFilter, HM.filter even hm)

-- | Property to check that after each operation that may change a hashmap's
-- size, the 'Int' field in the 'HashMap' wrapper always correctly represents
-- the hashmap's size.
sizeInvariantProperty :: [HashMapAction] -> Property
sizeInvariantProperty actionList =
    conjoin .
    map (\(sz, hm) -> sz === HM.size hm) .
    scanl applyActionToState (0, mempty) $ actionList

-- | Property to check that the hashmap built by 'fromList' applied to a list
-- without repeating keys will have the right size i.e. equal to the list's
-- length.
fromListProperty :: M.Map Key Int -> Bool
fromListProperty m =
    let sz   = M.size m
        list = M.toList m
        hm   = HM.fromList list
    in sz == HM.size hm

-- | Property to check that the hashmap built by 'fromListWith' applied to a
--list without repeating keys will have the right size i.e. equal to the list's
-- length.
fromListWithProperty :: M.Map Key Int -> Bool
fromListWithProperty m =
    let sz   = M.size m
        list = M.toList m
        hm   = HM.fromListWith (+) list
    in sz == HM.size hm

------------------------------------------------------------------------
-- * Test list

tests :: [Test]
tests = [
          testGroup "size invariant checks"
          [ testProperty "size" sizeInvariantProperty
          , testProperty "fromList" fromListProperty
          , testProperty "fromListWith" fromListWithProperty
          ]
        ]

------------------------------------------------------------------------
-- * Test harness

main :: IO ()
main = defaultMain tests
