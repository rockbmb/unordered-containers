{-# LANGUAGE BangPatterns, CPP, PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Trustworthy #-}

------------------------------------------------------------------------
-- |
-- Module      :  Data.HashMap.Strict
-- Copyright   :  2010-2012 Johan Tibell
-- License     :  BSD-style
-- Maintainer  :  johan.tibell@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- A map from /hashable/ keys to values.  A map cannot contain
-- duplicate keys; each key can map to at most one value.  A 'HashMap'
-- makes no guarantees as to the order of its elements.
--
-- The implementation is based on /hash array mapped tries/.  A
-- 'HashMap' is often faster than other tree-based set types,
-- especially when key comparison is expensive, as in the case of
-- strings.
--
-- Many operations have a average-case complexity of /O(log n)/.  The
-- implementation uses a large base (i.e. 16) so in practice these
-- operations are constant time.
module Data.HashMap.Strict
    (
      -- * Strictness properties
      -- $strictness

      HashMap

      -- * Construction
    , empty
    , singleton

      -- * Basic interface
    , HM.null
    , size
    , HM.member
    , HM.lookup
    , lookupDefault
    , (!)
    , insert
    , insertWith
    , delete
    , adjust
    , update
    , alter

      -- * Combine
      -- ** Union
    , union
    , unionWith
    , unionWithKey
    , unions

      -- * Transformations
    , map
    , mapWithKey
    , traverseWithKey

      -- * Difference and intersection
    , difference
    , differenceWith
    , intersection
    , intersectionWith
    , intersectionWithKey

      -- * Folds
    , foldl'
    , foldlWithKey'
    , HM.foldr
    , foldrWithKey

      -- * Filter
    , HM.filter
    , filterWithKey
    , mapMaybe
    , mapMaybeWithKey

      -- * Conversions
    , keys
    , elems

      -- ** Lists
    , toList
    , fromList
    , fromListWith
    ) where

import Data.Bits ((.&.), (.|.))
import qualified Data.List as L
import Data.Hashable (Hashable)
import Prelude hiding (map)

import qualified Data.HashMap.Array as A
import qualified Data.HashMap.Base as HM
import Data.HashMap.Base hiding (
    alter, adjust, fromList, fromListWith, insert, insertWith, differenceWith,
    intersectionWith, intersectionWithKey, map, mapWithKey, mapMaybe,
    mapMaybeWithKey, singleton, update, unionWith, unionWithKey)
import Data.HashMap.Unsafe (runST)

-- $strictness
--
-- This module satisfies the following strictness properties:
--
-- 1. Key arguments are evaluated to WHNF;
--
-- 2. Keys and values are evaluated to WHNF before they are stored in
--    the map.

------------------------------------------------------------------------
-- * Construction

-- | /O(1)/ Construct a map with a single element.
singleton :: (Hashable k) => k -> v -> HashMap k v
singleton k !v = HM.singleton k v

------------------------------------------------------------------------
-- * Basic interface

-- | /O(log n)/ Associate the specified value with the specified
-- key in this map.  If this map previously contained a mapping for
-- the key, the old value is replaced.
insert :: (Eq k, Hashable k) => k -> v -> HashMap k v -> HashMap k v
insert k !v = HM.insert k v
{-# INLINABLE insert #-}

-- | /O(log n)/ Associate the value with the key in this map.  If
-- this map previously contained a mapping for the key, the old value
-- is replaced by the result of applying the given function to the new
-- and old value.  Example:
--
-- > insertWith f k v map
-- >   where f new old = new + old
insertWith :: (Eq k, Hashable k) => (v -> v -> v) -> k -> v -> HashMap k v
            -> HashMap k v
insertWith f k0 v0 (HashMap sz m0) =
    let A.Sized diff m0' = insertWithInternal f k0 v0 m0
    in HashMap (diff + sz) m0'
{-# INLINABLE insertWith #-}

-- | /O(log n)/ Associate the value with the key in this map.  If
-- this map previously contained a mapping for the key, the old value
-- is replaced by the result of applying the given function to the new
-- and old value.
-- Returns a tuple where the first component is the
-- difference in size between the old and new hashmaps, and the second
-- is the new hashmap.
-- Example:
-- > insertWith f k v map
-- >   where f new old = new + old
insertWithInternal :: (Eq k, Hashable k) => (v -> v -> v) -> k -> v -> Tree k v
           -> A.Sized (Tree k v)
insertWithInternal f k0 v0 m0 = go h0 k0 v0 0 m0
  where
    h0 = hash k0
    go !h !k x !_ Empty = A.Sized 1 (leaf h k x)
    go h k x s (Leaf hy l@(L ky y))
        | hy == h = if ky == k
                    then A.Sized 0 (leaf h k (f x y))
                    else A.Sized 1 (x `seq` (collision h l (L k x)))
        | otherwise = A.Sized 1 (x `seq` runST (two s h k x hy ky y))
    go h k x s (BitmapIndexed b ary)
        | b .&. m == 0 =
            let ary' = A.insert ary i $! leaf h k x
            in A.Sized 1 (bitmapIndexedOrFull (b .|. m) ary')
        | otherwise =
            let st           = A.index ary i
                A.Sized sz st' = go h k x (s+bitsPerSubkey) st
                ary'         = A.update ary i $! st'
            in A.Sized sz (BitmapIndexed b ary')
      where m = mask h s
            i = sparseIndex b m
    go h k x s (Full ary) =
        let st           = A.index ary i
            A.Sized sz st' = go h k x (s+bitsPerSubkey) st
            ary'         = update16 ary i $! st'
        in A.Sized sz (Full ary')
      where i = index h s
    go h k x s t@(Collision hy v)
        | h == hy   =
            let !start = A.length v
                !newV  = updateOrSnocWith f k x v
                !end   = A.length newV
            in A.Sized (end - start) (Collision h newV)
        | otherwise = go h k x s $ BitmapIndexed (mask hy s) (A.singleton t)
{-# INLINABLE insertWithInternal #-}

-- | In-place update version of insertWith
unsafeInsertWith :: forall k v . (Eq k, Hashable k)
                 => (v -> v -> v) -> k -> v -> HashMap k v
                 -> HashMap k v
unsafeInsertWith f k0 v0 (HashMap sz m0) =
    let A.Sized diff m0' = unsafeInsertWithInternal f k0 v0 m0
    in HashMap (diff + sz) m0'
{-# INLINABLE unsafeInsertWith #-}

-- | In-place update version of insertWith
unsafeInsertWithInternal
    :: (Eq k, Hashable k)
    => (v -> v -> v)
    -> k
    -> v
    -> Tree k v
    -> A.Sized (Tree k v)
unsafeInsertWithInternal f k0 v0 m0 = runST (go h0 k0 v0 0 m0)
  where
    h0 = hash k0
    go !h !k x !_ Empty = return . A.Sized 1 $! leaf h k x
    go h k x s (Leaf hy l@(L ky y))
        | hy == h = if ky == k
                    then return . A.Sized 0 $! leaf h k (f x y)
                    else do
                        let l' = x `seq` (L k x)
                        return . A.Sized 1 $! collision h l l'
        | otherwise = do
              twoHM <- x `seq` two s h k x hy ky y
              return . A.Sized 1 $! twoHM
    go h k x s t@(BitmapIndexed b ary)
        | b .&. m == 0 = do
            ary' <- A.insertM ary i $! leaf h k x
            return . A.Sized 1 $! bitmapIndexedOrFull (b .|. m) ary'
        | otherwise = do
            st <- A.indexM ary i
            A.Sized sz st' <- go h k x (s+bitsPerSubkey) st
            A.unsafeUpdateM ary i $! st'
            return . A.Sized sz $! t
      where m = mask h s
            i = sparseIndex b m
    go h k x s t@(Full ary) = do
        st <- A.indexM ary i
        A.Sized sz st' <- go h k x (s+bitsPerSubkey) st
        A.unsafeUpdateM ary i $! st'
        return . A.Sized sz $! t
      where i = index h s
    go h k x s t@(Collision hy v)
        | h == hy   =
            let !start = A.length v
                !newV = updateOrSnocWith f k x v
                !end = A.length newV
            in return . A.Sized (end - start) $! Collision h newV
        | otherwise = go h k x s $ BitmapIndexed (mask hy s) (A.singleton t)
{-# INLINABLE unsafeInsertWithInternal #-}

-- | /O(log n)/ Adjust the value tied to a given key in this map only
-- if it is present. Otherwise, leave the map alone.
adjust :: (Eq k, Hashable k) => (v -> v) -> k -> HashMap k v -> HashMap k v
adjust f k0 (HashMap sz m0) = HashMap sz (go h0 k0 0 m0)
  where
    h0 = hash k0
    go !_ !_ !_ Empty = Empty
    go h k _ t@(Leaf hy (L ky y))
        | hy == h && ky == k = leaf h k (f y)
        | otherwise          = t
    go h k s t@(BitmapIndexed b ary)
        | b .&. m == 0 = t
        | otherwise = let st   = A.index ary i
                          st'  = go h k (s+bitsPerSubkey) st
                          ary' = A.update ary i $! st'
                      in BitmapIndexed b ary'
      where m = mask h s
            i = sparseIndex b m
    go h k s (Full ary) =
        let i    = index h s
            st   = A.index ary i
            st'  = go h k (s+bitsPerSubkey) st
            ary' = update16 ary i $! st'
        in Full ary'
    go h k _ t@(Collision hy v)
        | h == hy   = Collision h (updateWith f k v)
        | otherwise = t
{-# INLINABLE adjust #-}

-- | /O(log n)/  The expression (@'update' f k map@) updates the value @x@ at @k@,
-- (if it is in the map). If (f k x) is @'Nothing', the element is deleted.
-- If it is (@'Just' y), the key k is bound to the new value y.
update :: (Eq k, Hashable k) => (a -> Maybe a) -> k -> HashMap k a -> HashMap k a
update f = alter (>>= f)
{-# INLINABLE update #-}

-- | /O(log n)/  The expression (@'alter' f k map@) alters the value @x@ at @k@, or
-- absence thereof. @alter@ can be used to insert, delete, or update a value in a
-- map. In short : @'lookup' k ('alter' f k m) = f ('lookup' k m)@.
alter
    :: (Eq k, Hashable k)
    => (Maybe v -> Maybe v)
    -> k
    -> HashMap k v
    -> HashMap k v
alter f k m =
  case f (HM.lookup k m) of
    Nothing -> delete k m
    Just v  -> insert k v m
{-# INLINABLE alter #-}

------------------------------------------------------------------------
-- * Combine

-- | /O(n+m)/ The union of two maps.  If a key occurs in both maps,
-- the provided function (first argument) will be used to compute the result.
unionWith :: (Eq k, Hashable k) => (v -> v -> v) -> HashMap k v -> HashMap k v
          -> HashMap k v
unionWith f = unionWithKey (const f)
{-# INLINE unionWith #-}

-- | /O(n+m)/ The union of two maps.  If a key occurs in both maps,
-- the provided function (first argument) will be used to compute the
-- result.
unionWithKey
    :: (Eq k, Hashable k)
    => (k -> v -> v -> v)
    -> HashMap k v
    -> HashMap k v
    -> HashMap k v
unionWithKey f (HashMap sz m) hw =
    let A.Sized diff m' = unionWithKeyInternal f m hw
    in HashMap (diff + sz) m'
{-# INLINE unionWithKey #-}

-- | /O(n+m)/ The union of two maps.  If a key occurs in both maps,
-- the provided function (first argument) will be used to compute the result.
unionWithKeyInternal
    :: (Eq k, Hashable k)
    => (k -> v -> v -> v)
    -> Tree k v
    -> HashMap k v
    -> A.Sized (Tree k v)
unionWithKeyInternal f hm1 (HashMap siz hm2) = go 0 siz hm1 hm2
  where
    -- empty vs. anything
    go !_ !sz t1 Empty = A.Sized sz t1
    go _ !sz Empty t2 = A.Sized sz t2
    -- leaf vs. leaf
    go s !sz t1@(Leaf h1 l1@(L k1 v1)) t2@(Leaf h2 l2@(L k2 v2))
        | h1 == h2  = if k1 == k2
                      then A.Sized (sz - 1) (Leaf h1 (L k1 (f k1 v1 v2)))
                      else A.Sized sz (collision h1 l1 l2)
        | otherwise = goDifferentHash s sz h1 h2 t1 t2
    go s !sz t1@(Leaf h1 (L k1 v1)) t2@(Collision h2 ls2)
        | h1 == h2  =
            let !start = A.length ls2
                !newV = updateOrSnocWithKey f k1 v1 ls2
                !end = A.length newV
            in A.Sized (sz + end - start - 1) (Collision h1 newV)
        | otherwise = goDifferentHash s sz h1 h2 t1 t2
    go s !sz t1@(Collision h1 ls1) t2@(Leaf h2 (L k2 v2))
        | h1 == h2  =
            let !start = A.length ls1
                !newV = updateOrSnocWithKey (flip . f) k2 v2 ls1
                !end = A.length newV
            in A.Sized (sz + end - start - 1) (Collision h1 newV)
        | otherwise = goDifferentHash s sz h1 h2 t1 t2
    go s !sz t1@(Collision h1 ls1) t2@(Collision h2 ls2)
        | h1 == h2  =
            let !start = A.length ls1
                !newV = updateOrConcatWithKey f ls1 ls2
                !end = A.length newV
            in A.Sized (sz + (end - start - A.length ls2)) (Collision h1 newV)
        | otherwise = goDifferentHash s sz h1 h2 t1 t2
    -- branch vs. branch
    go s !sz (BitmapIndexed b1 ary1) (BitmapIndexed b2 ary2) =
        let b'         = b1 .|. b2
            A.RunRes dsz ary' =
                unionArrayByInternal sz
                                     (go (s+bitsPerSubkey))
                                     b1
                                     b2
                                     ary1
                                     ary2
        in A.Sized dsz (bitmapIndexedOrFull b' ary')
    go s !sz (BitmapIndexed b1 ary1) (Full ary2) =
        let A.RunRes dsz ary' =
                unionArrayByInternal sz
                                     (go (s+bitsPerSubkey))
                                     b1
                                     fullNodeMask
                                     ary1
                                     ary2
        in A.Sized dsz (Full ary')
    go s !sz (Full ary1) (BitmapIndexed b2 ary2) =
        let A.RunRes dsz ary' =
                unionArrayByInternal sz
                                     (go (s+bitsPerSubkey))
                                     fullNodeMask
                                     b2
                                     ary1
                                     ary2
        in A.Sized dsz (Full ary')
    go s !sz (Full ary1) (Full ary2) =
        let A.RunRes dsz ary' =
                unionArrayByInternal sz
                                     (go (s+bitsPerSubkey))
                                     fullNodeMask
                                     fullNodeMask
                                     ary1
                                     ary2
        in A.Sized dsz (Full ary')
    -- leaf vs. branch
    go s !sz (BitmapIndexed b1 ary1) t2
        | b1 .&. m2 == 0 = let ary' = A.insert ary1 i t2
                               b'   = b1 .|. m2
                           in A.Sized sz (bitmapIndexedOrFull b' ary')
        | otherwise      = let A.RunRes dsz ary' =
                                   A.updateWithInternal' ary1 i $ \st1 ->
                                       go (s+bitsPerSubkey) sz st1 t2
                           in A.Sized dsz (BitmapIndexed b1 ary')
        where
          h2 = leafHashCode t2
          m2 = mask h2 s
          i = sparseIndex b1 m2
    go s !sz t1 (BitmapIndexed b2 ary2)
        | b2 .&. m1 == 0 = let ary' = A.insert ary2 i $! t1
                               b'   = b2 .|. m1
                           in A.Sized sz (bitmapIndexedOrFull b' ary')
        | otherwise      = let A.RunRes dsz ary' =
                                   A.updateWithInternal' ary2 i $ \st2 ->
                                       go (s+bitsPerSubkey) sz t1 st2
                           in A.Sized dsz (BitmapIndexed b2 ary')
      where
        h1 = leafHashCode t1
        m1 = mask h1 s
        i = sparseIndex b2 m1
    go s !sz (Full ary1) t2 =
        let h2   = leafHashCode t2
            i    = index h2 s
            A.RunRes dsz ary' =
                update16WithInternal' ary1 i $ \st1 ->
                    go (s+bitsPerSubkey) sz st1 t2
        in A.Sized dsz (Full ary')
    go s !sz t1 (Full ary2) =
        let h1   = leafHashCode t1
            i    = index h1 s
            A.RunRes dsz ary' =
                update16WithInternal' ary2 i $ \st2 ->
                    go (s+bitsPerSubkey) sz t1 st2
        in A.Sized dsz (Full ary')

    leafHashCode (Leaf h _) = h
    leafHashCode (Collision h _) = h
    leafHashCode _ = error "leafHashCode"

    goDifferentHash s sz h1 h2 t1 t2
        | m1 == m2  = let A.Sized dsz hm = go (s+bitsPerSubkey) sz t1 t2
                      in A.Sized dsz (BitmapIndexed m1 (A.singleton hm))
        | m1 <  m2  = A.Sized sz (BitmapIndexed (m1 .|. m2) (A.pair t1 t2))
        | otherwise = A.Sized sz (BitmapIndexed (m1 .|. m2) (A.pair t2 t1))
      where
        m1 = mask h1 s
        m2 = mask h2 s
{-# INLINE unionWithKeyInternal #-}

------------------------------------------------------------------------
-- * Transformations

-- | /O(n)/ Transform this map by applying a function to every value.
mapWithKey :: (k -> v1 -> v2) -> HashMap k v1 -> HashMap k v2
mapWithKey f (HashMap sz m) = HashMap sz (go m)
  where
    go Empty                 = Empty
    go (Leaf h (L k v))      = leaf h k (f k v)
    go (BitmapIndexed b ary) = BitmapIndexed b $ A.map' go ary
    go (Full ary)            = Full $ A.map' go ary
    go (Collision h ary)     =
        Collision h $ A.map' (\ (L k v) -> let !v' = f k v in L k v') ary
{-# INLINE mapWithKey #-}

-- | /O(n)/ Transform this map by applying a function to every value.
map :: (v1 -> v2) -> HashMap k v1 -> HashMap k v2
map f = mapWithKey (const f)
{-# INLINE map #-}


------------------------------------------------------------------------
-- * Filter

-- | /O(n)/ Transform this map by applying a function to every value
--   and retaining only some of them.
mapMaybeWithKey :: (k -> v1 -> Maybe v2) -> HashMap k v1 -> HashMap k v2
mapMaybeWithKey f (HashMap _ m) = HashMap size' m'
  where onLeaf (Leaf h (L k v)) | Just v' <- f k v = Just (leaf h k v')
        onLeaf _ = Nothing

        onColl (L k v) | Just v' <- f k v = Just (L k v')
                       | otherwise = Nothing

        A.Sized size' m' = filterMapAuxInternal onLeaf onColl m
{-# INLINE mapMaybeWithKey #-}

-- | /O(n)/ Transform this map by applying a function to every value
--   and retaining only some of them.
mapMaybe :: (v1 -> Maybe v2) -> HashMap k v1 -> HashMap k v2
mapMaybe f = mapMaybeWithKey (const f)
{-# INLINE mapMaybe #-}


-- TODO: Should we add a strict traverseWithKey?

------------------------------------------------------------------------
-- * Difference and intersection

-- | /O(n*log m)/ Difference with a combining function. When two equal keys are
-- encountered, the combining function is applied to the values of these keys.
-- If it returns 'Nothing', the element is discarded (proper set difference). If
-- it returns (@'Just' y@), the element is updated with a new value @y@.
differenceWith
    :: (Eq k, Hashable k)
    => (v -> w -> Maybe v)
    -> HashMap k v
    -> HashMap k w
    -> HashMap k v
differenceWith f a b = foldlWithKey' go empty a
  where
    go m k v = case HM.lookup k b of
                 Nothing -> insert k v m
                 Just w  -> maybe m (\y -> insert k y m) (f v w)
{-# INLINABLE differenceWith #-}

-- | /O(n+m)/ Intersection of two maps. If a key occurs in both maps
-- the provided function is used to combine the values from the two
-- maps.
intersectionWith :: (Eq k, Hashable k) => (v1 -> v2 -> v3) -> HashMap k v1
                 -> HashMap k v2 -> HashMap k v3
intersectionWith f a b = foldlWithKey' go empty a
  where
    go m k v = case HM.lookup k b of
                 Just w -> insert k (f v w) m
                 _      -> m
{-# INLINABLE intersectionWith #-}

-- | /O(n+m)/ Intersection of two maps. If a key occurs in both maps
-- the provided function is used to combine the values from the two
-- maps.
intersectionWithKey :: (Eq k, Hashable k) => (k -> v1 -> v2 -> v3)
                    -> HashMap k v1 -> HashMap k v2 -> HashMap k v3
intersectionWithKey f a b = foldlWithKey' go empty a
  where
    go m k v = case HM.lookup k b of
                 Just w -> insert k (f k v w) m
                 _      -> m
{-# INLINABLE intersectionWithKey #-}

------------------------------------------------------------------------
-- ** Lists

-- | /O(n*log n)/ Construct a map with the supplied mappings.  If the
-- list contains duplicate mappings, the later mappings take
-- precedence.
fromList :: (Eq k, Hashable k) => [(k, v)] -> HashMap k v
fromList = L.foldl' (\ m (k, !v) -> HM.unsafeInsert k v m) empty
{-# INLINABLE fromList #-}

-- | /O(n*log n)/ Construct a map from a list of elements.  Uses
-- the provided function f to merge duplicate entries (f newVal oldVal).
--
-- For example:
--
-- > fromListWith (+) [ (x, 1) | x <- xs ]
--
-- will create a map with number of occurrences of each element in xs.
--
-- > fromListWith (++) [ (k, [v]) | (k, v) <- xs ]
--
-- will group all values by their keys in a list 'xs :: [(k, v)]' and
-- return a 'HashMap k [v]'.
fromListWith :: (Eq k, Hashable k) => (v -> v -> v) -> [(k, v)] -> HashMap k v
fromListWith f = L.foldl' (\ m (k, v) -> unsafeInsertWith f k v m) empty
{-# INLINE fromListWith #-}

------------------------------------------------------------------------
-- Array operations

updateWith :: Eq k => (v -> v) -> k -> A.Array (Leaf k v) -> A.Array (Leaf k v)
updateWith f k0 ary0 = go k0 ary0 0 (A.length ary0)
  where
    go !k !ary !i !n
        | i >= n    = ary
        | otherwise = case A.index ary i of
            (L kx y) | k == kx   -> let !v' = f y in A.update ary i (L k v')
                     | otherwise -> go k ary (i+1) n
{-# INLINABLE updateWith #-}

-- | Append the given key and value to the array. If the key is
-- already present, instead update the value of the key by applying
-- the given function to the new and old value (in that order). The
-- value is always evaluated to WHNF before being inserted into the
-- array.
updateOrSnocWith :: Eq k => (v -> v -> v) -> k -> v -> A.Array (Leaf k v)
                 -> A.Array (Leaf k v)
updateOrSnocWith f = updateOrSnocWithKey (const f)
{-# INLINABLE updateOrSnocWith #-}

-- | Append the given key and value to the array. If the key is
-- already present, instead update the value of the key by applying
-- the given function to the new and old value (in that order). The
-- value is always evaluated to WHNF before being inserted into the
-- array.
updateOrSnocWithKey :: Eq k => (k -> v -> v -> v) -> k -> v -> A.Array (Leaf k v)
                 -> A.Array (Leaf k v)
updateOrSnocWithKey f k0 v0 ary0 = go k0 v0 ary0 0 (A.length ary0)
  where
    go !k v !ary !i !n
        | i >= n = A.run $ do
            -- Not found, append to the end.
            mary <- A.new_ (n + 1)
            A.copy ary 0 mary 0 n
            let !l = v `seq` (L k v)
            A.write mary n l
            return mary
        | otherwise = case A.index ary i of
            (L kx y) | k == kx   -> let !v' = f k v y in A.update ary i (L k v')
                     | otherwise -> go k v ary (i+1) n
{-# INLINABLE updateOrSnocWithKey #-}

------------------------------------------------------------------------
-- Smart constructors
--
-- These constructors make sure the value is in WHNF before it's
-- inserted into the constructor.

leaf :: Hash -> k -> v -> Tree k v
leaf h k !v = Leaf h (L k v)
{-# INLINE leaf #-}
