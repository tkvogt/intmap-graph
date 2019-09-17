{-# LANGUAGE Strict, StrictData, DeriveGeneric, AllowAmbiguousTypes #-}
{-|
Module      :  Graph.IntMap
Copyright   :  (C) 2019 Tillmann Vogt

License     :  BSD-style (see the file LICENSE)
Maintainer  :  Tillmann Vogt <tillk.vogt@gmail.com>
Stability   :  provisional
Portability :  POSIX

-}
module Graph.IntMap (
    EdgeAttribute(..), Graph(..),
    Edge, Edge8(..), NodeEdge, Index, Bits(..),
    -- * Construction
    empty, fromLists, fromMaps,
    insertNode, insertNodes,
    insertEdge, insertEdges,
    union,
    -- * Traversal
    mapNode, mapNodeWithKey,
    -- * Deletion
    deleteNode, deleteNodes,
    deleteEdge, deleteEdges,
    -- * Query
    isNull, nodes, edges,
    lookupNode, lookupEdge,
    adjacentNodesByAttr, adjacentNodes, adjacentNodeCount,
    parents, children,
    -- * Bit Operations
    buildWord64, extractFirstWord32, extractSecondWord32,
    buildWord32, extractFirstWord24, extractSecondWord8,
    edgeBackward,
    -- * Displaying in hex for debugging
    showHex, showHex32
  ) where

import           Data.Bits((.&.), (.|.))
import           Data.Char (intToDigit)
import qualified Data.IntMap as I
import           Data.IntMap(IntMap)
import           Data.Map(Map)
import qualified Data.Map as Map
import           Data.Maybe(fromJust, isJust, isNothing, catMaybes, fromMaybe)
import qualified Data.Set as Set
import           Data.Set(Set(..))
import qualified Data.Vector.Unboxed as VU
import           Data.Word(Word8, Word32)
import           Foreign.Marshal.Alloc(allocaBytes)
import           Foreign.Ptr(castPtr, plusPtr)
import           Foreign.Storable(peek, pokeByteOff)
import           GHC.Generics
import           System.IO.Unsafe(unsafePerformIO)
import Debug.Trace


newtype Edge8 = Edge8 Word8
-- ^ Although both node and edge are Word32 we want to differentiate them

instance Show Edge8 where show (Edge8 e) = "Edge " ++ (showHex32 (fromIntegral e))

type Index    = Word32
type NodeEdge = Word
-- ^ combination of 32 bit (node+attr) and 32 bit edge

type Edge = (Word32,Word32)
-- ^ A tuple of nodes
type Bits = Int

edgeBackward :: Word8
edgeBackward = 128 -- the highest bit of a 8 bit word


-- | The edges are enumerated, because sometimes the edge attrs are not continuous
--   and it is impossible to try all possible 32 bit attrs
data Graph nl el = Graph {
  intmapGraph :: IntMap (Set Word32), -- ^ A Graph with 24 bit nodes and 8 bit edges
  nodeLabels :: IntMap nl, -- only the first 32 bits of the key are used
  edgeLabels :: Map (Word32, Word32) el, -- the intmap-key of the edge from n0 to n1 is formed by n0 + n1*2^32
  showEdge :: Map Word8 el
} deriving Generic

-- | Convert a complex edge label to an attribute with (n<32) bits
--   How to do this depends on which edges have to be filtered fast
class EdgeAttribute el where
    fastEdgeAttr :: el -> Word8 -- The key that is used for counting
    edgeFromAttr :: Map Word8 el -- 
    show_e :: Maybe el -> String
    bases :: el ->  [Edge8] -- the list of all attributes, so that we can compute all children an all parents
                             -- Only in the typeclass so that people do not forget to specify it

--    edgeBackward :: el -> Word32 -- 0 if the edge is "in direction", otherwise a value (a bit) that 
--                      -- does not interfere with the rest of the attr (orthogonal attr)
  --   main attr of the arbitraryKeygraph
  --   e.g. unicode leaves 10 bits of the 32 bits unused, that could be used for the
  --   direction of the edge, if its a right or left edge in a binary tree, etc.


instance (EdgeAttribute el, Eq el, Eq nl) => Eq (Graph nl el)
  where (Graph i0 n0 e0 _) == (Graph i1 n1 e1 _) = i0 == i1 && n0 == n1 && e0 == e1


instance (EdgeAttribute el, Show nl, Show el, Enum nl) =>
         Show (Graph nl el) where
  show (Graph nodeEdgeGraph nlGraph elGraph showEdge) =
         "\ndigraph graphviz {\n"++
         concat (zipWith3 line nodeOrigins edges nodeDests) ++
         "}\n nodes\n" ++ show nlGraph ++ "\n edges\n" ++ show elGraph
    where
      nodeOrigins = map extractFirstWord24 (map fromIntegral (I.keys nodeEdgeGraph))
      edges      = map extractSecondWord8 (map fromIntegral (I.keys nodeEdgeGraph))
      nodeDests = map (head . Set.toList) (I.elems nodeEdgeGraph)
      line or e dest = show or ++" -> "++ show dest ++" [ label = \""++ 
                       (backLabel e) ++ show_e (Map.lookup e showEdge) ++
                       "\" ];\n"

------------------------------------------------------------------------------------------

-- | Generate two empty intmaps and two empty intmaps for complex node and edge
--   labels. The purpose of the range list is to give a special interpretation of edges
--   depending on the node type.
empty :: EdgeAttribute el => Graph nl el
empty = Graph I.empty I.empty Map.empty edgeFromAttr

fromLists :: (EdgeAttribute el, Enum nl, Show nl, Show el) =>
             [(Word32, nl)] -> [((Word32, Word32), el)] -> [((Word32, Word32), el)] -> Graph nl el
fromLists ns es esDir = -- Debug.Trace.trace ("fromLists"++ show (es,nls,els,elsd,ms)) $
                        ms
  where ms = fromMaps nls els elsd True
        nls = I.fromList (map t ns)
        els = Map.fromList es
        elsd = Map.fromList esDir
        t (k,v) = (fromIntegral k, v)

-- | Make sure that elabels and elabelsDir have sorted node indexes, eg (0,1,el) and not (1,0,el)
fromMaps :: EdgeAttribute el => IntMap nl -> Map (Word32,Word32) el -> Map (Word32,Word32) el -> Bool -> Graph nl el
fromMaps nlabels elabels elabelsDir dir = -- Debug.Trace.trace "fromMaps " $
                                          Graph graph nlabels unionEdges edgeFromAttr
  where graph = insertNodeEdges (es ++ esDir) I.empty
        unionEdges = Map.union (Map.mapKeys ord elabels)
                               (Map.mapKeys ord elabelsDir)
        es = (map toQuad    (Map.toList elabels)) ++ -- an undirected edge (a,b) is the same as two
             (map toQuadRev (Map.toList elabels))   -- directed edges (a,b), (b,a)
        esDir = (map toQuad    (Map.toList elabelsDir)) ++
                (if dir then map toQuadRev2 (Map.toList elabelsDir) else [])
        toQuad     ((n0,n1),v) = (n0, n1, [v], True)
        toQuadRev  ((n0,n1),v) = (n1, n0, [v], True)
        toQuadRev2 ((n0,n1),v) = (n1, n0, [v], False)

        ord (n0,n1) | n0 <= n1  = (n0,n1)
                    | otherwise = (n1,n0)

insertNode :: EdgeAttribute el => Word32 -> nl -> Graph nl el -> Graph nl el
insertNode n nl graph = -- Debug.Trace.trace "insertNode" $
                        graph { nodeLabels = I.insert (fromIntegral n) nl (nodeLabels graph) }


insertNodes :: EdgeAttribute el => [(Word32, nl)] -> Graph nl el -> Graph nl el
insertNodes nodes graph = foldr f graph nodes
  where f (n, nl) g = insertNode n nl g


-- | Inserting an edge
--   If maybeIsBack is Nothing only one directed is edge from n0 to n1 is inserted
--   If maybeIsBack is Just then a second directed edge from n1 to n0 is inserted
--   isBack = False means a directed edge that can be explored in both directions
--   isBack = True means a undirected edge that also can be explored in both directions
insertEdge :: EdgeAttribute el => Maybe Bool -> Edge -> el -> Graph nl el -> Graph nl el
insertEdge maybeIsBack (n0, n1) elabel graph = -- Debug.Trace.trace "insertEdge" $
    graph { intmapGraph = newGraph,
            edgeLabels = if n0 <= n1 then Map.insert (n0,n1) elabel (edgeLabels graph)
                                     else Map.insert (n1,n0) elabel (edgeLabels graph) }
  where newGraph = insertNodeEdge (n0, n1, [elabel], True) revEdgeGraph
        revEdgeGraph | isJust maybeIsBack = insertNodeEdge (n1, n0, [elabel], fromJust maybeIsBack) (intmapGraph graph)
                     | otherwise = intmapGraph graph

-- | Inserting an edge
--   If maybeIsBack is Nothing only one directed is edge from n0 to n1 is inserted
--   If maybeIsBack is Just then a second directed edge from n1 to n0 is inserted
--   isBack = False means a directed edge that can be explored in both directions
--   isBack = True means a undirected edge that also can be explored in both directions
insertEdges :: EdgeAttribute el => Maybe Bool -> [(Edge, el)] -> Graph nl el -> Graph nl el
insertEdges maybeIsBack edges graph = foldr f graph edges
  where f (e, el) g = insertEdge maybeIsBack e el g


-- TODO test
insertNodeEdges :: EdgeAttribute el => [(Word32,Word32,[el],Bool)] -> IntMap (Set Word32) -> IntMap (Set Word32)
insertNodeEdges es graph = -- Debug.Trace.trace "insertNodeEdges" $
                           foldr insertNodeEdge graph es


insertNodeEdge :: EdgeAttribute el => (Word32,Word32,[el],Bool) -> IntMap (Set Word32) -> IntMap (Set Word32)
insertNodeEdge (n0, n1, edgeLs, dir) g = -- Debug.Trace.trace ("insertNodeEdge (dir, e)"++ show (dir, e)) $
                                         insertNodeEdgeAttr e g
  where e = (n0, n1, overlay edgeLs)
        overlay el = Edge8 (sum (map (addDir . fastEdgeAttr) el))
        addDir attr | dir = attr
                    | otherwise = attr + edgeBackward


-- | 
insertNodeEdgeAttr :: (Word32,Word32,Edge8) -> IntMap (Set Word32) -> IntMap (Set Word32)
insertNodeEdgeAttr (n0, n1, Edge8 attr) graph = -- Debug.Trace.trace ("insertNodeEdgeAttr(n0,n1,attr)" ++ show (n0,n1,Edge8 attr)) $
    I.insertWith Set.union (fromIntegral newValKey) (Set.singleton n1) graph
  where newValKey = buildWord32 n0 attr


union (Graph bg bnlg belg s) (Graph sg snlg selg _) =
       Graph (I.union bg sg) (I.union bnlg snlg) (Map.union belg selg) s

----------------------------------------------------------------------------------------

mapNode :: EdgeAttribute el => (nl0 -> nl1) -> Graph nl0 el -> Graph nl1 el
mapNode f g = Graph (intmapGraph g) (I.map f (nodeLabels g)) (edgeLabels g) (showEdge g)


mapNodeWithKey :: EdgeAttribute el => (I.Key -> nl0 -> nl1) -> Graph nl0 el -> Graph nl1 el
mapNodeWithKey f g = Graph (intmapGraph g) (I.mapWithKey f (nodeLabels g)) (edgeLabels g) (showEdge g)

----------------------------------------------------------------------------------------

deleteNode :: EdgeAttribute el => Word32 -> Graph nl el -> Graph nl el
deleteNode n graph = graph { nodeLabels = I.delete (fromIntegral n) (nodeLabels graph) }

deleteNodes graph nodes = foldr deleteNode nodes graph

-- | "deleteEdge (n0, n1) graph" deletes the edge that points from n0 to n1
deleteEdge :: EdgeAttribute el => Maybe Bool -> Edge -> Graph nl el -> Graph nl el
deleteEdge maybeIsBack (n0, n1) graph
    | isNothing elabel = graph
    | otherwise = graph { intmapGraph = newGraph1,
                          edgeLabels = Map.delete (if n0 <= n1 then (n0, n1) else (n1, n0)) (edgeLabels graph) }
  where elabel = Map.lookup (if n0 <= n1 then (n0, n1) else (n1, n0)) (edgeLabels graph)
        e8 = fastEdgeAttr (fromJust elabel)
        ne = fromIntegral (buildWord32 n0 e8)
        ne1 = fromIntegral (buildWord32 n1 e8)
        newGraph = I.adjust (Set.delete n1) ne (intmapGraph graph)
        newGraph1 = I.adjust (Set.delete n0) ne1 newGraph

deleteEdges maybeIsBack graph edges = foldr (deleteEdge maybeIsBack) edges graph

----------------------------------------------------------------------------------------

-- | the nodelabel of the given node
lookupNode :: (Show nl, EdgeAttribute el) => Word32 -> Graph nl el -> Maybe nl
lookupNode n g = -- Debug.Trace.trace ("lookupNode(n,lu)" ++ show (n,lu)) $
                 lu
  where lu = I.lookup (fromIntegral n) (nodeLabels g)

-- | the edgelabel of the given edge of type (Word32, Word32)
lookupEdge :: (EdgeAttribute el, Show el) => Edge -> Graph nl el -> Maybe el
lookupEdge (n0, n1) g = -- Debug.Trace.trace ("lookupEdge(n0,n1,lu,edgeLabels g)"++ show (n0, n1, lu,edgeLabels g) ) $
                        lu
  where lu | n0 <= n1  = Map.lookup (n0,n1) (edgeLabels g)
           | otherwise = Map.lookup (n1,n0) (edgeLabels g)

-----------------------------------------------------------------------------------------
-- Query

-- | Are the intmaps of the graph all empty?
isNull (Graph graph nlgr elgr _) = I.null graph && I.null nlgr && Map.null elgr

nodes (Graph graph nlgr elgr _) = I.keys nlgr

edges (Graph graph nlgr elgr _) = Map.keys elgr

adjacentNodesByAttr :: EdgeAttribute el => Graph nl el -> Bool -> Word32 -> Edge8 -> VU.Vector Word32
adjacentNodesByAttr graph dir node (Edge8 attr) = -- Debug.Trace.trace ("adjacentNodesByAttr(n,str,val)" ++ show (node, Edge8 attr, val)) $
                                                   maybe VU.empty (VU.fromList . Set.toList) val
  where
    val = I.lookup (fromIntegral key) (intmapGraph graph)
    key = buildWord32 node (attr + if dir then 0 else edgeBackward)


adjacentNodes :: EdgeAttribute el => Graph nl el -> Word32 -> el -> [Word32]
adjacentNodes graph node someEdge = -- Debug.Trace.trace "adjacentNodes" $
    VU.toList $
    VU.concat $ (map (adjacentNodesByAttr graph True node) bs) ++
                (map (adjacentNodesByAttr graph False node) bs)
  where bs = bases someEdge


-- | The number of adjacent edges
adjacentNodeCount :: EdgeAttribute el => Graph nl el -> Word32 -> Edge8 -> Int
adjacentNodeCount graph node (Edge8 attrBase) = -- Debug.Trace.trace "adjacentNodeCount" $
    maybe 0 Set.size (I.lookup edgeCountKey i)
  where
    -- the first index lookup is the count
    edgeCountKey = fromIntegral (buildWord32 node attrBase)
    i = intmapGraph graph


children :: EdgeAttribute el => Graph nl el -> Word32 -> el -> VU.Vector Word32
children graph node someEdge = -- Debug.Trace.trace "children" $
    VU.concat $ (map (adjacentNodesByAttr graph True node) bs)
  where bs = bases someEdge


parents :: EdgeAttribute el => Graph nl el -> Word32 -> el -> VU.Vector Word32
parents graph node someEdge = -- Debug.Trace.trace "parents" $
    VU.concat $ (map (adjacentNodesByAttr graph False node) bs)
  where bs = bases someEdge

-------------------------------------------------------------------------
-- Bit Operations

-- | concatenate two Word32 to a Word (64 bit)
{-# INLINE buildWord64 #-}
buildWord64 :: Word32 -> Word32 -> Word
buildWord64 w0 w1
    = unsafePerformIO . allocaBytes 8 $ \p -> do
        pokeByteOff p 0 w0
        pokeByteOff p 4 w1
        peek (castPtr p)

-- | extract the first 32 bit of a 64 bit word
{-# INLINE extractFirstWord32 #-}
extractFirstWord32 :: Word -> Word32
extractFirstWord32 w
    = unsafePerformIO . allocaBytes 4 $ \p -> do
        pokeByteOff p 0 w
        peek (castPtr p)

-- | extract the second 32 bit of a 64 bit word
{-# INLINE extractSecondWord32 #-}
extractSecondWord32 :: Word -> Word32
extractSecondWord32 w
    = unsafePerformIO . allocaBytes 4 $ \p -> do
        pokeByteOff p 0 w
        peek (castPtr (plusPtr p 4))

--------------------------------------------------
-- Javascript does not support 64 bit Ints, we have to use 32 bit

-- | nodes can use 24 bits, edges 8 bits
buildWord32 :: Word32 -> Word8 -> Word32
buildWord32 w0 w1
    = unsafePerformIO . allocaBytes 4 $ \p -> do
        pokeByteOff p 0 w0
        pokeByteOff p 3 w1
        peek (castPtr p)

-- | extract the first 24 bit of a 32 bit word
{-# INLINE extractFirstWord24 #-}
extractFirstWord24 :: Word32 -> Word32
extractFirstWord24 w = w .&. 0xFFFFFF

-- | extract the last 8 bit of a 32 bit word
{-# INLINE extractSecondWord8 #-}
extractSecondWord8 :: Word32 -> Word8
extractSecondWord8 w
    = unsafePerformIO . allocaBytes 1 $ \p -> do
        pokeByteOff p 0 w
        peek (castPtr (plusPtr p 3))

------------------------------------------------------------------
-- Debugging

-- | display a 64 bit word so that we can see the bits better
showHex :: Word -> String
showHex n = showIt 16 n ""
   where
    showIt :: Int -> Word -> String -> String
    showIt 0 _ r = r
    showIt i x r = case quotRem x 16 of
                       (y, z) -> let c = intToDigit (fromIntegral z)
                                 in c `seq` showIt (i-1) y (c:r)

-- | display a 32 bit word so that we can see the bits better
showHex32 :: Word32 -> String
showHex32 n = showIt 8 n ""
   where
    showIt :: Int -> Word32 -> String -> String
    showIt 0 _ r = r
    showIt i x r = case quotRem x 16 of
                       (y, z) -> let c = intToDigit (fromIntegral z)
                                 in c `seq` showIt (i-1) y (c:r)

backLabel :: Word8 -> String
backLabel e | (e .&. edgeBackward) /= 0 = "back "
            | otherwise = ""

