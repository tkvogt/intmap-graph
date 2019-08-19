{-# LANGUAGE Strict, StrictData #-}
{-|
Module      :  Graph.IntMap
Copyright   :  (C) 2019 Tillmann Vogt

License     :  BSD-style (see the file LICENSE)
Maintainer  :  Tillmann Vogt <tillk.vogt@gmail.com>
Stability   :  provisional
Portability :  POSIX

-}
module Graph.IntMap (
    EdgeAttribute(..), IntMapGraph(..),
    Edge, Node32(..), Edge32(..), NodeEdge, Index, Bits(..),
    -- * Construction
    empty, fromMaps,
    insertNode, insertNodes,
    insertEdge, insertEdges,
    union,
        -- * Traversal
    mapNode, mapNodeWithKey,
    -- * Deletion
    deleteNode, deleteNodes,
    deleteEdge, deleteEdges,
    -- * Query
    isNull,
    lookupNode, lookupEdge,
    adjacentNodesByAttr, adjacentNodeCount,
    --allChildNodes,
    -- * Handling Labels
    buildWord64, extractFirstWord32, extractSecondWord32,
    edgeBackward,
    -- * Displaying in hex for debugging
    showHex, showHex32
  ) where

import           Data.Bits((.&.), (.|.))
import           Data.Char (intToDigit)
import qualified Data.IntMap as I
import           Data.IntMap(IntMap)
import           Data.Maybe(fromJust, isJust, isNothing, catMaybes, fromMaybe)
import qualified Data.Set as Set
import           Data.Set(Set(..))
import           Data.Word(Word32)
import           Foreign.Marshal.Alloc(allocaBytes)
import           Foreign.Ptr(castPtr, plusPtr)
import           Foreign.Storable(peek, pokeByteOff)
import           System.IO.Unsafe(unsafePerformIO)
import Debug.Trace


newtype Edge32 = Edge32 Word32
-- ^ Although both node and edge are Word32 we want to differentiate them
newtype Node32 = Node32 Word32 deriving (Eq, Ord)
-- ^ A typesafe Word32

instance Show Edge32 where show (Edge32 e) = "Edge " ++ (showHex32 e)
instance Show Node32 where show (Node32 n) = "Node " ++ show n

type Index    = Node32
type NodeEdge = Word
-- ^ combination of 32 bit (node+attr) and 32 bit edge

type Edge = (Node32,Node32)
-- ^ A tuple of nodes
type Bits = Int

edgeBackward = 0x80000000 -- the highest bit of a 32 bit word


-- | The edges are enumerated, because sometimes the edge attrs are not continuous
--   and it is impossible to try all possible 32 bit attrs
data EdgeAttribute el =>
     IntMapGraph nl el = IntMapGraph {
  intmapGraph :: IntMap (Set Word32), -- ^ A Graph with 32 bit keys on the edge
  nodeLabels :: IntMap nl, -- only the first 32 bits of the key are used
  edgeLabels :: IntMap el, -- the intmap-key of the edge from n0 to n1 is formed by n0 + n1*2^32
  showEdge :: Word32 -> el
}


-- | Convert a complex edge label to an attribute with (n<32) bits
--   How to do this depends on which edges have to be filtered fast
class EdgeAttribute el where
    fastEdgeAttr :: el -> Word32 -- The key that is used for counting
    edgeFromAttr :: Word32 -> el
--    edgeBackward :: el -> Word32 -- 0 if the edge is "in direction", otherwise a value (a bit) that 
--                      -- does not interfere with the rest of the attr (orthogonal attr)
  --   main attr of the arbitraryKeygraph
  --   e.g. unicode leaves 10 bits of the 32 bits unused, that could be used for the
  --   direction of the edge, if its a right or left edge in a binary tree, etc.


instance (EdgeAttribute el, Show nl, Show el, Enum nl) =>
         Show (IntMapGraph nl el) where
  show (IntMapGraph nodeEdgeGraph nlGraph elGraph showEdge) =
         "\ndigraph graphviz {\n"++
         concat (zipWith3 line nodeOrigins edges nodeDests) ++
         "}\n"
    where
      nodeOrigins = map extractFirstWord32 (map fromIntegral (I.keys nodeEdgeGraph))
      edges      = map extractSecondWord32 (map fromIntegral (I.keys nodeEdgeGraph))
      nodeDests = I.elems nodeEdgeGraph
      line or e dest = show or ++" -> "++ show dest ++" [ label = \""++ 
                       (backLabel e) ++ show (showEdge e) ++ "\" ];\n"

------------------------------------------------------------------------------------------

-- | Generate two empty intmaps and two empty intmaps for complex node and edge
--   labels. The purpose of the range list is to give a special interpretation of edges
--   depending on the node type.
empty :: EdgeAttribute el => IntMapGraph nl el
empty = IntMapGraph I.empty I.empty I.empty edgeFromAttr

-- | Are the intmaps of the graph all empty?
isNull (IntMapGraph graph nlgr elgr _) = I.null graph && I.null nlgr && I.null elgr


fromMaps :: EdgeAttribute el => IntMap nl -> IntMap el -> IntMap el -> IntMapGraph nl el
fromMaps nlabels elabels elabelsDir = IntMapGraph graph nlabels elabels edgeFromAttr
  where graph = insertNodeEdges (es ++ esDir) I.empty
        es = (map (toQuad True) (I.toList elabels)) ++ -- an undirected edge (a,b) is the same as two
             (map (toQuad False) (I.toList elabels))   -- directed edges (a,b), (b,a)
        esDir = map (toQuad True) (I.toList elabelsDir)
        toQuad b (k,v) = (Node32 (extractFirstWord32 (fromIntegral k)), -- TODO check that k has 64 bits
                          Node32 (extractSecondWord32 (fromIntegral k)), [v], b)


insertNode :: EdgeAttribute el => Node32 -> nl -> IntMapGraph nl el -> IntMapGraph nl el
insertNode (Node32 n) nl graph = graph { nodeLabels = I.insert (fromIntegral n) nl (nodeLabels graph) }


insertNodes :: EdgeAttribute el => [(Node32, nl)] -> IntMapGraph nl el -> IntMapGraph nl el
insertNodes nodes graph = foldr f graph nodes
  where f (n, nl) g = insertNode n nl g

---------------------------------------------

-- | Inserting a directed edge
insertEdge :: EdgeAttribute el => Edge -> el -> IntMapGraph nl el -> IntMapGraph nl el
insertEdge (Node32 n0, Node32 n1) elabel graph =
    graph { intmapGraph = newGraph,
            edgeLabels = I.insert e elabel (edgeLabels graph) }
  where e = fromIntegral (buildWord64 n0 n1)
        newGraph = I.insertWith Set.union ne (Set.singleton n1) (intmapGraph graph)
        ne = fromIntegral (buildWord64 n0 e32)
        e32 = fastEdgeAttr elabel


insertEdges :: EdgeAttribute el => [(Edge, el)] -> IntMapGraph nl el -> IntMapGraph nl el
insertEdges edges graph = foldr f graph edges
  where f (e, el) g = insertEdge e el g

-- TODO test
insertNodeEdges :: EdgeAttribute el => [(Node32,Node32,[el],Bool)] -> IntMap (Set Word32) -> IntMap (Set Word32)
insertNodeEdges es graph = foldr foldEs graph es
  where
    foldEs (n0, n1, edgeLs, dir) g = insertNodeEdgeAttr e g
      where e = (n0, n1, overlay edgeLs)
            overlay el = Edge32 (sum (map (addDir . fastEdgeAttr) el))
            addDir attr | dir = attr
                        | otherwise = attr + edgeBackward


-- | 
insertNodeEdgeAttr :: (Node32,Node32,Edge32) -> IntMap (Set Word32) -> IntMap (Set Word32)
insertNodeEdgeAttr (Node32 n0, Node32 n1, Edge32 attr) graph =
    I.insertWith Set.union (fromIntegral newValKey) (Set.singleton n1) graph
  where newValKey = buildWord64 n0 attr


union (IntMapGraph bg bnlg belg se0) (IntMapGraph sg snlg selg se1) =
      (IntMapGraph (I.union bg sg) (I.union bnlg snlg) (I.union belg selg) se0)

----------------------------------------------------------------------------------------

mapNode :: EdgeAttribute el => (nl0 -> nl1) -> IntMapGraph nl0 el -> IntMapGraph nl1 el
mapNode f g = IntMapGraph (intmapGraph g)
                          (I.map f (nodeLabels g))
                          (edgeLabels g) (showEdge g)

mapNodeWithKey :: EdgeAttribute el => (I.Key -> nl0 -> nl1) -> IntMapGraph nl0 el -> IntMapGraph nl1 el
mapNodeWithKey f g = IntMapGraph (intmapGraph g)
                                 (I.mapWithKey f (nodeLabels g))
                                 (edgeLabels g) (showEdge g)

----------------------------------------------------------------------------------------

deleteNode :: EdgeAttribute el => Node32 -> IntMapGraph nl el -> IntMapGraph nl el
deleteNode (Node32 n) graph = graph { nodeLabels = I.delete (fromIntegral n) (nodeLabels graph) }

deleteNodes graph nodes = foldr deleteNode nodes graph

-- | "deleteEdge (n0, n1) graph" deletes the edge that points from n0 to n1
deleteEdge :: EdgeAttribute el => Edge -> IntMapGraph nl el -> IntMapGraph nl el
deleteEdge (Node32 n0, Node32 n1) graph
    | isNothing elabel = graph
    | otherwise = graph { intmapGraph = newGraph,
                          edgeLabels = I.delete n64 (edgeLabels graph) }
  where elabel = I.lookup n64 (edgeLabels graph)
        n64 = fromIntegral (buildWord64 n0 n1)
        e32 = fastEdgeAttr (fromJust elabel)
        ne = fromIntegral (buildWord64 n0 e32)
        newGraph = I.adjust (Set.delete n1) ne (intmapGraph graph)


deleteEdges graph edges = foldr deleteEdge edges graph

----------------------------------------------------------------------------------------
-- | the nodelabel of the given node
lookupNode :: EdgeAttribute el => IntMapGraph nl el -> Node32 -> Maybe nl
lookupNode g (Node32 n) = I.lookup (fromIntegral n) (nodeLabels g)

-- | the edgelabel of the given edge of type (Node32, Node32)
lookupEdge :: EdgeAttribute el => IntMapGraph nl el -> Edge -> Maybe el
lookupEdge g (Node32 n0, Node32 n1) = I.lookup n (edgeLabels g)
  where n = fromIntegral (buildWord64 n0 n1)

{-
-- | All adjacent child nodes
allChildNodes :: EdgeAttribute el => IntMapGraph nl el -> Node32 -> [Node32]
allChildNodes graph (Node32 node) = 
-}

-----------------------------------------------------------------------------------------
-- Query

adjacentNodesByAttr :: EdgeAttribute el => IntMapGraph nl el -> Node32 -> Edge32 -> Bool -> [Node32]
adjacentNodesByAttr graph (Node32 node) (Edge32 attr) dir = maybe [] ((map Node32) . Set.toList) val
  where
    val = I.lookup (fromIntegral key) (intmapGraph graph)
    key = buildWord64 node (attr + if dir then 0 else edgeBackward)


---------------------------------------------------------------------------
-- | The number of adjacent edges
adjacentNodeCount :: EdgeAttribute el => IntMapGraph nl el -> Node32 -> Edge32 -> Int
adjacentNodeCount graph (Node32 node) (Edge32 attrBase) = maybe 0 Set.size (I.lookup edgeCountKey i)
  where
    -- the first index lookup is the count
    edgeCountKey = fromIntegral (buildWord64 node attrBase)
    i = intmapGraph graph

-------------------------------------------------------------------------
-- Handling labels

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

backLabel :: Word32 -> String
backLabel e | (e .&. edgeBackward) /= 0 = "back "
            | otherwise = ""
