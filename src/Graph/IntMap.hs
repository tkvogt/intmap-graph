{-# LANGUAGE Strict, StrictData, DeriveGeneric, AllowAmbiguousTypes #-}
{-|
Module      :  Graph.IntMap
Copyright   :  (C) 2019 Tillmann Vogt

License     :  BSD-style (see the file LICENSE)
Maintainer  :  Tillmann Vogt <tillk.vogt@gmail.com>
Stability   :  stable
Portability :  GHC

The general idea of this library is that edges can put into classes. 
As it is faster to lookup a 32/64-bit integer in an intmap than a tuple of integers in a Data.Map-map, we construct a graph by putting a node (24 bit) and its class (8 bit) of adjacent nodes into a 32 bit integer. We need to restrict it to 32 bit, because Javascript (and therefore GHCJS) only has 32 bit integers. If you want to use this library outside of a browser, use 64 bit and set the bool arg of some functions to False. Then there are 32 bits for the node and 32 bits for the edge class.

-}
module Graph.IntMap (
    EdgeAttribute(..), Graph(..), ExtractNodeType(..),
    Edge, Edge8(..),
    -- * Construction
    empty, fromLists, fromMaps,
    insertNode, insertNodes, adjustNode, adjustEdge,
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
    adjacentNodesByAttr, adjacentNodes,
    parents, children,
    -- * Bit Operations
    buildWord64, extractFirstWord32, extractSecondWord32,
    buildWord32, extractFirstWord24, extractSecondWord8,
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
-- ^ In Javascript there are only 32 bit integers.
--   If we want to squeeze a node and an edge into this we use 24 bits for the node and 8 bits for the edge

instance Show Edge8 where show (Edge8 e) = "Edge " ++ (showHex32 (fromIntegral e))

type Node = Word32
-- ^ Assuming that 24 bits (~16 million) is enough for Javascript UI graph code

type Edge = (Node,Node)
-- ^ A tuple of nodes

-- | The edges are enumerated, because sometimes the edge attrs are not continuous
--   and it is impossible to try all possible 32 bit attrs
data Graph nl el = Graph {
  outgoingNodes :: IntMap (Set Node), -- ^ A Graph of outgoing 32 bit nodeEdges with 24 bit nodes and 8 bit edges
  incomingNodes :: IntMap (Set Node), -- ^ A Graph of incoming 32 bit nodeEdges with 24 bit nodes and 8 bit edges
  nodeLabels :: IntMap nl, -- only the first 32 bits of the key are used
  edgeLabels :: Map (Node, Node) el, -- the intmap-key of the edge from n0 to n1 is formed by n0 + n1*2^32
  is32BitInt :: Bool,
  showEdge :: Map Word8 el
} deriving Generic

-- | Convert a complex edge label to an attribute with 8 bits
--   How to do this depends on which edges have to be filtered fast
class EdgeAttribute el where
    fastEdgeAttr :: el -> Word8 -- The key that is used for counting
    edgeFromAttr :: Map Word8 el -- 
    show_e :: Maybe el -> String
    bases :: el ->  [Edge8] -- the list of all attributes, so that we can compute all children and all parents
                            -- Only in the typeclass so that people do not forget to specify it
  --   main attr of the arbitraryKeygraph
  --   e.g. unicode leaves 10 bits of the 32 bits unused, that could be used for the
  --   direction of the edge, if its a right or left edge in a binary tree, etc.

-- | if a node label is complicated, specify a short string to understand its type
class ExtractNodeType nl where
    extractNodeType :: nl -> String

instance (EdgeAttribute el, Eq el, Eq nl) => Eq (Graph nl el)
  where (Graph o0 i0 n0 e0 b0 _) == (Graph o1 i1 n1 e1 b1 _) = b0 == b1 && o0 == o1 && i0 == i1 && n0 == n1 && e0 == e1


instance (EdgeAttribute el, Show nl, ExtractNodeType nl, Show el, Enum nl) =>
         Show (Graph nl el) where
  show (Graph outgoingNodes incomingNodes nlGraph elGraph b showEdge) =
         (if b then "32bit graph\n" else "64 bit graph\n") ++
         "\noutgoing\ndigraph graphviz {\n" ++
         concat (zipWith3 lines nodeOrigins0 edges0 nodeDests0) ++
         "}\n" ++
         "\nincoming\ndigraph graphviz {\n"++
         concat (zipWith3 lines nodeOrigins1 edges1 nodeDests1) ++
         "}\n\n nodes\n" ++ concat (map ((++"\n"). show) (I.toList nlGraph)) ++
         "\n\n edges\n" ++ concat (map ((++"\n"). show) (Map.toList  elGraph))
    where
      nodeOrigins0 = map (if b then extractFirstWord24 . fromIntegral
                               else extractFirstWord32 . fromIntegral)
                         (I.keys outgoingNodes)
      edges0       = map (if b then extractSecondWord8 . fromIntegral
                               else fromIntegral . extractSecondWord32 . fromIntegral)
                         (I.keys outgoingNodes)
      nodeDests0 = map Set.toList (I.elems outgoingNodes)

      nodeOrigins1 = map (if b then extractFirstWord24 . fromIntegral
                               else extractFirstWord32 . fromIntegral)
                         (I.keys incomingNodes)
      edges1       = map (if b then extractSecondWord8 . fromIntegral
                               else fromIntegral . extractSecondWord32 .fromIntegral)
                         (I.keys incomingNodes)
      nodeDests1 = map Set.toList (I.elems incomingNodes)

      lines or e dests = concat (map (line . f) dests) where f d = (or,e,d)
      line (or, e, dest) = extr nlGraph or ++ show or ++ " -> "++ extr nlGraph dest ++ show dest ++" [ label = \"" ++
                           show_e (Map.lookup e showEdge) ++ "\" ];\n"

extr g n = maybe "" extractNodeType (I.lookup (fromIntegral n) g)

------------------------------------------------------------------------------------------

-- | Generate an empty graph with 32 bit node-edges (24 bit for the node) that can be 
--   used with code that ghcjs compiled to javascript
empty :: EdgeAttribute el => Graph nl el
empty = Graph I.empty I.empty I.empty Map.empty True edgeFromAttr

-- | Generate an empty graph with 64 bit node-edges, 32 bit for the node
empty64 :: EdgeAttribute el => Graph nl el
empty64 = Graph I.empty I.empty I.empty Map.empty False edgeFromAttr

-- | Construct a graph from a  list of nodes, undirected edges and directed edges,
--   the bool has to be true it uses 32 bit integers, if false it uses 64 bit integers
fromLists :: (EdgeAttribute el, Enum nl, Show nl, Show el) =>
             Bool -> [(Node, nl)] -> [((Node, Node), el)] -> [((Node, Node), el)] -> Graph nl el
fromLists b ns es esDir = -- Debug.Trace.trace ("fromLists"++ show (es,nls,els,elsd,ms)) $
                          ms
  where ms = fromMaps b nls els elsd True
        nls = I.fromList (map t ns)
        els = Map.fromList es
        elsd = Map.fromList esDir
        t (k,v) = (fromIntegral k, v)


-- | Construct a graph from a node map, undirected edges map and directed edges map, b = True means 32 bit integers
fromMaps :: (EdgeAttribute el, Show nl, Show el, Enum nl) =>
            Bool -> IntMap nl -> Map (Node,Node) el -> Map (Node,Node) el -> Bool -> Graph nl el
fromMaps b nlabels elabels elabelsDir dir = -- Debug.Trace.trace ("fromMaps " ++ show newGraph )$
                                            newGraph
  where newGraph = Graph ograph igraph nlabels unionEdges b edgeFromAttr
        ograph = insertNodeEdges b (es0 ++ esDir0) I.empty
        igraph = insertNodeEdges b         esDir1  I.empty
        unionEdges = Map.union (Map.mapKeys ord elabels)
                               (Map.mapKeys ord elabelsDir)
        es0    = (map triple (Map.toList elabels)) ++ (map rev (Map.toList elabels))
        esDir0 = map triple (Map.toList elabelsDir)
        esDir1 = if dir then map rev (Map.toList elabelsDir) else []
        rev  ((n0,n1),v) = ((n1,n0), [v])
        triple ((n0,n1),v) = ((n0,n1), [v])

        ord (n0,n1) | n0 <= n1  = (n0,n1)
                    | otherwise = (n1,n0)


-- | Insert node with node label
insertNode :: EdgeAttribute el => Node -> nl -> Graph nl el -> Graph nl el
insertNode n nl graph = -- Debug.Trace.trace "insertNode" $
                        graph { nodeLabels = I.insert (fromIntegral n) nl (nodeLabels graph) }


-- | Insert nodes with their label
insertNodes :: EdgeAttribute el => [(Node, nl)] -> Graph nl el -> Graph nl el
insertNodes nodes graph = foldr f graph nodes
  where f (n, nl) g = insertNode n nl g


-- | Adjust a node label of a specific node. When the node is not a member of the graph, the original graph is returned.
adjustNode :: EdgeAttribute el => (nl -> nl) -> Node -> Graph nl el -> Graph nl el
adjustNode f n graph = -- Debug.Trace.trace "insertNode" $
                       graph { nodeLabels = I.adjust f (fromIntegral n) (nodeLabels graph) }


-- | Adjust an edge label of a specific edge. When the edge is not a member of the graph, the original graph is returned.
adjustEdge :: EdgeAttribute el => (el -> el) -> Edge -> Graph nl el -> Graph nl el
adjustEdge f (n0,n1) graph = -- Debug.Trace.trace "insertNode" $
                             graph { edgeLabels = Map.adjust f (fromIntegral n0, fromIntegral n1) (edgeLabels graph) }


-- | Inserting an edge
--   If maybeIsBack is Nothing only one directed is edge from n0 to n1 is inserted
--   If maybeIsBack is Just then a second directed edge from n1 to n0 is inserted
--   isBack = True means an opposite directed edge that can be explored in both directions
--   isBack = False means a undirected edge that also can be explored in both directions
insertEdge :: EdgeAttribute el => Maybe Bool -> Edge -> el -> Graph nl el -> Graph nl el
insertEdge maybeIsBack (n0, n1) elabel graph =
    graph { outgoingNodes = newOutGraph,
            incomingNodes = newInGraph,
            edgeLabels = if n0 <= n1 then Map.insert (n0,n1) elabel (edgeLabels graph)
                                     else Map.insert (n1,n0) elabel (edgeLabels graph) }
  where newOutGraph | isNothing maybeIsBack = insertNodeEdge b ((n0, n1), [elabel]) (outgoingNodes graph)
                    | not (fromJust maybeIsBack) = insertNodeEdge b ((n0, n1), [elabel])
                                                  (insertNodeEdge b ((n1, n0), [elabel]) (outgoingNodes graph))
                    | otherwise             = insertNodeEdge b ((n0, n1), [elabel]) (outgoingNodes graph)
        newInGraph | isNothing maybeIsBack = incomingNodes graph
                   | not (fromJust maybeIsBack) = insertNodeEdge b ((n0, n1), [elabel])
                                                 (insertNodeEdge b ((n1, n0), [elabel]) (incomingNodes graph))
                   | otherwise = insertNodeEdge b ((n1, n0), [elabel]) (incomingNodes graph)
        b = is32BitInt graph

-- | Inserting an edge
--   If maybeIsBack is Nothing only one directed is edge from n0 to n1 is inserted
--   If maybeIsBack is Just then a second directed edge from n1 to n0 is inserted
--   isBack = True means an opposite directed edge that can be explored in both directions
--   isBack = False means a undirected edge that also can be explored in both directions
insertEdges :: EdgeAttribute el => Maybe Bool -> [(Edge, el)] -> Graph nl el -> Graph nl el
insertEdges maybeIsBack edges graph = foldr f graph edges
  where f (e, el) g = insertEdge maybeIsBack e el g


-- | Inserting node-edges
insertNodeEdges :: EdgeAttribute el => Bool -> [((Node,Node),[el])] -> IntMap (Set Node) -> IntMap (Set Node)
insertNodeEdges b es graph = -- Debug.Trace.trace "insertNodeEdges" $
                             foldr (insertNodeEdge b) graph es


-- | Inserting a node edge.
--   Exploring a graph is faster if a node and edge is combined into an 32/64 bit integer that points to a node
insertNodeEdge :: EdgeAttribute el => Bool -> ((Node,Node),[el]) -> IntMap (Set Node) -> IntMap (Set Node)
insertNodeEdge b ((n0, n1), edgeLs) g = -- Debug.Trace.trace ("insertNodeEdge (dir, e)"++ show (dir, e)) $
                                        insertNodeEdgeAttr b e g
  where e = ((n0, n1), overlay edgeLs)
        overlay el = Edge8 (sum (map fastEdgeAttr el)) -- TODO handling several edges


-- | An 8 bit value is computed from the edge and combined with the emanating node
insertNodeEdgeAttr :: Bool -> ((Node,Node),Edge8) -> IntMap (Set Node) -> IntMap (Set Node)
insertNodeEdgeAttr b ((n0, n1), Edge8 attr) graph =
       -- Debug.Trace.trace ("insertNodeEdgeAttr(n0,n1,attr,imap)" ++ show (n0,n1,Edge8 attr, imap)) $
                                                    imap
  where newValKey | b         = fromIntegral (buildWord32 n0 attr)
                  | otherwise = fromIntegral (buildWord64 n0 (fromIntegral attr))
        imap = I.insertWith Set.union newValKey (Set.singleton n1) graph


-- | Makes a union over all components of the graph
union (Graph og0 ig0 nlg0 elg0 b0 s)
      (Graph og1 ig1 nlg1 elg1 b1 _)
        | b0 /= b1 = error "cannot combine 32 bit wiht 62 bit graph"
        | otherwise = -- Debug.Trace.trace ("\nunion\n" ++ show g) $
                      g
  where g = Graph (I.union og0 og1) (I.union ig0 ig1) (I.union nlg0 nlg1) (Map.union elg0 elg1) b0 s

----------------------------------------------------------------------------------------

-- | Mapping a function over the node labels
mapNode :: EdgeAttribute el => (nl0 -> nl1) -> Graph nl0 el -> Graph nl1 el
mapNode f g = Graph (outgoingNodes g)
                    (incomingNodes g)
                    (I.map f (nodeLabels g))
                    (edgeLabels g) (is32BitInt g) (showEdge g)


-- | Mapping a function over the node labels with node key
mapNodeWithKey :: EdgeAttribute el => (I.Key -> nl0 -> nl1) -> Graph nl0 el -> Graph nl1 el
mapNodeWithKey f g = Graph (outgoingNodes g)
                           (incomingNodes g)
                           (I.mapWithKey f (nodeLabels g))
                           (edgeLabels g) (is32BitInt g) (showEdge g)

----------------------------------------------------------------------------------------

-- | Delete node with its nodelabel and also all outgoing and incoming edges with their edgeLabels
deleteNode :: (EdgeAttribute el, Show nl, Show el, Enum nl) => el -> Node -> Graph nl el -> Graph nl el
deleteNode elabel n graph = graph { outgoingNodes = newOutGraph,
                                    incomingNodes = newInGraph,
                                    nodeLabels = I.delete (fromIntegral n) (nodeLabels graph),
                                    edgeLabels = foldr Map.delete (edgeLabels graph) (map ord edgeLabelsToDelete) }
  where newOutGraphOrigin = foldr I.delete (outgoingNodes graph) nodeEdges
        newInGraphOrigin  = foldr I.delete (incomingNodes graph) nodeEdges
        newOutGraph = foldr deleten newOutGraphOrigin (map fromIntegral adjNEs)
        newInGraph  = foldr deleten newInGraphOrigin  (map fromIntegral adjNEs)
        deleten ne g = I.update delEmpty ne (I.adjust (Set.delete n) ne g)
        adjNEs | b         = concat $ map (\a -> map (\b -> buildWord32 a (fromIntegral b)) bs) adj
               | otherwise = map fromIntegral $
                             concat $ map (\a -> map (\b -> buildWord64 a (fromIntegral b)) bs) adj
        edgeLabelsToDelete = zip (repeat n) adj
        adj = adjacentNodes graph n elabel
        ord (n0,n1) | n0 <= n1  = (n0,n1)
                    | otherwise = (n1,n0)
        nodeEdges | b         = map fromIntegral (map (buildWord32 n) bs)
                  | otherwise = map fromIntegral (map (buildWord64 n) (map fromIntegral bs))
        bs = map (\(Edge8 e) -> e) (bases elabel)
        b = is32BitInt graph


-- | Delete nodes with their label
deleteNodes elabel graph nodes = foldr (deleteNode elabel) nodes graph


delEmpty x | null x = Nothing
           | otherwise = Just x


-- | "deleteEdge (n0, n1) graph" deletes the edgelabel of (n0,n1) and the nodeEdge that points from n0 to n1
--   If maybeIsBack is Just then a second directed edge from n1 to n0 is deleted
--   isBack = True means an opposite directed edge that can be explored in both directions
--   isBack = False means a undirected edge that also can be explored in both directions
deleteEdge :: EdgeAttribute el => Maybe Bool -> Edge -> Graph nl el -> Graph nl el
deleteEdge maybeIsBack (n0, n1) graph
    | isNothing elabel = graph
    | otherwise = -- Debug.Trace.trace ("deleteEdge "++ show (n0, n1, maybeIsBack)) $
                  graph { outgoingNodes = newOutGraph,
                          incomingNodes = newInGraph,
                          edgeLabels = Map.delete (if n0 <= n1 then (n0, n1) else (n1, n0)) (edgeLabels graph) }
  where elabel = Map.lookup (if n0 <= n1 then (n0, n1) else (n1, n0)) (edgeLabels graph)

        newOutGraph = ((I.update delEmpty ne0) . (I.update delEmpty ne1) .
                       (I.adjust (Set.delete n0) ne1) . (I.adjust (Set.delete n1) ne0)) (outgoingNodes graph)

        newInGraph = ((I.update delEmpty ne0) . (I.update delEmpty ne1) .
                       (I.adjust (Set.delete n0) ne1) . (I.adjust (Set.delete n1) ne0)) (incomingNodes graph)

        ne0 | is32BitInt graph = fromIntegral (buildWord32 n0 e8)
            | otherwise        = fromIntegral (buildWord64 n0 (fromIntegral e8))
        ne1 | is32BitInt graph = fromIntegral (buildWord32 n1 e8)
            | otherwise        = fromIntegral (buildWord64 n1 (fromIntegral e8))
        e8 = maybe 0 fastEdgeAttr elabel


-- | Delete a list of (Node,Node) edges from the graph
deleteEdges maybeIsBack graph edges = -- Debug.Trace.trace ("deleteEdges "++ show maybeIsBack) $
                                      foldr (deleteEdge maybeIsBack) edges graph

----------------------------------------------------------------------------------------

-- | The nodelabel of the given node
lookupNode :: (Show nl, EdgeAttribute el) => Node -> Graph nl el -> Maybe nl
lookupNode n g = -- Debug.Trace.trace ("lookupNode(n,lu)" ++ show (n,lu)) $
                 lu
  where lu = I.lookup (fromIntegral n) (nodeLabels g)


-- | The edgelabel of the given edge of type (Node, Node)
lookupEdge :: (EdgeAttribute el, Show el) => Edge -> Graph nl el -> Maybe el
lookupEdge (n0, n1) g = -- Debug.Trace.trace ("lookupEdge(n0,n1,lu,edgeLabels g)"++ show (n0, n1, lu,edgeLabels g) ) $
                        lu
  where lu | n0 <= n1  = Map.lookup (n0,n1) (edgeLabels g)
           | otherwise = Map.lookup (n1,n0) (edgeLabels g)

-----------------------------------------------------------------------------------------
-- Query

-- | Are the node-/edge-maps of the graph all empty?
isNull (Graph ograph igraph nlgr elgr b _) = I.null ograph && I.null igraph && I.null nlgr && Map.null elgr

-- | The word32 keys of the node labels
nodes (Graph ograph igraph nlgr elgr b _) = I.keys nlgr

-- | List of (Node, Node)
edges (Graph ograph igraph nlgr elgr b _) = Map.keys elgr


-- | The list of adjacent edges can be divided with 8 bit attributes and all edges with a certain attribute selected
adjacentNodesByAttr :: EdgeAttribute el => Graph nl el -> Bool -> Node -> Edge8 -> VU.Vector Node
adjacentNodesByAttr graph out node (Edge8 attr) = -- Debug.Trace.trace ("adjNByA(n,str,val)"++ show (node,Edge8 attr,val)) $
                                                  maybe VU.empty (VU.fromList . Set.toList) val
  where
    val = I.lookup key (if out then outgoingNodes graph else incomingNodes graph)
    key | is32BitInt graph = fromIntegral (buildWord32 node attr)
        | otherwise        = fromIntegral (buildWord64 node (fromIntegral attr))


-- | Looking at all incoming and outgoing edges we get all adjacent nodes
adjacentNodes :: EdgeAttribute el => Graph nl el -> Node -> el -> [Node]
adjacentNodes graph node someEdge = -- Debug.Trace.trace "adjacentNodes" $
    VU.toList $
    VU.concat $ (map (adjacentNodesByAttr graph True node) bs) ++
                (map (adjacentNodesByAttr graph False node) bs)
  where bs = bases someEdge


-- | Following the outgoing edges
children :: EdgeAttribute el => Graph nl el -> Node -> el -> VU.Vector Node
children graph node someEdge = -- Debug.Trace.trace "children" $
    VU.concat (map (adjacentNodesByAttr graph True node) bs)
  where bs = bases someEdge


-- | Following the incoming edges
parents :: EdgeAttribute el => Graph nl el -> Node -> el -> VU.Vector Node
parents graph node someEdge = -- Debug.Trace.trace "parents" $
    VU.concat (map (adjacentNodesByAttr graph False node) bs)
  where bs = bases someEdge

-------------------------------------------------------------------------
-- Bit Operations

-- | Concatenate two Word32 to a Word (64 bit)
{-# INLINE buildWord64 #-}
buildWord64 :: Word32 -> Word32 -> Word
buildWord64 w0 w1
    = unsafePerformIO . allocaBytes 8 $ \p -> do
        pokeByteOff p 0 w0
        pokeByteOff p 4 w1
        peek (castPtr p)


-- | Extract the first 32 bit of a 64 bit word
{-# INLINE extractFirstWord32 #-}
extractFirstWord32 :: Word -> Word32
extractFirstWord32 w
    = unsafePerformIO . allocaBytes 4 $ \p -> do
        pokeByteOff p 0 w
        peek (castPtr p)


-- | Extract the second 32 bit of a 64 bit word
{-# INLINE extractSecondWord32 #-}
extractSecondWord32 :: Word -> Word32
extractSecondWord32 w
    = unsafePerformIO . allocaBytes 4 $ \p -> do
        pokeByteOff p 0 w
        peek (castPtr (plusPtr p 4))

--------------------------------------------------
-- Javascript does not support 64 bit Ints, we have to use 32 bit

-- | Nodes can use 24 bits, edges 8 bits
buildWord32 :: Word32 -> Word8 -> Word32
buildWord32 w0 w1
    = unsafePerformIO . allocaBytes 4 $ \p -> do
        pokeByteOff p 0 w0
        pokeByteOff p 3 w1
        peek (castPtr p)


-- | Extract the first 24 bit of a 32 bit word
{-# INLINE extractFirstWord24 #-}
extractFirstWord24 :: Word32 -> Word32
extractFirstWord24 w = w .&. 0xFFFFFF


-- | Extract the last 8 bit of a 32 bit word
{-# INLINE extractSecondWord8 #-}
extractSecondWord8 :: Word32 -> Word8
extractSecondWord8 w
    = unsafePerformIO . allocaBytes 1 $ \p -> do
        pokeByteOff p 0 w
        peek (castPtr (plusPtr p 3))

------------------------------------------------------------------
-- Debugging

-- | Display a 64 bit word so that we can see the bits better
showHex :: Word -> String
showHex n = showIt 16 n ""
   where
    showIt :: Int -> Word -> String -> String
    showIt 0 _ r = r
    showIt i x r = case quotRem x 16 of
                       (y, z) -> let c = intToDigit (fromIntegral z)
                                 in c `seq` showIt (i-1) y (c:r)


-- | Display a 32 bit word so that we can see the bits better
showHex32 :: Word32 -> String
showHex32 n = showIt 8 n ""
   where
    showIt :: Int -> Word32 -> String -> String
    showIt 0 _ r = r
    showIt i x r = case quotRem x 16 of
                       (y, z) -> let c = intToDigit (fromIntegral z)
                                 in c `seq` showIt (i-1) y (c:r)

