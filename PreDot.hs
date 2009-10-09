module Main where

{-
Copyright (c) 2008 Russell O'connor

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
-}
{-
This program takes from standard input dependency files for Coq and
outputs a dot file (for graphviz) that diagrams the dependencies.

An un-transitive-closure algorithm is applied to dependecies to remove
edges A -> Z when some series of edges A -> B -> C -> ... -> Z already
exists.

This program takes command line arguments a list of directories.  Modules
in these directories will be removed from the output diagram.  Edges
going to removed modules will be redirected to the children of the module
being removed.

This program is just something I hacked together.  Feel free to completely
replace it if you cannot figure out how to modify it.
-}

import Data.List (isPrefixOf, isSuffixOf, isInfixOf)
import qualified Data.Set as Set
import Data.Set ((\\), notMember)
import qualified Data.Map as Map
import System.FilePath
import System.Environment

colour x | "/model/" `isInfixOf` x = "magenta"
         | "/ftc/" `isSuffixOf` x = "gold3"
         | "/fta/" `isSuffixOf` x = "green"
         | "/reals/" `isSuffixOf` x = "cyan4"
         | "/transc/" `isSuffixOf` x = "blue"
         | "/reals/fast/" `isSuffixOf` x = "blue4"
         | "/complex/" `isSuffixOf` x = "blueviolet"
         | "/metric2/" `isSuffixOf` x = "red"
         | "/metrics/" `isSuffixOf` x = "red4"
         | "/tactics/" `isSuffixOf` x = "gray"
         | "/logic/" `isSuffixOf` x = "chocolate"
         | "/raster/" `isSuffixOf` x = "yellow"
         | "/order/" `isSuffixOf` x = "orange"
         | "/coq_reals/" `isSuffixOf` x = "olivedrab"
         | otherwise = "black"

dropNode l x = any (`isInfixOf` (dropFileName x)) l

-- assume graphs are acylcic
type DiGraph a = Map.Map a (Set.Set a)

nodes :: (Ord a) => DiGraph a -> [a]
nodes g = Set.toList $ Set.unions ((Map.keysSet g):(Map.elems g))

edges :: (Ord a) => DiGraph a -> [(a,a)]
edges g = [(a,b) | (a,s)<-Map.toList g, b<-Set.toList s]

nodeFilter :: (Ord a) => (a -> Bool) -> DiGraph a -> DiGraph a
nodeFilter p g = Map.mapMaybeWithKey f g
 where
  f a s | p a = Just (h s)
        | otherwise = Nothing
  h = Set.fold h' Set.empty
  h' x s | p x = Set.insert x s
        | otherwise =
   Set.union (h (Map.findWithDefault Set.empty x g))
             s

-- Find all the nodes reachable from a set of nodes in a graph
reachable :: (Ord a) => DiGraph a -> (Set.Set a) -> (Set.Set a)
reachable graph l = reachableHelp graph Set.empty l
reachableHelp graph visted l | Set.null children = visted'
                             | otherwise = 
  reachableHelp graph visted' children
 where
  children = 
   join (Set.map (flip (Map.findWithDefault Set.empty) graph) l) \\
    visted
  join = Set.unions . Set.toList
  visted' = Set.union visted l

-- this removes direct edges A -> Z if there already exists an indirect
-- connection from A to Z.
untransitive :: (Ord a) => DiGraph a -> DiGraph a
untransitive g = Map.mapWithKey p g
 where
  p a s = Set.filter (f a) s
  f a b = b `notMember`
   reachable g 
    (Set.delete b (Map.findWithDefault Set.empty a g))

-- process a line of dependency information.  Return (a,s) where s is the set
-- of children of a
processLine l = (rmnewsuffix header, Set.fromList rest)
 where
  rmnewsuffix s = let (base, ext) = splitExtension s in
                  if ext == ".new" then base else s
  header:rest = filter f $ words l
   where
    f = \x -> let (base, ext)=splitExtension x in
              ext == ".vo" || ( ext == ".new" && takeExtension base == ".vo" )

name = dropExtension . takeFileName

-- a colour node output format for dot files.
colourNode a = "\""++(name a)++"\" ["++(colourize a)++"]"
 where
  colourize a = "color = \""++(colour (dropFileName a))++"\" "++
                "fontcolor = \""++(colour (dropFileName a))++"\""

-- a colour edge output format for dot files
colourEdge (a,b) = "\""++(name a)++"\" -> \""++(name b)++"\" ["++(colourize a)++"]"
 where
  colourize a = "color = \""++(colour (dropFileName a))++"\""

main = do
 args <- getArgs
 dep <- fmap lines getContents
 let graph = nodeFilter (not . dropNode args) $ 
             Map.fromList $ map processLine dep
 let outputNodes = map colourNode $ nodes graph
 let outputEdges = map colourEdge $ edges $ untransitive graph
 putStrLn "digraph tree {"
 putStr $ unlines outputNodes
 putStr $ unlines outputEdges
 putStrLn "}"