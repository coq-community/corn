module Main where

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

{- We assume graphs are acylcic -}
type DiGraph a = Map.Map a (Set.Set a)

nodes g = Set.toList $ Set.unions ((Map.keysSet g):(Map.elems g))

edges g = [(a,b) | (a,s)<-Map.toList g, b<-Set.toList s]

nodeFilter p g = Map.mapMaybeWithKey f g
 where
  f a s | p a = Just (h s)
        | otherwise = Nothing
  h = Set.fold h' Set.empty
  h' x s | p x = Set.insert x s
        | otherwise =
   Set.union (h (Map.findWithDefault Set.empty x g))
             s

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

untransitive :: (Ord a) => DiGraph a -> DiGraph a
untransitive g = Map.mapWithKey p g
 where
  p a s = Set.filter (f a) s
  f a b = b `notMember`
   reachable g 
    (Set.delete b (Map.findWithDefault Set.empty a g))

processLine l = (header, Set.fromList rest)
 where
  header:rest = filter (\x -> takeExtension x == ".vo") $ words l

name = dropExtension . takeFileName

colourNode a = "\""++(name a)++"\" ["++(colourize a)++"]"
 where
  colourize a = "color = \""++(colour (dropFileName a))++"\" "++
                "fontcolor = \""++(colour (dropFileName a))++"\""

printLine (a,b) = "\""++(name a)++"\" -> \""++(name b)++"\" ["++(colourize a)++"]"
 where
  colourize a = "color = \""++(colour (dropFileName a))++"\""

main = do
 args <- getArgs
 dep <- fmap lines getContents
 let graph = nodeFilter (not . dropNode args) $ 
             Map.fromList $ map processLine dep
 let outputNodes = map colourNode $ nodes graph
 let outputEdges = map printLine $ edges $ untransitive graph
 putStrLn "digraph tree {"
 putStr $ unlines outputNodes
 putStr $ unlines outputEdges
 putStrLn "}"