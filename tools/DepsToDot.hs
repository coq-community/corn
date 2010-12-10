#! /usr/bin/env runhaskell

{-# LANGUAGE UnicodeSyntax, ViewPatterns #-}
{-# OPTIONS_GHC -Wall #-}

import Data.Graph.Inductive
  (reachable, delEdge, mkGraph, nmap, Edge, Gr, DynGraph, UEdge, LEdge, efilter, LNode, labNodes, Graph, delNodes)
import Data.GraphViz
  (Attribute(..), Label(..), printDotGraph, nonClusteredParams, graphToDot, fmtNode, Color(..), X11Color(..))
import Data.List (nub, elemIndex, isSuffixOf, isPrefixOf, stripPrefix)
import Control.Monad (liftM2)
import Data.Maybe (fromJust)

import Prelude hiding ((.))

(.) :: Functor f ⇒ (a → b) → (f a → f b)
(.) = fmap

dropBack :: Int → [a] → [a]
dropBack n = reverse . drop n . reverse

uedge :: LEdge a → Edge
uedge (x, y, _) = (x, y)

nfilter :: Graph gr ⇒ (LNode a → Bool) → gr a b → gr a b
nfilter p g = delNodes (map fst $ filter (not . p) $ labNodes g) g

untransitive :: DynGraph gr ⇒ gr a b → gr a b
untransitive g = efilter (not . redundant . uedge) g
  where redundant e@(from, to) = to `elem` reachable from (delEdge e g)

read_deps :: String → Gr FilePath ()
read_deps input = mkGraph (zip [0..] nodes) edges
  where
    content :: [(FilePath, FilePath)]
    content = do
      (left, _ : right) ← break (==':') . lines input
      liftM2 (,) (words left) (words right)
    nodes :: [FilePath]
    nodes = nub $ map fst content ++ map snd content
    edges :: [UEdge]
    edges = map (\(from, to) →
      (fromJust $ elemIndex from nodes, fromJust $ elemIndex to nodes, ())) content

cut_dotvo :: String → String
cut_dotvo = dropBack 3

label :: FilePath → [Attribute]
label (stripPrefix "MathClasses/" → Just rest) = [Label (StrLabel (cut_dotvo rest))]
label p =
  [ Label (StrLabel (cut_dotvo p))
  , Color [X11Color color]
  , LabelFontColor (X11Color color)
  ]
  where
    color :: X11Color
    color
      | "model/" `isPrefixOf` p = Magenta
      | "ftc/" `isPrefixOf` p = Gold3
      | "fta/" `isPrefixOf` p = Green
      | "reals/" `isPrefixOf` p = Cyan4
      | "transc/" `isPrefixOf` p = Blue
      | "reals/fast/" `isPrefixOf` p = Blue4
      | "complex/" `isPrefixOf` p = BlueViolet
      | "metric2/" `isPrefixOf` p = Red
      | "metrics/" `isPrefixOf` p = Red4
      | "tactics/" `isPrefixOf` p = Gray
      | "logic/" `isPrefixOf` p = Chocolate
      | "raster/" `isPrefixOf` p = Yellow
      | "order/" `isPrefixOf` p = Orange
      | "coq_reals/" `isPrefixOf` p = OliveDrab
      | otherwise = Black

main :: IO ()
main = interact $
  printDotGraph .
  graphToDot (nonClusteredParams {fmtNode = snd}) .
  nmap label .
  untransitive .
  nfilter (isSuffixOf ".vo" . snd) .
  read_deps
