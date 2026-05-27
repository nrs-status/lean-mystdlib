import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Data.Rel

namespace Digraph

def edgeSetEmbedding (V : Type*) : Digraph V ↪o Set (V × V) :=
  OrderEmbedding.ofMapLEIff (Function.uncurry ·.Adj) fun g g' =>
    ⟨by intro h v w h'; apply @h ⟨v, w⟩ h', by rintro h ⟨v, w⟩ h'; apply h h'⟩

def edgeSet (G : Digraph V) : Set (V × V) :=
  edgeSetEmbedding V G

def edgeFinset {G : Digraph V} [Fintype G.edgeSet] : Finset (V × V) :=
  Set.toFinset G.edgeSet


def support (G : Digraph V) : Set V :=
  SetRel.dom {(u, v) : V × V | G.Adj u v} ∪ SetRel.cod {(u, v) : V × V | G.Adj u v}


