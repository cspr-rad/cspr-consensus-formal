import Mathlib.Data.Set.Finite

class StateId (α : Type) extends Inhabited α, BEq α, Repr α, Fintype α

variable {α : Type} [StateId α] [αFintype : Fintype α]

structure Time where
  time : Nat
  deriving Inhabited, DecidableEq, BEq, Repr

instance LETime : LE Time where
  le t1 t2 := t1.time ≤ t2.time

instance HAddTime : HAdd Time Time Time where
  hAdd t1 t2 := { time := t1.time + t2.time }

structure Node where
  id : α
deriving Inhabited, DecidableEq, BEq, Repr

theorem Node.mk_injective : @Function.Injective α  (@Node α) Node.mk := by apply Node.mk.inj
def Node.mkEmbedding : Function.Embedding α (@Node α) := Function.Embedding.mk Node.mk Node.mk_injective

instance nodeFintype : Fintype (@Node α) where
  elems := Finset.map Node.mkEmbedding αFintype.elems
  complete := by
    intro x
    apply Finset.mem_map.mpr
    simp [Node.mkEmbedding]
    exists x.id
    apply And.intro
    · apply αFintype.complete
    · rfl

structure Nodes where
  collection : Finset (@Node α)
  invariant : collection.card > 3

def Nodes.card (nodes : @Nodes α) : Nat := nodes.collection.card

structure Network where
  nodes : @Nodes α
  faultTolerance : Nat
  globalSynchronizationT : Time
  invariant : nodes.card > 3 * faultTolerance

def Network.quorumSize (net : @Network α) : Nat := 1 + (net.nodes.card + net.faultTolerance) / 2
