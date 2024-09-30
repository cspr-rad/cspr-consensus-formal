import Mathlib.Data.Set.Finite
import Zug.Network

class Value (β : Type) extends Inhabited β, BEq β, Repr β

variable {β : Type} [βValue : Value β]

structure Message where
  sender : @Node α
  receiver : @Node α
  payload : β
  sendTime : Time

structure NetworkModel where
  messageDelay : @Network α → @Message β → Time
  deliverMessage : @Network α → @Message β → (@Node α → Time) → Prop
  isPartiallySynchronous : @Network α → Prop :=
    λ net => ∃ δ : Time, ∀ (t : Time) (m : @Message β),
      t ≥ net.globalSynchronizationT → deliverMessage net m (λ _ => t + δ)

class Protocol (β : Type) [Value β] where
  input : @Network α → @Node α → Option β
  output : @Network α -> @Node α -> Option β
  is_correct : @Network α -> @Node α -> Prop
  /-- continuation for eventual properties -/
  eventually : (@Network α -> Prop) -> Prop
  /-- If any correct node outputs v, every corect node will eventually output v -/
  agreement : forall (net : @Network α) (n1 n2 : @Node α) (v : β),
    is_correct net n1 -> is_correct net n2 ->
    @output α net n1 = some v ->
    @eventually α (fun _ => @output α net n2 = some v)

instance BoolValue : Value Bool := by constructor

class WBA extends Protocol Bool where
  /-- If the correct nodes output b, more than q - f correct validators had input b -/
  validity : forall (net : @Network α) (n : @Node α) (b : Bool),
    is_correct net n ->
    @output α net n = some b ->
    Fintype.card {n0 : net.nodes.collection // @input α net n0 = some b} > net.quorumSize - net.faultTolerance
  /-- If more than q correct validators have input b, the correct nodes eventually output b -/
  weak_termination : forall (net : @Network α) (b : Bool),
    Fintype.card {n : net.nodes.collection // @input α net n = some b /- should be and is_correct net n, but bug. -/} > net.quorumSize ->
    forall n0, is_correct net n0 ->
    @eventually α (fun _ => @output α net n0 = some b)

class RB (β : Type) [Value β] extends Protocol β where
  /-- If the proposer is correct and has input v, the correct nodes eventually output v -/
  weak_termination : 1 = 1 -- TODO
  -- need a story for eventually first

class AB (β : Type) [Value β] extends Protocol β where
  /-- If any correct node outputs v before w, all correct nodes output v before w -/
  total_order : 1 = 1 -- TODO
  /-- Every input v to a corect proposer is eventually output by the correct nodes -/
  censorship_resilience : 1 = 1 -- TODO

structure RoundIdx where
  round : Nat
  deriving BEq, Repr

def round (protocol : Protocol β) (r : RoundIdx) : β × Option RoundIdx := (Inhabited.default, some $ RoundIdx.mk 0)

def transform (w_binary_agreement : WBA) (reliable_broadcast : RB β) : AB β :=
  by sorry
