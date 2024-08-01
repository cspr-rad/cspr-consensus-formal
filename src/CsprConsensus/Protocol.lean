import CsprConsensus.Network

class Value (β : Type) extends Inhabited β, BEq β, Repr β

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
  validity : 1 = 1 := by rfl -- TODO
  /-- If more than q correct validators have input b, the correct nodes eventually output b -/
  weak_termination : 1 = 1 := by rfl -- TODO
