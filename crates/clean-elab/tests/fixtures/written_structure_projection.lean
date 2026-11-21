universe u v

structure ProjectionBox (α : Type u) (β : Type v) where
  left : α
  right : β
  pos : Nat
  previous : Nat
  valid : pos = pos

inductive ProjectionPacket (α : Type u) where
  | mk : Nat → α → ProjectionPacket α

def writtenNamed {α : Type u} {β : Type v} (p : ProjectionBox α β) : β := p.right
def writtenOrdinal {α : Type u} {β : Type v} (p : ProjectionBox α β) : β := p.2
def writtenQualified {α : Type u} {β : Type v} (p : ProjectionBox α β) : β := @ProjectionBox.right α β p
def writtenDependent {α : Type u} {β : Type v} (p : ProjectionBox α β) : p.pos = p.pos := p.valid
def plainOrdinal {α : Type u} (p : ProjectionPacket α) : α := p.2
theorem projectedValue : (ProjectionBox.mk 7 3 9 2 rfl).previous = 2 := rfl
