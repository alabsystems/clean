module
public def ModProbe.visible : Nat := 1
private def ModProbe.hidden : Nat := 2
def ModProbe.internal : Nat := ModProbe.hidden + 1
